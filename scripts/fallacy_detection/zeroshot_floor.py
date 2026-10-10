#!/usr/bin/env python3
"""Plancher zero-shot du gate de Phase 3 (brique 2, #20244 ; EPIC #10355).

Les baselines de #20233 fixent les references du gate (majoritaire, aleatoire, a
regles, lexicale). Cette brique mesure la reference qui manquait : **ou se pose un
modele instruct non entraine de la famille cible** sur le meme corpus, aux memes plis.

Pourquoi c'est falsifiable : si le zero-shot du plus petit Qwen instruct reste sous la
baseline lexicale, la marge du fine-tuning est reelle et le gate est sain tel quel ;
s'il la depasse largement, le seuil du gate mesure autre chose que l'apport de
l'entrainement -- a savoir avant le premier FT, pas apres.

Quatre decisions portent l'instrument, chacune verifiable :

1. **Les organes existants sont reutilises, pas reimplementes.** Le chargement du
   corpus, les plis groupes par scenario et le calcul de macro-F1 viennent de
   `baseline_branch_detection` (brique 1). Le zero-shot ne reecrit aucun d'eux.

2. **La mesure lit les logits des lettres, pas une generation libre.** Le smoke et un
   diagnostic (consignes dans l'issue) ont mesure deux defauts de la generation libre
   sur un 0,6B : degenerescence en lettre constante (reponse « E » sur 8 items sur 9,
   familles evidentes comprises) et piege de lecture (une prose francaise « L'option
   correspondante est : ... » se resout faussement en lettre « L »). La mesure v2
   fait une seule passe avant par item et prend l'argmax des 14 logits de
   tokens-lettres a la position de reponse : deterministe, sans piege de parse, et la
   distribution complete sur les 14 lettres est consignee par item.

3. **Le biais positionnel est mesure, pas suppose.** Chaque item est evalue deux fois :
   options triees (bras fixe) et options dans un ordre tourne par graine derivee
   (graine protocolaire + index d'item, consigne). Le taux d'accord entre bras est une
   grandeur publiee du rapport : un accord eleve dit que le signal est de contenu, un
   accord bas dit que le biais positionnel domine et le verdict est INCONCLUSIF avec
   cette preuve en main.

4. **Le predicat zero-shot n'apprend rien des plis.** `evaluate` lui donne un pli
   d'entrainement comme aux autres predicats ; il l'ignore, et c'est documente : la
   variance inter-plis du zero-shot mesure le decoupage, pas un quelconque entrainement.

Le modele par defaut est `Qwen/Qwen3-0.6B`, le plus petit instruct eligible de la
famille Qwen3 presente sur le Hub a jour de cette brique. L'inference est CPU.

Usage::

    python scripts/fallacy_detection/zeroshot_floor.py \
        --corpus MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl \
        --out-dir d:/dev/coursia-out/fallacy-zeroshot \
        --level branch --folds 5 --seed 42 --model Qwen/Qwen3-0.6B
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import sys
import time
from pathlib import Path

if __package__:
    from .baseline_branch_detection import (  # type: ignore[attr-defined]
        LEVEL_FIELDS,
        evaluate,
        grouped_folds,
        load_corpus,
    )
else:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from baseline_branch_detection import (
        LEVEL_FIELDS,
        evaluate,
        grouped_folds,
        load_corpus,
    )

#: Instruction du prompt. La liste des familles y est inseree, une par ligne.
INSTRUCTION = (
    "Tu es un expert en sophismes. Voici un court dialogue contenant un sophisme. "
    "Identifie la famille de premier niveau du sophisme parmi les familles suivantes,\n"
    "et reponds par la SEULE lettre correspondante, sans autre texte :\n"
    "{options}\n"
    "Dialogue :\n"
    "{text}\n"
    "Reponse (une lettre) :"
)


def build_prompt(text: str, ordered_labels: list[str]) -> str:
    """Construit le prompt de classification fermee ; l'ordre des options est un parametre.

    Le bras fixe passe les etiquettes triees ; le bras tourne passe un ordre derive
    d'une graine. La correspondance lettre-etiquette suit TOUJOURS l'ordre transmis :
    c'est l'appelant qui sait quel ordre il a passe, et le journal consigne l'ordre.
    """
    options = "\n".join(
        f"{chr(ord('A') + i)}. {label}" for i, label in enumerate(ordered_labels)
    )
    return INSTRUCTION.format(options=options, text=text.strip())


def rotate_order(labels: list[str], seed: str) -> list[str]:
    """Tourne l'ordre des options d'une graine textuelle derivee (deterministe)."""
    rotated = list(labels)
    random.Random(seed).shuffle(rotated)
    return rotated


def sha256_of(path: Path) -> str:
    """Empreinte SHA-256 du corpus, lue par blocs (identique a la brique 1)."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_model(model_name: str):
    """Charge le modele en inference CPU ; torch/transformers en import tardif.

    L'import tardif garde le module importable sans torch (les tests hermetiques n'en
    ont pas besoin) ; l'absence de la bibliotheque est une erreur nominale, pas un
    traceback.
    """
    try:
        import torch
        from transformers import AutoModelForCausalLM, AutoTokenizer
    except ImportError as exc:  # pragma: no cover - depend de l'environnement
        raise SystemExit(
            f"Inference zero-shot indisponible : {exc}. Installer torch et transformers "
            "dans l'environnement d'execution ; le depot n'ajoute aucune dependance."
        ) from exc
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForCausalLM.from_pretrained(model_name, dtype=torch.float32)
    model.eval()
    return tokenizer, model


def letter_token_ids(tokenizer, ordered_labels: list[str]) -> dict[str, int]:
    """Identifiants de tokens des lettres d'option ; echoue sur une lettre multi-tokens.

    Un token lettre code A..N seul ; si le tokenizer fragmentait une lettre en
    plusieurs tokens, la lecture par argmax du premier token mesurerait autre chose
    que la distribution sur les options -- l'organe refuse plutot que de mesurer.
    """
    ids: dict[str, int] = {}
    for i in range(len(ordered_labels)):
        letter = chr(ord("A") + i)
        tokens = tokenizer.encode(letter, add_special_tokens=False)
        if len(tokens) != 1:
            raise SystemExit(
                f"Lettre '{letter}' fragmentee en {len(tokens)} tokens : la lecture par "
                "logit du premier token ne mesurerait pas la distribution sur les options."
            )
        ids[letter] = tokens[0]
    return ids


def score_item(tokenizer, model, text: str, ordered_labels: list[str],
               token_ids: dict[str, int]) -> dict[str, float]:
    """Distribution brute (logits) des lettres d'option a la position de reponse.

    Une seule passe avant, aucun decodage : la position suivante du prompt render
    est celle ou le modele emettrait sa reponse, et les logits y sont lus pour
    chacune des lettres d'option. Deterministe par construction.
    """
    import torch

    prompt = build_prompt(text, ordered_labels)
    rendered = tokenizer.apply_chat_template(
        [{"role": "user", "content": prompt}],
        tokenize=False,
        add_generation_prompt=True,
        enable_thinking=False,
    )
    inputs = tokenizer(rendered, return_tensors="pt")
    with torch.no_grad():
        logits = model(**inputs).logits[0, -1]
    return {letter: float(logits[token_id]) for letter, token_id in token_ids.items()}


def predictor_zeroshot(tokenizer, model, labels: list[str], seed: int,
                       log_path: Path | None = None):
    """Predicat zero-shot compatible `evaluate` : ignore le pli d'entrainement.

    Chaque item est score deux fois (bras fixe trie, bras tourne par graine derivee
    de la graine protocolaire et de l'index global d'item -- pas du pli, pour qu'un
    meme item ait le meme ordre tourne quel que soit le decoupage). Le journal
    consigne par item : les deux distributions completes, les deux predictions, la
    duree. L'index global passe par une fermeture sequentielle : `evaluate` appelle
    les plis dans l'ordre, et l'ordre des items dans chaque pli est trire.
    """
    sorted_labels = sorted(labels)
    token_ids = letter_token_ids(tokenizer, sorted_labels)
    state = {"index": 0}
    handle = log_path.open("a", encoding="utf-8") if log_path else None

    def argmax_label(distribution: dict[str, float], ordered: list[str]) -> str:
        letter = max(sorted(distribution), key=lambda l: distribution[l])
        return ordered[ord(letter) - ord("A")]

    def predict(_train_items, test_items, _fold: int) -> list[str]:
        predictions: list[str] = []
        for position, item in enumerate(test_items, start=1):
            started = time.monotonic()
            fixed = score_item(tokenizer, model, item["text"], sorted_labels, token_ids)
            rotated_order = rotate_order(sorted_labels, f"{seed}:{state['index']}")
            rotated = score_item(tokenizer, model, item["text"], rotated_order, token_ids)
            elapsed = time.monotonic() - started
            fixed_label = argmax_label(fixed, sorted_labels)
            rotated_label = argmax_label(rotated, rotated_order)
            predictions.append(fixed_label)
            if handle:
                handle.write(
                    json.dumps(
                        {
                            "index": state["index"],
                            "anchor": item["text"][:60],
                            "label": item["label"],
                            "fixed_scores": fixed,
                            "fixed_pred": fixed_label,
                            "rotated_order": rotated_order,
                            "rotated_scores": rotated,
                            "rotated_pred": rotated_label,
                            "agree": fixed_label == rotated_label,
                            "seconds": round(elapsed, 2),
                        },
                        ensure_ascii=False,
                    )
                    + "\n"
                )
                handle.flush()
            state["index"] += 1
            print(
                f"  [{state['index']}|pli {_fold}] {item['label'][:22]:<22} -> "
                f"{fixed_label[:22]:<22} agree={fixed_label == rotated_label} "
                f"({elapsed:.1f}s)",
                file=sys.stderr,
            )
        return predictions

    return predict


def agreement_rate(log_path: Path) -> float | None:
    """Taux d'accord entre bras fixe et bras tourne, relu depuis le journal."""
    agreements = []
    for line in log_path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            agreements.append(json.loads(line)["agree"])
    return sum(agreements) / len(agreements) if agreements else None


def run(corpus_path: Path, out_dir: Path, level: str, folds_count: int, seed: int,
        model_name: str, limit: int | None = None) -> dict:
    """Mesure le plancher zero-shot sur le corpus de reference des baselines."""
    items = load_corpus(corpus_path, level)
    if limit:
        items = items[:limit]
    labels = sorted(set(item["label"] for item in items))
    folds = grouped_folds(items, folds_count)
    out_dir.mkdir(parents=True, exist_ok=True)
    log_path = out_dir / "predictions_zero_shot.jsonl"
    log_path.write_text("", encoding="utf-8")

    tokenizer, model = load_model(model_name)
    predict = predictor_zeroshot(tokenizer, model, labels, seed=seed, log_path=log_path)
    result = evaluate(predict, items, folds)

    report = {
        "issue": "Phase 3 brique 2 : plancher zero-shot (#20244, EPIC #10355)",
        "corpus": {
            "path": str(corpus_path),
            "sha256": sha256_of(corpus_path),
            "rows": len(items),
        },
        "model": model_name,
        "level": level,
        "seed": seed,
        "folds": folds_count,
        "prompt": INSTRUCTION,
        "labels": labels,
        "measure": "logit argmax sur les 14 tokens-lettres a la position de reponse",
        "bias_control": {
            "arm": "ordre des options tourne par graine derivee (seed:index)",
            "agreement_rate": agreement_rate(log_path),
        },
        "zero_shot": result,
        "baselines_reference": "data/teacher/baselines_branch.json (brique 1, #20233)",
    }
    report_path = out_dir / "zeroshot_report.json"
    report_path.write_text(
        json.dumps(report, indent=1, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, indent=1, ensure_ascii=False))
    print(f"rapport : {report_path}")
    print(f"predictions : {log_path}")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--level", choices=sorted(LEVEL_FIELDS), default="branch")
    parser.add_argument("--folds", type=int, default=5)
    parser.add_argument("--seed", type=int, default=42,
                        help="Graine protocolaire (plis groupes et rotations d'options).")
    parser.add_argument("--model", default="Qwen/Qwen3-0.6B")
    parser.add_argument("--limit", type=int, default=None,
                        help="Borne de fumee (mesure partielle, a declarer non conclusive).")
    args = parser.parse_args(argv)
    run(args.corpus, args.out_dir, args.level, args.folds, args.seed, args.model, args.limit)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
