#!/usr/bin/env python3
"""Marge du fine-tuning LoRA sur le gate de Phase 3 (brique 3, #20359 ; EPIC #10355).

La brique 2 (#20244) a fixe la premesse : le zero-shot du 0,6B est inutilisable comme
reference (macro-F1 0,0145, accord positionnel 16,8 %, verdict INCONCLUSIVE), et le rung
ladder a eteint l'axe echelle (0,5B a 4B zéro-shot vivent sous le random). Cette brique
mesure la contrepartie : **ou se pose le meme modele apres fine-tuning LoRA sur le corpus
teacher**, aux memes plis, avec la meme lecture et le meme controle de biais.

Pourquoi c'est falsifiable : si le FT ne decolle pas non plus la lexicale (0,2198, brique
1), le corpus ne porte pas de signal apprenable par la famille cible et le gate se
recalibre ; s'il decolle, la marge FT est reelle et le seuil du gate se cale sur elle.

Quatre decisions portent l'instrument, chacune verifiable :

1. **Les organes des briques 1-2 sont reutilises, pas reimplementes.** Corpus, plis
   groupes, macro-F1 (brique 1), prompt, rotation d'options, lecture argmax des lettres
   et chargement du modele (brique 2) viennent d'imports. Le FT n'ecrit que ce que le
   zero-shot n'avait pas : la boucle d'entrainement et le reset par pli.

2. **L'entrainement cible le token-lettre, pas une generation libre.** Meme contract de
   lecture que l'inference : la loss est l'entropie croisee du logit du token-lettre
   correct a la position de reponse. Le modele apprend exactement ce que la mesure lit.

3. **Le reset par pli est explicite.** Chaque pli repart du modele de base intact :
   l'adapter LoRA est monte en debut de pli et decharge (`unload`) en fin de pli --
   un poids LoRA du pli precedent ne peut pas fuir dans le pli suivant. Les poids du
   modele de base ne sont jamais modifies (LoRA gèle tout sauf les adapters).

4. **Le protocole est fixe, pas tuné sur le test.** Hyperparametres par defaut constants
   (r=16, alpha=32, dropout 0,05, 3 epochs, lr 2e-4, batch 4), consignes au rapport ;
   aucune early stopping sur la metrique du pli test. La courbe de loss par epoch et par
   pli est publiee dans les artefacts hors depot.

Le modele par defaut est le checkpoint epingle du run #20244 : ``Qwen/Qwen3-0.6B`` @
``c1899de289a04d12100db370d81485cdf75e47ca`` (criteres 1 de #20244 et #20359 : nom ET
sha du checkpoint). L'inference et l'entrainement sont CPU-tolerants ; torch et peft
sont des dependances d'execution en import tardif, jamais du depot.

Usage::

    python scripts/fallacy_detection/ft_floor.py \
        --corpus MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl \
        --out-dir d:/dev/coursia-out/fallacy-ft \
        --level branch --folds 5 --seed 42 --model Qwen/Qwen3-0.6B \
        --revision c1899de289a04d12100db370d81485cdf75e47ca
"""

from __future__ import annotations

import argparse
import contextlib
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
    from .zeroshot_floor import (  # type: ignore[attr-defined]
        agreement_rate,
        build_prompt,
        letter_token_ids,
        load_model,
        rotate_order,
        score_item,
        sha256_of,
    )
else:
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from baseline_branch_detection import (
        LEVEL_FIELDS,
        evaluate,
        grouped_folds,
        load_corpus,
    )
    from zeroshot_floor import (
        agreement_rate,
        build_prompt,
        letter_token_ids,
        load_model,
        rotate_order,
        score_item,
        sha256_of,
    )

#: Hyperparametres du protocole fixe (#20359, critere 6 : consignes, pas tunes).
LORA_RANK = 16
LORA_ALPHA = 32
LORA_DROPOUT = 0.05
LORA_TARGETS = ["q_proj", "v_proj"]
EPOCHS = 3
LEARNING_RATE = 2e-4
BATCH_SIZE = 4


def target_letter(label: str, ordered_labels: list[str]) -> str:
    """Lettre d'option de l'etiquette dans l'ordre transmis (bras fixe : ordre trie).

    La cible d'entrainement est le token de cette lettre : le modele apprend a monter
    le logit de la lettre correcte a la position de reponse, exactement ce que la
    mesure lit ensuite par argmax.
    """
    return chr(ord("A") + ordered_labels.index(label))


def mount_lora(base_model, rank: int = LORA_RANK, alpha: int = LORA_ALPHA,
               dropout: float = LORA_DROPOUT,
               targets: list[str] | None = None):
    """Monte l'adapter LoRA sur le modele de base ; peft en import tardif.

    L'absence de peft est une erreur nominale, pas un traceback (meme contract que
    torch dans la brique 2). Le modele de base reste gele : seuls les adapters portent
    des poids entrainables.
    """
    try:
        from peft import LoraConfig, get_peft_model
    except ImportError as exc:  # pragma: no cover - depend de l'environnement
        raise SystemExit(
            f"Fine-tuning indisponible : {exc}. Installer peft dans l'environnement "
            "d'execution ; le depot n'ajoute aucune dependance."
        ) from exc
    config = LoraConfig(
        r=rank,
        lora_alpha=alpha,
        lora_dropout=dropout,
        target_modules=list(targets or LORA_TARGETS),
        bias="none",
        task_type="CAUSAL_LM",
    )
    return get_peft_model(base_model, config)


@contextlib.contextmanager
def fold_scope(base_model):
    """Un pli d'entrainement : adapter monte en entree, decharge en sortie.

    ``unload`` demonte les wrappers LoRA et rend le modele de base avec ses poids
    originaux -- le pli suivant repart de la meme base, sans fuite d'adapter.
    """
    import torch  # noqa: F401 - echec nominal si torch absent

    peft_model = mount_lora(base_model)
    try:
        yield peft_model
    finally:
        # Le contrat de ``peft`` ``unload()`` : demonte les wrappers LoRA et rend
        # le modele de base avec ses poids originaux. Contrat documente de peft,
        # non verifie par assert : l'identite d'objet rendue depend de la version.
        peft_model.unload()


def letter_batches(n: int, batch_size: int, seed: int, epoch: int = 0) -> list[list[int]]:
    """Index d'items par lot, ordre melange deterministe par (graine, epoch).

    Chaque epoch recoit sa propre permutation -- derivee de
    ``f"{seed}:train:{epoch}"``, reproductible sans etat global : meme graine et
    meme epoch donnent toujours le meme ordre, deux epochs distinctes ne
    partagent pas la permutation.
    """
    order = list(range(n))
    random.Random(f"{seed}:train:{epoch}").shuffle(order)
    return [order[i:i + batch_size] for i in range(0, n, batch_size)]


def train_letter_token(peft_model, tokenizer, text: str, label: str,
                       ordered_labels: list[str], token_ids: dict[str, int]):
    """Une passe avant + arriere sur un item : entropie croisee du token-lettre cible.

    Le render est identique a l'inference (``build_prompt`` + chat template, thinking
    desactive) ; la loss porte uniquement le logit du token-lettre correct a la
    position suivante. La valeur est retournee pour la courbe de loss.
    """
    import torch
    import torch.nn.functional as F

    prompt = build_prompt(text, ordered_labels)
    rendered = tokenizer.apply_chat_template(
        [{"role": "user", "content": prompt}],
        tokenize=False,
        add_generation_prompt=True,
        enable_thinking=False,
    )
    inputs = tokenizer(rendered, return_tensors="pt")
    target_id = token_ids[target_letter(label, ordered_labels)]
    logits = peft_model(**inputs).logits[0, -1]
    loss = F.cross_entropy(logits.unsqueeze(0),
                           torch.tensor([target_id], dtype=torch.long))
    loss.backward()
    return float(loss.detach())


def run(corpus_path: Path, out_dir: Path, level: str, folds_count: int, seed: int,
        model_name: str, limit: int | None = None,
        revision: str | None = None) -> dict:
    """Mesure la marge FT LoRA sur le corpus de reference des baselines."""
    items = load_corpus(corpus_path, level)
    if limit:
        items = items[:limit]
    labels = sorted(set(item["label"] for item in items))
    folds = grouped_folds(items, folds_count)
    out_dir.mkdir(parents=True, exist_ok=True)
    log_path = out_dir / "predictions_ft.jsonl"
    log_path.write_text("", encoding="utf-8")

    tokenizer, model, revision_resolved = load_model(model_name, revision=revision)
    token_ids = letter_token_ids(tokenizer, labels)
    state = {"index": 0}
    handle = log_path.open("a", encoding="utf-8")
    loss_curve: dict[int, list[list[float]]] = {}

    def argmax_label(distribution: dict[str, float], ordered: list[str]) -> str:
        letter = max(sorted(distribution), key=lambda l: distribution[l])
        return ordered[ord(letter) - ord("A")]

    def predict(train_items, test_items, fold: int) -> list[str]:
        import torch

        loss_curve[fold] = []
        started_fold = time.monotonic()
        with fold_scope(model) as peft_model:
            optimizer = torch.optim.AdamW(
                (p for p in peft_model.parameters() if p.requires_grad),
                lr=LEARNING_RATE,
            )
            peft_model.train()
            for epoch in range(EPOCHS):
                epoch_losses: list[float] = []
                batches = letter_batches(len(train_items), BATCH_SIZE, seed, epoch=epoch)
                for batch in batches:
                    optimizer.zero_grad()
                    for idx in batch:
                        item = train_items[idx]
                        epoch_losses.append(train_letter_token(
                            peft_model, tokenizer, item["text"], item["label"],
                            labels, token_ids))
                    optimizer.step()
                loss_curve[fold].append([round(l, 4) for l in epoch_losses])
                print(
                    f"  [pli {fold}] epoch {epoch + 1}/{EPOCHS} : "
                    f"loss moyenne {sum(epoch_losses) / len(epoch_losses):.4f}",
                    file=sys.stderr,
                )
            peft_model.eval()
            predictions: list[str] = []
            for item in test_items:
                started = time.monotonic()
                fixed = score_item(tokenizer, peft_model, item["text"], labels,
                                   token_ids)
                rotated_order = rotate_order(labels, f"{seed}:{state['index']}")
                rotated = score_item(tokenizer, peft_model, item["text"],
                                     rotated_order, token_ids)
                elapsed = time.monotonic() - started
                fixed_label = argmax_label(fixed, labels)
                rotated_label = argmax_label(rotated, rotated_order)
                predictions.append(fixed_label)
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
                    f"  [{state['index']}|pli {fold}] {item['label'][:22]:<22} -> "
                    f"{fixed_label[:22]:<22} agree={fixed_label == rotated_label} "
                    f"({elapsed:.1f}s)",
                    file=sys.stderr,
                )
        print(
            f"  [pli {fold}] fait en {time.monotonic() - started_fold:.0f}s "
            f"(adapter decharge, base intacte)",
            file=sys.stderr,
        )
        return predictions

    result = evaluate(predict, items, folds)
    handle.close()

    report = {
        "issue": "Phase 3 brique 3 : marge FT LoRA (#20359, EPIC #10355)",
        "corpus": {
            "path": str(corpus_path),
            "sha256": sha256_of(corpus_path),
            "rows": len(items),
        },
        "model": model_name,
        "model_revision": revision_resolved,
        "model_revision_pinned": revision,
        "level": level,
        "seed": seed,
        "folds": folds_count,
        "lora": {
            "rank": LORA_RANK,
            "alpha": LORA_ALPHA,
            "dropout": LORA_DROPOUT,
            "targets": LORA_TARGETS,
            "epochs": EPOCHS,
            "learning_rate": LEARNING_RATE,
            "batch_size": BATCH_SIZE,
            "reset_per_fold": "mount/unload (base intacte)",
        },
        "measure": "loss = CE du token-lettre cible ; prediction = logit argmax "
                   "sur les 14 tokens-lettres a la position de reponse",
        "loss_curve_per_fold": loss_curve,
        "bias_control": {
            "arm": "ordre des options tourne par graine derivee (seed:index)",
            "agreement_rate": agreement_rate(log_path),
        },
        "ft": result,
        "references": {
            "zero_shot": "brique 2 (#20244) : macro-F1 0,0145, accord 16,8 %",
            "lexicale": "brique 1 (#20233) : macro-F1 0,2198",
        },
    }
    report_path = out_dir / "ft_report.json"
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
                        help="Graine protocolaire (plis groupes, rotations, ordre "
                             "d'entrainement).")
    parser.add_argument("--model", default="Qwen/Qwen3-0.6B")
    parser.add_argument("--revision", default=None,
                        help="Commit HF epingle pour le modele (le run #20244 : "
                             "c1899de289a04d12100db370d81485cdf75e47ca). Sans epinglage, "
                             "la revision resolue est quand meme consignee au rapport.")
    parser.add_argument("--limit", type=int, default=None,
                        help="Borne de fumee (mesure partielle, a declarer non conclusive).")
    args = parser.parse_args(argv)
    run(args.corpus, args.out_dir, args.level, args.folds, args.seed, args.model,
        args.limit, revision=args.revision)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
