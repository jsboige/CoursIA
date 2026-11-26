#!/usr/bin/env python3
"""Sonde S0 du corpus PT-22 : probabilité de base du modèle sur les faits fictifs.

Scellé de référence : ``docs/genai/pt16-sleep-dreaming-pre-enregistrement.md``,
section « Corpus de faits et stades » : « noms inventés, jamais vus en
pré-entraînement — vérification par probabilité de base du modèle au stade S0,
à documenter au pilote ».

La sonde tourne sur **CPU seul, hors ligne** (poids déjà en cache) : elle vide
``CUDA_VISIBLE_DEVICES`` avant l'import de torch, donc elle ne touche aucune carte.
Le régime est **float32** ; c'est un écart déclaré avec le scellé, dont les captures
SAE se font en bf16 — cette sonde mesure le prior du modèle de base, pas une lecture
SAE, et ne remplace pas le S0 du pilote.

Règles posées **avant** la mesure (elles ne se recalibrent pas après les résultats) :

* **R0 — aucun nom inventé n'est un jeton unique.** Pour chacun des 180 noms des
  60 faits fictifs (60 prénoms, 60 noms de famille, 60 attributs), le nom vaut au
  moins deux jetons du tokenizer, avec et sans espace initial.
* **R1 — rappel glouton nul.** La réponse gloutonne à la question n'égale l'attribut
  pour aucun des 60 faits fictifs (exactitude 0/60, comparaison normalisée).
* **R2 — le prior est bas sur le premier jeton de la cible.** Le rang du premier
  jeton de l'attribut dépasse 20 pour au moins 54 des 60 faits (90 %) ; les
  exceptions sont nommées, avec la raison lue dans la sortie (jeton initial
  fréquent ou non).
* **R3 — témoin positif.** Sur 12 faits réels du même gabarit, jamais entraînés, le
  modèle rappelle au moins 8 attributs sur 12 (comparaison normalisée, chaque fait
  compté une fois : une réponse exacte est déjà une réponse contenant l'attribut).
  Un témoin qui échoue accuse le gabarit de question, pas le corpus. La sortie
  porte un témoin de seuil qui expose la somme naïve et le comptage distinct côte
  à côte, calculés sur les valeurs observées.

Sortie : ``pt22_facts_s0_probe.json``, à côté de ce script — environnement, empreinte
du corpus, empreinte du snapshot de modèle, résumé par règle, puis une entrée par fait
(prior, rang, réponse gloutonne, NLL du sujet) et le bloc témoin. Aucun chemin machine
absolu n'est écrit dans le JSON.

Usage, depuis la racine du dépôt ::

    python MyIA.AI.Notebooks/GenAI/PostTraining/assets/pt22_s0_probe.py
    python MyIA.AI.Notebooks/GenAI/PostTraining/assets/pt22_s0_probe.py --limit 4
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import statistics
import sys
import time
import unicodedata
from pathlib import Path
from typing import Any

os.environ.setdefault("HF_HUB_OFFLINE", "1")
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
os.environ.setdefault("TOKENIZERS_PARALLELISM", "false")
os.environ["CUDA_VISIBLE_DEVICES"] = ""

import torch  # noqa: E402
from transformers import AutoModelForCausalLM, AutoTokenizer  # noqa: E402
from transformers.utils import logging as hf_logging  # noqa: E402

MODEL_REPO = "Qwen/Qwen3-1.7B-Base"
HERE = Path(__file__).resolve().parent
FACTS_NAME = "pt22_facts.json"
OUT_NAME = "pt22_facts_s0_probe.json"
SCHEMA = "pt22-facts-s0-probe/v1"
SEALED_DOC = "docs/genai/pt16-sleep-dreaming-pre-enregistrement.md"
ISSUE = 27376
MAX_NEW_TOKENS = 16
RANK_MIN = 20
RANK_MIN_SHARE = 0.90
CONTROL_MIN_EXACT = 8

# Témoin positif : des faits réels du même gabarit, hors corpus, jamais entraînés.
# Les attributs multi-mots sont acceptés par contenance (comptage séparé).
POSITIVE_CONTROL: tuple[tuple[str, str, str], ...] = (
    ("birthplace", "Victor Hugo", "Besançon"),
    ("birthplace", "Albert Einstein", "Ulm"),
    ("birthplace", "Charles Darwin", "Shrewsbury"),
    ("native_language", "Victor Hugo", "French"),
    ("native_language", "Miguel de Cervantes", "Spanish"),
    ("native_language", "Dante Alighieri", "Italian"),
    ("novel", "Mary Shelley", "Frankenstein"),
    ("novel", "Bram Stoker", "Dracula"),
    ("novel", "Harper Lee", "To Kill a Mockingbird"),
    ("company", "Bill Gates", "Microsoft"),
    ("company", "Mark Zuckerberg", "Facebook"),
    ("company", "Henry Ford", "Ford Motor Company"),
)


def _norm(text: str) -> str:
    """Normalisation de comparaison : minuscules, sans accents ni ponctuation."""
    flat = unicodedata.normalize("NFKD", text)
    flat = "".join(char for char in flat if not unicodedata.combining(char))
    flat = re.sub(r"[^a-z0-9]+", " ", flat.lower())
    return " ".join(flat.split())


def _first_line(text: str) -> str:
    return text.split("\n", 1)[0].strip()


def _find_subsequence(hay: list[int], needle: list[int]) -> int | None:
    if not needle:
        return None
    for start in range(len(hay) - len(needle) + 1):
        if hay[start:start + len(needle)] == needle:
            return start
    return None


def _encode(tok: Any, text: str) -> list[int]:
    return tok.encode(text, add_special_tokens=False)


def _score_fact(model: Any, tok: Any, fact: dict[str, Any]) -> dict[str, Any]:
    """Prior, rang, réponse gloutonne et NLL du sujet pour un fait."""
    prompt, target = fact["prompt"], fact["target"]
    prompt_ids = tok.encode(prompt, add_special_tokens=True)
    target_ids = _encode(tok, target)
    full_ids = tok.encode(prompt + target, add_special_tokens=True)
    if full_ids[:len(prompt_ids)] != prompt_ids or full_ids[len(prompt_ids):] != target_ids:
        raise RuntimeError(f"{fact['id']} : frontière prompt/cible non alignée sur les jetons")

    input_ids = torch.tensor([full_ids], dtype=torch.long)
    logits = model(input_ids=input_ids, attention_mask=torch.ones_like(input_ids)).logits[0]
    logprobs = torch.log_softmax(logits.float(), dim=-1)
    start = len(prompt_ids)
    target_logp = 0.0
    for offset, token_id in enumerate(target_ids):
        target_logp += float(logprobs[start + offset - 1, token_id])
    first_logits = logits[start - 1]
    first_rank = int((first_logits > first_logits[target_ids[0]]).sum().item()) + 1
    top1_id = int(first_logits.argmax().item())

    with torch.inference_mode():
        generated = model.generate(
            input_ids=torch.tensor([prompt_ids], dtype=torch.long),
            attention_mask=torch.ones((1, len(prompt_ids)), dtype=torch.long),
            max_new_tokens=MAX_NEW_TOKENS,
            do_sample=False,
            num_beams=1,
            pad_token_id=tok.pad_token_id if tok.pad_token_id is not None else tok.eos_token_id,
        )
    answer = _first_line(tok.decode(generated[0, len(prompt_ids):], skip_special_tokens=True))

    subject = fact["subject"]
    subject_ids = _encode(tok, " " + subject)
    subject_start = _find_subsequence(prompt_ids, subject_ids)
    if subject_start is None:
        subject_ids = _encode(tok, subject)
        subject_start = _find_subsequence(prompt_ids, subject_ids)
    subject_logp: float | None = None
    subject_mean_logp: float | None = None
    if subject_start is not None and subject_start > 0:
        total = 0.0
        for offset, token_id in enumerate(subject_ids):
            total += float(logprobs[subject_start + offset - 1, token_id])
        subject_logp = total
        subject_mean_logp = total / len(subject_ids)

    single_token = [
        name for name in (subject.split(" ")[0], subject.split(" ")[-1], fact["attribute"])
        if len(_encode(tok, name)) < 2 or len(_encode(tok, " " + name)) < 2
    ]
    return {
        "id": fact["id"],
        "split": fact["split"],
        "slot": fact["slot"],
        "subject": subject,
        "attribute": fact["attribute"],
        "prompt": prompt,
        "target_tokens": len(target_ids),
        "logp_target": round(target_logp, 6),
        "mean_logp_target": round(target_logp / len(target_ids), 6),
        "p_target": round(float(torch.exp(torch.tensor(target_logp))), 10),
        "rank_first": first_rank,
        "top1": tok.decode([top1_id]),
        "p_top1": round(float(torch.softmax(first_logits.float(), dim=-1)[top1_id]), 6),
        "greedy": answer,
        "greedy_exact": _norm(answer) == _norm(fact["attribute"]),
        "greedy_contains": _norm(fact["attribute"]) in _norm(answer),
        "subject_logp": round(subject_logp, 6) if subject_logp is not None else None,
        "subject_mean_logp": round(subject_mean_logp, 6) if subject_mean_logp is not None else None,
        "single_token_names": single_token,
    }


def _summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ranks = [row["rank_first"] for row in rows]
    means = [row["mean_logp_target"] for row in rows]
    return {
        "n": len(rows),
        "greedy_exact": sum(1 for row in rows if row["greedy_exact"]),
        "greedy_contains": sum(1 for row in rows if row["greedy_contains"]),
        # Une réponse exacte est déjà contenante : chaque fait ne compte qu'une fois.
        "greedy_distinct": sum(1 for row in rows if row["greedy_exact"] or row["greedy_contains"]),
        "rank_first_gt_20": sum(1 for rank in ranks if rank > RANK_MIN),
        "rank_first_median": statistics.median(ranks),
        "rank_first_min": min(ranks),
        "mean_logp_target_median": round(statistics.median(means), 6),
        "mean_logp_target_max": round(max(means), 6),
        "p_top1_max": max(row["p_top1"] for row in rows),
        "single_token_violations": sorted({
            name for row in rows for name in row["single_token_names"]
        }),
        "per_slot_rank_median": {
            slot: statistics.median([row["rank_first"] for row in rows if row["slot"] == slot])
            for slot in sorted({row["slot"] for row in rows})
        },
    }


def _threshold_position(value: int) -> str:
    if value > CONTROL_MIN_EXACT:
        return "au-dessus du seuil"
    if value == CONTROL_MIN_EXACT:
        return "au seuil"
    return "sous le seuil"


def _threshold_witness(exact: int, contains: int, distinct: int, total: int) -> dict[str, Any]:
    """Témoin de seuil R3 : somme naïve des deux compteurs contre comptage distinct.

    Une réponse exacte est déjà une réponse contenant l'attribut : additionner
    ``greedy_exact`` et ``greedy_contains`` double chaque réponse exacte. Le témoin
    rend les deux arithmétiques côte à côte sur les valeurs observées, puis dérive
    le cas frontière où la somme naïve atteint le seuil alors que le comptage
    distinct n'y arrive pas (les réponses ajoutées sont supposées contenantes mais
    non exactes). Tout est calculé ici, rien n'est recopié à la main.
    """
    naive = exact + contains
    deficit = max(0, CONTROL_MIN_EXACT - naive)
    frontier_exact = exact
    frontier_contains = contains + deficit
    frontier_naive = frontier_exact + frontier_contains
    frontier_distinct = frontier_exact + (frontier_contains - frontier_exact)
    naive_pass = naive >= CONTROL_MIN_EXACT
    distinct_pass = distinct >= CONTROL_MIN_EXACT
    frontier_naive_pass = frontier_naive >= CONTROL_MIN_EXACT
    frontier_distinct_pass = frontier_distinct >= CONTROL_MIN_EXACT
    divergence = frontier_naive_pass and not frontier_distinct_pass
    line = (
        f"temoin de seuil R3 (seuil = {CONTROL_MIN_EXACT} attributs sur {total}) : "
        f"observe {exact} exactes + {contains} contenues, somme naive {naive} "
        f"({_threshold_position(naive)}) contre comptage distinct {distinct} "
        f"({_threshold_position(distinct)}) ; "
        f"cas frontiere {frontier_exact} exactes + {frontier_contains} contenues : "
        f"somme naive {frontier_naive} ({_threshold_position(frontier_naive)})"
    )
    if divergence:
        line += (
            " ferait passer la garde du cote PASS, alors que le comptage distinct "
            f"{frontier_distinct} ({_threshold_position(frontier_distinct)}) la laisse du cote FAIL."
        )
    else:
        line += (
            f" ; comptage distinct {frontier_distinct} "
            f"({_threshold_position(frontier_distinct)}) : pas de divergence a la frontiere derivee."
        )
    return {
        "threshold": CONTROL_MIN_EXACT,
        "total": total,
        "observed": {
            "greedy_exact": exact,
            "greedy_contains": contains,
            "naive_sum": naive,
            "distinct_count": distinct,
            "naive_verdict_pass": naive_pass,
            "distinct_verdict_pass": distinct_pass,
        },
        "frontier": {
            "greedy_exact": frontier_exact,
            "greedy_contains": frontier_contains,
            "naive_sum": frontier_naive,
            "distinct_count": frontier_distinct,
            "naive_verdict_pass": frontier_naive_pass,
            "distinct_verdict_pass": frontier_distinct_pass,
        },
        "assumption": "les reponses ajoutees a la frontiere sont contenantes mais non exactes",
        "line": line,
    }


def _snapshot_commit() -> str | None:
    """Nom du snapshot HF résolu hors ligne — l'empreinte du modèle effectivement lu."""
    try:
        from huggingface_hub import snapshot_download

        return Path(snapshot_download(MODEL_REPO, local_files_only=True)).name
    except Exception:
        return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Sonde S0 du corpus de faits fictifs PT-22.")
    parser.add_argument("--limit", type=int, default=0,
                        help="ne mesure que les N premiers faits fictifs (contrôle de mise au point)")
    parser.add_argument("--out", type=Path, default=HERE / OUT_NAME, help="chemin de sortie")
    args = parser.parse_args(argv)
    hf_logging.set_verbosity_error()

    facts_path = HERE / FACTS_NAME
    raw = facts_path.read_bytes()
    doc = json.loads(raw.decode("utf-8"))
    facts = doc["facts"]
    if args.limit:
        facts = facts[:args.limit]
    templates = {slot["slot"]: slot["question_template"] for slot in doc["slots"]}

    threads = max(1, (os.cpu_count() or 4) // 2)
    torch.set_num_threads(threads)
    started = time.time()
    tok = AutoTokenizer.from_pretrained(MODEL_REPO)
    try:
        model = AutoModelForCausalLM.from_pretrained(MODEL_REPO, dtype=torch.float32)
    except TypeError:
        model = AutoModelForCausalLM.from_pretrained(MODEL_REPO, torch_dtype=torch.float32)
    model.eval()

    fictitious: list[dict[str, Any]] = []
    with torch.inference_mode():
        for index, fact in enumerate(facts, start=1):
            row = _score_fact(model, tok, fact)
            fictitious.append(row)
            print(f"[{index}/{len(facts)}] {row['id']} rank={row['rank_first']} "
                  f"greedy={row['greedy']!r} exact={row['greedy_exact']}", flush=True)

    control: list[dict[str, Any]] = []
    if not args.limit:
        control_facts = []
        for position, (slot, subject, attribute) in enumerate(POSITIVE_CONTROL, start=1):
            question = templates[slot].format(subject=subject)
            control_facts.append({
                "id": f"control-{position:02d}",
                "split": "control",
                "slot": slot,
                "subject": subject,
                "attribute": attribute,
                "question": question,
                "prompt": f"Question: {question}\nAnswer:",
                "target": f" {attribute}",
                "subject_parts": subject.split(" "),
            })
        with torch.inference_mode():
            for fact in control_facts:
                row = _score_fact(model, tok, fact)
                control.append(row)
                print(f"[control] {row['id']} exact={row['greedy_exact']} "
                      f"greedy={row['greedy']!r}", flush=True)

    fictitious_summary = _summary(fictitious)
    control_summary = _summary(control) if control else {}
    threshold_witness = _threshold_witness(
        control_summary.get("greedy_exact", 0),
        control_summary.get("greedy_contains", 0),
        control_summary.get("greedy_distinct", 0),
        control_summary.get("n", 0),
    ) if control else {}
    rules = {
        "R0_no_single_token_name": not fictitious_summary["single_token_violations"],
        "R1_greedy_exact_zero": fictitious_summary["greedy_exact"] == 0,
        "R2_rank_above_threshold_share": (
            fictitious_summary["rank_first_gt_20"] >= RANK_MIN_SHARE * fictitious_summary["n"]
        ),
        "R3_control_recall": (control_summary.get("greedy_distinct", 0) >= CONTROL_MIN_EXACT) if control else None,
    }
    out = {
        "schema": SCHEMA,
        "issue": ISSUE,
        "sealed_doc": SEALED_DOC,
        "facts_file": FACTS_NAME,
        "facts_sha256": hashlib.sha256(raw).hexdigest(),
        "environment": {
            "python": platform.python_version(),
            "torch": torch.__version__,
            "transformers": __import__("transformers").__version__,
            "device": "cpu",
            "dtype": "float32",
            "offline": True,
            "torch_threads": threads,
            "elapsed_seconds": round(time.time() - started, 1),
        },
        "model": {
            "repo": MODEL_REPO,
            "commit": getattr(model.config, "_commit_hash", None) or _snapshot_commit(),
            "parameters": int(sum(parameter.numel() for parameter in model.parameters())),
        },
        "rules": {
            "R0": "aucun nom inventé (prénom, nom de famille, attribut) n'est un jeton unique",
            "R1": "la réponse gloutonne n'égale l'attribut pour aucun des faits fictifs",
            "R2": f"rang du premier jeton de la cible > {RANK_MIN} pour au moins "
                  f"{int(RANK_MIN_SHARE * 100)} % des faits fictifs",
            "R3": f"témoin positif : au moins {CONTROL_MIN_EXACT} attributs réels sur 12, chaque fait "
                  f"compté une fois (exactitude exacte ou contenance, comparaison normalisée)",
            "verdict": rules,
        },
        "threshold_witness": threshold_witness,
        "summary": {"fictitious": fictitious_summary, "positive_control": control_summary},
        "fictitious": fictitious,
        "positive_control": control,
    }
    args.out.write_bytes((json.dumps(out, indent=2, ensure_ascii=False) + "\n").encode("utf-8"))
    print(f"ECRIT : {args.out.name} ({len(fictitious)} faits fictifs, {len(control)} temoins)")
    print(f"RESUME : {json.dumps(fictitious_summary, ensure_ascii=False)}")
    print(f"TEMOIN : {json.dumps(control_summary, ensure_ascii=False)}")
    print(f"REGLES : {json.dumps(rules, ensure_ascii=False)}")
    if threshold_witness:
        print(f"TEMOIN DE SEUIL : {threshold_witness['line']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())