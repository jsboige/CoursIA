#!/usr/bin/env python3
"""Campagne d'annotation multi-modeles du corpus ColBERT (#20301).

Les textes proviennent d'un CSV local dont la provenance et la licence ont ete
etablies avant telechargement. Le corpus entier et les sorties de campagne
restent hors depot. Le generateur reutilise les clients OpenAI/vLLM de la serie
FallacyDetection ; la mesure est celle de ``ict.humor_agreement``. Cette tranche
produit des annotations, elle ne simule ni accord ni cout.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import random
import sys
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Mapping, Protocol, Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fallacy_detection import generate_teacher_corpus as G  # noqa: E402
from fallacy_detection.judge_family_agreement import JUDGE_SPECS, OpenAIJudge  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
ICT_PATH = REPO_ROOT / "MyIA.AI.Notebooks/IIT/ICT-Series"
if str(ICT_PATH) not in sys.path:
    sys.path.insert(0, str(ICT_PATH))
from ict.humor_agreement import (  # noqa: E402
    agreement_report,
    chance_kappa_distribution,
    cohen_kappa,
    token_cost,
)

FORMES = ("pun", "sociale", "topical")
INTENSITES = ("0", "1", "2", "3")
SOURCE_URL = "https://raw.githubusercontent.com/Moradnejad/ColBERT-Using-BERT-Sentence-Embedding-for-Humor-Detection/master/Data/dataset.csv"
# Canal de telechargement effectif = le depot GitHub (SOURCE_URL), dont le README
# declare code et dataset sous MIT (verifie 2026-11-23). Le depot auteur IEEE
# Dataport (DOI 10.21227/fw8e-z983) declare CC BY 4.0. Les deux exigent
# l'attribution, portee par PUBLICATION_ARCHIVE et les citations du body.
DATASET_LICENSE = (
    "MIT (depot GitHub Moradnejad, canal de telechargement effectif de SOURCE_URL) ; "
    "depot auteur IEEE Dataport (DOI 10.21227/fw8e-z983) declare CC BY 4.0 -- "
    "attribution requise dans les deux cas"
)
PUBLICATION_ARCHIVE = (
    "G:/Mon Drive/MyIA/IA/Bibliographie IA/MachineLearning/Computational Humor/"
    "2022 - Annamoradnejad and Zoghi - ColBERT Using BERT Sentence Embedding "
    "in Parallel Neural Networks for Computational Humor (arXiv 2004.12765).pdf"
)
FORM_DEFINITIONS = {
    "pun": "jeu de mots, double sens, homophonie ou detournement lexical",
    "sociale": "mecanisme relationnel ou social intemporel, sans dependre d'une reference d'actualite",
    "topical": "reference culturelle, politique, professionnelle ou d'actualite necessaire au comique",
}
FORM_KEYS = {forme: chr(ord("A") + index) for index, forme in enumerate(FORMES)}
INTENSITY_KEYS = {level: chr(ord("A") + index) for index, level in enumerate(INTENSITES)}


class Teacher(Protocol):
    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> G.Reply: ...


@dataclass(frozen=True)
class CorpusItem:
    item_id: str
    text: str
    humor: bool


def load_corpus(path: str | Path) -> list[CorpusItem]:
    """Charge le CSV et refuse les etiquettes inconnues ou les textes vides."""
    items: list[CorpusItem] = []
    with Path(path).open(encoding="utf-8-sig", newline="") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames is None or not {"text", "humor"} <= set(reader.fieldnames):
            raise ValueError("le CSV doit porter les colonnes text et humor")
        for index, row in enumerate(reader):
            text = (row["text"] or "").strip()
            raw_label = (row["humor"] or "").strip().casefold()
            if raw_label not in {"true", "false"} or not text:
                raise ValueError(f"ligne {index + 2} invalide : texte vide ou etiquette inconnue")
            items.append(CorpusItem(f"colbert-{index:06d}", text, raw_label == "true"))
    if not items:
        raise ValueError("corpus vide")
    return items


def stratified_draw(items: Sequence[CorpusItem], limit: int, seed: int = 42) -> list[CorpusItem]:
    """Tirage equilibre, reproductible et independant de l'ordre du CSV."""
    if not 1 <= limit <= len(items):
        raise ValueError(f"limit doit etre dans 1..{len(items)}")
    rng = random.Random(seed)
    groups = {label: sorted((item for item in items if item.humor == label),
                            key=lambda item: item.item_id)
              for label in (False, True)}
    for members in groups.values():
        rng.shuffle(members)
    drawn: list[CorpusItem] = []
    while len(drawn) < limit:
        progressed = False
        for label in (False, True):
            if groups[label] and len(drawn) < limit:
                drawn.append(groups[label].pop())
                progressed = True
        if not progressed:
            break
    return sorted(drawn, key=lambda item: item.item_id)


def annotation_prompt(item: CorpusItem) -> str:
    """Question fermee : une forme dominante, l'intensite separee."""
    return (
        "Classifie le mecanisme comique dominant de ce texte. Reponds par UNE lettre :\n"
        + "\n".join(f"{FORM_KEYS[f]}. {f} : {FORM_DEFINITIONS[f]}" for f in FORMES)
        + f"\n\nTexte :\n{item.text}\n\nReponds uniquement par la lettre."
    )


def intensity_prompt(item: CorpusItem) -> str:
    return (
        "Evalue l'intensite comique du texte, independamment de sa forme :\n"
        "A. 0 : pas humoristique\nB. 1 : faible\nC. 2 : net\nD. 3 : tres fort\n\n"
        f"Texte :\n{item.text}\n\nReponds uniquement par la lettre."
    )


def roundtrip_prompt(text: str, target: str, seed: int) -> tuple[str, list[str]]:
    """Controle ferme contre les deux autres formes, ordre seede par item."""
    candidates = [target] + [forme for forme in FORMES if forme != target]
    random.Random(seed).shuffle(candidates)
    lines = [
        f"{chr(ord('A') + index)}. {forme} : {FORM_DEFINITIONS[forme]}"
        for index, forme in enumerate(candidates)
    ]
    return (
        "Quel mecanisme comique dominant ce texte illustre-t-il ?\n\n"
        f"{text}\n\n" + "\n".join(lines) + "\n\nReponds uniquement par la lettre.",
        candidates,
    )


def _annotate(annotator: str, family: str, model: str, task: str, item_id: str,
              label: str | None, reply: G.Reply, prompt: str, answer: str) -> dict:
    return {
        "id": item_id,
        "annotator": annotator,
        "family": family,
        "model": model,
        "task": task,
        "label": label,
        "raw_label": answer.strip(),
        "parse_failed": label is None,
        "finish_reason": reply.finish_reason,
        "prompt_tokens": reply.prompt_tokens,
        "prompt_tokens_source": "api" if reply.prompt_tokens > 0 else "absent",
        "completion_tokens": reply.completion_tokens,
    }


def annotate_item(item: CorpusItem, annotator: str, family: str, model: str,
                  teacher: Teacher, seed: int = 42, *,
                  existing: Sequence[Mapping] = ()) -> list[dict]:
    """Complete les taches manquantes ; un vote existant n'est jamais rejoue."""
    previous = {(row["task"], row["id"], row["annotator"]): row
                for row in existing}
    records: list[dict] = []
    prompt = annotation_prompt(item)
    if ("forme", item.item_id, annotator) in previous:
        forme = previous[("forme", item.item_id, annotator)]["label"]
    else:
        reply = teacher.complete(prompt, max_tokens=40, temperature=0.0)
        forme = G.parse_choice(reply.text, list(FORMES))
        records.append(_annotate(annotator, family, model, "forme", item.item_id,
                                 forme, reply, prompt, reply.text))
    prompt = intensity_prompt(item)
    if ("intensite", item.item_id, annotator) not in previous:
        reply = teacher.complete(prompt, max_tokens=40, temperature=0.0)
        intensite = G.parse_choice(reply.text, list(INTENSITES))
        records.append(_annotate(annotator, family, model, "intensite", item.item_id,
                                 intensite, reply, prompt, reply.text))
    if forme is None or ("roundtrip", item.item_id, annotator) in previous:
        return records
    prompt, candidates = roundtrip_prompt(item.text, forme, seed)
    reply = teacher.complete(prompt, max_tokens=40, temperature=0.0)
    verdict = G.parse_choice(reply.text, candidates)
    records.append(_annotate(annotator, family, model, "roundtrip", item.item_id,
                             verdict, reply, prompt, reply.text))
    return records


def disambiguate(item: CorpusItem, original: Mapping, annotator: str, family: str,
                 model: str, teacher: Teacher, seed: int) -> dict | None:
    """Un vote supplementaire justifie : le premier n'est jamais reecrit."""
    label = original.get("label")
    if label not in FORMES:
        return None
    prompt, candidates = roundtrip_prompt(item.text, label, seed + 1009)
    prompt += "\nJustifie d'abord en une phrase, puis ecris « reponse : <lettre> »."
    reply = teacher.complete(prompt, max_tokens=160, temperature=0.0)
    return _annotate(annotator, family, model, "disambiguation", item.item_id,
                     G.parse_choice(reply.text, candidates), reply, prompt, reply.text)


def _task_views(records: Sequence[Mapping]) -> tuple[list[dict], ...]:
    """Un echec d'analyse reste mesure, mais n'est pas une categorie d'accord."""
    views = []
    for task in ("forme", "intensite", "roundtrip"):
        rows = [dict(row) for row in records
                if row["task"] == task and not row["parse_failed"]]
        for row in rows:
            row["id"] = f"{row['id']}|{task}"
        views.append(rows)
    return tuple(views)


def roundtrip_measures(records: Sequence[Mapping]) -> dict:
    """Taux par annotateur : seul un reclassage parse compte au denominateur."""
    by_annotator: dict[str, list[Mapping]] = {}
    for row in records:
        if row["task"] == "roundtrip":
            by_annotator.setdefault(str(row["annotator"]), []).append(row)
    result = {}
    for annotator, rows in sorted(by_annotator.items()):
        parsed = [row for row in rows if not row["parse_failed"]]
        form_by_id = {
            row["id"]: row["label"] for row in records
            if row["task"] == "forme" and row["annotator"] == annotator
        }
        result[annotator] = {
            "measured": len(parsed),
            "unparsed": len(rows) - len(parsed),
            "same_label": sum(row["label"] == form_by_id.get(row["id"]) for row in parsed),
            "rate": (sum(row["label"] == form_by_id.get(row["id"]) for row in parsed) / len(parsed)
                     if parsed else None),
        }
    return result


def chance_baseline(forms: Sequence[Mapping], seed: int = 42, draws: int = 200) -> dict | None:
    """Témoin negatif sur les memes items et les memes categories figees."""
    by_annotator: dict[str, dict[str, str]] = {}
    for row in forms:
        if not row["parse_failed"]:
            by_annotator.setdefault(str(row["annotator"]), {})[str(row["id"])] = str(row["label"])
    if len(by_annotator) != 2:
        return None
    first, second = sorted(by_annotator)
    shared = sorted(set(by_annotator[first]) & set(by_annotator[second]))
    if not shared:
        return None
    baseline = chance_kappa_distribution(
        [by_annotator[first][item] for item in shared],
        [by_annotator[second][item] for item in shared],
        n_draws=draws,
        seed=seed,
    )
    baseline.pop("values", None)
    return baseline


def campaign_report(records: Sequence[Mapping], items: Sequence[CorpusItem], *, seed: int = 42,
                    chance_draws: int = 200) -> dict:
    """Mesure forme, intensite et verdicts finaux, avec stratification honnete.

    ColBERT n'a aucune reference humaine de forme. ``par_forme`` conditionne donc
    l'accord par la forme initiale de chaque annotateur, pris tour a tour comme
    ancre : ce sont deux vues des votes, jamais une verite-terrain.
    """
    forms, intensities, roundtrips = _task_views(records)
    by_form = {}
    for task, rows in (("forme", forms), ("roundtrip", roundtrips)):
        views = {}
        for anchor in sorted({str(row["annotator"]) for row in forms}):
            initial = {row["id"].split("|", 1)[0]: row["label"]
                       for row in forms if row["annotator"] == anchor
                       and not row["parse_failed"]}
            for forme in FORMES:
                ids = {item for item, label in initial.items() if label == forme}
                subset = [row for row in rows
                          if str(row["id"]).split("|", 1)[0] in ids]
                if subset:
                    views.setdefault(anchor, {})[forme] = agreement_report(
                        subset, categories=FORMES)
        by_form[task] = views
    return {
        "n_items": len(items),
        "n_annotations": len(records),
        "n_disambiguation": sum(row["task"] == "disambiguation" for row in records),
        "parse_failures": dict(Counter(
            row["task"] for row in records if row["parse_failed"]
        )),
        "forme": agreement_report(forms, categories=FORMES),
        "intensite": agreement_report(intensities, categories=INTENSITES),
        "roundtrip_agreement": agreement_report(roundtrips, categories=FORMES),
        "par_forme": by_form,
        "par_forme_note": (
            "Conditionnement par la forme initiale de chaque annotateur d'ancrage, "
            "pas verite humaine : ColBERT ne fournit qu'une reference binaire."
        ),
        "roundtrip": roundtrip_measures(records),
        "chance": chance_baseline(roundtrips, seed=seed, draws=chance_draws),
        "token_cost": token_cost(records),
        "token_cost_note": (
            "Tokens lus dans usage des API pour forme, intensite, reclassage et "
            "desambiguisation ; une absence de prompt_tokens est declaree, jamais estimee."
        ),
    }


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def write_jsonl(path: Path, records: Sequence[Mapping]) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def _append_jsonl(path: Path, records: Sequence[Mapping]) -> None:
    with path.open("a", encoding="utf-8", newline="\n") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n")


def run_campaign(items: Sequence[CorpusItem],
                 clients: Mapping[str, tuple[str, str, Teacher]], out: Path,
                 *, seed: int = 42, disambiguation_floor: float = 0.6,
                 chance_draws: int = 200, corpus_path: Path | None = None) -> dict:
    """Reprend chaque tache separement, sans ecraser ni dupliquer un vote."""
    if not items or len(clients) != 2:
        raise ValueError("la campagne exige des items et exactement deux annotateurs")
    out.mkdir(parents=True, exist_ok=True)
    checkpoint = out / "annotations.jsonl"
    records = read_jsonl(checkpoint) if checkpoint.exists() else []
    keys = [(row["id"], row["annotator"], row["task"]) for row in records]
    if len(keys) != len(set(keys)):
        raise ValueError("checkpoint duplique : preservation refusee, reparer avant reprise")
    for item in items:
        for annotator, (family, model, teacher) in clients.items():
            produced = annotate_item(item, annotator, family, model, teacher, seed,
                                     existing=records)
            _append_jsonl(checkpoint, produced)
            records.extend(produced)
    _, _, roundtrips = _task_views(records)
    initial = agreement_report(roundtrips, categories=FORMES)
    pairwise = initial["pairwise"]
    kappa = next(iter(pairwise.values()))["kappa"] if len(pairwise) == 1 else None
    if kappa is not None and kappa < disambiguation_floor:
        item_by_id = {item.item_id: item for item in items}
        disagreements = {
            (row["id"], row["annotator"])
            for row in records
            if row["task"] == "roundtrip" and not row["parse_failed"]
            and row["label"] != next(
                (candidate["label"] for candidate in records
                 if candidate["task"] == "forme" and candidate["id"] == row["id"]
                 and candidate["annotator"] == row["annotator"]), None)
        }
        already = {(row["id"], row["annotator"]) for row in records if row["task"] == "disambiguation"}
        for item_id, annotator in sorted(disagreements - already):
            if item_id not in item_by_id:
                continue
            original = next(row for row in records if row["task"] == "forme"
                            and row["id"] == item_id and row["annotator"] == annotator)
            family, model, teacher = clients[annotator]
            extra = disambiguate(item_by_id[item_id], original, annotator, family,
                                 model, teacher, seed)
            if extra is not None:
                _append_jsonl(checkpoint, [extra])
                records.append(extra)
    report = campaign_report(records, items, seed=seed, chance_draws=chance_draws)
    report["disambiguation_triggered"] = kappa is not None and kappa < disambiguation_floor
    report["disambiguation_floor"] = disambiguation_floor
    report["models"] = {name: {"family": family, "model": model}
                        for name, (family, model, _) in clients.items()}
    report["source_url"] = SOURCE_URL
    if corpus_path is not None:
        report["corpus_sha256"] = hashlib.sha256(corpus_path.read_bytes()).hexdigest()
        report["sample_item_ids"] = [item.item_id for item in items]
    report["dataset_license"] = DATASET_LICENSE
    report["publication_archive"] = PUBLICATION_ARCHIVE
    report["seed"] = seed
    report["generated_at"] = datetime.now(timezone.utc).isoformat()
    (out / "report.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )
    return report


def load_shared_env(path: str | Path | None = None) -> dict[str, str]:
    """Lit les cles du .env GenAI gitignore, sans jamais les journaliser."""
    path = Path(path) if path is not None else REPO_ROOT / "MyIA.AI.Notebooks/GenAI/.env"
    values: dict[str, str] = {}
    if path.exists():
        for line in path.read_text(encoding="utf-8-sig").splitlines():
            if "=" in line and not line.lstrip().startswith("#"):
                key, value = line.split("=", 1)
                values[key.strip()] = value.strip()
    return values


def build_clients(env: Mapping[str, str], annotator_b: str = "claudish") -> dict:
    """Construit A (hub Qwen) et B (claudish, hors famille Qwen) sans reseau."""
    if annotator_b not in JUDGE_SPECS:
        raise ValueError(f"annotateur B inconnu : {annotator_b}")
    spec = JUDGE_SPECS[annotator_b]
    return {
        "qwen": ("Qwen", G.DEFAULT_MODEL,
                 G.HubTeacher(api_key=env.get("VLLM_API_KEY_MEDIUM") or env.get("VLLM_API_KEY"))),
        annotator_b: (
            spec["family"], spec["model"],
            OpenAIJudge(annotator_b, spec["url"], spec["model"], spec["api_key_env"],
                        api_key=env.get(spec["api_key_env"])),
        ),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--annotator-b", choices=sorted(JUDGE_SPECS), default="claudish")
    parser.add_argument("--env-file", type=Path,
                        help="chemin du .env gitignore (defaut : GenAI/.env du checkout)")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(argv)
    items = stratified_draw(load_corpus(args.corpus), args.limit, args.seed)
    if args.dry_run:
        print(json.dumps({"items": len(items), "humor": sum(item.humor for item in items),
                          "controls": sum(not item.humor for item in items)}))
        return 0
    env = load_shared_env(args.env_file)
    clients = build_clients(env, args.annotator_b)
    report = run_campaign(items, clients, args.out, seed=args.seed, corpus_path=args.corpus)
    print(json.dumps({"n_items": report["n_items"], "n_annotations": report["n_annotations"],
                      "total_tokens": report["token_cost"]["total_tokens"],
                      "out": str(args.out)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
