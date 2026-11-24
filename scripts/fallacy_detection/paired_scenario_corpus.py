#!/usr/bin/env python3
"""Lot apparie meme scenario/meme locuteur, avec et sans sophisme (#10355, 2b).

La revue EPITA (c.6344505010) relève que le corpus historique donne le role du
locuteur comme raccourci de classe : ``smoothTalker`` porte tous les sophismes,
``drawer`` toutes les vertus. Ce module construit des paires de textes pour
lesquelles ce raccourci ne contient plus aucune information.

* Le bras positif est le texte deja produit par ``render_prompt`` et valide par
  le controle aller-retour du corpus val FR. Son prompt est reconstruit pour la
  preuve de provenance, sans appel de generation.
* Le bras negatif reutilise exactement les memes champs de scenario et le meme
  locuteur ``smoothTalker``, mais demande une defense loyale de la meme these,
  sans nommer le sophisme. Seule la consigne d'argumentation change.
* La verite-terrain du negatif est mesuree : un vote de reclassement sur le
  sophisme cible doit echouer. Si une vertu declare opposition a ce sophisme
  dans la taxonomie Argumentum (``crossLink_Opposes``), un second vote doit la
  retrouver parmi d'autres vertus. Tout echec, vote muet ou incertain entraine
  le rejet de la paire avec un motif explicite : aucun texte n'est publie comme
  « sans sophisme » sur la seule foi de sa consigne.

Le checkpoint JSONL est un artefact local, non committe. ``--report-only``
relit ce checkpoint, ou a defaut le rapport JSON commite, sans cle ni reseau.

Usage::

    python -m fallacy_detection.paired_scenario_corpus --limit 60
    python -m fallacy_detection.paired_scenario_corpus --probe
    python -m fallacy_detection.paired_scenario_corpus --report-only
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import random
import sys
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, Protocol, Sequence

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fallacy_detection import cartesian_dataset_builder as B  # noqa: E402
from fallacy_detection import generate_teacher_corpus as G  # noqa: E402

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUT = G.DEFAULT_OUT
DEFAULT_CORPUS = G.DEFAULT_OUT / "val_fr.jsonl"
DEFAULT_SEED = 42
DEFAULT_LIMIT = 60
DEFAULT_MAX_ATTEMPTS = 2
CHECKPOINT_NAME = "paired_scenario_corpus.checkpoint.jsonl"
CORPUS_NAME = "paired_scenario_corpus.jsonl"
REPORT_NAME = "paired_scenario_report.json"
REPORT_MD_NAME = "paired_scenario_report.md"


class Teacher(Protocol):
    def complete(self, prompt: str, *, max_tokens: int, temperature: float) -> G.Reply:
        """Interface du maitre local, injectable pour les tests hermetiques."""


@dataclass(frozen=True)
class Arm:
    """Un texte du lot, rattache a sa paire par ``pair_group_id``."""

    pair_group_id: str
    pair_id: str
    split: str
    arm: str  # "with_fallacy" | "without_fallacy"
    has_fallacy: bool
    target_node: str
    scenario_path: str
    speaker_role: str
    speaker: str
    listener: str
    family: str
    lang: str
    text: str
    source: str
    completion_tokens: int
    finish_reason: str
    generation_attempt: int
    control: dict


def load_corpus(path: Path = DEFAULT_CORPUS) -> list[dict]:
    """Charge le corpus enseignant commite, ligne JSON par paire."""
    with open(path, encoding="utf-8") as handle:
        records = [json.loads(line) for line in handle if line.strip()]
    if not records:
        raise ValueError(f"corpus vide : {path}")
    return records


def pair_from_record(record: dict) -> B.Pair:
    """Retrouve la paire de tranche A conservee dans une ligne enseignant."""
    return B.Pair(
        pair_id=record["pair_id"], split=record["split"],
        polarity=record["polarity"], node_pk=int(record["node_pk"]),
        family=record["family"], depth=int(record["depth"]),
        is_leaf=bool(record["is_leaf"]), scenario_path=record["scenario_path"],
    )


def select_positive_pairs(records: Sequence[dict], limit: int, seed: int) -> list[dict]:
    """Selection stratifiee par famille de sophismes deja reconnus.

    Le bras positif ne doit pas fabriquer une reference douteuse : seules les
    lignes ``fallacy`` dont l'aller-retour vaut explicitement ``True`` entrent
    dans le lot. L'ordre final est stable par ``pair_id`` ; le hasard ne sert
    qu'au tirage a l'interieur de chaque famille.
    """
    eligible = [r for r in records
                if r.get("polarity") == "fallacy" and r.get("roundtrip") is True
                and r.get("text")]
    if limit <= 0 or limit > len(eligible):
        raise ValueError(f"limit={limit} hors de 1..{len(eligible)}")
    rng = random.Random(seed)
    by_family: dict[str, list[dict]] = {}
    for record in eligible:
        by_family.setdefault(record["family"], []).append(record)
    quotas = {family: limit * len(rows) // len(eligible)
              for family, rows in by_family.items()}
    remainder = [(limit * len(rows) / len(eligible) - quotas[family], family)
                 for family, rows in by_family.items()]
    rng.shuffle(remainder)
    for _, family in sorted(remainder, key=lambda item: -item[0])[:limit - sum(quotas.values())]:
        quotas[family] += 1
    drawn: list[dict] = []
    for family, rows in sorted(by_family.items()):
        drawn.extend(rng.sample(rows, quotas[family]))
    return sorted(drawn, key=lambda record: record["pair_id"])


def load_virtue_oppositions(path: Path = B.DEFAULT_VIRTUES) -> dict[str, tuple[str, ...]]:
    """Ponts vertu -> sophismes declares par la taxonomie, jamais par similarite.

    Les cibles de ``crossLink_Opposes`` sont des PK de sophismes (et non des
    chemins d'arbre), contrairement aux autres relations du graphe. Une vertu
    qui n'oppose pas la cible ne devient pas un contrôle positif par
    approximation de titres.
    """
    with open(path, encoding="utf-8-sig", newline="") as handle:
        rows = list(csv.DictReader(handle))
    result: dict[str, list[str]] = {}
    for row in rows:
        virtue = "V" + row["pk"].strip()
        for target in (row.get("crossLink_Opposes") or "").split(";"):
            target = target.strip()
            if target.isdigit() and int(target) > 0:
                result.setdefault("F" + str(int(target)), []).append(virtue)
    return {key: tuple(sorted(values)) for key, values in result.items()}


def counterpart_virtues(target: str, oppositions: dict[str, tuple[str, ...]]) -> tuple[str, ...]:
    """Toutes les vertus liees a la cible, preservees comme cibles acceptees."""
    return oppositions.get(target, ())


def render_loyal_prompt(pair: B.Pair, texts: dict, lang: str = "fr") -> str:
    """Consigne loyale, seule difference semantique avec le bras positif."""
    if pair.polarity != "fallacy":
        raise ValueError("le lot apparie part d'une paire de polarite fallacy")
    row = texts["scenarios"][pair.scenario_path]
    talker = B._scen_field(row, "smoothTalker", lang)
    drawer = B._scen_field(row, "drawer", lang)
    return (
        f"Scenario: {B._scen_field(row, 'title', lang)}\n"
        f"Context: {B._scen_field(row, 'context', lang)} {B._scen_field(row, 'issue', lang)}\n"
        f"Speaker: {talker}. Listener: {drawer}.\n"
        f"Task: write, in {B.LANG_NAMES[lang]}, 2 to 4 sentences said by the speaker to "
        "the listener, defending the speaker's position loyally. Support it with relevant, "
        "verifiable reasons and acknowledge reasonable limits without abandoning it. "
        "Do not use deception, manipulation, personal attacks, invented evidence, or "
        "irrelevant pressure. Do not explain the instruction: give only the spoken reply."
    )


def _speaker_fields(pair: B.Pair, texts: dict, lang: str) -> tuple[str, str]:
    row = texts["scenarios"][pair.scenario_path]
    return B._scen_field(row, "smoothTalker", lang), B._scen_field(row, "drawer", lang)


def make_vote(text: str, target: str, texts: dict, *, seed: int,
              distractors: int = G.DEFAULT_DISTRACTORS, lang: str = "fr") -> dict:
    """Question deterministe de reclassement : cible + distracteurs de meme polarite."""
    rng = random.Random(seed)
    candidates = [target] + G.pick_distractors(
        target, list(texts["nodes"]), distractors, rng)
    rng.shuffle(candidates)
    return {
        "target": target,
        "candidates": candidates,
        "question": G.build_choice_question(text, candidates, texts, lang),
    }


def _call_generation(teacher: Teacher, prompt: str, max_tokens: int) -> G.Reply:
    return teacher.complete(prompt, max_tokens=max_tokens, temperature=0.8)


def _call_vote(teacher: Teacher, vote: dict) -> Optional[str]:
    reply = teacher.complete(vote["question"], max_tokens=400, temperature=0.0)
    return G.parse_choice(reply.text, vote["candidates"])


def classify_attempt(picks: Sequence[Optional[str]], target: str) -> str:
    """Accepte seulement un vote mesure hors cible ; muet ou cible = rejet."""
    if not picks:
        return "vote_missing"
    if any(pick is None for pick in picks):
        return "vote_unparsed"
    return "accepted" if all(pick != target for pick in picks) else "target_reclassified"


def evaluate_negative(text: str, target: str, virtues: Sequence[str], texts: dict,
                      teacher: Teacher, *, seed: int, distractors: int,
                      lang: str = "fr") -> tuple[dict, list[str]]:
    """Controle croise : rejet du sophisme, puis vertu liee si elle existe.

    Un vote non mesure est un rejet de prudence, jamais une preuve d'absence du
    sophisme. Les plusieurs vertus opposees sont toutes acceptees : le pont
    taxonomique n'en privilegie pas une arbitrairement.
    """
    reasons: list[str] = []
    fallacy_vote = make_vote(text, target, texts, seed=seed,
                             distractors=distractors, lang=lang)
    fallacy_pick = _call_vote(teacher, fallacy_vote)
    verdict = classify_attempt([fallacy_pick], target)
    if verdict != "accepted":
        reasons.append("negative_" + verdict)
    virtue_picks: dict[str, Optional[str]] = {}
    if verdict == "accepted" and virtues:
        for index, virtue in enumerate(virtues):
            vote = make_vote(text, virtue, texts, seed=seed + 1009 * (index + 1),
                             distractors=distractors, lang=lang)
            virtue_picks[virtue] = _call_vote(teacher, vote)
        if any(pick is None for pick in virtue_picks.values()):
            reasons.append("virtue_vote_unparsed")
        elif not any(pick in virtues for pick in virtue_picks.values()):
            reasons.append("virtue_not_reclassified")
    control = {
        "fallacy_question_seed": seed,
        "fallacy_pick": fallacy_pick,
        "fallacy_rejected": fallacy_pick is not None and fallacy_pick != target,
        "counterpart_candidates": list(virtues),
        "virtue_picks": virtue_picks,
        "virtue_reclassified": any(pick in virtues for pick in virtue_picks.values()),
    }
    return control, reasons


def positive_arm(record: dict, texts: dict, lang: str = "fr") -> Arm:
    """Le bras positif existant, avec son prompt et son verdict d'origine."""
    pair = pair_from_record(record)
    speaker, listener = _speaker_fields(pair, texts, lang)
    return Arm(
        pair_group_id="paired-" + record["pair_id"], pair_id=record["pair_id"],
        split=record["split"], arm="with_fallacy", has_fallacy=True,
        target_node=record["node_key"], scenario_path=record["scenario_path"],
        speaker_role="smoothTalker", speaker=speaker, listener=listener,
        family=record["family"], lang=lang, text=record["text"],
        source="val_fr.jsonl:generate_one(render_prompt)",
        completion_tokens=int(record.get("completion_tokens") or 0),
        finish_reason=str(record.get("finish_reason") or ""), generation_attempt=0,
        control={
            "source_roundtrip": record.get("roundtrip"),
            "source_prompt": B.render_prompt(pair, texts, lang=lang),
        },
    )


def generate_pair(record: dict, texts: dict, teacher: Teacher, *,
                  oppositions: dict[str, tuple[str, ...]], seed: int,
                  lang: str = "fr", distractors: int = G.DEFAULT_DISTRACTORS,
                  max_attempts: int = DEFAULT_MAX_ATTEMPTS,
                  max_tokens: int = G.DEFAULT_MAX_TOKENS) -> dict:
    """Genere un negatif, controle chaque tentative et publie ou rejette la paire."""
    target = record["node_key"]
    virtues = counterpart_virtues(target, oppositions)
    prompt = render_loyal_prompt(pair_from_record(record), texts, lang)
    attempts: list[dict] = []
    accepted: Optional[Arm] = None
    for attempt in range(1, max_attempts + 1):
        reply = _call_generation(teacher, prompt, max_tokens)
        if not reply.text or reply.completion_tokens < G.MIN_COMPLETION_TOKENS:
            control = {"completion_tokens": reply.completion_tokens}
            reasons = ["negative_empty" if not reply.text else "negative_below_token_floor"]
            attempts.append({"attempt": attempt, "text": reply.text,
                             "finish_reason": reply.finish_reason,
                             "control": control, "rejection_reasons": reasons})
            continue
        control, reasons = evaluate_negative(
            reply.text, target, virtues, texts, teacher,
            seed=seed + attempt, distractors=distractors, lang=lang)
        attempts.append({"attempt": attempt, "text": reply.text,
                         "finish_reason": reply.finish_reason,
                         "completion_tokens": reply.completion_tokens,
                         "control": control, "rejection_reasons": reasons})
        if not reasons:
            pair = pair_from_record(record)
            speaker, listener = _speaker_fields(pair, texts, lang)
            accepted = Arm(
                pair_group_id="paired-" + record["pair_id"], pair_id=record["pair_id"],
                split=record["split"], arm="without_fallacy", has_fallacy=False,
                target_node=target, scenario_path=record["scenario_path"],
                speaker_role="smoothTalker", speaker=speaker, listener=listener,
                family=record["family"], lang=lang, text=reply.text,
                source="paired_scenario_corpus:render_loyal_prompt",
                completion_tokens=reply.completion_tokens,
                finish_reason=reply.finish_reason, generation_attempt=attempt,
                control={**control, "generation_prompt": prompt},
            )
            break
    return {
        "pair_id": record["pair_id"], "status": "accepted" if accepted else "rejected",
        "arms": ([positive_arm(record, texts, lang), accepted] if accepted else []),
        "attempts": attempts,
    }


def validate_pair(rows: Sequence[Arm]) -> None:
    """Invariants structurels : deux bras, meme scenario et meme locuteur."""
    if len(rows) != 2:
        raise ValueError("une paire publiee doit contenir exactement deux bras")
    positive, negative = rows
    if positive.arm != "with_fallacy" or negative.arm != "without_fallacy":
        raise ValueError("ordre ou nom des bras invalide")
    if len({row.pair_group_id for row in rows}) != 1:
        raise ValueError("pair_group_id different entre les bras")
    for field in ("scenario_path", "speaker_role", "speaker", "listener", "target_node"):
        if getattr(positive, field) != getattr(negative, field):
            raise ValueError(f"appariement viole sur {field}")
    if positive.has_fallacy == negative.has_fallacy:
        raise ValueError("les deux bras doivent avoir des polarites opposees")
    if not negative.control["fallacy_rejected"]:
        raise ValueError("un negatif non controle ne peut pas etre publie")


def run_generation(records: Sequence[dict], texts: dict, teacher: Teacher, *,
                   out_dir: Path, oppositions: dict[str, tuple[str, ...]],
                   seed: int, lang: str, distractors: int,
                   max_attempts: int, max_tokens: int) -> None:
    """Reprend apres chaque paire, sans rappeler les paires deja checkpointees."""
    checkpoint = out_dir / CHECKPOINT_NAME
    done = {row["pair_id"] for row in load_checkpoint(checkpoint)}
    with open(checkpoint, "a", encoding="utf-8") as sink:
        for index, record in enumerate(records, start=1):
            if record["pair_id"] in done:
                continue
            result = generate_pair(
                record, texts, teacher, oppositions=oppositions,
                seed=seed + 10007 * index, lang=lang, distractors=distractors,
                max_attempts=max_attempts, max_tokens=max_tokens)
            sink.write(json.dumps(result, ensure_ascii=False, default=_json_default) + "\n")
            sink.flush()
            print(f"[{index}/{len(records)}] {record['pair_id']} {result['status']}", flush=True)


def _json_default(value):
    if isinstance(value, Arm):
        return value.__dict__
    raise TypeError(type(value).__name__)


def load_checkpoint(path: Path) -> list[dict]:
    """Dernier etat par paire, ordre stable ; ignore seulement les lignes vides."""
    if not path.exists():
        return []
    by_pair: dict[str, dict] = {}
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                row = json.loads(line)
                by_pair[row["pair_id"]] = row
    return [by_pair[key] for key in sorted(by_pair)]


def load_results_for_report(out_dir: Path) -> tuple[list[dict], str]:
    """Checkpoint local d'abord ; sinon les tentatives consignees au rapport."""
    checkpoint = out_dir / CHECKPOINT_NAME
    if checkpoint.exists():
        return load_checkpoint(checkpoint), "checkpoint_local"
    report_path = out_dir / REPORT_NAME
    if not report_path.exists():
        raise FileNotFoundError(
            f"--report-only : ni {checkpoint} ni {report_path} — rien a rejouer.")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    return report["attempted_pairs"], "rapport_publie"


def role_shortcut(rows: Sequence[Arm]) -> dict:
    """Le role predit-il la polarite ? Ici il ne le peut pas par construction."""
    roles = sorted({row.speaker_role for row in rows})
    per_role = {}
    for role in roles:
        selected = [row for row in rows if row.speaker_role == role]
        positives = sum(row.has_fallacy for row in selected)
        per_role[role] = {"n": len(selected), "with_fallacy": positives,
                          "without_fallacy": len(selected) - positives,
                          "fallacy_rate": positives / len(selected) if selected else None}
    rules = [(row.speaker_role, row.has_fallacy) for row in rows]
    best_rate = None
    if rules:
        best_rate = max(sum(actual == prediction for _, actual in rules)
                        for prediction in (True, False)) / len(rules)
    return {"roles": roles, "by_role": per_role,
            "best_role_only_accuracy": best_rate,
            "role_is_constant_within_pair": True,
            "interpretation": ("Le role du locuteur est constant dans chaque paire et la polarite y varie : "
                               "il ne contient aucune information sur la classe.")}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _relative(path: Path) -> str:
    try:
        return path.resolve().relative_to(_REPO_ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def write_report(out_dir: Path, results: Sequence[dict], *, corpus_path: Path,
                 source_corpus: Path, params: dict, provenance: str) -> tuple[Path, Path]:
    """Publie les deux bras acceptes, les rejets nommes et leurs empreintes."""
    arms: list[Arm] = []
    for result in results:
        if result["status"] == "accepted":
            pair = [row if isinstance(row, Arm) else Arm(**row) for row in result["arms"]]
            validate_pair(pair)
            arms.extend(pair)
    corpus_path.write_text(
        "".join(json.dumps(row.__dict__, ensure_ascii=False) + "\n" for row in arms),
        encoding="utf-8", newline="\n")
    rejection_counts = Counter(
        reason for result in results if result["status"] == "rejected"
        for reason in (result["attempts"][-1]["rejection_reasons"] if result["attempts"]
                       else ["no_attempt"]))
    virtue_available = sum(
        bool(result["attempts"][-1]["control"].get("counterpart_candidates"))
        for result in results if result["status"] == "accepted" and result["attempts"])
    accepted = [r for r in results if r["status"] == "accepted"]
    report = {
        "schema": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "what": "Lot apparie meme scenario/meme locuteur, avec et sans sophisme (#10355, section 2b)",
        "source_corpus": {"path": _relative(source_corpus), "sha256": sha256_file(source_corpus)},
        "params": params,
        "report_provenance": provenance,
        "n_attempted_pairs": len(results),
        "n_accepted_pairs": len(accepted),
        "n_rejected_pairs": len(results) - len(accepted),
        "n_rows": len(arms),
        "rejection_reasons_final_attempt": dict(sorted(rejection_counts.items())),
        "accepted_with_counterpart_control": virtue_available,
        "role_shortcut": role_shortcut(arms),
        "attempted_pairs": list(results),
        "corpus": {"path": _relative(corpus_path), "sha256": sha256_file(corpus_path)},
    }
    report_path = out_dir / REPORT_NAME
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2,
                                      default=_json_default) + "\n",
                           encoding="utf-8", newline="\n")
    md_path = out_dir / REPORT_MD_NAME
    md_path.write_text(render_markdown(report, report_path), encoding="utf-8", newline="\n")
    return report_path, md_path


def _rate(part: int, total: int) -> str:
    return f"{part / total:.4f}" if total else "non mesure"


def render_markdown(report: dict, report_path: Path) -> str:
    """Rendu lisible ; les valeurs sont lues du rapport, jamais reconstituees."""
    role = report["role_shortcut"]
    lines = [
        "# Lot apparie avec et sans sophisme",
        "",
        "Chaque paire conserve le scenario, la position defendue, le locuteur",
        "(`smoothTalker`) et l'interlocuteur. Seule la maniere d'argumenter change.",
        "Le bras positif est le texte du corpus val FR deja valide ; le negatif est",
        "accepte seulement si son reclassement rejette le sophisme cible et, quand la",
        "taxonomie declare une vertu opposee, si un controle la retrouve.",
        "",
        "## Resultat",
        "",
        f"- paires tentees : {report['n_attempted_pairs']}",
        f"- paires acceptees : **{report['n_accepted_pairs']}**",
        f"- paires rejetees : **{report['n_rejected_pairs']}** (motifs dans le rapport JSON)",
        f"- lignes publiees : {report['n_rows']} (deux par paire acceptee)",
        f"- paires acceptees avec controle positif sur vertu liee : {report['accepted_with_counterpart_control']}",
        "",
        "| Mesure | Valeur |",
        "|---|---:|",
        f"| Taux d'acceptation | {_rate(report['n_accepted_pairs'], report['n_attempted_pairs'])} |",
        f"| Accuracy du raccourci role -> polarite | {_rate(0, 1) if role['best_role_only_accuracy'] is None else format(role['best_role_only_accuracy'], '.4f')} |",
        "",
        "Le role reste `smoothTalker` dans les deux bras : il ne predit plus la",
        "polarite. L'accuracy affichee est celle de la meilleure regle constante",
        "utilisant uniquement ce role ; 0,5 sur un lot equilibre est le hasard.",
        "",
        "## Rejets a la derniere tentative",
        "",
        "| Motif | Paires |",
        "|---|---:|",
    ]
    for reason, count in report["rejection_reasons_final_attempt"].items():
        lines.append(f"| `{reason}` | {count} |")
    if not report["rejection_reasons_final_attempt"]:
        lines.append("| aucun | 0 |")
    lines += [
        "",
        "## Empreintes et rejeu",
        "",
        f"- corpus source : `{report['source_corpus']['sha256']}`",
        f"- lot JSONL : `{report['corpus']['sha256']}`",
        f"- rapport JSON : `{sha256_file(report_path)}`",
        "",
        "Le checkpoint est local et non committe. `--report-only` le relit sans",
        "cle ni reseau ; sur un clone frais, il reconstruit depuis le rapport",
        "publie, dont `attempted_pairs` conserve toutes les tentatives et tous",
        "les votes. Les motifs `vote_unparsed` et `vote_missing` sont des rejets",
        "de prudence, jamais des preuves d'absence de sophisme.",
        "",
    ]
    return "\n".join(lines)


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT)
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    parser.add_argument("--lang", default="fr", choices=("fr", "en"))
    parser.add_argument("--distractors", type=int, default=G.DEFAULT_DISTRACTORS)
    parser.add_argument("--max-attempts", type=int, default=DEFAULT_MAX_ATTEMPTS)
    parser.add_argument("--max-tokens", type=int, default=G.DEFAULT_MAX_TOKENS)
    parser.add_argument("--api-key-env", default=G.DEFAULT_API_KEY_ENV)
    parser.add_argument("--probe", action="store_true",
                        help="une generation et ses controles, sans ecrire de corpus")
    parser.add_argument("--report-only", action="store_true",
                        help="reconstruit sans maitre, cle ni reseau")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_arg_parser().parse_args(argv)
    records = select_positive_pairs(load_corpus(args.corpus), args.limit, args.seed)
    texts = B.load_texts()
    oppositions = load_virtue_oppositions()
    params = {
        "limit": args.limit, "seed": args.seed, "lang": args.lang,
        "distractors": args.distractors, "max_attempts": args.max_attempts,
        "max_tokens": args.max_tokens, "temperature_generation": 0.8,
        "temperature_control": 0.0, "teacher_model": G.DEFAULT_MODEL,
    }
    if not args.report_only:
        teacher = G.HubTeacher(api_key_env=args.api_key_env)
        if args.probe:
            result = generate_pair(
                records[0], texts, teacher, oppositions=oppositions,
                seed=args.seed + 10007, lang=args.lang, distractors=args.distractors,
                max_attempts=args.max_attempts, max_tokens=args.max_tokens)
            print(json.dumps({"pair_id": result["pair_id"], "status": result["status"],
                              "attempts": result["attempts"]}, ensure_ascii=False, indent=2))
            return 0 if result["status"] == "accepted" else 1
        args.out_dir.mkdir(parents=True, exist_ok=True)
        run_generation(records, texts, teacher, out_dir=args.out_dir,
                       oppositions=oppositions, seed=args.seed, lang=args.lang,
                       distractors=args.distractors, max_attempts=args.max_attempts,
                       max_tokens=args.max_tokens)
    results, provenance = load_results_for_report(args.out_dir)
    report_path, md_path = write_report(
        args.out_dir, results, corpus_path=args.out_dir / CORPUS_NAME,
        source_corpus=args.corpus, params=params, provenance=provenance)
    print(f"rapport : {report_path}")
    print(f"rendu   : {md_path}")
    print(f"paires  : {sum(r['status'] == 'accepted' for r in results)}/{len(results)} acceptees")
    return 0


if __name__ == "__main__":
    sys.exit(main())
