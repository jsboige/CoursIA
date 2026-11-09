#!/usr/bin/env python3
"""Verdict du gate de Phase 3 : un rapport candidat confronte a la reference commitee.

Sous-grain de #20233 (« brancher ces chiffres comme reference du gate »). Les
briques 1-3 ont mesure les references (majoritaire 0.0034 et lexicale 0.2198 en
plis groupes, #20233 ; zero-shot 0.0145, #20244 ; marge FT LoRA, #20359) mais
aucune ne rend le verdict : ``ft_floor`` cite la reference en prose
(``"references": {"lexicale": "brique 1 (#20233) : macro-F1 0,2198"}``) sans
jamais comparer. Tant que le verdict n'est pas machine, « BEATS » reste une
phrase, pas une mesure falsifiable -- c'est la classe de defaut que le gate de
Phase 3 (ai-01, rappele dans #17578) voulait fermer en nommant une reference
que personne ne pouvait calculer.

Le gate est deliberement etroit : il ne re-evalue rien, n'entraine rien, et ne
reecrit aucun organe. Il lit un rapport produit par les organes existants
(``zeroshot_report.json``, ``ft_report.json`` ou tout rapport au meme contrat),
verifie que la mesure est COMPARABLE a la reference, puis rend l'un des
verdicts :

- ``BEATS`` : la macro-F1 depasse la lexicale ET le plancher majoritaire ;
- ``BEATS_MAJORITY_ONLY`` : elle depasse le majoritaire mais pas la lexicale ;
- ``NO_BEATS`` : elle ne depasse meme pas le majoritaire ;
- ``REFUSED_*`` : la mesure n'est pas comparable, et un chiffre non comparable
  ne doit jamais avoir l'air d'un resultat (le niveau noeud refuse deja ainsi
  dans ``measure_baselines_tranche_b``, #21865).

Comparabilite (tout manquement = REFUSED, valeur fautive citee dans le verdict) :

1. **meme niveau** : ``report["level"]`` == niveau de la reference ; le niveau
   noeud est declare non mesurable par la reference elle-meme
   (``node_level.measurable = false``, 280 etiquettes pour 280 paires) ;
2. **meme corpus** : le sha256 du corpus candidat == celui de la reference ;
3. **meme protocole de plis** : meme graine protocolaire et meme nombre de plis
   -- sinon les plis ne sont pas ceux ou les references ont ete mesurees ;
4. **une mesure rendue** : ``macro_f1_mean`` n'est pas None.

La marge est publiee en points ET en ecarts-types de la reference lexicale
(``margin_vs_lexical_sigma``) : un BEATS a +0.1 sigma est un verdict fragile,
et le dire fait partie du verdict.

Limites dites :

- ``ft_floor --limit`` (mesure partielle) n'est pas consigne au rapport : le
  gate ne peut pas le detecter, le rapport doit porter la mesure complete ;
- le champ candidat est cherche parmi ``("ft", "zero_shot")`` -- si le rapport
  porte les deux, ``ft`` est lu (c'est lui, le plus fort des deux, que le gate
  doit juger).

Usage::

    python scripts/fallacy_detection/gate_phase3.py --report ft_report.json
    python scripts/fallacy_detection/gate_phase3.py --report ft_report.json \\
        --reference MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/baselines_branch.json

stdlib only. Verdict imprime en clair et en JSON (``--json``). rc 0 chaque fois
que le gate a rendu un verdict -- refuser EST repondre ; rc 2 si l'entree ou la
reference est illisible.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

DEFAULT_REFERENCE = Path(
    "MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/baselines_branch.json")

# Cles candidates, par ordre de lecture : un rapport qui porte les deux mesure
# le zero-shot ET le FT ; c'est le FT que le gate doit juger.
CANDIDATE_KEYS = ("ft", "zero_shot")

REQUIRED_REFERENCE_KEYS = (
    "corpus", "level", "seed", "folds", "baselines", "node_level")


class GateInputError(SystemExit):
    """Entree ou reference illisible : le gate n'a pas de verdict a rendre."""


def load_reference(path: Path) -> dict:
    """Charge la reference commitee et valide les champs que le gate lit."""
    try:
        reference = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise GateInputError(f"reference illisible : {path} ({exc})") from exc
    except json.JSONDecodeError as exc:
        raise GateInputError(f"reference non-JSON : {path} ({exc})") from exc
    missing = [key for key in REQUIRED_REFERENCE_KEYS if key not in reference]
    if missing:
        raise GateInputError(
            f"reference incomplete : {path} (champs absents : {', '.join(missing)})")
    try:
        sha = reference["corpus"]["sha256"]
        majority = reference["baselines"]["majority_grouped"]["macro_f1_mean"]
        lexical = reference["baselines"]["lexical_centroid_grouped"]["macro_f1_mean"]
        lexical_std = reference["baselines"]["lexical_centroid_grouped"]["macro_f1_std"]
    except (KeyError, TypeError) as exc:
        raise GateInputError(
            f"reference incomplete : {path} (champ {exc} absent ou mal forme)") from exc
    if majority is None or lexical is None or lexical_std in (None, 0):
        raise GateInputError(
            f"reference non mesurable : {path} (majoritaire/lexicale sans valeur, "
            "ou ecart-type lexical nul)")
    return reference


def candidate_measure(report: dict) -> tuple[str, dict] | None:
    """Rend (cle, mesure) du rapport candidat, None si le contrat n'est pas tenu."""
    for key in CANDIDATE_KEYS:
        measure = report.get(key)
        if isinstance(measure, dict):
            return key, measure
    return None


def gate(reference: dict, report: dict, reference_path: Path = DEFAULT_REFERENCE) -> dict:
    """Rend le verdict du gate : comparabilite d'abord, comparaison ensuite.

    Un refus porte toujours son motif et la valeur fautive : un lecteur du
    verdict doit pouvoir corriger le rapport sans relire le code.
    """
    found = candidate_measure(report)
    if found is None:
        return _refused(report, "REFUSED_NO_MEASURE",
                        f"aucune cle candidate parmi {CANDIDATE_KEYS} dans le rapport")
    source, measure = found
    macro = measure.get("macro_f1_mean")
    majority = reference["baselines"]["majority_grouped"]["macro_f1_mean"]
    lexical = reference["baselines"]["lexical_centroid_grouped"]["macro_f1_mean"]
    lexical_std = reference["baselines"]["lexical_centroid_grouped"]["macro_f1_std"]

    if report.get("level") != reference["level"]:
        return _refused(report, "REFUSED_LEVEL",
                        f"niveau {report.get('level')!r} != {reference['level']!r} "
                        "(reference mesuree au niveau branche ; le niveau noeud y est "
                        f"declare non mesurable : {reference['node_level']})",
                        source=source)
    corpus = report.get("corpus") or {}
    if corpus.get("sha256") != reference["corpus"]["sha256"]:
        return _refused(report, "REFUSED_CORPUS",
                        f"corpus sha256 {str(corpus.get('sha256'))[:12]}… != "
                        f"{str(reference['corpus']['sha256'])[:12]}… "
                        f"({reference['corpus']['path']})",
                        source=source)
    if report.get("seed") != reference["seed"]:
        return _refused(report, "REFUSED_FOLDS",
                        f"graine protocolaire {report.get('seed')!r} != "
                        f"{reference['seed']!r} : les plis ne sont pas ceux de la "
                        "reference", source=source)
    if report.get("folds") != reference["folds"]:
        return _refused(report, "REFUSED_FOLDS",
                        f"{report.get('folds')!r} plis != {reference['folds']!r} "
                        "plis de la reference : les plis ne sont pas ceux de la "
                        "reference", source=source)
    if macro is None:
        return _refused(report, "REFUSED_NO_MEASURE",
                        "macro_f1_mean absent du rapport (aucun pli score)",
                        source=source)

    verdict = ("BEATS" if macro > lexical and macro > majority
               else "BEATS_MAJORITY_ONLY" if macro > majority
               else "NO_BEATS")
    return {
        "verdict": verdict,
        "refusal_reason": None,
        "candidate": {
            "source": source,
            "model": report.get("model"),
            "model_revision": report.get("model_revision"),
            "level": report.get("level"),
            "corpus_sha256": corpus.get("sha256"),
            "seed": report.get("seed"),
            "folds": report.get("folds"),
            "macro_f1_mean": macro,
            "macro_f1_std": measure.get("macro_f1_std"),
        },
        "reference": {
            "path": str(reference_path),
            "level": reference["level"],
            "corpus_sha256": reference["corpus"]["sha256"],
            "seed": reference["seed"],
            "folds": reference["folds"],
            "majority_macro_f1": majority,
            "lexical_macro_f1": lexical,
            "lexical_macro_f1_std": lexical_std,
        },
        "margins": {
            "vs_majority_points": round(macro - majority, 4),
            "vs_lexical_points": round(macro - lexical, 4),
            "margin_vs_lexical_sigma": round((macro - lexical) / lexical_std, 2),
        },
    }


def _refused(report: dict, verdict: str, reason: str, *, source: str | None = None) -> dict:
    """Verdict de refus : la raison citee, jamais un chiffre qui aurait l'air d'un resultat."""
    return {
        "verdict": verdict,
        "refusal_reason": reason,
        "candidate": {"source": source,
                      "model": report.get("model"),
                      "level": report.get("level"),
                      "corpus_sha256": (report.get("corpus") or {}).get("sha256"),
                      "seed": report.get("seed"),
                      "folds": report.get("folds")},
        "reference": None,
        "margins": None,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--report", type=Path, required=True,
                        help="Rapport candidat (zeroshot_report.json, ft_report.json…)")
    parser.add_argument("--reference", type=Path, default=DEFAULT_REFERENCE,
                        help="Reference commitee du gate (defaut : %(default)s)")
    parser.add_argument("--json", action="store_true",
                        help="Rend aussi le verdict en JSON sur stdout.")
    args = parser.parse_args(argv)

    try:
        reference = load_reference(args.reference)
        try:
            report = json.loads(args.report.read_text(encoding="utf-8"))
        except OSError as exc:
            raise GateInputError(
                f"rapport illisible : {args.report} ({exc})") from exc
        except json.JSONDecodeError as exc:
            raise GateInputError(
                f"rapport non-JSON : {args.report} ({exc})") from exc
    except GateInputError as exc:
        print(f"gate_phase3 : {exc}", file=sys.stderr)
        return 2

    verdict = gate(reference, report, reference_path=args.reference)
    if args.json:
        print(json.dumps(verdict, indent=1, ensure_ascii=False))
    margins = verdict.get("margins")
    if verdict["refusal_reason"]:
        print(f"{verdict['verdict']} : {verdict['refusal_reason']}")
    else:
        candidate = verdict["candidate"]
        print(f"{verdict['verdict']} : macro-F1 {candidate['macro_f1_mean']:.4f} "
              f"({candidate['source']}, {candidate['model']}) vs lexicale "
              f"{verdict['reference']['lexical_macro_f1']:.4f} et majoritaire "
              f"{verdict['reference']['majority_macro_f1']:.4f} ; marge "
              f"{margins['vs_lexical_points']:+.4f} points "
              f"({margins['margin_vs_lexical_sigma']:+.2f} sigma de la reference)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
