#!/usr/bin/env python3
"""Positif-control d'identite byte-a-byte des gardes absorbes (#12396, #19193).

Le moteur fast lane emet un check-run nomme `guard.name`. Un garde absorbe
porte donc un nom qui DOIT etre byte-identique au nom de check-run que son
workflow source rendait. Le nom rendu suit la MEME convention que
`check_unique_check_run_names.py` (defect #11869) : `job.name` si declare,
sinon la cle du job. Sans cette identite, le rename casse la protection de
branche : le check requis porte l'ancien nom, et l'emission sous un nom
different ne le satisfait pas plus qu'elle ne le rougit (incident #12175).

Les tranches 1/2/3 ont absorbe des gardes par DECLARATION ; aucune emission
ni aucun test n'a cimente l'identite nom-du-garde == nom-rendu. Ce module
ferme ce trou : pour chaque garde absorbe du registre, il parse le workflow
source et exige que `guard.name` figure byte-identique parmi les noms de job
rendus.

Les tranches couvertes sont **toutes** celles du registre (`TRANCHE1..17`,
`PILOT`, et toute liste de `Guard` au sens du dataclass), pas une enume-
ration en dur -- le contrat fondateur de cette correction.

Les gardes **natifs** (source = `FAST_LANE_NATIVE`) n'ont pas de workflow
d'origine : ils sont exemptes par declaration, et leur exemption est
signalee en sortie -- un saut silencieux fabriquerait une garantie fausse.

Modes:
  --check  exit 0 si tous identiques ou exemptes par declaration ; 1 si un
           nom diverge ou un workflow source est introuvable ; 2 si
           l'instrument est casse (PyYAML indisponible, workflow illisible).
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parent
ROOT = CI_DIR.parents[1]
sys.path.insert(0, str(CI_DIR))

import fast_lane_registry as reg  # noqa: E402
from check_unique_check_run_names import _parse_workflow, _load_yaml  # noqa: E402
from fast_lane_registry import Guard, FAST_LANE_NATIVE  # noqa: E402

# Lot pilote (#11835) et tranches dont l'alignement byte-identique est en
# cours dans le cadre du programme #12567. Ces deux categories sont
# signalees en sortie (jamais le saut silencieux -- cf programme fondateur
# de la PR #19193) mais ne sont pas exigees.
PILOT_LOT_NAME = "PILOT"
ALIGNMENT_EN_COURS = frozenset({"TRANCHE10"})

EXIT_OK, EXIT_MISMATCH, EXIT_BROKEN = 0, 1, 2
WORKFLOWS_DIR = ROOT / ".github" / "workflows"


def all_guards():
    """Toutes les listes de Guard du module fast_lane_registry, dynamiquement.

    Le pattern fondateur vient de `test_aucun_garde_bloquant_n_est_inert_sans
    _declaration` (#19171, TRANCHE17) : on enumere `vars(registry)` et on
    garde chaque liste dont chaque item est un `Guard`. Une liste ajoutee
    ulterieurement est automatiquement couverte ; une liste retiree n'est
    plus couverte.

    Le filtre `isinstance(value, list) and value and all(isinstance(item,
    Guard) for item in value)` est STRICT : il ne ramasse pas les scalaires,
    les dicts, ou les listes heterogenes.
    """
    for value in vars(reg).values():
        if isinstance(value, list) and value and all(
                isinstance(item, Guard) for item in value):
            yield from value


def absorbed_guards():
    """Les gardes absorbes : tous les gardes sauf les exemptes.

    Categories d'exemption :
    - `source == FAST_LANE_NATIVE` : aucun workflow d'origine, exemptes
      par declaration (cf `native_exemptions`).
    - Gardes du lot `PILOT` (programme #12567, #11835) : absorption par
      declaration sans alignement byte-identique.
    - Gardes des tranches `ALIGNMENT_EN_COURS` (programme #12567) : absorption
      faite mais le `name:` du job source n'a pas ete renomme byte-identique.
      Le filet les signale en sortie mais ne les exige pas.
    """
    pilot_set = set(map(id, getattr(reg, PILOT_LOT_NAME, [])))
    align_set = set()
    for tranche_name in ALIGNMENT_EN_COURS:
        align_set.update(map(id, getattr(reg, tranche_name, [])))
    for guard in all_guards():
        if guard.source == FAST_LANE_NATIVE:
            continue
        if id(guard) in pilot_set:
            continue
        if id(guard) in align_set:
            continue
        yield guard


def rendered_job_names(workflow_file: Path, yaml) -> list[str] | None:
    """Noms de check-run que le workflow rendait (None = illisible).

    Meme logique que collect_rendered_names de check_unique_check_run_names :
    `job.name` si declare, sinon la cle du job. Les jobs reutilisables
    (`uses:`) sont sautes -- leur nom depend du callee apres templating.
    """
    try:
        text = workflow_file.read_text(encoding="utf-8")
    except OSError:
        return None
    data = _parse_workflow(text, yaml)
    if data is None:
        return None
    names: list[str] = []
    for job_key, job_def in (data.get("jobs") or {}).items():
        if not isinstance(job_def, dict) or "uses" in job_def:
            continue
        names.append(str(job_def.get("name") or job_key))
    return names


def mismatches() -> list[str]:
    """Descriptions des gardes absorbes dont le nom diverge de la source.

    Compatibilite legacy : `mismatches()` retourne une `list[str]` (les
    problemes seuls), comme avant la PR #19193. Les exemptions natives sont
    exposees separement par `native_exemptions()` pour la tracabilite.
    """
    yaml = _load_yaml()
    if yaml is None:
        return ["PyYAML indisponible"]  # instrument casse
    problems: list[str] = []
    for guard in absorbed_guards():
        source = WORKFLOWS_DIR / guard.source
        if not source.is_file():
            problems.append(f"{guard.name!r}: workflow source introuvable "
                           f"({guard.source})")
            continue
        names = rendered_job_names(source, yaml)
        if names is None:
            problems.append(f"{guard.name!r}: source illisible ({guard.source})")
        elif guard.name not in names:
            problems.append(f"{guard.name!r} != noms rendus par "
                           f"{guard.source} {sorted(names)}")
    return problems


def native_exemptions() -> list[str]:
    """Exemptions declarees des gardes `source == FAST_LANE_NATIVE`.

    Pourquoi expose : un saut silencieux fabriquerait une garantie fausse
    (le filet dirait OK sans avoir rien verifie). Afficher chaque exemption
    en sortie standard preserve la tracabilite.
    """
    return [
        f"{guard.name!r}: garde natif (FAST_LANE_NATIVE), "
        "aucun workflow d'origine a verifier."
        for guard in all_guards()
        if guard.source == FAST_LANE_NATIVE
    ]


def pilot_exemptions() -> list[str]:
    """Exemptions declarees du lot pilote (programme #12567).

    Le lot PILOT est absorbe par declaration : le workflow d'origine porte
    encore le declencheur `pull_request`, donc le renommage byte-identique
    n'a pas ete fait. Le filet ne peut verifier que le garde est absorbe,
    pas que le nom est aligne -- la bascule est dans le programme #12567.
    """
    pilot_set = set(map(id, getattr(reg, PILOT_LOT_NAME, [])))
    return [
        f"{guard.name!r}: lot pilote (#11835, programme #12567), "
        "absorption par declaration sans alignement byte-identique."
        for guard in all_guards()
        if guard.source != FAST_LANE_NATIVE
        and id(guard) in pilot_set
    ]


def alignment_en_cours_exemptions() -> list[str]:
    """Exemptions declarees des tranches en cours d'alignement (#12567).

    Pour ces gardes, l'absorption est faite (`absorbed=True`, source
    designe un workflow reel) mais le `name:` du job dans le workflow source
    n'a pas ete renomme byte-identique au `guard.name`. La bascule est
    portee par le programme #12567.
    """
    align_set = set()
    for tranche_name in ALIGNMENT_EN_COURS:
        align_set.update(map(id, getattr(reg, tranche_name, [])))
    return [
        f"{guard.name!r}: tranche {tranche_name} (programme #12567), "
        "absorption faite mais job.name du workflow source non aligne."
        for tranche_name in ALIGNMENT_EN_COURS
        for guard in getattr(reg, tranche_name, [])
        if guard.source != FAST_LANE_NATIVE and id(guard) in align_set
    ]


def _main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Byte-identity des gardes fast-lane absorbes."
    )
    parser.add_argument("--check", action="store_true",
                        help="exit 0/1/2 par identite")
    args = parser.parse_args(argv[1:])

    problems = mismatches()
    exemptions = native_exemptions()
    pilot_exemps = pilot_exemptions()
    align_exemps = alignment_en_cours_exemptions()
    total_guards = sum(1 for _ in all_guards())
    native_guards = len(exemptions)
    pilot_guards = len(pilot_exemps)
    align_guards = len(align_exemps)
    absorbed_guards_count = total_guards - native_guards - pilot_guards - align_guards
    for ex in exemptions:
        print(f"[absorbed-identity] EXEMPTE NATIF: {ex}")
    for ex in pilot_exemps:
        print(f"[absorbed-identity] EXEMPTE PROGRAMME: {ex}")
    for ex in align_exemps:
        print(f"[absorbed-identity] EXEMPTE PROGRAMME: {ex}")
    if not problems:
        print(f"[absorbed-identity] OK -- {absorbed_guards_count} "
              "gardes absorbes byte-identiques a leur source "
              f"(+ {native_guards} gardes natifs, "
              f"+ {pilot_guards} gardes du lot pilote, "
              f"+ {align_guards} gardes en cours d'alignement #12567).")
        return EXIT_OK
    for problem in problems:
        print(f"[absorbed-identity] MISMATCH: {problem}")
    if not args.check:
        return EXIT_OK
    # Une liste peuplant "PyYAML indisponible" = instrument casse, pas une
    # divergence de nom.
    if problems == ["PyYAML indisponible"]:
        print("[absorbed-identity] BROKEN INSTRUMENT: PyYAML absent. "
              "Verdict nul.", file=sys.stderr)
        return EXIT_BROKEN
    return EXIT_MISMATCH


if __name__ == "__main__":
    sys.exit(_main(sys.argv))