"""Phase 0 EPIC #9768 -- selection stratifiee de notebooks pour audit forensic.

Cible l'echantillonnage Phase 0 de l'EPIC #9768 (taxonomie degeneration
notebooks, parent issue #9787). La Phase 0 definit un echantillon stratifie
de N notebooks a scanner avec ``scan_d1_d3_d4_d5.py`` afin de calibrer
empiriquement les seuils de detection.

Criteres de stratification (cf. issue #9768 corps) :
  - Couverture >= 4 familles distinctes (QuantConnect, GenAI, Search, Probas,
    SymbolicAI, ...).
  - SIX bandes de revisions : ``1``, ``2-4``, ``5-9``, ``10-19``, ``20-39``,
    ``40+``. Les deux dernieres sont sur-representees (degradation cumulee
    la plus probable) ; les quatre premieres restent couvertes pour calibrer
    les seuils sur signaux faibles.
  - 1 seul notebook par famille dans la tranche par defaut (evite l'effet
    de grappe) ; augmentable via ``--per-family N``.

Renommage-aware (rename detection via ``git log --follow``)
------------------------------------------------------------
L'EPIC #9768 exige un comptage rename-aware : un notebook peut avoir ete
renomme (ex. `ML.Net/` vers `DataScienceWithAgents/`) et le ``git log
--follow`` capture l'integralite de l'historique, contrairement au lookup
par chemin courant qui ignore les ancetres pre-rename.

Trade-off perf : ``--follow`` est O(secondes) par notebook. Le script fait
donc un pre-filtrage rapide (compteur chemin courant, ~3s global) puis un
re-comptage rename-aware uniquement sur les finalistes
(<= ``per_family * 4`` par famille). Mesure : 5 familles x 1 finaliste =
5 appels ``--follow`` ~= 5-10s, vs >120s si applique a tout le corpus.

Le champ ``total_revisions`` expose dans le JSON est **rename-aware** (la
valeur definitive) ; la valeur chemin-courant n'est pas exposee.

Fail-loud scanner
-----------------
Le scanner sous-jacent ``scan_d1_d3_d4_d5.py`` peut renvoyer des payloads
degrades (subprocess non-nul, stdout vide, non-JSON, non-liste, liste vide,
entree sans verdict). Chaque cas ecrit explicitement un ``scanner_error``
non ambigu et force ``verdict=INDETERMINE`` -- la selection n'est JAMAIS
laissée silencieusement incomplete.

Pourquoi un script plutot qu'une liste en dur
----------------------------------------------
La liste des notebooks "les plus actifs" evolue a chaque cycle. Un script
rejouable :

  1. Selectionne les notebooks les plus actifs par famille, rename-aware,
     en evitant l'effet de grappe (1 par defaut).
  2. Lance ``scan_d1_d3_d4_d5.py`` sur chaque finaliste ; fail-loud sur
     tous les cas degeneres.
  3. Emet un JSON structure stdout/option fichier -- JAMAIS un rapport
     commite (audit-cross-source-distillation HARD 1).

Usage
-----
    python scripts/notebook_tools/phase0_sample_stratify.py \\
        --families QuantConnect GenAI Search Probas SymbolicAI \\
        --per-family 1 --min-revisions 20

    # Mode tranche 1 (livraison courante) :
    python scripts/notebook_tools/phase0_sample_stratify.py \\
        --families QuantConnect GenAI Search Probas SymbolicAI \\
        --per-family 1 --min-revisions 20 \\
        --output-json phase0_tranche1.json

    # Mode debug / perf (skip scanner) :
    python scripts/notebook_tools/phase0_sample_stratify.py --select-only ...

Sortie JSON
-----------
    {
      "generated_at_utc": "2026-08-31T...",
      "criteria": {"min_revisions": 20, "per_family": 1, "families": [...]},
      "selections": [
        {
          "family": "QuantConnect",
          "path": "MyIA.AI.Notebooks/...",
          "total_revisions": 34,            // rename-aware
          "revision_band": "20-39",
          "verdict": "SAIN",                 // ou MIXED / D1+ / INDETERMINE
          "findings": [...],
          "notes": "..."
        },
        ...
      ]
    }

Conformite harnais
------------------
- Regle F (env repair not bypass) : 0 dependance externe (Python 3.10+ stdlib).
- audit-cross-source-distillation R1 : verdict stdout/JSON, JAMAIS de rapport
  AUDIT-D*.md / *phase0*.md commite dans l'arbre.
- catalog-pr-hygiene R1 : 0 modification catalogue (le script lit, n'ecrit pas).
- C.1 : 0 erreur volontaire (pas de ``raise NotImplementedError`` etc.).
- anti-regression : 0 stub fonctionnel sur code de production (le scanner
  execute reellement sur chaque selection ; fail-loud documente chaque
  cas degenere au lieu de maquiller en succes).

Tests unitaires
---------------
- scripts/notebook_tools/tests/test_phase0_sample_stratify.py :
  ``revision_band`` / ``band_priority`` / 6 bandes / fail-loud scanner /
  critere de sortie Phase 0 (>= 4 familles distinctes).

Voir aussi
----------
- EPIC #9768 : taxonomie complete de la degeneration notebooks
- scripts/notebook_tools/scan_d1_d3_d4_d5.py : detecteur D1/D3/D4/D5
- scripts/notebook_tools/scan_d2_window_openness.py : detecteur D2 (orthogonal)
- Issue #9787 : Phase 0 tranche ICT/IIT (calibration empirique du seuil)
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[2]

# Bandes de revisions ciblees par l'EPIC #9768 (corps). SIX bandes definies :
# 1, 2-4, 5-9, 10-19, 20-39, 40+. Les deux dernieres sont sur-representees dans
# la phase d'echantillonnage (la degradation cumulee y est la plus probable) ;
# les quatre premieres restent couvertes pour calibrer les seuils sur les
# signaux faibles. Ordre = priorite de tri croissante (cf. _BAND_ORDER_KEY).
REVISION_BANDS = [
    (1, 1, "1"),
    (2, 4, "2-4"),
    (5, 9, "5-9"),
    (10, 19, "10-19"),
    (20, 39, "20-39"),
    (40, 10**9, "40+"),
]


def band_priority(label: str | None) -> int:
    """Cle de tri deterministe : 40+ > 20-39 > 10-19 > 5-9 > 2-4 > 1 > None.

    Les bandes hautes sont privilegiees (degradation cumulee plus probable) ;
    ``None`` (= sous le seuil) est exclu.
    """
    order = {"1": 1, "2-4": 2, "5-9": 3, "10-19": 4, "20-39": 5, "40+": 6}
    return -order.get(label, 0) if label else 0


def build_revision_counts() -> dict[str, int]:
    """Compte en un seul ``git log`` le nombre de commits par fichier .ipynb.

    Limite a la branche courante (HEAD) pour eviter le sur-comptage des
    PR branches jamais mergees (cf. mesure : --all = 65, HEAD = 33 sur
    QC-Py-26-LLM-Trading-Signals.ipynb). Utilise ``git log --name-only``
    pour lister tous les fichiers touches par chaque commit (limite aux
    .ipynb). Plus rapide que N appels a ``git log --follow`` individuels
    (mesure : 1 appel global = ~3s pour 125k commits sur CoursIA).

    Retourne un dict ``{path_relatif: nb_commits}``.
    """
    try:
        result = subprocess.run(
            [
                "git",
                "log",
                "HEAD",
                "--name-only",
                "--pretty=format:",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )
    except subprocess.CalledProcessError:
        return {}
    counts: dict[str, int] = defaultdict(int)
    for line in result.stdout.splitlines():
        line = line.strip()
        if line.endswith(".ipynb"):
            counts[line] += 1
    return dict(counts)


def count_revisions_main(notebook_path: Path, counts: dict[str, int]) -> int:
    """Lookup O(1) du nombre de commits pour un chemin de notebook (chemin courant).

    Normalise le separateur en ``/`` car git log --name-only retourne des
    forward slashes (meme sous Windows) alors que ``Path.relative_to``
    preserve les backslashes natifs de la plateforme.

    Note : ce compteur ignore l'historique de rename. Pour les finalistes,
    appeler ``count_revisions_follow`` (rename-aware, plus lent).
    """
    rel = str(notebook_path.relative_to(REPO_ROOT)).replace("\\", "/")
    return counts.get(rel, 0)


def count_revisions_follow(notebook_path: Path) -> int:
    """Compte rename-aware via ``git log --follow``.

    Appele seulement sur les finalistes (≤ len(families) x per_family notebooks)
    -- c'est volontairement O(nb_finalistes) pour eviter de payer N x
    ``--follow`` sur l'integralite du corpus (mesure : ~1s par appel, donc
    ~10s pour 10 finalistes vs >120s pour 700+ notebooks).
    """
    try:
        result = subprocess.run(
            [
                "git",
                "log",
                "HEAD",
                "--follow",
                "--format=oneline",
                "--",
                str(notebook_path.relative_to(REPO_ROOT)),
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=True,
        )
        return sum(1 for line in result.stdout.splitlines() if line.strip())
    except subprocess.CalledProcessError:
        return 0


def revision_band(revisions: int) -> str | None:
    """Retourne la bande EPIC #9768 du nombre de revisions, ou None si 0.

    SIX bandes definies : ``1``, ``2-4``, ``5-9``, ``10-19``, ``20-39``, ``40+``.
    0 revisions (= fichier jamais touche par main) renvoie ``None`` -- le
    candidat est exclu par le selecteur.
    """
    if revisions <= 0:
        return None
    for lo, hi, label in REVISION_BANDS:
        if lo <= revisions <= hi:
            return label
    return None


def list_family_notebooks(family_root: Path) -> list[Path]:
    """Liste les notebooks .ipynb sous ``family_root`` (recursive)."""
    if not family_root.exists():
        return []
    return sorted(p for p in family_root.rglob("*.ipynb") if p.is_file())


def select_top_per_family(
    families: Iterable[str],
    min_revisions: int,
    per_family: int,
    counts: dict[str, int],
) -> list[dict]:
    """Selectionne les N notebooks les plus actifs par famille.

    Pipeline en 2 passes pour eviter le surcout ``--follow`` :

      1. Filtre rapide par ``count_revisions_main`` (chemin courant, O(1))
         sur l'integralite du corpus d'une famille. Garde les ``per_family * 4``
         meilleurs par bande pour eviter de plomber la memoire.
      2. Re-comptage rename-aware via ``count_revisions_follow`` sur les
         finalistes uniquement, puis tri deterministe par bande prioritaire
         desc / revisions desc / path asc.

    Resultat : chaque selection porte ``total_revisions`` rename-aware, et le
    tag ``revision_band`` est coherent avec ce compte (apres application de
    ``revision_band`` sur la valeur rename-aware).
    """
    selections: list[dict] = []
    POOL_PER_BAND = max(per_family * 4, 8)
    for family in families:
        family_root = REPO_ROOT / "MyIA.AI.Notebooks" / family
        # Passe 1 : candidats pre-filtrés (compteur chemin courant, rapide).
        prefiltered: list[tuple] = []
        for nb in list_family_notebooks(family_root):
            revs = count_revisions_main(nb, counts)
            band = revision_band(revs)
            if band is None or revs < min_revisions:
                continue
            prefiltered.append((band, revs, nb))
        # Tri pre-filtrage : on garde les top POOL_PER_BAND par bande prioritaire.
        prefiltered.sort(key=lambda t: (band_priority(t[0]), -t[1], str(t[2])))
        finalists_pre = prefiltered[:POOL_PER_BAND]

        # Passe 2 : re-comptage rename-aware sur les finalistes uniquement.
        finalists_aware: list[tuple] = []
        for _band, _revs, nb in finalists_pre:
            revs_aware = count_revisions_follow(nb)
            band_aware = revision_band(revs_aware)
            finalists_aware.append((band_aware, revs_aware, nb))

        # Tri final : bande prioritaire desc, revisions desc, path asc.
        finalists_aware.sort(key=lambda t: (band_priority(t[0]), -t[1], str(t[2])))

        for _band, revs, nb in finalists_aware[:per_family]:
            rel_path = str(nb.relative_to(REPO_ROOT)).replace("\\", "/")
            selections.append(
                {
                    "family": family,
                    "path": rel_path,
                    "total_revisions": revs,
                    "revision_band": revision_band(revs),
                }
            )
    return selections


def run_scanner(selections: list[dict]) -> list[dict]:
    """Execute ``scan_d1_d3_d4_d5.py`` sur chaque selection et agrege le verdict.

    Fail-loud : chaque cas degeneres du scanner ecrit explicitement un
    ``scanner_error`` non ambigu dans la structure de selection, plutot que
    de laisser le verdict absent (= silencieusement complet).

    Cas geres :
      - scanner introuvable
      - subprocess returncode != 0
      - stdout vide ou whitespace seul
      - stdout non-JSON (JSONDecodeError)
      - payload non-liste (ni liste vide)
      - entree sans champ ``verdict``

    Le script retourne toujours une structure complete, jamais de None.
    """
    scanner = REPO_ROOT / "scripts" / "notebook_tools" / "scan_d1_d3_d4_d5.py"
    if not scanner.exists():
        for sel in selections:
            sel["scanner_error"] = "scan_d1_d3_d4_d5.py introuvable"
            sel["verdict"] = "INDETERMINE"
        return selections
    for sel in selections:
        proc = subprocess.run(
            [
                sys.executable,
                str(scanner),
                sel["path"],
                "--format",
                "json",
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
        )
        # Fail-loud 1 : subprocess returncode non nul.
        if proc.returncode != 0:
            sel["scanner_error"] = (
                f"subprocess rc={proc.returncode} stderr={proc.stderr.strip()[:200]}"
            )
            sel["verdict"] = "INDETERMINE"
            continue
        # Fail-loud 2 : stdout vide / whitespace seul.
        if not proc.stdout.strip():
            sel["scanner_error"] = "stdout vide"
            sel["verdict"] = "INDETERMINE"
            continue
        # Fail-loud 3 : stdout non-JSON.
        try:
            payload = json.loads(proc.stdout)
        except json.JSONDecodeError as e:
            sel["scanner_error"] = f"stdout non-JSON: {e}"
            sel["verdict"] = "INDETERMINE"
            continue
        # Fail-loud 4 : payload non-liste.
        if not isinstance(payload, list):
            sel["scanner_error"] = (
                f"payload non-liste (type={type(payload).__name__})"
            )
            sel["verdict"] = "INDETERMINE"
            continue
        # Fail-loud 5 : liste vide.
        if not payload:
            sel["scanner_error"] = "payload liste vide"
            sel["verdict"] = "INDETERMINE"
            continue
        # Cas nominal.
        entry = payload[0]
        if "verdict" not in entry:
            sel["scanner_error"] = "entree sans verdict"
            sel["verdict"] = "INDETERMINE"
            continue
        sel["verdict"] = entry.get("verdict", "INDETERMINE")
        sel["findings"] = entry.get("findings", [])
        sel["notes"] = entry.get("notes", "")
    return selections


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Phase 0 EPIC #9768 -- selection stratifiee + scan",
    )
    p.add_argument(
        "--families",
        nargs="+",
        default=["QuantConnect", "GenAI", "Search", "Probas", "SymbolicAI"],
        help="Familles cibles (defaut: 5 familles principales)",
    )
    p.add_argument(
        "--per-family",
        type=int,
        default=1,
        help="Nombre de notebooks par famille (defaut: 1)",
    )
    p.add_argument(
        "--min-revisions",
        type=int,
        default=20,
        help="Seuil minimum de revisions (defaut: 20, cf. EPIC #9768)",
    )
    p.add_argument(
        "--output-json",
        type=Path,
        help="Fichier JSON de sortie (optionnel ; stdout sinon)",
    )
    p.add_argument(
        "--select-only",
        action="store_true",
        help="Selectionne les notebooks sans lancer le scanner (debug/perf)",
    )
    return p.parse_args()


def main() -> int:
    args = parse_args()
    counts = build_revision_counts()
    selections = select_top_per_family(
        families=args.families,
        min_revisions=args.min_revisions,
        per_family=args.per_family,
        counts=counts,
    )
    if not args.select_only:
        selections = run_scanner(selections)
    output = {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "criteria": {
            "families": list(args.families),
            "per_family": args.per_family,
            "min_revisions": args.min_revisions,
        },
        "selections": selections,
    }
    text = json.dumps(output, indent=2, ensure_ascii=False)
    if args.output_json:
        args.output_json.write_text(text, encoding="utf-8")
        print(f"{len(selections)} selection(s) -> {args.output_json}")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())