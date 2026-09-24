#!/usr/bin/env python3
"""Guard de dérive : testpaths pytest.ini vs couverture CI.

Compare les testpaths déclarés dans pytest.ini (les suites du dépôt) à la
couverture réelle des workflows qui invoquent pytest. Rougit sur tout
testpath ni couvert par un workflow ni déclaré `CI-EXCLUDED`.

Couverture = cibles déclarées dans WORKFLOW_COVERAGE. Chaque cible déclarée
doit apparaître littéralement dans son fichier workflow : si un run perd une
cible sans mise à jour ici, le guard le détecte (dérive workflow sans
mise à jour du guard, dans les deux sens).

Exclusions = marqueurs `# CI-EXCLUDED: <testpath> — <raison>` lus dans les
fichiers workflows (co-localisés avec les runs qu'ils exemptent).

Usage:
    python scripts/check_testpaths_coverage.py [--verbose] [--repo-root DIR]

Exit 0 = aucune dérive. Exit 1 = au moins un testpath non couvert non exclu,
ou une cible déclarée disparue de son workflow.
"""

from __future__ import annotations

import argparse
import configparser
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
PYTEST_INI = REPO_ROOT / "pytest.ini"

# Cibles pytest par workflow (déclarées, source de vérité du guard). Chacune
# doit apparaître verbatim dans le fichier : le guard échoue si une cible
# disparaît du workflow sans mise à jour ici. Les cibles FICHIER (ex.
# test_gitleaks_*.py) ne couvrent aucun testpath (un testpath = un dossier
# entier) — elles sont déclarées pour la vérification verbatim, pas pour la
# couverture.
WORKFLOW_COVERAGE: dict[str, list[str]] = {
    ".github/workflows/scripts-tests.yml": [
        "scripts/tests",
        # scripts/secrets/tests : dir entier (famille 4 de #14615) — les 2
        # modules gitleaks y skip sans binaire (gate binaire = secret-scan.yml,
        # cibles fichier ci-dessous).
        "scripts/secrets/tests",
        "scripts/notebook_tools/tests",
        "scripts/lean/tests",
        "scripts/translation/tests",
        "scripts/audit/tests",
        # scripts/fallacy_detection/tests : dir entier (#17580) — la garde
        # argumentum_snapshot (14 tests) devient un test de la collection.
        "scripts/fallacy_detection/tests",
        "MyIA.AI.Notebooks/GameTheory/tests",
        "MyIA.AI.Notebooks/QuantConnect/scripts/tests",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_bg_tree_lock.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_prover_forensic_guards.py",
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-PythonForDataScience/tests",
        # scripts/quantconnect/tests : dir entier (famille 3 de #14615) —
        # 254 tests / 9 modules, hermétique (mesure firsthand 2026-09-05 :
        # 253 verts + 1 skip de donnée, yfinance absent de l'env).
        "scripts/quantconnect/tests",
        # GradeBookApp : dir entier (famille 5 de #14615) — 15 tests
        # (test_fuzzy_match_group.py seul), deps rapidfuzz/unidecode/openpyxl
        # ajoutées au pip install du job, zéro PII (journal auto-créé).
        "GradeBookApp",
    ],
    ".github/workflows/ml-tests.yml": [
        "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/tests",
    ],
    # genai-helpers-tests.yml : famille GenAI helpers, dir entier (tranche 2
    # de #13746) — 138 tests (errants racine helpers/ + helpers/tests/),
    # deps numpy/requests/python-dotenv/pillow/librosa au pip install du job.
    ".github/workflows/genai-helpers-tests.yml": [
        "MyIA.AI.Notebooks/GenAI/shared/helpers",
    ],
    ".github/workflows/secret-scan.yml": [
        "scripts/secrets/tests/test_gitleaks_qwen_rule.py",
        "scripts/secrets/tests/test_gitleaks_10143_classes.py",
    ],
    # ict-tests.yml : scopé à MyIA.AI.Notebooks/IIT/ICT-Series (test-cwd
    # local, test-args relatifs) — ne couvre aucun testpath de la racine.
    # Présent dans le dict avec liste vide = inspecté et tranché volontaire.
    ".github/workflows/ict-tests.yml": [],
}

# Marqueur d'exclusion : `# CI-EXCLUDED: <testpath> — <raison>` en commentaire
# d'un workflow. L'em-dash "—" est le séparateur (format #10903).
CI_EXCLUDED_MARKER = re.compile(r"^\s*#\s*CI-EXCLUDED:\s*(\S+?)\s*—\s*(.+)$")


def load_testpaths(pytest_ini: Path) -> list[str]:
    """Lit les testpaths de pytest.ini (ordre de déclaration préservé)."""
    parser = configparser.ConfigParser()
    with pytest_ini.open(encoding="utf-8") as fh:
        parser.read_file(fh)
    raw = parser.get("pytest", "testpaths")
    return [line.strip() for line in raw.splitlines() if line.strip()]


def load_ci_excluded(repo_root: Path) -> dict[str, str]:
    """Lit les marqueurs CI-EXCLUDED dans tous les workflows."""
    excluded: dict[str, str] = {}
    for wf in sorted((repo_root / ".github/workflows").glob("*.yml")):
        for line in wf.read_text(encoding="utf-8").splitlines():
            m = CI_EXCLUDED_MARKER.match(line)
            if m:
                path, reason = m.group(1), m.group(2).strip()
                if path in excluded:
                    raise SystemExit(
                        f"CI-EXCLUDED dupliqué pour {path} "
                        f"({excluded[path]} vs {reason})"
                    )
                excluded[path] = reason
    return excluded


def _partition_run_blocks(text: str) -> tuple[set[str], set[str]]:
    """Sépare les cibles en (couvertes, floors) selon les blocs `run:` réels.

    Chaque ligne `run: |` initie un nouveau bloc ; la fermeture se base
    sur l'**indentation du `run: |`** : toute ligne indentée **strictement
    plus** que `run: |` appartient au bloc, toute ligne à la même
    indentation ou moins le ferme. On distingue les steps frères en
    s'appuyant strictement sur cette règle YAML — l'implémentation
    d'origine considérait la condition `non indentée`, ce qui fusionnait
    indûment des steps `run: |` frères quand le premier était aligné en
    colonne 0.

    Un bloc est classé `floor` si toutes ses lignes actives (non
    commentaire, non vide) contiennent `--collect-only`. Sinon (au moins
    une ligne d'exécution pure), il est classé `covered`.

    Le défaut mesuré dans #17250 : un step floor `--collect-only`
    satisfaisait verbatim le garde de dérive. La séparation selon le rôle
    du bloc ferme ce défaut sans changer l'API publique.
    """
    covered: set[str] = set()
    floors: set[str] = set()
    block_targets: set[str] = set()
    block_collect_only: bool | None = None
    block_indent: int | None = None

    def _flush() -> None:
        nonlocal block_targets, block_collect_only, covered, floors
        if block_collect_only is True:
            floors |= block_targets
        elif block_collect_only is False:
            covered |= block_targets
        block_targets = set()
        block_collect_only = None
        block_indent = None

    def _indent(line: str) -> int:
        n = 0
        for ch in line:
            if ch == " ":
                n += 1
            elif ch == "\t":
                n += 1
            else:
                break
        return n

    for line in text.splitlines():
        # Détection d'un début de bloc `run: |` à n'importe quelle indentation
        stripped_no_indent = line.lstrip(" \t")
        if stripped_no_indent.startswith("run: |"):
            # Ferme tout bloc en cours avant d'en ouvrir un nouveau
            _flush()
            block_indent = _indent(line)
            block_collect_only = None
            continue
        if stripped_no_indent.startswith("run: pytest"):
            # Ferme tout bloc en cours avant d'émettre la ligne inline
            _flush()
            for token in stripped_no_indent.split()[2:]:
                _maybe_target(token, covered)
            continue
        if block_indent is None:
            # Pas dans un bloc `run: |`
            continue
        # Dans un bloc : ligne vide ou commentaire = neutre
        if not line.strip() or line.lstrip(" \t").startswith("#"):
            continue
        # Vérifie qu'on est encore DANS le bloc : indentation strictement
        # supérieure à celle du `run: |`.
        cur_indent = _indent(line)
        if cur_indent <= block_indent:
            _flush()
            # Traite la ligne courante comme nouveau départ
            stripped = line.lstrip(" \t")
            if stripped.startswith("run: |"):
                block_indent = _indent(line)
                block_collect_only = None
            elif stripped.startswith("run: pytest"):
                for token in stripped.split()[2:]:
                    _maybe_target(token, covered)
                block_indent = None
            continue
        # Ligne à l'intérieur du bloc : on l'analyse
        # On ne classe une ligne que si elle invoque explicitement `pytest` —
        # les lignes `if [...] then`, `echo "::error::..."`, `exit 1` etc.
        # portent souvent le mot `--collect-only` dans leur texte sans être
        # une commande de collecte. Une ligne qui appelle `pytest` SANS
        # `--collect-only` invalide la classification floor du bloc.
        is_pytest = "pytest" in line
        has_collect = "--collect-only" in line
        if is_pytest and block_collect_only is None:
            # Premier appel pytest du bloc : on initie la classification
            block_collect_only = has_collect
        elif is_pytest and block_collect_only is True and not has_collect:
            # Un vrai pytest sans --collect-only dans le même bloc =
            # exécution, pas floor pur
            block_collect_only = False
        # Les lignes non-pytest (if/echo/exit/fi/fail) sont neutres pour
        # la classification : elles n'invalident ni n'établissent le floor.
        for token in line.split():
            _maybe_target(token, block_targets)

    _flush()
    return covered, floors


def extract_run_targets(text: str) -> set[str]:
    """Cibles de couverture d'un workflow : chemins sous un bloc `run:` réel.

    Les steps de garde `--collect-only` (`#17250`) sont **exclus** : leur
    rôle est de sonder la collecte d'un dossier, pas de l'exécuter — si
    la seule mention d'un testpath est dans un tel step, le testpath n'est
    pas couvert en exécution.

    Retourne les tokens qui ressemblent à un chemin relatif (contient `/`,
    finit en `.py`, ou token nu sans slash ni caractère shell, ex.
    `GradeBookApp`). Chaque bloc `run: |` est traité comme un step
    indépendant (fermeture par indentation stricte).
    """
    covered, _floors = _partition_run_blocks(text)
    return covered


def _maybe_target(token: str, targets: set[str]) -> None:
    """Ajoute le token s'il ressemble à un chemin relatif.

    Chemin = contient un `/`, finit en `.py`, OU est un token nu sans slash
    ni caractère shell (cas des répertoires racine du dépôt, ex. GradeBookApp
    — famille 5 de #14615). Les flags (préfixe `-`) et variables (`$`) ne
    sont jamais des cibles.
    """
    if token in ("\\",) or token.startswith("-") or "$" in token:
        return
    if "/" in token or token.endswith(".py") or re.fullmatch(r"[A-Za-z0-9_.-]+", token):
        targets.add(token)


def verify_declared_targets(repo_root: Path, verbose: bool) -> list[str]:
    """Vérifie que chaque cible déclarée apparaît dans un bloc `run:` réel.

    Le check se fait sur les cibles extraites des blocs `run:` (pas une
    recherche verbatim dans le fichier : un commentaire mentionnant un chemin
    ne satisfait pas la couverture — c'est précisément la dérive que le garde
    doit attraper).
    """
    problems: list[str] = []
    for wf_rel, targets in WORKFLOW_COVERAGE.items():
        wf_path = repo_root / wf_rel
        if not wf_path.exists():
            problems.append(f"workflow déclaré introuvable: {wf_rel}")
            continue
        run_targets = extract_run_targets(wf_path.read_text(encoding="utf-8"))
        for target in targets:
            if target not in run_targets:
                problems.append(
                    f"cible déclarée disparue du run réel: {wf_rel} -> {target} "
                    f"(retirée du run ? mettre à jour WORKFLOW_COVERAGE)"
                )
            elif verbose:
                print(f"  [ok] {wf_rel} couvre {target}")
    return problems


def is_covered(testpath: str, covered_dirs: list[str]) -> bool:
    """Un testpath est couvert si une cible-dossier lui est égale ou ancêtre."""
    return any(
        testpath == c or testpath.startswith(c + "/") for c in covered_dirs
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    args = ap.parse_args()

    repo_root = args.repo_root.resolve()
    testpaths = load_testpaths(repo_root / "pytest.ini")
    excluded = load_ci_excluded(repo_root)

    # Cibles-dossier uniquement (les cibles fichier ne couvrent aucun testpath).
    covered_dirs = sorted(
        {
            t
            for targets in WORKFLOW_COVERAGE.values()
            for t in targets
            if not t.endswith(".py")
        }
    )

    if args.verbose:
        print(f"[info] {len(testpaths)} testpaths, "
              f"{len(covered_dirs)} cibles-dossier, "
              f"{len(excluded)} exclusions CI-EXCLUDED")

    problems = verify_declared_targets(repo_root, args.verbose)

    uncovered: list[str] = []
    for tp in testpaths:
        if is_covered(tp, covered_dirs):
            if args.verbose:
                print(f"  [ok] couvert: {tp}")
        elif tp in excluded:
            if args.verbose:
                print(f"  [ok] exclu:   {tp} — {excluded[tp]}")
        else:
            uncovered.append(tp)

    if uncovered:
        print("Testpaths non couverts et non CI-EXCLUDED :")
        for tp in uncovered:
            print(f"  FAIL {tp}")
    elif args.verbose:
        print("[ok] tous les testpaths sont couverts ou exclus")

    if problems:
        print("Dérives de cibles déclarées :")
        for p in problems:
            print(f"  FAIL {p}")

    return 1 if (uncovered or problems) else 0


if __name__ == "__main__":
    sys.exit(main())
