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
        "scripts/notebook_tools/tests",
        "scripts/lean/tests",
        "MyIA.AI.Notebooks/GameTheory/tests",
        "MyIA.AI.Notebooks/QuantConnect/scripts/tests",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_bg_tree_lock.py",
        "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/tests/test_prover_forensic_guards.py",
        "MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-PythonForDataScience/tests",
    ],
    ".github/workflows/ml-tests.yml": [
        "MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/tests",
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


def extract_run_targets(text: str) -> set[str]:
    """Extrait les arguments de chemins des blocs `run:` d'un workflow.

    Ne considère QUE les lignes sous un `run: |` (ou une commande `run: pytest ...`
    sur une ligne) — pas les commentaires qui mentionnent un chemin. Retourne les
    tokens qui ressemblent à un chemin relatif (contient un `/` ou `.py`).
    Gère la continuation par backslash : on reste dans le bloc tant que la
    ligne est indentée, la commande pytest elle-même (avec ou sans backslash
    final) incluse.
    """
    targets: set[str] = set()
    in_run_block = False
    for line in text.splitlines():
        if in_run_block:
            # Fin du bloc : ligne non indentée non vide
            if line.strip() and not line.startswith((" ", "\t")):
                in_run_block = False
            else:
                stripped = line.strip()
                if stripped and not stripped.startswith("#"):
                    for token in stripped.split():
                        if token in ("\\",):
                            continue
                        if "/" in token or token.endswith(".py"):
                            targets.add(token)
                continue
        stripped = line.strip()
        if stripped.startswith("run: |"):
            in_run_block = True
            continue
        # run: pytest <cibles> sur une seule ligne (pas de pipe)
        if stripped.startswith("run: pytest"):
            for token in stripped.split()[2:]:
                if "/" in token or token.endswith(".py"):
                    targets.add(token)
    return targets


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
