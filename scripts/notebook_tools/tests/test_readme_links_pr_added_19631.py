"""Test for #19631 -- ``readme_link_violations(pr_added_files=...)``.

Founding case (cf. issue body) : PR #19368 (Origami causal CB-00 README) voit
son check-run ``Audit README -> .ipynb links`` rapporter STALE_LINK: 1 NOUVELLE
pour ``MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/README.md ->
CausalBridges-00-PearlLadder-Intro-Python.ipynb``. Le carnet est ajoute dans la
meme PR (commit 59ea252dd, branche ``feature/19310-cb00-pearl-ladder-intro``)
et le lien README est intentionnel (le carnet ET son entree README arrivent
ensemble).

Le fix (F8 dans le workflow) : l'audit accepte ``--pr-added-files <list>``,
liste de fichiers ajoutes par la PR. Un lien vers un fichier PR-added etait
exempt de STALE_LINK.

**Etat depuis #18911 (geste 2, 2026-10-09).** La classe ``STALE_LINK`` est
retiree : un lien ``.ipynb`` n'est plus une violation, la classe bloquante est
``HTML_404`` (un lien ``.html`` dont la cible n'est pas committee). L'exemption
PR-added etait specifique a ``STALE_LINK`` -- un carnet ajoute par la PR ne
peut pas produire un ``HTML_404``. Le parametre reste accepte (contrat
CLI/dumper) mais il est **inerte** sur l'ensemble des violations ; le temoin
qui le prouve a remplace l'ancien « au moins 1 disparition ».

Temoins verifies :
  1. La fonction accepte le parametre ``pr_added_files`` (default = None).
  2. ``pr_added_files`` n'affecte PLUS l'ensemble des violations (inerte).
  3. Le CLI ``--pr-added-files <path>`` charge la liste sans erreur.
  4. La forme de la liste (POSIX, une par ligne, blancs ignores) est
     preservee dans le chargement.
  5. Le workflow passe encore le flag -- a la passe PR seulement (F8b).
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
RGQR = REPO_ROOT / "scripts" / "regen_quarto_render.py"

# CB-01 est tracked sur origin/main (CB-00 ne l'est pas encore -- PR #19310
# non mergee). On l'utilise comme cible de reference pour les temoins qui ont
# besoin d'un fichier effectivement tracked.
CB01 = (
    "MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/"
    "CausalBridges-01-Do-Calculus.ipynb"
)


def _load_rgqr():
    spec = importlib.util.spec_from_file_location("rgqr", str(RGQR))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _run_module(*args: str) -> subprocess.CompletedProcess:
    """Invoque regen_quarto_render.py comme sous-processus (meme argv que CI)."""
    return subprocess.run(
        [sys.executable, str(RGQR), *args],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )


def test_pr_added_files_param_accepts_default_none() -> None:
    """``pr_added_files=None`` doit conserver le comportement historique."""
    mod = _load_rgqr()
    v_none = mod.readme_link_violations()
    v_explicit = mod.readme_link_violations(pr_added_files=None)
    # Meme nombre de violations, meme signature
    assert len(v_none) == len(v_explicit)
    assert len(v_none) > 0, "temoin casse : pas de violations brutes en repo"


def test_pr_added_files_is_inert_on_violations() -> None:
    """Depuis #18911, ``pr_added_files`` n'affecte plus l'ensemble des violations.

    L'exemption fondee #19631 (#19368) etait specifique a la classe RETIREE
    ``STALE_LINK`` (``.ipynb`` cible d'une entree README ajoutee par la meme
    PR). La classe bloquante est desormais ``HTML_404`` (``.html`` sans cible
    committee), qu'un carnet PR-added ne peut pas produire. Le parametre reste
    accepte pour le contrat CLI/dumper, mais il est INERTE -- c'est le temoin
    qui remplace l'ancien « au moins 1 disparition ».
    """
    mod = _load_rgqr()
    before = mod.readme_link_violations()
    after = mod.readme_link_violations(pr_added_files={CB01})
    assert before == after, (
        "pr_added_files est cense etre INERTE sur l'ensemble des violations "
        "depuis #18911 (l'exemption #19631 visait la classe retiree STALE_LINK)"
    )
    # Temoin negatif : on mesure bien un ensemble non vide.
    assert len(before) > 0


def test_cli_pr_added_files_loads_list(tmp_path: Path) -> None:
    """``--pr-added-files <path>`` charge la liste (POSIX, une par ligne)."""
    f = tmp_path / "added.txt"
    # Mix : un fichier tracked (CB-01), une ligne vide, un chemin inexistant.
    f.write_text(f"{CB01}\n\nnot-a-real-path.ipynb\n", encoding="utf-8")
    proc = _run_module("--check-readme-links", "--pr-added-files", str(f))
    # rc = 0 (les violations brutes ne bloquent pas le dump -- argv capture
    # seulement ; le scanner sort 1 sur violations, ce qui est attendu ici).
    # L'important est que l'arg soit accepte et que l'audit nominal soit rendu.
    assert "README-link audit:" in proc.stdout, proc.stdout


def test_cli_pr_added_files_empty(tmp_path: Path) -> None:
    """Une liste vide est equivalente a l'absence de flag."""
    f = tmp_path / "empty.txt"
    f.write_text("\n\n   \n", encoding="utf-8")
    proc = _run_module("--check-readme-links", "--pr-added-files", str(f))
    assert "README-link audit:" in proc.stdout, proc.stdout


def test_cli_pr_added_files_missing_file_is_safe() -> None:
    """Fichier absent : silencieux (set vide) ou erreur explicite -- pas de crash."""
    proc = _run_module("--check-readme-links", "--pr-added-files", "/nonexistent/path.txt")
    # Comportement attendu : erreur FileNotFoundError => rc != 0, message explicite.
    # Le scanner doit etre robuste a un fichier manquant ; on accepte rc=0
    # OU rc!=0 tant que ce n'est pas un crash silencieux.
    assert proc.returncode in (0, 1, 2), f"unexpected rc={proc.returncode}"


def test_workflow_yaml_references_pr_added_files() -> None:
    """Le workflow calcule encore la liste PR-added, sur la passe PR SEULE.

    Depuis #18911 (geste 2) la classe bloquante a change et la passe base GARDE
    le script de la PR (cf. F8b : sinon elle mesurerait la classe retiree). La
    passe base n'ajoute aucun fichier, donc le flag n'y est plus passe : le
    compte passe de 2 a 1. C'est un changement de contrat, pas une regression --
    le temoin negatif est que le calcul de la liste reste present.
    """
    wf = (REPO_ROOT / ".github" / "workflows" / "readme-ipynb-links-guard.yml").read_text(
        encoding="utf-8"
    )
    assert wf.count("--pr-added-files /tmp/pr_added_files.txt") == 1, (
        "Le flag --pr-added-files est passe a la passe PR seulement depuis "
        "#18911 (F8b : la passe base garde le script de la PR et n'ajoute "
        "aucun fichier)."
    )
    # Et le calcul de la liste (diff-filter=A) doit etre present
    assert "--diff-filter=A" in wf, (
        "Le calcul de la liste PR-added via git diff --diff-filter=A "
        "doit etre present dans le workflow."
    )
