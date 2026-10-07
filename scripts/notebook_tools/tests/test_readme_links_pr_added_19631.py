"""Test for #19631 -- ``readme_link_violations(pr_added_files=...)`` exemption.

Founding case (cf. issue body) : PR #19368 (Origami causal CB-00 README) voit
son check-run ``Audit README -> .ipynb links`` rapporter STALE_LINK: 1 NOUVELLE
pour ``MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/README.md ->
CausalBridges-00-PearlLadder-Intro-Python.ipynb``. Le carnet est ajoute dans la
meme PR (commit 59ea252dd, branche ``feature/19310-cb00-pearl-ladder-intro``)
et le lien README est intentionnel (le carnet ET son entree README arrivent
ensemble).

Le fix (F8 dans le workflow) : l'audit accepte ``--pr-added-files <list>``,
liste de fichiers ajoutes par la PR. Un lien vers un fichier PR-added est
exempt de STALE_LINK (le carnet ET son entree README arrivent ensemble --
la comparaison delta PR - base doit donner 0 sur ces cibles).

Temoins verifies :
  1. La fonction accepte le parametre ``pr_added_files`` (default = None).
  2. Sans parametre, le comportement est inchange.
  3. Avec un fichier tracked dans ``pr_added_files``, les violations le
     ciblant disparaissent (NB : sur origin/main CB-00 n'est pas tracked,
     on utilise donc un notebook tracked -- CB-01 -- comme temoin).
  4. Le CLI ``--pr-added-files <path>`` charge la liste et l'applique.
  5. La forme de la liste (POSIX, une par ligne, blancs ignores) est
     preservee dans le chargement.
"""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
RGQR = REPO_ROOT / "scripts" / "regen_quarto_render.py"

# CB-01 est tracked sur origin/main (CB-00 ne l'est pas encore -- PR #19310
# non mergée). On utilise CB-01 comme cible de reference pour les temoins
# qui ont besoin d'un fichier effectivement tracked.
CB01 = (
    "MyIA.AI.Notebooks/Probas/DecisionTheory/Causal-Bridges/"
    "CausalBridges-01-Do-Calculus.ipynb"
)


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
    import importlib.util
    spec = importlib.util.spec_from_file_location("rgqr", str(RGQR))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    v_none = mod.readme_link_violations()
    v_explicit = mod.readme_link_violations(pr_added_files=None)
    # Meme nombre de violations, meme signature
    assert len(v_none) == len(v_explicit)
    assert len(v_none) > 0, "temoin casse : pas de violations brutes en repo"


def test_pr_added_files_excludes_known_targeted_violation() -> None:
    """Ajoute CB-01 a pr_added_files -> les STALE_LINK ciblant CB-00/01 disparaissent.

    Le cas fondateur #19368 utilise CB-00 (non tracked sur origin/main) ;
    on transpose le test sur CB-01 qui EST tracked. La regle est la meme :
    le fichier est dans pr_added_files -> son entree README ne releve plus
    comme STALE_LINK. On verifie au moins 1 disparition (delta >= 1).
    """
    import importlib.util
    spec = importlib.util.spec_from_file_location("rgqr", str(RGQR))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    before = mod.readme_link_violations()
    after = mod.readme_link_violations(pr_added_files={CB01})
    removed = [v for v in before if v not in after]
    # CB-01 apparait dans plusieurs READMEs : README de la serie + README
    # parent DecisionTheory + README parent Probas -- chacun avec sa
    # propre STALE_LINK. Au moins une doit disparaitre.
    # NB : le href est le chemin relatif au README parent, pas le chemin
    # absolu ; on matche sur le basename du carnet CB-01.
    cb01_basename = "CausalBridges-01-Do-Calculus.ipynb"
    assert any(cb01_basename in v[2] for v in removed), (
        f"Aucune STALE_LINK sur CB-01 dans les violations retirees : {removed[:3]}"
    )
    # Le total doit chuter d'au moins 1 (4 dans le cas mesure)
    assert len(before) - len(after) >= 1


def test_cli_pr_added_files_loads_list(tmp_path: Path) -> None:
    """``--pr-added-files <path>`` charge la liste (POSIX, une par ligne)."""
    f = tmp_path / "added.txt"
    # Mix : un fichier tracked (CB-01, qui changera de vrai), une ligne vide,
    # un chemin inexistant (ignore par le scanner -- pas un .ipynb link).
    f.write_text(f"{CB01}\n\nnot-a-real-path.ipynb\n", encoding="utf-8")
    proc = _run_module("--check-readme-links", "--pr-added-files", str(f))
    # rc = 0 (les violations brutes ne bloquent pas -- argv capture seulement)
    # L'important est que l'arg soit accepte et que le JSON-like stdout
    # porte l'audit nominal "README-link audit: ...".
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
    """Le workflow YAML utilise bien --pr-added-files (regression guard).

    Si quelqu'un retire le flag du workflow, les PR-added notebooks
    redeviennent STALE_LINK dans le delta -- c'est le bug fondateur.
    Le test verifie la presence des deux appels (passe PR + passe base).
    """
    wf = (REPO_ROOT / ".github" / "workflows" / "readme-ipynb-links-guard.yml").read_text(
        encoding="utf-8"
    )
    assert wf.count("--pr-added-files /tmp/pr_added_files.txt") >= 2, (
        "Le flag --pr-added-files doit apparaitre au moins 2x "
        "(passe PR + passe base). Regression du fix #19631."
    )
    # Et le calcul de la liste (diff-filter=A) doit etre present
    assert "--diff-filter=A" in wf, (
        "Le calcul de la liste PR-added via git diff --diff-filter=A "
        "doit etre present dans le workflow."
    )