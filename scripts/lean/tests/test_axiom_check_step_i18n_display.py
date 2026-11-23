"""L'affichage i18n de axiom_check_step.py doit nommer le MODE applique (#24160).

Reserve laissee par la revue structurelle de PR #24108 :

    "(cosmétique) branche liste explicite : `include_i18n` de l'env est
     ignoré et l'affichage dit toujours « INCLUS (liste explicite) »"

Le defaut n'etait pas dans le COMPORTEMENT de la porte (correct : une
liste explicite qui nomme un module `_en` l'inspecte, c'est le contrat de
`lean-axiom.yml` -- l'input y est « Ignored when target-modules is an
explicit list »), mais dans le LIBELLE : « INCLUS » sans dire ce qui
l'avait decide. Le meme mot annonçait deux causes opposees -- le joker
derive la surface `_en` de `include_i18n`, la liste explicite l'impose --
et une ligne « INCLUS » posee a cote de `include_i18n=false` se lisait
comme si le drapeau avait decide.

Ce test fait tourner le VRAI step en sous-processus, sur un
GITHUB_WORKSPACE fabrique, dans les DEUX modes et pour les DEUX valeurs
du drapeau. Le step est un script plat (lecture d'environnement au
niveau module + `sys.exit`) : l'importer l'executerait, donc seule la
voie sous-processus teste le programme reellement livree.

Le harnais est hermetique : `lean_server` est un stub (aucun Lean dans
la boucle), et les DEUX modules que le step importe depuis
`scripts/lean/` -- `check_target_coverage` (le filtre `_en`, source
unique de la regle) et `allow_list` -- sont COPIES depuis le depot, pas
reecrits : le test doit exercer le vrai filtre, pas une copie.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
STEP = REPO_ROOT / "scripts" / "lean" / "axiom_check_step.py"

# Stub du harnais Lean : le step n'a besoin que de `LeanVerifier`
# (avec `check_axioms`) et, en cas d'ImportError, le step fournit
# lui-meme un `axiom_lookup_anomalies` de repli. Aucune dependance
# externe : ce test ne doit lancer aucun Lean.
_LEAN_SERVER_STUB = '''
class LeanVerifier:
    """Verificateur factice : un module, une declaration, aucun axiome."""

    def __init__(self):
        self.project_dir = None
        self.seen = []

    def check_axioms(self, module, whitelist=None, fail_on_sorry=False):
        self.seen.append(module)
        return {
            "declarations": ["stub.decl"],
            "axioms": [],
            "forbidden": [],
            "has_sorry": False,
            "success": True,
            "error": None,
            "empty_reason": None,
            "raw_output": "",
        }
'''


def _build_workspace(root: Path) -> Path:
    """Fabrique un GITHUB_WORKSPACE minimal mais complet pour le step."""
    agent_tests = root / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / "agent_tests"
    agent_tests.mkdir(parents=True)
    (agent_tests / "lean_server.py").write_text(_LEAN_SERVER_STUB, encoding="utf-8")

    # Les deux modules que le step importe depuis `scripts/lean/` sont
    # COPIES du depot : le filtre `_en` teste est le vrai, et la regle
    # reste dans son unique emplacement.
    lean_dir = root / "scripts" / "lean"
    lean_dir.mkdir(parents=True)
    for name in ("check_target_coverage.py", "allow_list.py"):
        shutil.copy2(REPO_ROOT / "scripts" / "lean" / name, lean_dir / name)

    # Un lac factice : deux modules, dont un jumeau `_en`. C'est ce que
    # la derivation `'*'` doit decouvrir.
    lake = root / "MyIA.AI.Notebooks" / "fake_lake"
    lake.mkdir(parents=True)
    (lake / "Alpha.lean").write_text("-- stub\n", encoding="utf-8")
    (lake / "Alpha_en.lean").write_text("-- stub\n", encoding="utf-8")
    return root


def _run(root: Path, modules: str, include_i18n: bool) -> str:
    """Execute le vrai step et rend sa sortie standard."""
    env = dict(os.environ)
    env.update({
        "GITHUB_WORKSPACE": str(root),
        "PROJECT_PATH": "MyIA.AI.Notebooks/fake_lake",
        "MODULES": modules,
        "DISPLAY_NAME": "fake_lake",
        "ALLOW": "",
        "FAIL_ON_SORRY": "false",
        "INCLUDE_I18N_SIBLINGS": "true" if include_i18n else "false",
    })
    proc = subprocess.run(
        [sys.executable, str(STEP)],
        env=env, cwd=str(root), capture_output=True, text=True,
    )
    assert proc.returncode == 0, (
        f"le step a echoue (rc={proc.returncode})\n"
        f"stdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
    )
    return proc.stdout


def _i18n_line(out: str) -> str:
    """La ligne de rapport i18n, telle qu'imprimee."""
    lines = [ln for ln in out.splitlines() if ln.startswith("i18n siblings (_en):")]
    assert len(lines) == 1, f"une seule ligne i18n attendue, vue:\n{out}"
    return lines[0]


def _modules_line(out: str) -> str:
    lines = [ln for ln in out.splitlines() if ln.startswith("Modules: ")]
    assert len(lines) == 1, f"une seule ligne Modules attendue, vue:\n{out}"
    return lines[0]


def test_joker_mode_names_the_flag_that_drove_the_derivation(tmp_path: Path) -> None:
    """Mode joker : `include_i18n` DECIDE, et le libelle le dit."""
    root = _build_workspace(tmp_path / "ws")
    line = _i18n_line(_run(root, "*", include_i18n=True))
    assert "mode joker" in line, line
    assert "include_i18n=true" in line, line
    assert "INCLUS" in line, line
    assert "sans effet" not in line, line


def test_joker_mode_excluded_names_the_flag_that_drove_the_derivation(tmp_path: Path) -> None:
    """Mode joker, drapeau faux : la surface `_en` est exclue, et nommee."""
    root = _build_workspace(tmp_path / "ws")
    out = _run(root, "*", include_i18n=False)
    line = _i18n_line(out)
    assert "mode joker" in line, line
    assert "include_i18n=false" in line, line
    assert "EXCLUS" in line, line
    assert "Alpha_en" not in _modules_line(out), out


def test_explicit_list_names_the_mode_and_the_flag_has_no_effect(tmp_path: Path) -> None:
    """Mode liste explicite : le libelle nomme le mode ET l'effet reel du drapeau.

    Le libelle historique annoncait « INCLUS (liste explicite) » sans dire
    que `include_i18n` n'y joue aucun role : le meme mot y recouvrait une
    cause que le drapeau n'avait pas decidee.
    """
    root = _build_workspace(tmp_path / "ws")
    line = _i18n_line(_run(root, "Alpha,Alpha_en", include_i18n=False))
    assert "mode liste explicite" in line, line
    assert "include_i18n=false" in line, line
    assert "sans effet" in line, line
    assert "INCLUS" in line, line
    # Le libelle historique, annonce inconditionnellement, ne doit plus
    # pouvoir disparaitre : c'est lui qui mentait sur le mode effectif.
    assert "INCLUS (liste explicite)" not in line, line


def test_explicit_list_inspects_the_named_en_module_whatever_the_flag(tmp_path: Path) -> None:
    """Le COMPORTEMENT de la porte ne bouge pas : la liste fait autorite.

    Un module `_en` nomme par la liste explicite est inspecte, que le
    drapeau vaille true ou false -- c'est le contrat de `lean-axiom.yml`
    (« Ignored when target-modules is an explicit list »). Le correctif est
    d'affichage : la liste des modules inspectes doit etre IDENTIQUE dans
    les deux cas, seul le libelle differe.
    """
    root = _build_workspace(tmp_path / "ws")
    out_true = _run(root, "Alpha,Alpha_en", include_i18n=True)
    out_false = _run(root, "Alpha,Alpha_en", include_i18n=False)

    assert _modules_line(out_true) == _modules_line(out_false), (
        "le comportement de la porte a change : la liste explicite doit "
        f"inspecter les memes modules dans les deux cas\n"
        f"true : {_modules_line(out_true)}\nfalse: {_modules_line(out_false)}")
    assert "Alpha_en" in _modules_line(out_true)
    # Le drapeau n'a aucun effet sur ce mode : le libelle le dit dans les
    # deux cas.
    assert "sans effet" in _i18n_line(out_true)
    assert "sans effet" in _i18n_line(out_false)


def test_the_two_modes_are_distinguished(tmp_path: Path) -> None:
    """Critere de mort : l'affichage DISTINGUE le mode liste explicite du joker."""
    root = _build_workspace(tmp_path / "ws")
    joker = _i18n_line(_run(root, "*", include_i18n=True))
    explicite = _i18n_line(_run(root, "Alpha,Alpha_en", include_i18n=True))
    assert joker != explicite, (
        "les deux modes doivent produire des libelles differents : "
        f"joker={joker!r} explicite={explicite!r}")
    assert "mode joker" in joker and "mode liste explicite" in explicite


def test_zero_siblings_still_names_the_mode(tmp_path: Path) -> None:
    """Un compte de zero ne dit pas QUOI etait nul : le mode le nomme aussi.

    « 0 » signifie deux choses selon la branche -- « le lac n'a aucun
    module `_en` » (joker) ou « la liste n'en nomme aucun » (liste
    explicite). Sans le mode, les deux lignes se confondent.
    """
    root = _build_workspace(tmp_path / "ws")
    # Liste explicite qui ne nomme aucun `_en` : le lac en contient un,
    # mais la liste ne le demande pas.
    line = _i18n_line(_run(root, "Alpha", include_i18n=False))
    assert "mode liste explicite" in line, line
    assert line.startswith("i18n siblings (_en): 0"), line
