"""Rejeu de `scripts/ym_openai_20261028/inventory.py`.

Deux familles de controles negatifs, chacune couplee a un fix de la PR :

1. CRLF du manifeste (`_verifie_manifeste`). La normalisation par checkout ne
   change QUE les fins de ligne. Un ecart de contenu reel (blob commite intact,
   fichier de travail modifie) ne doit PAS etre classe `normalises_par_checkout`
   : il reste `differents`.

2. `travail_dans_la_solution`. La closure d'imports ajoute `Solution` lui-meme,
   donc un `Solution.lean` qui n'importe que des modules de specification (ou
   rien du tout) ne doit PAS satisfaire l'epreuve : le controle exige un module
   d'implementation HORS spec et HORS `Solution`.

Les fixtures construisent de minuscules clones dans `tmp_path` ; le premier doit
etre un vrai depot git (la comparaison du manifeste lit les blobs `HEAD:` par
`git cat-file --batch`), les seconds sont des arbres de fichiers Lean.
"""

from __future__ import annotations

import hashlib
import subprocess
import sys
from pathlib import Path

import pytest

# `inventory.py` n'a pas de point dans son nom : on met son repertoire sur le
# chemin d'import (local au depot, pas un paquet installe).
_RACINE_REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_RACINE_REPO / "scripts" / "ym_openai_20261028"))

import inventory  # noqa: E402  (chemin local, ajoute au dessus)


def _git(racine: Path, *args: str) -> None:
    subprocess.run(
        ["git", "-C", str(racine), *args],
        check=True,
        capture_output=True,
    )


def _sha(donnees: bytes) -> str:
    return hashlib.sha256(donnees).hexdigest()


def _init_repo(racine: Path) -> None:
    """Repo git minimal, identite locale, checkout fide (pas d'autocrlf)."""
    racine.mkdir(parents=True, exist_ok=True)
    _git(racine, "init", "-q")
    _git(racine, "config", "user.email", "test@local.invalid")
    _git(racine, "config", "user.name", "test")
    # Pas de conversion de fins de ligne au checkout : on simule le CRLF a la main.
    _git(racine, "config", "core.autocrlf", "false")


# ---------------------------------------------------------------------------
# 1. CRLF du manifeste
# ---------------------------------------------------------------------------


@pytest.fixture
def repo_crlf(tmp_path: Path) -> Path:
    """Trois fichiers annonces, chacun avec un destin de travail distinct.

    - `clean.lean`  : fichier de travail fide au blob (LF)     -> verifie.
    - `crlf.lean`   : checkout CRLF d'un blob LF identique     -> normalise.
    - `edited.lean` : contenu reel modifie, blob intact       -> different.
    """
    racine = tmp_path / "clone"
    _init_repo(racine)

    clean = b"def A := 1\n"
    crlf = b"def B := 2\n"
    edited = b"def C := 4\n"

    (racine / "clean.lean").write_bytes(clean)
    (racine / "crlf.lean").write_bytes(crlf)
    (racine / "edited.lean").write_bytes(edited)
    (racine / "SOURCES.sha256").write_text(
        f"{_sha(clean)}  clean.lean\n"
        f"{_sha(crlf)}  crlf.lean\n"
        f"{_sha(edited)}  edited.lean\n",
        encoding="utf-8",
    )
    _git(racine, "add", "-A")
    _git(racine, "commit", "-q", "-m", "init")

    # Destins de travail, APRES le commit (le blob HEAD reste donc intact) :
    (racine / "crlf.lean").write_bytes(crlf.replace(b"\n", b"\r\n"))  # CRLF seul
    (racine / "edited.lean").write_bytes(b"def C := 5\n")  # vrai edit de contenu
    return racine


def test_crlf_checkout_classe_normalise(repo_crlf: Path) -> None:
    """Fins de ligne CRLF seules -> `normalises_par_checkout`, pas `differents`."""
    resultat = inventory._verifie_manifeste(repo_crlf)
    assert "crlf.lean" in resultat["normalises_par_checkout"]
    assert "crlf.lean" not in resultat["differents"]


def test_edit_reel_classe_different(repo_crlf: Path) -> None:
    """Contenu reel modifie (blob intact) -> `differents`, PAS `normalises`."""
    resultat = inventory._verifie_manifeste(repo_crlf)
    assert "edited.lean" in resultat["differents"]
    assert "edited.lean" not in resultat["normalises_par_checkout"]


def test_fichier_fide_classe_verifie(repo_crlf: Path) -> None:
    """Fichier de travail fide au blob -> ni normalise ni different, verifie."""
    resultat = inventory._verifie_manifeste(repo_crlf)
    assert "clean.lean" not in resultat["differents"]
    assert "clean.lean" not in resultat["normalises_par_checkout"]
    # `clean` (fide) et `crlf` (blob intact, checkout normalise) sont tous deux
    # verifies ; seul `edited` (contenu reel modifie) est exclu.
    assert resultat["verifies"] == 2


# ---------------------------------------------------------------------------
# 2. travail_dans_la_solution
# ---------------------------------------------------------------------------


def _statut(controles: list, cle: str) -> str:
    for controle in controles:
        if controle.key == cle:
            return controle.statut
    raise AssertionError(f"check `{cle}` introuvable")


_CHALLENGE = (
    "import ChallengeSpec\n\n"
    "theorem challenge : JointExistence := by\n"
    "  sorry\n"
)
_CHALLENGE_SPEC = "def JointExistence : Prop := True\n"


@pytest.fixture
def repo_solution_spec_seule(tmp_path: Path) -> Path:
    """`Solution` n'importe que la specification (pas de module d'implémentation)."""
    racine = tmp_path / "clone"
    _init_repo(racine)
    (racine / "Challenge.lean").write_text(_CHALLENGE, encoding="utf-8")
    (racine / "ChallengeSpec.lean").write_text(_CHALLENGE_SPEC, encoding="utf-8")
    (racine / "Solution.lean").write_text(
        "import ChallengeSpec\n\n"
        "theorem solution : JointExistence := by\n"
        "  exact trivial\n",
        encoding="utf-8",
    )
    return racine


def test_solution_spec_seule_ne_passe_pas(repo_solution_spec_seule: Path) -> None:
    """Un `Solution` sans module d'implementation -> `travail_dans_la_solution` FAIL."""
    controles, _ = inventory._construit_controles(repo_solution_spec_seule)
    assert _statut(controles, "travail_dans_la_solution") == "FAIL"


@pytest.fixture
def repo_solution_avec_impl(tmp_path: Path) -> Path:
    """`Solution` importe un module d'implementation (hors specification)."""
    racine = tmp_path / "clone"
    _init_repo(racine)
    (racine / "Challenge.lean").write_text(_CHALLENGE, encoding="utf-8")
    (racine / "ChallengeSpec.lean").write_text(_CHALLENGE_SPEC, encoding="utf-8")
    (racine / "YM" / "Ac").mkdir(parents=True)
    (racine / "YM" / "Ac" / "Wilson.lean").write_text(
        "def wilsonWork : True := trivial\n",
        encoding="utf-8",
    )
    (racine / "Solution.lean").write_text(
        "import ChallengeSpec\n"
        "import YM.Ac.Wilson\n\n"
        "theorem solution : JointExistence := by\n"
        "  exact trivial\n",
        encoding="utf-8",
    )
    return racine


def test_solution_avec_impl_passe(repo_solution_avec_impl: Path) -> None:
    """Un `Solution` qui importe un module d'implementation -> PASS."""
    controles, _ = inventory._construit_controles(repo_solution_avec_impl)
    assert _statut(controles, "travail_dans_la_solution") == "PASS"
