"""Tests du module `leandojo_feasibility` (pli 2 #18562 via #18915).

Ces tests verifient les conditions RECOVERABLE-LOCAL qui n'ont PAS
besoin de Lean toolchain local ni de GPU. Si lean-dojo n'est pas
installe, les tests sont skippees (mode `RECOVERABLE-LOCAL`, pas un
defaut de l'integration).

Le scope de pli 1 (verdict SOTA, c.76) est documente dans l'issue
#18915 et le carnet `Lean-11-LeanDojo-V2-Faisabilite.ipynb`.
"""
from __future__ import annotations

import pytest

from .leandojo_feasibility import (
    MIN_LEAN_DOJO_VERSION,
    check_lean_dojo_installed,
    check_lean_dojo_public_api,
    check_lean_dojo_version_meets_min,
    check_lean_git_repo_has_cache_method,
    check_python_compatibility,
    summarize_axes_1_3,
)


def test_python_compatibility_returns_tuple() -> None:
    """Axe 1 : `check_python_compatibility` rend (compat: bool, version: str).

    On ne fait pas d'assertion sur la valeur de `compat` (depend de
    l'env). On verifie seulement la forme.
    """
    compat, version = check_python_compatibility()
    assert isinstance(compat, bool)
    assert isinstance(version, str)
    # version est au format "X.Y.Z"
    parts = version.split(".")
    assert len(parts) >= 2
    assert all(p.isdigit() for p in parts[:3])


def test_lean_dojo_installed_returns_tuple() -> None:
    """Axe 2 : `check_lean_dojo_installed` rend (installed: bool, str).

    Si lean-dojo n'est pas installe dans l'env de pytest, on skip le
    reste (mode RECOVERABLE-LOCAL) ; sinon on valide la version.
    """
    installed, info = check_lean_dojo_installed()
    if not installed:
        pytest.skip(f"lean-dojo non installe dans cet env : {info!r}")
    assert isinstance(installed, bool) and installed is True
    assert isinstance(info, str)
    # Format semver X.Y.Z (au moins)
    assert info.count(".") >= 1


def test_lean_dojo_version_meets_minimum() -> None:
    """Axe 2 (precision) : la version installee est >= MIN_LEAN_DOJO_VERSION.

    Si lean-dojo n'est pas installe, skip. Sinon la version doit etre
    >= 2.2.0 (cf. verdict SOTA c.76 et Requires-Python c.78).
    """
    installed, _ = check_lean_dojo_installed()
    if not installed:
        pytest.skip("lean-dojo non installe dans cet env")
    ok, current, min_v = check_lean_dojo_version_meets_min()
    assert ok, f"lean-dojo {current} < min {min_v}"
    assert current != "0.0.0"
    assert min_v == MIN_LEAN_DOJO_VERSION


def test_lean_dojo_public_api_present() -> None:
    """Axe 3 : tous les symboles documentes c.78 sont dans lean_dojo.

    Si lean-dojo n'est pas installe, tous les symboles sont `False`
    (cf. `check_lean_dojo_public_api`). On tolere ce cas (skip).
    Sinon, on exige la presence des 8 symboles.
    """
    installed, _ = check_lean_dojo_installed()
    api = check_lean_dojo_public_api()
    if not installed:
        # Pas de lean-dojo : tous les symboles sont False. On tolere
        # car c'est le comportement nominal en cas d'absence.
        # Le dict contient les 8 cles attendues avec valeur False.
        assert len(api) == 8
        assert all(v is False for v in api.values())
        pytest.skip("lean-dojo non installe ; public_api est vide (8 False)")
    expected = {
        "LeanGitRepo",
        "trace",
        "Dojo",
        "Theorem",
        "ProofFinished",
        "LeanError",
        "check_proof",
        "parse_goals",
    }
    assert set(api.keys()) == expected
    assert all(api.values()), (
        f"Certains symboles manquent dans lean_dojo : "
        f"{[k for k, v in api.items() if not v]}"
    )


def test_lean_git_repo_has_cache_method() -> None:
    """Axe 3 (precision) : LeanGitRepo.is_available_in_cache existe.

    La signature a change entre lean-dojo 2.2.0 et 4.20.0 ; on
    verifie que la methode est toujours presente (meme nom).
    """
    installed, _ = check_lean_dojo_installed()
    if not installed:
        pytest.skip("lean-dojo non installe dans cet env")
    assert check_lean_git_repo_has_cache_method(), (
        "LeanGitRepo.is_available_in_cache absent dans la version installee ; "
        "le verdict c.78 sur la signature 4.20.0 est invalide"
    )


def test_summarize_axes_1_3_returns_dict() -> None:
    """Recapitulatif : `summarize_axes_1_3` rend un dict struct avec
    les 4 sous-dicts attendus.
    """
    summary = summarize_axes_1_3()
    assert isinstance(summary, dict)
    assert set(summary.keys()) == {
        "python",
        "lean_dojo",
        "public_api",
        "lean_git_repo_cache_method",
    }
    # Python
    assert set(summary["python"].keys()) == {"compatible", "version"}
    # Lean_dojo
    assert set(summary["lean_dojo"].keys()) == {
        "installed",
        "version_or_error",
        "min_version_ok",
        "current",
        "min",
    }
    assert summary["lean_dojo"]["min"] == MIN_LEAN_DOJO_VERSION