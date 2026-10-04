"""Faisabilite LeanDojo v2 -- integration dans le prouveur maison (pli 2).

Verdict SOTA documente en c.76 / c.78 sur 5 axes :
  1. Compatibilite Python + lean-dojo    RECOVERABLE-LOCAL
  2. Modules sans torch                  RECOVERABLE-LOCAL
  3. LeanGitRepo + is_available_in_cache RECOVERABLE-LOCAL
  4. Trace repo Lean 4 (model only)     RECOVERABLE-LOCAL conditionnel
  5. Model ML LeanDojo (torch)          INTRINSIC (GPU only)

Ce module implemente les fonctions de test des axes 1-3, qui
s'executent SANS Lean toolchain locale (juste `pip install lean-dojo`).
L'axe 4 (trace repo Lean 4) necessite Lean 4 toolchain + reseau et
est documente comme conditionnel dans le carnet.

L'integration dans le prouveur maison (agent_tests/prover/) reste
`INTRINSIC` tant qu'une machine GPU n'est pas mobilisee (axe 5).
"""
from __future__ import annotations

import importlib
import sys
from typing import Tuple

# Version minimale de lean-dojo pour le verdict SOTA c.76 / c.78.
MIN_LEAN_DOJO_VERSION = "2.2.0"


def check_python_compatibility() -> Tuple[bool, str]:
    """Axe 1 : verifie que la version Python est compatible avec lean-dojo.

    LeanDojo 4.20.0 declare `Requires-Python: >=3.9,<=3.12`. Python 3.13+
    declenche une erreur d'installation. On documente la version observee.

    Returns:
        (compat, version_str) -- compat=True si 3.10 <= version <= 3.12.
    """
    version = sys.version_info
    major, minor = version.major, version.minor
    version_str = f"{major}.{minor}.{version.micro}"
    compat = (major, minor) >= (3, 10) and (major, minor) <= (3, 12)
    return compat, version_str


def check_lean_dojo_installed() -> Tuple[bool, str]:
    """Axe 2 : verifie que lean-dojo est importable.

    Returns:
        (installed, version_or_error) -- version_str si OK, message
        d'erreur sinon.
    """
    try:
        mod = importlib.import_module("lean_dojo")
        version = getattr(mod, "__version__", "unknown")
        return True, version
    except ImportError as exc:
        return False, str(exc)


def check_lean_dojo_version_meets_min() -> Tuple[bool, str, str]:
    """Axe 2 (precision) : verifie que lean-dojo >= MIN_LEAN_DOJO_VERSION.

    Returns:
        (ok, current_version, min_version)
    """
    try:
        mod = importlib.import_module("lean_dojo")
        current = getattr(mod, "__version__", "0.0.0")
    except ImportError:
        return False, "0.0.0", MIN_LEAN_DOJO_VERSION
    # Comparaison semver basique : split sur '.' et comparer en tuples.
    def _vtuple(v: str) -> tuple[int, ...]:
        parts: list[int] = []
        for p in v.split("."):
            try:
                parts.append(int(p))
            except ValueError:
                # Cas "2.2.0rc1" -> on garde 2 et on ignore le suffixe.
                break
        return tuple(parts)
    return _vtuple(current) >= _vtuple(MIN_LEAN_DOJO_VERSION), current, MIN_LEAN_DOJO_VERSION


def check_lean_dojo_public_api() -> dict[str, bool]:
    """Axe 3 : verifie que les symboles publics documentes c.78 sont presents
    dans `lean_dojo` (sans importer torch).

    Symboles attendus (cf. verdict SOTA c.78) :
        - LeanGitRepo, trace, is_available_in_cache(repo)
        - Dojo, Theorem, ProofFinished, LeanError
        - check_proof, parse_goals
    """
    expected = {
        "LeanGitRepo": False,
        "trace": False,
        "Dojo": False,
        "Theorem": False,
        "ProofFinished": False,
        "LeanError": False,
        "check_proof": False,
        "parse_goals": False,
    }
    # `is_available_in_cache` n'est pas un attribut module-level ;
    # c'est une methode de LeanGitRepo. On le verifie separement.
    try:
        mod = importlib.import_module("lean_dojo")
    except ImportError:
        return expected
    for name in expected:
        expected[name] = hasattr(mod, name)
    return expected


def check_lean_git_repo_has_cache_method() -> bool:
    """Axe 3 (precision) : verifie que LeanGitRepo a bien une methode
    `is_available_in_cache` (signature 4.20.0 documentee c.78).

    La signature a change depuis lean-dojo 2.2.0 ; on verifie que la
    methode existe au runtime.
    """
    try:
        mod = importlib.import_module("lean_dojo")
        LeanGitRepo = getattr(mod, "LeanGitRepo", None)
    except ImportError:
        return False
    if LeanGitRepo is None:
        return False
    return hasattr(LeanGitRepo, "is_available_in_cache")


def summarize_axes_1_3() -> dict[str, object]:
    """Axe 1-3 : recapitulatif des conditions RECOVERABLE-LOCAL qui
    n'ont PAS besoin de Lean toolchain local ni de GPU.

    Returns:
        Dict avec les verdicts par axe. Utilise par le carnet
        `Lean-11-LeanDojo-V2-Faisabilite.ipynb` et par
        `test_leandojo_feasibility.py`.
    """
    py_compat, py_version = check_python_compatibility()
    ld_installed, ld_version_or_err = check_lean_dojo_installed()
    ld_min_ok, ld_current, ld_min = check_lean_dojo_version_meets_min()
    public_api = check_lean_dojo_public_api()
    has_cache_method = check_lean_git_repo_has_cache_method()
    return {
        "python": {"compatible": py_compat, "version": py_version},
        "lean_dojo": {
            "installed": ld_installed,
            "version_or_error": ld_version_or_err,
            "min_version_ok": ld_min_ok,
            "current": ld_current,
            "min": ld_min,
        },
        "public_api": public_api,
        "lean_git_repo_cache_method": has_cache_method,
    }