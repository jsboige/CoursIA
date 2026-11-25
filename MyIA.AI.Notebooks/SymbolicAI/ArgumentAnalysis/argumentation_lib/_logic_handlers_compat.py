# _logic_handlers_compat.py -- EPITA logic-handler import compatibility layer
# for EPIC #4960, volet B etape 4 (branchement formel, sous-grain du 2026-11-14).
#
# PURPOSE
# -------
# The verbatim upstream bridge `_tweety_bridge.py` (commit a8025f60) imports
# its 12 logic handlers + `TweetyInitializer` at module level via
# `from .pl_handler import PLHandler ...`, while the delivered distilled
# modules live under underscore names (`_pl_handler.py`, C186b/c sub-tranches).
# Same re-routing need as the C186f `tweety_initializer` alias already
# registered in `__init__.py` -- this module generalises that alias to the
# whole handler chain, so the bridge becomes importable WITHOUT any
# modification of its verbatim body.
#
# Three families of virtual modules are installed (idempotent):
#
#   1. `argumentation_lib.{pl,fol,modal,af,ranking,adf,belief_revision,
#      probabilistic,dialogue}_handler` -> aliases to the delivered
#      underscore modules (jpype-dependent, each guarded: without jpype the
#      handler itself is already unavailable, the rest stays importable --
#      same degradation contract as the initializer alias).
#
#   2. `argumentation_lib.{bipolar,aba,aspic}_handler` -> NON-PORT guards.
#      The EPIC body (volet B, TweetyBridge line) FORBIDS porting
#      ASPIC+/ABA/bipolar (NL->structured translation gap not closed --
#      porting them would consecrate a workaround, #3801). The guard classes
#      import safely and raise a documented RuntimeError at INSTANTIATION
#      only, so the bridge import chain stays green and the decision stays
#      executable ("decide or fail loudly", the 05b router philosophy).
#
#   3. `argumentation_analysis.core.{config,prover9_runner,mace4_runner}` ->
#      minimal EPITA-namespace virtuals completing the C186g coverage
#      (which already covers `jvm_setup` + `utils.logging_utils`):
#        - `config`: `settings` (solver=TWEETY by default -- the branchement
#          IS the Tweety leg; `pysat_solver='cadical195'` aligned with the
#          depot organ `ext_tools/sat_solver.py`) + the `SolverChoice` /
#          `PLSolverChoice` enums the verbatim handlers import.
#        - `prover9_runner` / `mace4_runner`: call-time RuntimeError proxies.
#          The external binaries are NOT vendored (volet B "bruit" interdit
#          d'import); with `settings.solver == TWEETY` the prover9/mace4
#          branches are never taken, and the mace4 reliability sentinel
#          (`_fol_handler._mace4_delivery_is_reliable`) catches the raise and
#          falls back -- the degradation is by design, not a workaround.
#
# ANTI-REGRESSION (D)
# -------------------
# 0 `pass`, 0 `return None`, 0 `sorry`, 0 `raise NotImplementedError`.
# This is glue: it registers already-delivered modules under the dotted
# names the verbatim upstream files import, plus decision-bearing guards.
# No derivation logic, no fake solver output.
#
# See NOTICE-EPITA at the root of this directory for the vendoring contract.

from __future__ import annotations

import sys
import types
from enum import Enum
from types import SimpleNamespace

_INSTALLED: bool = False

# Depot organ default (ext_tools/sat_solver.py, solve_sat default solver).
_PYSAT_DEFAULT_SOLVER = "cadical195"


class SolverChoice(str, Enum):
    """FOL solver selection — ported verbatim (members) from upstream
    `argumentation_analysis/core/config.py` @ a8025f60 (lines 5-17)."""

    TWEETY = "tweety"
    PROVER9 = "prover9"
    EPROVER = "eprover"
    MACE4 = "mace4"


class ModalSolverChoice(str, Enum):
    """Modal solver selection — ported verbatim (members) from upstream
    `config.py` @ a8025f60 (lines 20-24)."""

    TWEETY = "tweety"
    SPASS = "spass"


class PLSolverChoice(str, Enum):
    """PL solver selection — ported verbatim (members) from upstream
    `config.py` @ a8025f60 (lines 27-31)."""

    TWEETY = "tweety"
    PYSAT = "pysat"


class _NonPortedHandlerGuard:
    """Instantiation-time guard for a handler the EPIC forbids porting.

    Import-safe (the bridge chain stays green); raises at construction with
    the decision verbatim so a consumer gets the rationale, not a mystery.
    """

    _DECISION = (
        "non porte par decision EPIC #4960 volet B : translation-gap "
        "NL->structure non bouche (ASPIC+/ABA/bipolar, cf corps de l'EPIC) ; "
        "porter ce handler consacrerait un workaround (#3801)"
    )

    def __init__(self, *args, **kwargs):
        raise RuntimeError(
            f"{type(self).__name__}: {self._DECISION}"
        )


def _external_prover_disabled(name: str):
    """Build the call-time proxy for a non-vendored external prover."""

    def _disabled(*args, **kwargs):
        raise RuntimeError(
            f"{name}: binaire externe non vendu dans CoursIA (volet B, bruit "
            "interdit d'import) ; le handler FOL reste sur la jambe Tweety "
            "par defaut (settings.solver == TWEETY) et la sentinelle mace4 "
            "retombe proprement"
        )

    return _disabled


def _install_argumentation_analysis_config() -> None:
    """Register `argumentation_analysis.core.config` (settings + enums)."""
    _ensure_package("argumentation_analysis.core")
    if "argumentation_analysis.core.config" in sys.modules:
        return
    settings = SimpleNamespace(
        # Divergences documentees vs amont (config.py @ a8025f60) :
        # - solver : amont EPROVER (Tweety EFOLReasoner, binaire externe) ;
        #   CoursIA TWEETY (SimpleFolReasoner, pure-Java) car aucun binaire
        #   eprover n'est vendu ici (volet B, bruit interdit d'import).
        # - modal_prefer_spass_when_available : amont True (SPASS vendor
        #   ext_tools/spass) ; CoursIA False, aucun SPASS vende.
        # Les autres defauts sont portes tels quels.
        solver=SolverChoice.TWEETY,
        modal_solver=ModalSolverChoice.TWEETY,
        modal_prefer_spass_when_available=False,
        pl_solver=PLSolverChoice.TWEETY,
        pysat_solver=_PYSAT_DEFAULT_SOLVER,
    )
    mod = types.ModuleType("argumentation_analysis.core.config")
    mod.settings = settings
    mod.SolverChoice = SolverChoice
    mod.ModalSolverChoice = ModalSolverChoice
    mod.PLSolverChoice = PLSolverChoice
    sys.modules["argumentation_analysis.core.config"] = mod


def _install_argumentation_analysis_provers() -> None:
    """Register the prover9/mace4 runner virtuals (call-time disabled)."""
    _ensure_package("argumentation_analysis.core")
    if "argumentation_analysis.core.prover9_runner" not in sys.modules:
        p9 = types.ModuleType("argumentation_analysis.core.prover9_runner")
        p9.run_prover9 = _external_prover_disabled("run_prover9")
        sys.modules["argumentation_analysis.core.prover9_runner"] = p9
    if "argumentation_analysis.core.mace4_runner" not in sys.modules:
        m4 = types.ModuleType("argumentation_analysis.core.mace4_runner")
        m4.run_mace4 = _external_prover_disabled("run_mace4")
        m4.interpret_mace4_output = _external_prover_disabled(
            "interpret_mace4_output"
        )
        # The reliability sentinel caches per `str(MACE4_EXECUTABLE)`;
        # None keeps that key stable and truthful (no binary).
        m4.MACE4_EXECUTABLE = None
        sys.modules["argumentation_analysis.core.mace4_runner"] = m4


def _install_non_ported_guards() -> None:
    """Register the bipolar/aba/aspic import-safe guard modules."""
    for short in ("bipolar_handler", "aba_handler", "aspic_handler"):
        full = f"argumentation_lib.{short}"
        if full in sys.modules:
            continue
        mod = types.ModuleType(full)
        # Noms de classes exacts qu'importe le pont verbatim (lignes 77-80).
        cls_name = {
            "bipolar_handler": "BipolarHandler",
            "aba_handler": "ABAHandler",
            "aspic_handler": "ASPICHandler",
        }[short]
        guard = type(cls_name, (_NonPortedHandlerGuard,), {})
        setattr(mod, cls_name, guard)
        sys.modules[full] = mod


def _alias_delivered_handlers() -> None:
    """Alias the delivered underscore handlers under their upstream names.

    jpype-dependent, guarded per handler: without jpype (CPU-only jobs) the
    handler module itself cannot load, and the alias is simply not
    installed -- the degradation contract of the C186f initializer alias.
    """
    delivered = (
        "pl", "fol", "modal", "af", "ranking", "adf",
        "belief_revision", "probabilistic", "dialogue",
    )
    for short in delivered:
        upstream = f"argumentation_lib.{short}_handler"
        delivered_name = f"argumentation_lib._{short}_handler"
        if sys.modules.get(upstream) is not None:
            continue
        module = sys.modules.get(delivered_name)
        if module is None:
            try:
                module = __import__(
                    delivered_name, fromlist=["__name__"]
                )
            except ImportError:
                # jpype absent, or an upstream dep still missing: the
                # corresponding handler (and the bridge) stays deferred,
                # the rest of the package remains importable.
                continue
        sys.modules.setdefault(upstream, module)


def _ensure_package(dotted: str) -> None:
    """Ensure `dotted` exists as a namespace-ish package in sys.modules."""
    parts = dotted.split(".")
    for i in range(1, len(parts) + 1):
        name = ".".join(parts[:i])
        if name not in sys.modules:
            pkg = types.ModuleType(name)
            pkg.__path__ = []  # mark as package for submodule imports
            sys.modules[name] = pkg


def _alias_modal_normalizer() -> None:
    """Alias the vendored normalizer under the name `_modal_handler` imports.

    Dependency-free (stdlib only), so this alias installs unconditionally.
    """
    upstream = "argumentation_lib.modal_kb_identifier_normalizer"
    if sys.modules.get(upstream) is not None:
        return
    try:
        module = __import__(
            "argumentation_lib._modal_kb_identifier_normalizer",
            fromlist=["__name__"],
        )
    except ImportError:  # pragma: no cover - stdlib-only module
        return
    sys.modules.setdefault(upstream, module)


def install() -> bool:
    """Install every compatibility virtual (idempotent).

    Returns True when the handler aliases could be installed (jpype
    available), False otherwise -- the caller degrades gracefully.
    """
    global _INSTALLED
    # Virtuals first: the handlers import config/prover9/mace4 at module
    # level, so those must resolve BEFORE `_pl_handler` et al. are loaded.
    _install_argumentation_analysis_config()
    _install_argumentation_analysis_provers()
    _install_non_ported_guards()
    _alias_modal_normalizer()
    _alias_delivered_handlers()
    _INSTALLED = True
    return all(
        f"argumentation_lib.{short}_handler" in sys.modules
        for short in ("pl", "fol", "modal", "af")
    )
