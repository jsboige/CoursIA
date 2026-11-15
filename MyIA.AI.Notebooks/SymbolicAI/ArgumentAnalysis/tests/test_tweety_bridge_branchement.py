"""Contract test for the etape-4 branchement (EPIC #4960, volet B).

Before the branchement, importing the verbatim upstream bridge raised at
module load::

    ImportError: cannot import name 'PLHandler' from
    'argumentation_lib.pl_handler'

because the delivered distilled modules live under underscore names
(``_pl_handler.py``) while the verbatim bridge imports the dotted siblings
(``from .pl_handler import PLHandler``). The compat layer
``_logic_handlers_compat.install()`` (registered at package load,
generalising the C186f ``tweety_initializer`` alias) re-routes those imports
WITHOUT touching the verbatim body. This file holds that contract:

- handler aliases: dotted module IS the delivered underscore module;
- non-ported guards (bipolar/ABA/ASPIC): import-safe, raise at instantiation
  with the EPIC decision (volet B forbids porting them -- #3801);
- config virtual: ``settings.solver == TWEETY`` (no external binary vendored),
  ``pysat_solver`` aligned with the depot organ ``ext_tools/sat_solver.py``;
- prover9/mace4 proxies: call-time RuntimeError (binaries not vendored);
- the bridge itself imports (the ImportError the G.9 fingerprint documented);
- package import stays JVM-free and survives a missing jpype (degradation
  contract of the C186f alias, extended to the whole handler chain).

The end-to-end runtime proof (JVM up, ``TweetyBridge()`` built, a real PL
consistency decision) runs only where the Tweety jars are present: they are
gitignored runtimes (``Tweety/libs``, see ``kernels-runtime.md``), so the
CPU-only CI jobs skip that leg instead of failing.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

# Make `argumentation_lib` importable (../argumentation_lib relative to tests/).
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)

import pytest  # noqa: E402

import argumentation_lib  # noqa: E402

try:  # bridge dependency; absent from the CPU-only jobs
    import jpype  # noqa: F401
except ImportError:  # pragma: no cover - depends on the runner's wheels
    _HAS_JPYPE = False
else:
    _HAS_JPYPE = True

requires_jpype = pytest.mark.skipif(
    not _HAS_JPYPE,
    reason="the bridge (verbatim upstream) imports jpype; CPU-only jobs skip",
)

# Tweety jars are a gitignored runtime: present on the worker seats (junction
# or clone), absent on CI runners. The end-to-end leg skips where absent.
_LIBS_DIR = (
    Path(_ARG_ANALYSIS_DIR).parent / "Tweety" / "libs"
)
requires_tweety_runtime = pytest.mark.skipif(
    not (_LIBS_DIR.exists() and any(_LIBS_DIR.glob("*.jar"))),
    reason="Tweety jars are a gitignored runtime; absent on CI-only seats",
)


# -- 1. Handler aliases: the dotted names resolve to the DELIVERED modules --

_DELIVERED_HANDLERS = (
    "pl", "fol", "modal", "af", "ranking", "adf",
    "belief_revision", "probabilistic", "dialogue",
)


@requires_jpype
@pytest.mark.parametrize("short", _DELIVERED_HANDLERS)
def test_delivered_handler_alias_identity(short: str):
    """`argumentation_lib.<x>_handler` IS `argumentation_lib._<x>_handler`."""
    dotted = f"argumentation_lib.{short}_handler"
    underscore = f"argumentation_lib._{short}_handler"
    assert dotted in sys.modules, (
        f"alias not installed at package load: {dotted} missing"
    )
    assert sys.modules[dotted] is sys.modules.get(
        underscore
    ), f"{dotted} is not the delivered module {underscore}"


# -- 2. Non-ported guards: import-safe, decide-or-fail-loudly at build time --

_NON_PORTED = {
    "bipolar_handler": "BipolarHandler",
    "aba_handler": "ABAHandler",
    "aspic_handler": "ASPICHandler",
}


@pytest.mark.parametrize("short,cls_name", sorted(_NON_PORTED.items()))
def test_non_ported_guard_contract(short: str, cls_name: str):
    """Volet B decision executable: import passes, construction explains.

    The EPIC forbids porting these handlers (NL->structured translation gap
    not closed, #3801): the guard raises at INSTANTIATION with the decision
    verbatim, so a consumer gets the rationale, not a mystery ImportError.
    This leg has no jpype dependency (the guards are pure CoursIA glue) and
    therefore runs on every seat, CPU-only jobs included.
    """
    dotted = f"argumentation_lib.{short}"
    assert dotted in sys.modules, f"guard module not installed: {dotted}"
    guard_cls = getattr(sys.modules[dotted], cls_name)
    with pytest.raises(RuntimeError, match=r"#4960|#3801"):
        guard_cls()


# -- 3. Config virtual: defaults aligned with what CoursIA actually ships --

def test_config_virtual_defaults():
    """`settings` lives at its upstream dotted name with depot-true defaults.

    Divergences vs upstream config.py @ a8025f60 are documented ones:
    solver TWEETY (upstream EPROVER -- no binary vendored here),
    modal_prefer_spass_when_available False (upstream True -- no SPASS
    vendored). pysat_solver carries the depot organ default.
    """
    from argumentation_analysis.core.config import (  # noqa: I001
        ModalSolverChoice,
        PLSolverChoice,
        SolverChoice,
        settings,
    )

    assert settings.solver == SolverChoice.TWEETY
    assert settings.modal_solver == ModalSolverChoice.TWEETY
    assert settings.modal_prefer_spass_when_available is False
    assert settings.pl_solver == PLSolverChoice.TWEETY
    # Depot organ alignment (ext_tools/sat_solver.py default solver).
    assert settings.pysat_solver == "cadical195"
    # The enums are the ported members, not a reduced set.
    assert {m.name for m in SolverChoice} == {
        "TWEETY", "PROVER9", "EPROVER", "MACE4"
    }
    assert {m.name for m in ModalSolverChoice} == {"TWEETY", "SPASS"}
    assert {m.name for m in PLSolverChoice} == {"TWEETY", "PYSAT"}


def test_prover_proxies_raise_at_call_time():
    """Non-vendored external provers fail loudly WHEN CALLED, not at import.

    With `settings.solver == TWEETY` these branches are never taken on the
    default path; the proxy makes an explicit opt-in impossible to mistake
    for a working solver (decide or fail loudly, 05b router philosophy).
    """
    from argumentation_analysis.core import mace4_runner, prover9_runner

    with pytest.raises(RuntimeError, match="non vendu"):
        prover9_runner.run_prover9("goal")
    with pytest.raises(RuntimeError, match="non vendu"):
        mace4_runner.run_mace4("goal")
    # The reliability sentinel keys on the executable: None = no binary.
    assert mace4_runner.MACE4_EXECUTABLE is None


# -- 4. The bridge itself: the G.9-documented ImportError is resolved --

@requires_jpype
def test_bridge_imports_after_branchement():
    """The import the verbatim DEPENDENCY NOTICE documented as failing."""
    from argumentation_lib._tweety_bridge import TweetyBridge  # noqa: F401


@requires_jpype
def test_lazy_accessor_agrees():
    """The public lazy accessor returns the verbatim class, not a shim.

    Regression guard: until the branchement, this accessor was never
    exercisable (the upstream ImportError masked its own phantom imports
    of `TweetyBridgeSK` / module-level `initialize_jvm`). It now returns
    the one module-level symbol the verbatim bridge actually exposes.
    """
    direct = argumentation_lib.get_tweety_bridge_symbol()
    assert direct.__name__ == "TweetyBridge"
    assert (
        direct is sys.modules["argumentation_lib._tweety_bridge"].TweetyBridge
    )


@requires_jpype
def test_bridge_handler_is_the_delivered_pl_handler():
    """The class the bridge imported IS the delivered C186b class.

    The verbatim body does `from .pl_handler import PLHandler as
    PropositionalLogicHandler` at module level: the alias layer must have
    resolved that dotted name to the DELIVERED underscore module BEFORE the
    bridge loaded. Identity of the bound class is the proof.
    """
    from argumentation_lib import _tweety_bridge

    assert (
        _tweety_bridge.PropositionalLogicHandler
        is sys.modules["argumentation_lib._pl_handler"].PLHandler
    )


# -- 5. Package import hygiene: JVM-free, jpype-optional --

@requires_jpype
def test_package_import_starts_no_jvm():
    """Importing the package must not start a JVM (subprocess probe)."""
    import subprocess

    probe = (
        "import sys; sys.path.insert(0, r'"
        + str(_ARG_ANALYSIS_DIR)
        + "'); import argumentation_lib, jpype; "
        "print(jpype.isJVMStarted())"
    )
    out = subprocess.run(
        [sys.executable, "-c", probe],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "False"


def test_package_import_survives_missing_jpype():
    """The compat layer must not make the package jpype-mandatory.

    A meta_path blocker reproduces a seat without the wheel: the package
    import must still succeed and must NOT register the handler aliases
    (the whole handler chain is unavailable without jpype by construction,
    same degradation contract as the C186f initializer alias).
    """
    import subprocess

    probe = (
        "import sys, importlib.abc\n"
        "class _BlockJpype(importlib.abc.MetaPathFinder):\n"
        "    def find_spec(self, fullname, path=None, target=None):\n"
        "        if fullname == 'jpype' or fullname.startswith('jpype.'):\n"
        "            raise ModuleNotFoundError(\"No module named 'jpype'\")\n"
        "        return None\n"
        "sys.meta_path.insert(0, _BlockJpype())\n"
        "sys.path.insert(0, r'" + str(_ARG_ANALYSIS_DIR) + "')\n"
        "import argumentation_lib\n"
        "state = 'aliased' if 'argumentation_lib.pl_handler' in sys.modules"
        " else 'not-aliased'\n"
        "guards = all(\n"
        "    f'argumentation_lib.{s}' in sys.modules\n"
        "    for s in ('bipolar_handler', 'aba_handler', 'aspic_handler')\n"
        ")\n"
        "print(argumentation_lib.__version__, state, guards)\n"
    )
    out = subprocess.run(
        [sys.executable, "-c", probe],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=120,
    )
    assert out.returncode == 0, out.stderr
    version, state, guards = out.stdout.split()
    assert version == argumentation_lib.__version__
    assert state == "not-aliased"
    # The guards are pure glue (no jpype): they install even without it.
    assert guards == "True"


# -- 6. End-to-end runtime proof (seats with the Tweety runtime only) --

@requires_jpype
@requires_tweety_runtime
def test_bridge_decides_pl_end_to_end():
    """JVM up, bridge built, REAL Tweety decisions rendered.

    This is the branchement milestone the EPIC volet B asked for: the
    verbatim bridge running against the real Tweety jars through the alias
    layer, via its PUBLIC decision API (`pl_query`, `validate_pl_formula`).
    Both verdicts matter: an entailment that holds and one that does not --
    the decision is real, not a green import.
    """
    from argumentation_lib._tweety_bridge import TweetyBridge

    bridge = TweetyBridge()
    assert bridge is TweetyBridge(), "the bridge must stay a singleton"

    # Syntax validation: well-formed vs malformed formula. NB: Tweety's
    # PL parser is LENIENT on some junk (`a b`, `a &&& b` parse) but
    # rejects an unbalanced parenthesis -- the probe-verified counter-
    # example, kept here so the contract pins parser reality, not folklore.
    assert bridge.validate_pl_formula("a && b")
    assert not bridge.validate_pl_formula("(a")

    # Entailment both ways (SimplePlReasoner via the JVM):
    assert bridge.pl_query("a && b", "a"), "a && b must entail a"
    assert not bridge.pl_query("a", "b"), "a must NOT entail b"
