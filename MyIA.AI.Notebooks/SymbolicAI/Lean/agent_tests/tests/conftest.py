"""CI hermeticity guard for the prover harness suites (#21331).

The suites in this directory mix two populations:

* **hermetic tests** — they exercise the stdlib-only spine of the harness
  (``prover.state``, ``prover.trace``, ``prover.tools``, ``prover.knowledge``,
  ``prover.lean_utils``) and must run (and pass) on a bare runner;
* **LLM-stack tests** — they import ``prover.workflow`` / ``prover.provers`` /
  ``prover.agents`` / ``prover.config`` *inside* the test body, which drags
  ``agent_framework`` / ``agent_framework_openai`` at call time.

Collection no longer dies on a bare runner: ``prover/__init__.py`` resolves
the stack-bound subpackages lazily (PEP 562 ``__getattr__``), so pytest can
collect every test. At RUN time, however, the stack tests would fail with
``ModuleNotFoundError`` on a runner without the LLM stack.

This conftest reclassifies exactly that failure — a ``ModuleNotFoundError``
naming one of the two stack packages, raised inside a test or fixture — as a
SKIP, the same classification ``pytest.importorskip`` would give. It does NOT
install stub modules: ``prover/trace.py`` (and any other consumer) keeps its
graceful ``try/except ImportError`` degradation working untouched, and on a
machine where the stack IS installed nothing is intercepted at all.

Precedent: ``test_bg_tree_lock.py`` runs 14 pass / 3 skip on a bare runner
by ``importorskip``; this guard extends the same contract to the mixed
suites without touching their 116 deferred import sites.
"""

import importlib.util
import pytest

_STACK_PACKAGES = ("agent_framework", "agent_framework_openai")

_STACK_PRESENT = all(
    importlib.util.find_spec(name) is not None for name in _STACK_PACKAGES
)


def _is_stack_absence(exc: BaseException) -> bool:
    return (
        isinstance(exc, ModuleNotFoundError)
        and exc.name in _STACK_PACKAGES
    )


if not _STACK_PRESENT:

    @pytest.hookimpl(hookwrapper=True)
    def pytest_runtest_makereport(item, call):
        outcome = yield
        rep = outcome.get_result()
        if (
            rep.when in ("setup", "call")
            and rep.outcome == "failed"
            and call.excinfo is not None
            and _is_stack_absence(call.excinfo.value)
        ):
            rep.outcome = "skipped"
            # pytest attends un 3-tuple ``(fichier, ligne, raison)`` -- pas une
            # chaine. Une chaine passe sur les rapporteurs compacts, mais en
            # mode verbeux ``_get_raw_skip_reason`` fait ``assert
            # isinstance(report.longrepr, tuple)`` et levee d'un
            # ``INTERNALERROR`` fait echouer la jambe de tests ENTIERE, sans
            # qu'aucun test ne soit en echec (#21331, mesure 2026-10-30).
            rep.longrepr = (
                str(item.path),
                item.location[1] or 0,
                f"SKIPPED: {call.excinfo.value.name} absent — LLM-stack "
                f"test skipped on bare runner (#21331)",
            )
