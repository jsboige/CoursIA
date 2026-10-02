"""Gate fail-fast partage + lanceur inner — #18709.

Cas fondateur (po-2025, 2026-10-01, mesure firsthand x2) : le lanceur inner
``prover/run_prover_bg.py`` n'exposait ni les overrides
``--search/--critic/--diagnosis-provider`` ni le gate de cles #1453 — sur une
lane sans ``ZAI_API_KEY``, le pin P6 (Search/Critic -> zai) crashait
'Missing credentials' ~45 min apres le depart (build + GoalExtract deja
faits), sans aucun signal au lancement.

Ces tests prouvent : (1) la resolution partagee reflete le pin P6 et les
overrides, (2) la semantique diagnosis (gate seulement si active/override),
(3) le lanceur inner refuse AVANT le tree lock en nommant la cle manquante,
(4) les flags atteignent bien le constructeur MultiAgentSorryProver.
"""

import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))


def _stub_llm_stack_if_absent() -> None:
    """Stub la stack LLM absente des runners CI nus (finding Hermes PR #18722).

    ``prover/__init__`` tire ``provers``/``workflow``/``config`` qui importent
    ``agent_framework`` / ``agent_framework_openai`` au top-level : sur un
    runner CPU sans la stack, ces imports cassent la COLLECTE pytest avant
    meme que les fixtures ne jouent. Ces tests ne declenchent jamais d'appel
    LLM (constructeur mocke via mock.patch.object), des placeholders
    suffisent. Si la vraie stack est presente (machine de dev), elle est
    utilisee telle quelle -- le stub ne s'active que sur ImportError.
    """
    try:
        import agent_framework  # noqa: F401
        return  # vraie stack disponible : rien a stubber
    except ImportError:
        pass

    class _Placeholder:
        def __init__(self, *args, **kwargs):
            raise RuntimeError(
                "stub agent_framework : suite jouee sans stack LLM"
            )

        @classmethod
        def __class_getitem__(cls, item):  # annotations generiques
            return cls                      # (WorkflowContext[ProofMessage])

    def _handler(*args, **kwargs):
        # Decorateur : usage nu ``@handler`` (workflow.py) -- pass-through.
        if len(args) == 1 and not kwargs and callable(args[0]):
            return args[0]
        return lambda f: f

    af = types.ModuleType("agent_framework")
    for name in (
        "Agent",
        "ChatOptions",
        "Executor",
        "WorkflowBuilder",
        "WorkflowContext",
        "Case",
        "Default",
        "ToolResultCompactionStrategy",
    ):
        setattr(af, name, _Placeholder)
    af.handler = _handler
    sys.modules["agent_framework"] = af
    afo = types.ModuleType("agent_framework_openai")
    afo.OpenAIChatCompletionClient = _Placeholder
    sys.modules["agent_framework_openai"] = afo


_stub_llm_stack_if_absent()

from prover import run_prover_bg as inner  # noqa: E402
from prover.provider_gate import (  # noqa: E402
    effective_agent_providers,
    validate_provider_credentials,
)

# Fixture providers : zai distant sans cle (le cas fondateur), local
# keyless-by-design sur localhost, openrouter distant avec cle.
KEYLESS = {
    "zai": {"base_url": "https://api.z.ai/v1", "api_key": ""},
    "local": {"base_url": "http://localhost:5002/v1", "api_key": ""},
    "openrouter": {"base_url": "https://openrouter.ai/api/v1",
                   "api_key": "sk-or-ok"},
}


class TestEffectiveAgentProvidersShared(unittest.TestCase):
    def test_defaults_mirror_p6(self):
        eff = effective_agent_providers("zai", "local")
        self.assertEqual(eff["search"], "zai")
        self.assertEqual(eff["critic"], "zai")
        self.assertEqual(eff["coordinator"], "openrouter")
        self.assertEqual(eff["tactic"], "openrouter")
        self.assertNotIn("diagnosis", eff)  # agent desactive -> pas de gate

    def test_diagnosis_gated_on_activation_or_override(self):
        eff = effective_agent_providers("zai", "local",
                                        use_diagnosis_agent=True)
        self.assertEqual(eff["diagnosis"], "zai")  # pin P6
        eff = effective_agent_providers("zai", "local",
                                        diagnosis_provider="openrouter")
        self.assertEqual(eff["diagnosis"], "openrouter")

    def test_overrides_win_over_p6(self):
        eff = effective_agent_providers(
            "zai", "local",
            search_provider="openrouter", critic_provider="openrouter")
        self.assertEqual(eff["search"], "openrouter")
        self.assertEqual(eff["critic"], "openrouter")


class TestValidateProviderCredentialsShared(unittest.TestCase):
    def test_keyless_p6_pin_named_before_launch(self):
        eff = effective_agent_providers("zai", "local")
        problems = validate_provider_credentials(eff, KEYLESS)
        joined = " ; ".join(problems)
        self.assertIn("ZAI_API_KEY", joined)
        self.assertIn("search", joined)
        self.assertIn("critic", joined)

    def test_override_removes_the_problem(self):
        # reasoning/fast ont leurs cles ; seuls les pins P6 (search/critic
        # -> zai) posent probleme, et les overrides les corrigent.
        eff = effective_agent_providers(
            "openrouter", "local",
            search_provider="openrouter", critic_provider="openrouter")
        self.assertEqual(validate_provider_credentials(eff, KEYLESS), [])

    def test_localhost_keyless_passes(self):
        self.assertEqual(
            validate_provider_credentials(
                {"fast": "local"}, KEYLESS), []
        )


class TestInnerLauncherGate(unittest.TestCase):
    """Le lanceur inner doit refuser AVANT le tree lock (#18709)."""

    def test_gate_refuses_before_tree_lock(self):
        with mock.patch.object(inner, "PROVIDERS", KEYLESS), \
             mock.patch.object(inner, "acquire_tree_lock") as lock, \
             mock.patch.object(inner, "find_lean_project_root"):
            summary = inner.run_prover(
                filepath="fake/Foo.lean", line=1,
                provider="zai", local_provider="local",
            )
        lock.assert_not_called()
        self.assertEqual(summary["result_kind"], "provider_gate")
        self.assertIn("ZAI_API_KEY", summary["reason"])

    def test_gate_passes_with_overrides(self):
        fake_root = Path("fake")
        with mock.patch.object(inner, "PROVIDERS", KEYLESS), \
             mock.patch.object(inner, "acquire_tree_lock",
                               return_value=(fake_root / ".prover.lock",
                                             "")) as lock, \
             mock.patch.object(inner, "release_tree_lock"), \
             mock.patch.object(inner, "find_lean_project_root",
                               return_value=fake_root), \
             mock.patch.object(inner, "_run_with_calibration_stub",
                               return_value={"result_kind": "stubbed"}) as run:
            summary = inner.run_prover(
                filepath="fake/Foo.lean", line=1,
                provider="openrouter", local_provider="local",
                search_provider="openrouter", critic_provider="openrouter",
            )
        lock.assert_called_once()
        self.assertEqual(summary["result_kind"], "stubbed")
        # les overrides traversent la couche calibration (#18709 plumbing)
        self.assertEqual(
            run.call_args.kwargs.get("search_provider")
            or run.call_args.args[11],
            "openrouter",
        )
        self.assertEqual(
            run.call_args.kwargs.get("critic_provider")
            or run.call_args.args[12],
            "openrouter",
        )


class TestFlagsReachConstructor(unittest.TestCase):
    """--search/--critic/--diagnosis-provider atteignent le constructeur."""

    def test_run_prover_locked_passes_provider_kwargs(self):
        with tempfile.TemporaryDirectory() as td:
            target = Path(td) / "Foo.lean"
            target.write_text(
                "theorem foo : True := by sorry\n", encoding="utf-8"
            )
            prover = mock.MagicMock()
            prover.prove_sorry = mock.AsyncMock(
                return_value={"success": False, "iterations": 0}
            )
            with mock.patch.object(inner, "MultiAgentSorryProver",
                                   return_value=prover) as ctor, \
                 mock.patch.object(inner, "TraceLogger"), \
                 mock.patch.object(inner, "TRACES_DIR", Path(td)):
                inner._run_prover_locked(
                    demo={"file": str(target), "name": "foo", "line": 1,
                          "goal": ""},
                    name="foo", filepath=str(target), line=1,
                    mode="multi", iterations=1,
                    provider="zai", local_provider="local",
                    director_provider=None, coordinator_provider=None,
                    tactic_provider=None,
                    search_provider="openrouter",
                    critic_provider="openrouter",
                    diagnosis_provider="openrouter",
                    use_diagnosis_agent=False, concurrent_search_count=0,
                )
        kwargs = ctor.call_args.kwargs
        self.assertEqual(kwargs["search_provider"], "openrouter")
        self.assertEqual(kwargs["critic_provider"], "openrouter")
        self.assertEqual(kwargs["diagnosis_provider"], "openrouter")


if __name__ == "__main__":
    unittest.main()
