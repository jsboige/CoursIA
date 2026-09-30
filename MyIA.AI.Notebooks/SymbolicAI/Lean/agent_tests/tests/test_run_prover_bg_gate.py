"""Gate fail-fast des credentials provider — run_prover_bg (#1453, 2026-09-19).

Cas fondateur (mesure firsthand, calibration DEMOS 45/41/52 passe 1) : sur une
lane sans clés, ``--provider local`` seul laisse Coordinator/Tactic sur le
défaut ``openrouter`` et Search/Critic sur le routage p6 ``zai`` — le run
stubbe la cible, prend le tree lock, puis meurt 3x401 -> provider_outage sans
aucune tentative. Le gate doit nommer chaque rôle mal configuré AVANT le
lock, et ne pas bloquer une config localhost valide (Ollama/vLLM).
"""

import argparse
import sys
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import run_prover_bg  # noqa: E402


def _args(**kw):
    base = dict(
        demo_id=45,
        line=None,
        provider="local",
        local_provider="local",
        max_iter=1,
        workflow_timeout=60,
        director_provider=None,
        coordinator_provider=None,
        tactic_provider=None,
        search_provider=None,
        critic_provider=None,
        force_lock=False,
    )
    base.update(kw)
    return argparse.Namespace(**base)


class TestEffectiveAgentProviders(unittest.TestCase):
    def test_defaults_mirror_provers_and_p6(self):
        eff = run_prover_bg._effective_agent_providers(_args())
        self.assertEqual(eff["coordinator"], "openrouter")
        self.assertEqual(eff["tactic"], "openrouter")
        # p6_routing route Search/Critic vers zai par defaut
        self.assertEqual(eff["search"], "zai")
        self.assertEqual(eff["critic"], "zai")
        self.assertEqual(eff["reasoning"], "local")

    def test_overrides_win(self):
        eff = run_prover_bg._effective_agent_providers(
            _args(
                coordinator_provider="local",
                tactic_provider="local",
                search_provider="local",
                critic_provider="local",
            )
        )
        self.assertEqual(
            eff,
            {
                "reasoning": "local",
                "fast": "local",
                "coordinator": "local",
                "tactic": "local",
                "search": "local",
                "critic": "local",
            },
        )

    def test_director_included_only_when_set(self):
        self.assertNotIn(
            "director", run_prover_bg._effective_agent_providers(_args())
        )
        self.assertIn(
            "director",
            run_prover_bg._effective_agent_providers(
                _args(director_provider="openrouter")
            ),
        )


class TestValidateProviderCredentials(unittest.TestCase):
    KEYLESS = {
        "local": {
            "base_url": "http://localhost:11434/v1",
            "api_key": "ollama",
        },
        "openrouter": {"base_url": "https://openrouter.ai/api/v1", "api_key": ""},
        "zai": {"base_url": "https://api.z.ai/api/coding/paas/v4", "api_key": ""},
    }

    def test_keyless_lane_names_every_misrouted_role(self):
        with mock.patch.object(run_prover_bg, "PROVIDERS", self.KEYLESS):
            eff = run_prover_bg._effective_agent_providers(_args())
            problems = run_prover_bg._validate_provider_credentials(eff)
        joined = "\n".join(problems)
        # les 4 roles mal routees sont nommes avec leur var d'env
        for role, env in (
            ("coordinator", "OPENROUTER_API_KEY"),
            ("tactic", "OPENROUTER_API_KEY"),
            ("search", "ZAI_API_KEY"),
            ("critic", "ZAI_API_KEY"),
        ):
            self.assertIn(role, joined, joined)
            self.assertIn(env, joined, joined)
        # localhost (Ollama) jamais signale
        self.assertNotIn("reasoning", joined)
        self.assertNotIn("fast", joined)

    def test_valid_all_local_config_passes(self):
        with mock.patch.object(run_prover_bg, "PROVIDERS", self.KEYLESS):
            eff = run_prover_bg._effective_agent_providers(
                _args(
                    coordinator_provider="local",
                    tactic_provider="local",
                    search_provider="local",
                    critic_provider="local",
                )
            )
            self.assertEqual(run_prover_bg._validate_provider_credentials(eff), [])

    def test_local_without_base_url_refused(self):
        cfg = dict(self.KEYLESS, local={"base_url": "", "api_key": ""})
        with mock.patch.object(run_prover_bg, "PROVIDERS", cfg):
            problems = run_prover_bg._validate_provider_credentials(
                {"reasoning": "local"}
            )
        self.assertEqual(len(problems), 1)
        self.assertIn("base_url vide", problems[0])

    def test_unknown_provider_reported(self):
        with mock.patch.object(run_prover_bg, "PROVIDERS", self.KEYLESS):
            problems = run_prover_bg._validate_provider_credentials(
                {"tactic": "nosuchprovider"}
            )
        self.assertIn("unknown provider", problems[0])

    def test_remote_with_key_passes(self):
        cfg = dict(
            self.KEYLESS,
            openrouter={
                "base_url": "https://openrouter.ai/api/v1",
                "api_key": "sk-or-x",
            },
        )
        with mock.patch.object(run_prover_bg, "PROVIDERS", cfg):
            self.assertEqual(
                run_prover_bg._validate_provider_credentials(
                    {"tactic": "openrouter"}
                ),
                [],
            )


if __name__ == "__main__":
    unittest.main()
