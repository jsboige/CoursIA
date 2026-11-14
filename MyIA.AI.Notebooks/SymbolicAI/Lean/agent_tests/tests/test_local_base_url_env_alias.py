"""Le provider local accepte les deux orthographes de sa base URL (#1453).

Cas fondateur (mesure firsthand, po-2025, 2026-11-04) : le shell de la machine
exporte ``LOCAL_LLM_API_BASE`` (et ``LOCAL_LLM_API_KEY``), alors que
``prover/config.py`` ne lisait que ``LOCAL_LLM_BASE_URL``. Le gate #1453 a donc
refuse cinq fois de lancer la passe 24 en annoncant « base_url vide », pour un
endpoint qui repondait en realite (``401`` sur le port 5003 = auth requise,
transport vivant). Le nom de variable ne rencontrait pas le code, pas la cle.

Ces tests fixent les trois choses qui doivent rester vraies : les deux noms
sont lus, l'ancien garde la preseance quand les deux sont poses (aucun
environnement qui marchait ne change de comportement en silence), et le
message de refus du gate nomme les deux — un operateur ne doit pas avoir a
deviner quelle variable le gate attendait.

``PROVIDERS`` est construit a l'import du module : chaque cas de resolution
tourne donc dans un interpreteur neuf (sous-processus), sans polluer l'etat
des autres tests de la session par un ``importlib.reload``.
"""

import os
import subprocess
import sys
import unittest
from pathlib import Path

AGENT_TESTS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(AGENT_TESTS))

from prover import config, provider_gate  # noqa: E402

_PROBE = "from prover.config import PROVIDERS; print(PROVIDERS['local']['base_url'])"


def _local_base_url(env_extra):
    """Return ``PROVIDERS['local']['base_url']`` in a fresh interpreter."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("LOCAL_LLM_")}
    env.update(env_extra)
    proc = subprocess.run(
        [sys.executable, "-c", _PROBE],
        cwd=str(AGENT_TESTS),
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=True,
    )
    return proc.stdout.strip()


class TestLocalBaseUrlResolution(unittest.TestCase):
    def test_api_base_alias_is_read(self):
        """The machine spelling alone must reach the provider config."""
        self.assertEqual(
            _local_base_url({"LOCAL_LLM_API_BASE": "http://127.0.0.1:5003/v1"}),
            "http://127.0.0.1:5003/v1",
        )

    def test_base_url_spelling_still_read(self):
        self.assertEqual(
            _local_base_url({"LOCAL_LLM_BASE_URL": "http://127.0.0.1:8000/v1"}),
            "http://127.0.0.1:8000/v1",
        )

    def test_base_url_wins_when_both_are_set(self):
        """An environment that already worked keeps its behaviour."""
        self.assertEqual(
            _local_base_url(
                {
                    "LOCAL_LLM_BASE_URL": "http://127.0.0.1:8000/v1",
                    "LOCAL_LLM_API_BASE": "http://127.0.0.1:5003/v1",
                }
            ),
            "http://127.0.0.1:8000/v1",
        )

    def test_empty_whitespace_does_not_win(self):
        """A blank primary must not shadow a configured alias."""
        self.assertEqual(
            _local_base_url(
                {
                    "LOCAL_LLM_BASE_URL": "   ",
                    "LOCAL_LLM_API_BASE": "http://127.0.0.1:5003/v1",
                }
            ),
            "http://127.0.0.1:5003/v1",
        )

    def test_none_configured_stays_empty(self):
        self.assertEqual(_local_base_url({}), "")


class TestGateAgreesWithConfig(unittest.TestCase):
    def test_env_name_tuples_do_not_drift(self):
        """The gate names what ``config`` reads; the two must stay equal."""
        self.assertEqual(
            provider_gate.PROVIDER_ENV_BASE_URLS["local"],
            config.LOCAL_BASE_URL_ENV_NAMES,
        )

    def test_local_base_reached_through_alias_is_not_refused(self):
        """The exact po-2025 situation: alias + key -> the gate must pass."""
        eff = {"reasoning": "local"}
        providers = {
            "local": {
                "base_url": "http://127.0.0.1:5003/v1",
                "api_key": "sk-local",
            }
        }
        self.assertEqual(provider_gate.validate_provider_credentials(eff, providers), [])

    def test_empty_base_names_both_variables(self):
        eff = {"reasoning": "local"}
        providers = {"local": {"base_url": "", "api_key": "sk-local"}}
        problems = provider_gate.validate_provider_credentials(eff, providers)
        self.assertEqual(len(problems), 1)
        self.assertIn("LOCAL_LLM_BASE_URL", problems[0])
        self.assertIn("LOCAL_LLM_API_BASE", problems[0])

    def test_localhost_still_keyless(self):
        """Unchanged contract: a localhost endpoint needs no key (#1453)."""
        eff = {"reasoning": "local"}
        providers = {"local": {"base_url": "http://localhost:11434/v1", "api_key": ""}}
        self.assertEqual(provider_gate.validate_provider_credentials(eff, providers), [])


if __name__ == "__main__":
    unittest.main()
