"""Garde partagee : sauter les tests EndToEnd quand le budget `gh` est epuise.

Plusieurs tests de ce repertoire invoquent le **vrai** `gh` (directement, ou a
travers les scripts testes). Ce sont des verifications bout-en-bout honnetes,
mais elles virent au **rouge trompeur** quand le budget GraphQL du compte est
epuise : la sortie devient vide et le seul message utile est
`gh error: GraphQL: API rate limit already exceeded` (#17201, triage du
21/09/2026 : les 4 `TestEndToEnd` de `test_prune_merged_worktrees` et
`test_check_pr_perimeter::test_founding_incident_11227_criteria_met_on_main`).

Le budget est **partage par compte** (les merges du coordinateur tournent sous
le meme utilisateur), donc la rougeur est intermittente par construction : elle
suit les fenetres d'activite de la flotte, pas le code teste.

ATTENTION — piege de diagnostic : `gh api rate_limit` n'est PAS une sonde
valide. Il repond `graphql: 5000/5000` alors que les appels GraphQL reels sont
refuses. Seule une sonde GraphQL reelle discrimine.

Usage :

    from ._gh_availability import skip_if_gh_exhausted
    ...
    def test_something(self):
        skip_if_gh_exhausted()

ou, pour un test qui lance un script appelant `gh` :

    skip_if_output_rate_limited(proc.stdout + proc.stderr)
"""

from __future__ import annotations

import shutil
import subprocess

# Marqueurs de refus du budget. La sonde GraphQL renvoie le message dans
# `errors[].message` ; le script teste peut le propager tel quel.
_RATE_LIMIT_MARKERS = (
    "rate limit already exceeded",
    "graphql_rate_limit",
    "api rate limit exceeded",
    "secondary rate limit",
)

_PROBE = ("gh", "api", "graphql", "-f", "query={ viewer { login } }")

# Cache module : une seule sonde par session (cout = 1 point de budget).
_probe_verdict: bool | None = None


def is_rate_limited(output: str) -> bool:
    """True si `output` porte une signature de budget gh epuise."""
    lowered = (output or "").lower()
    return any(marker in lowered for marker in _RATE_LIMIT_MARKERS)


def gh_graphql_ok() -> bool | None:
    """Sonde le budget GraphQL reel.

    Returns:
        True  -- un appel GraphQL a abouti ;
        False -- l'appel a ete refuse pour cause de budget ;
        None  -- verdict indetermine (gh absent, erreur de transport) : dans
                 ce cas on ne saute pas, le test garde son comportement
                 anterieur (les suites concernent toutes `gh`).
    """
    global _probe_verdict
    if _probe_verdict is not None:
        return _probe_verdict
    if shutil.which("gh") is None:
        return None
    try:
        probe = subprocess.run(
            list(_PROBE),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if probe.returncode == 0:
        _probe_verdict = True
        return True
    combined = (probe.stdout or "") + (probe.stderr or "")
    if is_rate_limited(combined):
        _probe_verdict = False
        return False
    return None


def skip_if_gh_exhausted() -> None:
    """Saute le test courant si le budget GraphQL du compte est epuise.

    A appeler au debut d'un test EndToEnd dependant de `gh`. Un budget epuise
    n'est pas un defaut du livrable teste : un rouge ici est un faux positif.
    """
    if gh_graphql_ok() is False:
        import pytest

        pytest.skip(
            "gh GraphQL budget exhausted (shared account quota) — "
            "end-to-end verdict not measurable now (#17201)"
        )


def skip_if_output_rate_limited(output: str) -> None:
    """Saute le test si la sortie observee porte la signature du budget.

    Filet de course : le budget peut s'epuiser *pendant* le test, apres une
    sonde initiale favorable.
    """
    if is_rate_limited(output):
        import pytest

        pytest.skip(
            "gh GraphQL budget exhausted mid-run — end-to-end verdict not "
            "measurable now (#17201)"
        )
