"""Tests de scripts/ci/ci_overflow_probe.py (#26939) -- aucun reseau.

Contrat verifie ici :
1. le coeur `decide()` rejoue l'episode du 16/11 (386/false -> dispatch) et la
   reorientation (386/true -> dispatch), avec les controles negatifs ;
2. l'anti-repetition (hold si dernier passage < 15 min, fenetre de saturation
   de l'organe) ;
3. le budget d'appels : EXACTEMENT 2 au repos, 3 sur candidat (dry-run), 4 au
   dispatch effectif -- la promesse de l'issue, mesuree, pas declaree ;
4. les seuils viennent de l'organe (HOSTED_CONCURRENCY_CAP importe, pas copie) ;
5. la cadence du workflow tient le critere de latence (ecart max <= 15 min).

Pattern FakeAPI (forme de test_advisory_sticky) : les appels `gh` sont rejoues
depuis des payloads fixes, aucun appel reel n'est emis.
"""
from __future__ import annotations

import json
import re
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import ci_overflow_controller as controller  # noqa: E402
import ci_overflow_probe as probe  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[3]
WORKFLOW_FILE = REPO_ROOT / ".github" / "workflows" / "ci-overflow-probe.yml"


class FakeAPI:
    """Rejoue les reponses `gh api` et COMPTE les appels (preuve de budget)."""

    def __init__(self, queue_total: int, variable: str, last_created_at: str | None):
        self.queue_total = queue_total
        self.variable = variable
        self.last_created_at = last_created_at
        self.calls: list[list[str]] = []

    def __call__(self, args: list[str], token: str | None = None) -> tuple[int, str]:
        self.calls.append(list(args))
        path = args[0]
        if "status=queued" in path:
            return 0, json.dumps({"total_count": self.queue_total})
        if "/variables/" in path:
            return 0, json.dumps({"name": "V", "value": self.variable})
        if "/runs?" in path and "workflows/" in path:
            runs = (
                [{"created_at": self.last_created_at}] if self.last_created_at else []
            )
            return 0, json.dumps({"workflow_runs": runs})
        if path.endswith("/dispatches"):
            return 0, ""
        return 1, json.dumps({"message": f"unexpected path {path}"})


NOW = datetime(2026, 11, 16, 13, 0, tzinfo=timezone.utc)
OLD_RUN = (NOW - timedelta(minutes=61)).isoformat().replace("+00:00", "Z")
FRESH_RUN = (NOW - timedelta(minutes=5)).isoformat().replace("+00:00", "Z")


# --- 1. Coeur de decision -------------------------------------------------


def test_episode_16_11_dispatch():
    """Episode du 16/11 : 386 runs en file, variable false, controleur vieux de 61 min."""
    d = probe.decide(386, "false", last_pass_age_min=61.0)
    assert d.action == "dispatch"
    assert "386" in d.reason and "20" in d.reason


def test_episode_16_11_reorient():
    """Meme file apres bascule de la variable : le seuil double a 40, 386 passe encore."""
    d = probe.decide(386, "true", last_pass_age_min=61.0)
    assert d.action == "dispatch"
    assert "40" in d.reason


def test_hold_anti_repetition():
    """Candidat mais dernier passage recent : hold, pas de dispatch."""
    d = probe.decide(386, "false", last_pass_age_min=5.0)
    assert d.action == "hold"
    assert "anti-repetition" in d.reason


def test_gap_boundary_is_organ_saturation_window():
    """Le gap par defaut EST la fenetre de saturation du controleur (organ-first)."""
    assert probe.DEFAULT_MIN_DISPATCH_GAP_MINUTES == controller.DEFAULT_SATURATION_MINUTES == 15.0
    # Frontiere : age = gap -> dispatch (l'instantane controleur est perime).
    assert probe.decide(386, "false", last_pass_age_min=15.0).action == "dispatch"


def test_negative_controls_idle():
    """File basse ou seuils non franchis (strictement) : idle."""
    assert probe.decide(5, "false").action == "idle"
    assert probe.decide(20, "false").action == "idle"  # frontiere : pas strictement >
    assert probe.decide(25, "true").action == "idle"   # sous le seuil de reorientation
    assert probe.decide(40, "true").action == "idle"   # frontiere : pas strictement >


def test_no_known_passage_dispatches():
    """Aucun passage connu (age=None) : le candidat se dispatche (premier passage)."""
    assert probe.decide(386, "false", last_pass_age_min=None).action == "dispatch"


# --- 2. Budget d'appels (la promesse de l'issue, mesuree) ------------------


def test_budget_exactly_two_calls_at_rest():
    api = FakeAPI(5, "false", OLD_RUN)
    d, calls, dispatched = probe.run("r/v", "V", "wf.yml", None, 20.0, api=api, now=NOW)
    assert d.action == "idle"
    assert calls == 2, f"au repos la sonde doit faire EXACTEMENT 2 appels, pas {calls}"
    assert dispatched is False


def test_budget_three_calls_on_candidate_dry_run():
    api = FakeAPI(386, "false", OLD_RUN)
    d, calls, dispatched = probe.run(
        "r/v", "V", "wf.yml", None, 20.0, dry_run=True, api=api, now=NOW
    )
    assert d.action == "dispatch"
    assert calls == 3, f"sur candidat en dry-run : 3 appels (file, variable, age), pas {calls}"
    assert dispatched is False


def test_budget_four_calls_and_dispatch_on_fire():
    api = FakeAPI(386, "false", OLD_RUN)
    d, calls, dispatched = probe.run("r/v", "V", "wf.yml", None, 20.0, api=api, now=NOW)
    assert d.action == "dispatch"
    assert calls == 4
    assert dispatched is True
    dispatch_calls = [c for c in api.calls if c[0].endswith("/dispatches")]
    assert len(dispatch_calls) == 1
    assert "-X" in dispatch_calls[0] and "POST" in dispatch_calls[0]
    assert "ref=main" in dispatch_calls[0]


def test_hold_short_circuits_before_dispatch():
    """Age frais (5 min) : 3 appels, hold, aucune ecriture."""
    api = FakeAPI(386, "false", FRESH_RUN)
    d, calls, dispatched = probe.run("r/v", "V", "wf.yml", None, 20.0, api=api, now=NOW)
    assert d.action == "hold"
    assert calls == 3
    assert dispatched is False
    assert not any(c[0].endswith("/dispatches") for c in api.calls)


def test_unreadable_queue_is_hold_not_crash():
    class DeadAPI:
        def __call__(self, args, token=None):
            return 1, ""

    d, calls, _ = probe.run("r/v", "V", "wf.yml", None, 20.0, api=DeadAPI(), now=NOW)
    assert d.action == "hold" and "illisible" in d.reason and calls == 1


# --- 3. Seuils ancre's sur l'organe (organ-first) ---------------------------


def test_thresholds_imported_from_organ():
    assert probe.PROBE_TRIGGER_QUEUE == controller.HOSTED_CONCURRENCY_CAP == 20
    assert probe.PROBE_REORIENT_QUEUE == 2 * controller.HOSTED_CONCURRENCY_CAP == 40


# --- 4. Cadence du workflow (critere de latence <= 15 min) ----------------


def test_parse_cron_minutes_subset():
    assert probe.parse_cron_minutes("4-59/12") == [4, 16, 28, 40, 52]
    assert probe.parse_cron_minutes("*/5")[:3] == [0, 5, 10]
    assert probe.parse_cron_minutes("31") == [31]
    assert probe.parse_cron_minutes("0,30") == [0, 30]


def test_workflow_cadence_holds_latency_contract():
    """L'ecart max entre deux passages du workflow reste sous 15 min (wrap compris)."""
    text = WORKFLOW_FILE.read_text(encoding="utf-8")
    m = re.search(r"cron:\s*'([^']+)'", text)
    assert m, "cron introuvable dans ci-overflow-probe.yml"
    minutes = probe.parse_cron_minutes(m.group(1).split()[0])
    gap = probe.max_cadence_gap_minutes(minutes)
    assert gap <= probe.MAX_CADENCE_GAP_MINUTES, f"ecart max {gap} min > 15 min"


def test_workflow_cron_avoids_controller_collision():
    """La sonde ne tire jamais a la minute 31 du cron controleur, ni sur :00/:30."""
    text = WORKFLOW_FILE.read_text(encoding="utf-8")
    m = re.search(r"cron:\s*'([^']+)'", text)
    minutes = probe.parse_cron_minutes(m.group(1).split()[0])
    assert 31 not in minutes
    assert 0 not in minutes and 30 not in minutes
