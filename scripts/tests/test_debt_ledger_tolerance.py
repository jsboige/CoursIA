#!/usr/bin/env python3
"""Contrôles de tolérance bornée du journal et du spool (#22456).

Un libellé manuscrit se re-clé avec un avertissement ; une empreinte divergente
reste refusée. Un fichier illisible reste visible et bloque la gate GPU, sans
supprimer les autres enveloppes du lot.
"""
from __future__ import annotations

import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from test_debt_ledger import dl, held, issue_obs  # noqa: E402


NOW = datetime(2026, 9, 17, 20, 0, 0, tzinfo=timezone.utc)

REPO_ROOT = Path(__file__).resolve().parents[2]
RESERVATION_DOC = REPO_ROOT / "docs" / "coordination" / "gpu-reservation.md"

#: Ligne du tableau des verdicts : | `VERDICT` | code | lecture |
_VERDICT_ROW_RE = re.compile(
    r"^\|\s*`([A-Z_]+)`\s*\|\s*\*{0,2}(\d)\*{0,2}\s*\|", re.MULTILINE
)


def _manual_observation(observation_id: str = "obs-manuscrit0000001") -> dict:
    raw = issue_obs(state_class="open-blocked", eat_hours=2.0)
    raw["observation_id"] = observation_id
    return raw


def _journal_with(observation: dict) -> dict:
    return {
        "schema": dl.EXPORT_SCHEMA,
        "ledger": dl.ISSUE_DEBT,
        "window": {"kind": "full", "archives": []},
        "messages": [{
            "messageId": "msg-manuscrit",
            "author": observation["actor"],
            "createdAt": observation["observed_at"],
            "content": dl.envelope_line(observation),
        }],
    }


def _two_good_envelopes(spool: Path) -> list[dict]:
    observations = []
    for number, stamp in ((15545, "2026-09-17T19:00:00Z"), (15546, "2026-09-17T18:00:00Z")):
        observation = dl.parse_observation(
            issue_obs(issue=number, observed_at=stamp, state_class="open-blocked"),
            dl.ISSUE_DEBT,
        )
        dl.spool_observation(spool, observation)
        observations.append(observation)
    return observations


def _check_pending_args(state_dir: Path, *, json_output: bool) -> list[str]:
    args = [
        "check_pending",
        "--ledger", dl.GPU_RESERVATION,
        "--entity", "myia-ai-01#gpu2",
        "--state-dir", str(state_dir),
        "--now", "2026-09-17T20:00:00Z",
    ]
    if json_output:
        args.append("--json")
    return args


def test_manual_id_is_rekeyed_with_a_warning_and_survives_reduction():
    expected = dl.parse_observation(issue_obs(state_class="open-blocked", eat_hours=2.0), dl.ISSUE_DEBT)
    warnings: list[str] = []
    accepted = dl.parse_observation(_manual_observation(), dl.ISSUE_DEBT, warnings=warnings)

    assert accepted["observation_id"] == expected["observation_id"]
    assert len(warnings) == 1
    assert "observation_id_rekeyed" in warnings[0]
    assert "obs-manuscrit0000001" in warnings[0]
    assert set(accepted) <= dl.OBSERVATION_KEYS

    journal_warnings: list[str] = []
    window, records, rejections = dl.parse_journal_export(
        _journal_with(_manual_observation()), dl.ISSUE_DEBT, warnings=journal_warnings
    )
    assert window["kind"] == "full"
    assert len(records) == 1
    assert records[0].observation_id == expected["observation_id"]
    assert rejections == []
    assert journal_warnings == warnings

    folded = dl.reduce_ledger(
        ledger=dl.ISSUE_DEBT, export=_journal_with(_manual_observation()), now=NOW
    )
    assert folded.snapshot["rejections"] == []
    assert len(folded.snapshot["rows"]) == 1
    assert folded.snapshot["rows"][0]["provenance"]["eat_hours"]["observation_id"] == expected["observation_id"]
    assert folded.snapshot["warnings"] == warnings
    assert "warn: observation_id_rekeyed" in folded.status_text


def test_append_manual_id_surfaces_warning_on_stderr(tmp_path, capsys):
    source = tmp_path / "manuscrit.json"
    source.write_text(json.dumps(_manual_observation()), encoding="utf-8")

    rc = dl.main([
        "append", "--ledger", dl.ISSUE_DEBT,
        "--observation-file", str(source),
        "--state-dir", str(tmp_path / "state"), "--dry-run",
    ])

    assert rc == 0
    captured = capsys.readouterr()
    assert "WARNING observation_id_rekeyed" in captured.err
    assert "obs-manuscrit0000001" in captured.err
    assert '"observation_id": "obs-manuscrit0000001"' not in captured.out


def test_digest_shaped_disagreement_is_still_refused():
    for declared_id in ("obs-0000000000000000", "obs-ffffffffffffffff"):
        with pytest.raises(dl.ObservationError) as excinfo:
            dl.parse_observation(_manual_observation(declared_id), dl.ISSUE_DEBT)
        assert excinfo.value.reason == "observation_id_mismatch"


def test_legacy_canonicalisation_rekeys_without_warning_or_rejection(monkeypatch):
    monkeypatch.setattr(dl, "canonical_machine", lambda raw: raw.strip().lower())
    legacy = dl.parse_observation(held(machine="ai-01", gpu_index=2), dl.GPU_RESERVATION)
    monkeypatch.undo()
    stamped = dict(held(machine="ai-01", gpu_index=2), observation_id=legacy["observation_id"])
    warnings: list[str] = []

    accepted = dl.parse_observation(stamped, dl.GPU_RESERVATION, warnings=warnings)

    assert accepted["observation_id"] != legacy["observation_id"]
    assert accepted["entity"] == {"machine": "myia-ai-01", "gpu_index": 2}
    assert warnings == []
    export = {
        "schema": dl.EXPORT_SCHEMA,
        "ledger": dl.GPU_RESERVATION,
        "window": {"kind": "full"},
        "messages": [{
            "messageId": "legacy",
            "author": stamped["actor"],
            "createdAt": stamped["observed_at"],
            "content": dl.envelope_line(stamped),
        }],
    }
    folded = dl.reduce_ledger(ledger=dl.GPU_RESERVATION, export=export, now=NOW)
    assert folded.snapshot["rejections"] == []
    assert folded.snapshot["warnings"] == []


def test_spool_bad_file_is_reported_without_losing_good_envelopes(tmp_path):
    spool = tmp_path / "spool"
    observations = _two_good_envelopes(spool)
    bad = spool / "zz-bad.json"
    bad.write_text("[OBS] []", encoding="utf-8")

    status = dl.spool_status(spool)
    unreadable = dl.spool_unreadable(spool)
    pending = dl.spool_pending(spool, ledger=dl.ISSUE_DEBT)

    assert status[dl.ISSUE_DEBT]["pending"] == 2
    assert status[dl.ISSUE_DEBT]["oldest_observed_at"] == "2026-09-17T18:00:00Z"
    assert set(status) == set(dl.LEDGERS)
    assert unreadable == [{"path": str(bad), "reason": "unparsable_envelope: content JSON is not an object"}]
    assert [item["observation"]["observation_id"] for item in pending] == [
        observations[1]["observation_id"], observations[0]["observation_id"]
    ]
    manifest = dl.flush_manifest(dl.ISSUE_DEBT, pending)
    assert manifest["count"] == 2
    assert bad.exists(), "l'écart de l'index ne doit pas effacer la trace"
    dl.archive_posted(spool, [observation["observation_id"] for observation in observations])
    assert dl.spool_status(spool)[dl.ISSUE_DEBT]["pending"] == 0
    assert dl.spool_unreadable(spool) == unreadable


def test_index_spool_excludes_unreadable_file_even_by_filename(tmp_path):
    spool = tmp_path / "spool"
    observations = _two_good_envelopes(spool)
    bad = spool / "obs-manuscrit0000001.json"
    bad.write_text("[OBS] []", encoding="utf-8")

    index = dl._index_spool(spool, strict=False)

    assert "obs-manuscrit0000001" not in index
    assert bad.stem not in index
    assert {observation["observation_id"] for observation in observations} <= set(index)


def test_spool_status_cli_aggregates_each_ledger_once(tmp_path, capsys):
    state_dir = tmp_path / "state"
    _two_good_envelopes(state_dir / dl.ISSUE_DEBT / "spool")
    gpu = dl.parse_observation(held(), dl.GPU_RESERVATION)
    dl.spool_observation(state_dir / dl.GPU_RESERVATION / "spool", gpu)

    rc = dl.main(["spool", "--status", "--state-dir", str(state_dir)])

    assert rc == 0
    captured = capsys.readouterr()
    assert captured.out.count("issue-debt: pending=2 ") == 1
    assert captured.out.count("gpu-reservation: pending=1 ") == 1
    assert captured.err == ""


def test_check_pending_json_names_unreadable_spool_instead_of_releasing(tmp_path, capsys):
    state_dir = tmp_path / "state"
    spool = state_dir / dl.GPU_RESERVATION / "spool"
    observation = dl.parse_observation(held(), dl.GPU_RESERVATION)
    dl.spool_observation(spool, observation)
    bad = spool / "zz-bad.json"
    bad.write_text("[OBS] []", encoding="utf-8")

    rc = dl.main(_check_pending_args(state_dir, json_output=True))

    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err == ""
    payload = json.loads(captured.out)
    assert payload["verdict"] == "UNREADABLE_SPOOL"
    assert payload["verdict"] != "RELEASED"
    assert payload["entity"] == "myia-ai-01#gpu2"
    assert payload["now"] == "2026-09-17T20:00:00Z"
    assert str(bad) in payload["reason"]
    assert "content JSON is not an object" in payload["reason"]


def test_check_pending_human_form_names_unreadable_spool(tmp_path, capsys):
    state_dir = tmp_path / "state"
    spool = state_dir / dl.GPU_RESERVATION / "spool"
    bad = spool / "zz-bad.json"
    bad.parent.mkdir(parents=True)
    bad.write_text("not JSON", encoding="utf-8")

    rc = dl.main(_check_pending_args(state_dir, json_output=False))

    assert rc == 1
    captured = capsys.readouterr()
    assert captured.err == ""
    assert captured.out.startswith("UNREADABLE_SPOOL  myia-ai-01#gpu2  ")
    assert str(bad) in captured.out
    assert "content is not JSON" in captured.out
    assert "RELEASED" not in captured.out


def _documented_verdicts() -> dict[str, int]:
    text = RESERVATION_DOC.read_text(encoding="utf-8")
    return {verdict: int(code) for verdict, code in _VERDICT_ROW_RE.findall(text)}


def test_documented_verdicts_cover_every_verdict_the_gate_can_render():
    """La table de la doc et le code ne peuvent plus diverger en silence.

    Un verdict rendu par la gate sans ligne dans la doc laisse un appelant sans
    mode d'emploi ; une ligne dans la doc sans verdict dans le code promet une
    sortie qui n'existe pas. Les deux sens sont verifies ici (#22456).
    """
    documented = _documented_verdicts()

    renderable = set(dl.GPU_PENDING_VERDICTS) | set(dl.GPU_GATE_VERDICTS)
    assert renderable <= set(documented), (
        "verdict rendu par la gate mais absent de "
        f"{RESERVATION_DOC.name}: {sorted(renderable - set(documented))}"
    )
    assert set(documented) <= set(dl.GPU_VERDICT_EXIT_CODES), (
        "verdict documenté sans code de sortie dans le module : "
        f"{sorted(set(documented) - set(dl.GPU_VERDICT_EXIT_CODES))}"
    )
    assert set(dl.GPU_VERDICT_EXIT_CODES) == renderable, (
        "le code de sortie déclare un verdict que la gate ne rend pas : "
        f"{sorted(set(dl.GPU_VERDICT_EXIT_CODES) - renderable)}"
    )


def test_documented_exit_codes_match_the_code():
    documented = _documented_verdicts()

    for verdict, code in sorted(dl.GPU_VERDICT_EXIT_CODES.items()):
        assert documented[verdict] == code, (
            f"le code de sortie de {verdict} a dérivé : "
            f"doc={documented[verdict]} code={code}"
        )
