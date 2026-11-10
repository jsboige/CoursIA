"""Rejeu hors ligne du classement #25082, sans preuve de service vivant."""

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402

AS_OF = "2026-11-08T10:00:00Z"
ZONE_A = "MyIA.AI.Notebooks/GenAI/Texte"
ZONE_B = "MyIA.AI.Notebooks/GameTheory/Chaines"


def _replay_input():
    stamp = datetime.fromisoformat(AS_OF.replace("Z", "+00:00")).timestamp()
    pool = []
    for i in range(20):
        family = ZONE_A if i % 2 == 0 else ZONE_B
        labels = ["consolidation"] if i % 4 == 0 else []
        pool.append({
            "number": 26000 + i,
            "title": f"Issue {i}",
            "labels": labels,
            "created_at": "2026-01-01T00:00:00Z",
            "age": 311,
            "idle": 100,
            "idle_since_delivery": 100,
            "updated_at": "2026-07-31T00:00:00Z",
            "genre": "guard" if i % 2 else "notebook-python",
            "genre_confident": True,
            "body": "",
            "parent": None,
            "polarity": "neutral",
            "klass": "grain",
            "family": family,
            "family_new_notebooks": 0,
            "last_claim_stamp": None,
            "last_delivery_stamp": None,
            "last_child_stamp": None,
        })
    nums = [item["number"] for item in pool]
    return pig.seal_belt_replay_input({
        "schema": pig.BELT_REPLAY_SCHEMA,
        "repo": pig.REPO,
        "draw_at": AS_OF,
        "source": {
            "transport": "scripts/coordination/gh_snapshot.py",
            "repo": pig.REPO,
            "gh_snapshot_version": 1,
            "gh_snapshot_refreshed_at": AS_OF,
            "computed_at": AS_OF,
            "claim_comment_stamps": {str(n): stamp for n in nums},
        },
        "pool": pool,
        "claim_window": nums,
        "claim_payloads": {str(n): [] for n in nums},
        "family_signal": {"measured": True, "resolved": len(nums),
                          "total": len(nums), "ratio": 1.0},
        "series": {ZONE_A: {"new_notebooks": 0},
                   ZONE_B: {"new_notebooks": 0}},
        "issue_to_family": {str(n): pool[n - nums[0]]["family"] for n in nums},
        "merged_prs": [],
        "closed_issues": [],
        "closed_error": None,
        "open_count": 20,
        "seed_source": "myia-ai-01:CoursIA-2|2026-11-08T10|0",
    })


def test_rejeu_cli_reutilise_le_classement_sans_aucun_transport(monkeypatch,
                                                                tmp_path,
                                                                capsys):
    payload = _replay_input()
    source = tmp_path / "replay.json"
    source.write_text(json.dumps(payload), encoding="utf-8")

    def forbidden(*_args, **_kwargs):
        raise AssertionError("un rejeu hors ligne ne doit appeler aucun transport")

    monkeypatch.setattr(pig.gh_identity, "pin_gh_token", forbidden)
    monkeypatch.setattr(pig.subprocess, "run", forbidden)
    monkeypatch.setattr(pig, "_run_bounded", forbidden)
    monkeypatch.setattr(pig, "fetch_closed_issues", forbidden)
    monkeypatch.setattr(pig, "fetch_pool", forbidden)
    monkeypatch.setattr(pig, "fetch_merged", forbidden)
    monkeypatch.setattr(pig, "fetch_series_visits", forbidden)
    monkeypatch.setattr(pig, "check_claims", forbidden)
    monkeypatch.setattr(pig._gh_snapshot_module(), "_gh_api", forbidden)
    rc = pig.main(["--belt-replay-input", str(source), "--belt-replay-at",
                   AS_OF, "--grains", "10"])

    assert rc == 0
    output = json.loads(capsys.readouterr().out)
    assert output["service_effectif"] is False
    assert output["source"]["transport"] == "scripts/coordination/gh_snapshot.py"
    assert output["replay_at"] == AS_OF
    assert len(output["picks"]) == 10
    assert output["weighted_head"]["total"] == 10
    assert output["weighted_head"]["consolidation"] == 5
    assert [item["number"] for item in output["picks"]] == [
        26000, 26004, 26008, 26012, 26016,
        26001, 26002, 26003, 26005, 26006,
    ]
    assert output["family_coverage"]["ratio"] == 1.0


def test_export_reutilise_la_forme_canonique_gh_snapshot():
    base = _replay_input()
    now = datetime.now(timezone.utc).replace(microsecond=0)
    iso = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    stamp = now.timestamp()
    snapshot = {
        "meta": {"version": 1, "repo": pig.REPO, "refreshed_at": iso,
                 "comment_stamps": {
                     str(item["number"]): stamp for item in base["pool"]}},
        "issues": {},
        "comments": {str(item["number"]): [] for item in base["pool"]},
        "prs": {}, "checks": {}, "repair": {},
    }
    prepared = pig.build_belt_replay_input(
        pool=base["pool"], family_signal=base["family_signal"],
        series=base["series"],
        issue_to_family={int(k): v for k, v in base["issue_to_family"].items()},
        merged_prs=[], closed_issues=[], closed_error=None, open_count=20,
        seed_source=base["seed_source"], snapshot=snapshot, computed_at=now,
        captured_at=now,
    )
    assert prepared["source"]["transport"] == \
        "scripts/coordination/gh_snapshot.py"
    assert set(prepared["claim_payloads"]) == {
        str(item["number"]) for item in base["pool"]}
    assert pig.replay_belt_weights(prepared, iso, head=10)["replay_at"] == iso


def test_export_refuse_si_le_snapshot_canonique_ne_couvre_pas_tout_le_pool():
    base = _replay_input()
    now = datetime.now(timezone.utc).replace(microsecond=0)
    iso = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    snapshot = {
        "meta": {"version": 1, "repo": pig.REPO, "refreshed_at": iso,
                 "comment_stamps": {}},
        "issues": {}, "comments": {}, "prs": {}, "checks": {}, "repair": {},
    }
    with pytest.raises(pig.BeltReplayError, match="commentaires frais"):
        pig.build_belt_replay_input(
            pool=base["pool"], family_signal=base["family_signal"],
            series=base["series"],
            issue_to_family={int(k): v for k, v in base["issue_to_family"].items()},
            merged_prs=[], closed_issues=[], closed_error=None, open_count=20,
            seed_source=base["seed_source"], snapshot=snapshot, computed_at=now,
            captured_at=now,
        )


def test_snapshot_capture_apres_horloge_tirage_garde_le_meme_ordre():
    base = _replay_input()
    draw_at = datetime.now(timezone.utc).replace(microsecond=123456) - timedelta(seconds=1)
    refreshed_moment = draw_at + timedelta(milliseconds=300)
    claim_moment = draw_at + timedelta(milliseconds=400)
    captured_at = draw_at + timedelta(milliseconds=700)
    captured_iso = captured_at.isoformat(timespec="microseconds").replace(
        "+00:00", "Z")
    draw_iso = draw_at.isoformat().replace("+00:00", "Z")
    refreshed_at = refreshed_moment.isoformat(timespec="microseconds").replace(
        "+00:00", "Z")
    base["draw_at"] = draw_iso
    base["source"]["computed_at"] = captured_iso
    base["source"]["gh_snapshot_refreshed_at"] = refreshed_at
    base["source"]["claim_comment_stamps"] = {
        str(item["number"]): claim_moment.timestamp() for item in base["pool"]}
    snapshot = {
        "meta": {"version": 1, "repo": pig.REPO,
                 "refreshed_at": refreshed_at,
                 "comment_stamps": {
                     str(item["number"]): claim_moment.timestamp()
                     for item in base["pool"]}},
        "issues": {},
        "comments": {str(item["number"]): [] for item in base["pool"]},
        "prs": {}, "checks": {}, "repair": {},
    }
    prepared = pig.build_belt_replay_input(
        pool=base["pool"], family_signal=base["family_signal"],
        series=base["series"],
        issue_to_family={int(k): v for k, v in base["issue_to_family"].items()},
        merged_prs=[], closed_issues=[], closed_error=None, open_count=20,
        seed_source=base["seed_source"], snapshot=snapshot,
        computed_at=draw_at, captured_at=captured_at,
    )
    assert prepared["draw_at"] == draw_iso
    assert prepared["source"]["computed_at"] == captured_iso
    assert refreshed_moment > draw_at
    assert claim_moment > refreshed_moment
    assert captured_at > claim_moment
    replay = pig.replay_belt_weights(prepared, captured_iso, head=10)
    # `base` a ete modifie apres la fabrication de la fixture : il faut le
    # re-sceler, comme le ferait un producteur qui reecrit son export.
    base = pig.seal_belt_replay_input(base)
    original_order = pig.replay_belt_weights(base, captured_iso, head=10)["picks"]
    assert replay["picks"] == original_order


@pytest.mark.parametrize("mutation, message", [
    (lambda data: data["claim_payloads"].pop("26000"), "payload de commentaire"),
    (lambda data: data["source"]["claim_comment_stamps"].pop("26000"),
     "horodatage de commentaire"),
    (lambda data: data["source"]["claim_comment_stamps"].update(
        {"26000": float("nan")}), "horodatage de claim invalide"),
    (lambda data: data["source"]["claim_comment_stamps"].update(
        {"26000": datetime.fromisoformat(AS_OF.replace("Z", "+00:00"))
         .timestamp() + 0.1}), "claim perime"),
    (lambda data: data["source"].update(
        gh_snapshot_refreshed_at="2026-11-08T12:00:00+02:00"), "en UTC"),
    (lambda data: data["source"].update(gh_snapshot_refreshed_at="2026-11-07T00:00:00Z"),
     "perime"),
    (lambda data: ([item.update(family=None) for item in data["pool"][:5]],
                   data["family_signal"].update(resolved=15, ratio=0.75)),
     "couverture des familles"),
])
def test_entrees_incompletes_ou_perimees_refusees_avant_tirage(
        monkeypatch, mutation, message):
    payload = _replay_input()
    mutation(payload)

    def forbidden(*_args, **_kwargs):
        raise AssertionError("le tirage a commence avant validation complete")

    monkeypatch.setattr(pig, "apply_belt_weights", forbidden)
    with pytest.raises(pig.BeltReplayError, match=message):
        pig.replay_belt_weights(payload, AS_OF, head=10)


@pytest.mark.parametrize("mutation, message", [
    (lambda data: data.update(source=None), "provenance d'instantane malformee"),
    (lambda data: data["issue_to_family"].update({"oops": ZONE_A}),
     "cle issue-famille invalide"),
])
def test_entrees_malformees_rc2_sans_traceback_ni_tirage(
        monkeypatch, tmp_path, capsys, mutation, message):
    payload = _replay_input()
    mutation(payload)
    path = tmp_path / "invalid.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    def forbidden(*_args, **_kwargs):
        raise AssertionError("le mode invalide ne doit pas tirer ni appeler le reseau")

    monkeypatch.setattr(pig, "apply_belt_weights", forbidden)
    monkeypatch.setattr(pig.gh_identity, "pin_gh_token", forbidden)
    rc = pig.main(["--belt-replay-input", str(path), "--belt-replay-at",
                   AS_OF])
    out, err = capsys.readouterr()
    result = json.loads(out)
    assert rc == 2
    assert message in result["error"]
    assert result["draw"] == "aucun"
    assert "Traceback" not in out + err


def test_export_refuse_une_destination_dans_le_depot(tmp_path):
    repo_path = Path(pig.__file__).resolve().parents[1]
    with pytest.raises(pig.BeltReplayError, match="interdit dans le depot"):
        pig.write_belt_replay_input(repo_path / "replay.json", _replay_input())


# --- #25082 : l'empreinte qui scelle l'export -------------------------------
# Ces quatre attaques sont celles mesurees par la revue Hermes 5830473523 :
# le validateur ne verifiait que la coherence interne, et les quatre pasaient.
@pytest.mark.parametrize("mutation", [
    lambda data: data.update(seed_source="myia-ai-01:CoursIA-2|2026-11-08T10|999"),
    lambda data: data["pool"][0].update(title="Issue 0 -- traffichee"),
    lambda data: data.update(merged_prs=[{"number": 1, "title": "fabrique"}]),
    lambda data: data.update(open_count=9999),
])
def test_empreinte_refuse_les_quatre_attaques_avant_tirage(monkeypatch, mutation):
    payload = _replay_input()
    mutation(payload)

    def forbidden(*_args, **_kwargs):
        raise AssertionError("le tirage a commence avant validation complete")

    monkeypatch.setattr(pig, "apply_belt_weights", forbidden)
    with pytest.raises(pig.BeltReplayError, match="empreinte de l'export invalide"):
        pig.replay_belt_weights(payload, AS_OF, head=10)


def test_rejeu_refuse_un_export_sans_empreinte(monkeypatch):
    payload = _replay_input()
    payload.pop("fingerprint")

    def forbidden(*_args, **_kwargs):
        raise AssertionError("le tirage a commence avant validation complete")

    monkeypatch.setattr(pig, "apply_belt_weights", forbidden)
    with pytest.raises(pig.BeltReplayError, match="empreinte de l'export absente"):
        pig.replay_belt_weights(payload, AS_OF, head=10)


def test_empreinte_stable_et_sensible_a_un_octet():
    payload = _replay_input()
    digest = pig.belt_replay_fingerprint(payload)
    assert digest == pig.belt_replay_fingerprint(payload)
    assert digest.startswith(pig.BELT_REPLAY_FINGERPRINT_SCOPE + ":")
    altered = dict(payload)
    altered["seed_source"] = payload["seed_source"] + " "
    assert pig.belt_replay_fingerprint(altered) != digest


def test_le_rejeu_rend_l_empreinte_de_l_export_consomme():
    payload = _replay_input()
    replay = pig.replay_belt_weights(payload, AS_OF, head=5)
    assert replay["fingerprint"] == payload["fingerprint"]
