"""Tests du geste 5 #18203 : integration du journal des tirages dans le picker.

Le module ``scripts/coordination/tirage_journal.py`` (merge #19945) porte
l'API verrouillee ; ces tests verifient les TROIS points de consigne de
``main()`` (reparation, tapis, volee ponderee) et le caractere best-effort
du helper : un defaut de journal ne doit jamais priver la lane du grain que
la commande vient de lui rendre.

Fichier separe de ``test_pick_idle_grain.py`` et
``test_pick_idle_grain_belt.py`` deliberement : ces derniers sont portes
par des PRs ouvertes (#20052, #19594) -- les helpers sont dupliques ici
plutot que partages, pour que chaque PR avance sans rebase croise.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import pick_idle_grain as pig  # noqa: E402
import tirage_journal  # noqa: E402

LANE = "myia-po-2024:CoursIA-2"


def _journal_path(tmp_path):
    return tmp_path / "journal.jsonl"


# ==================================================================
# Helper _log_tirage_safe : best-effort par construction
# ==================================================================


def test_helper_writes_record_and_returns_it(monkeypatch, tmp_path):
    """Controle positif : la consigne ecrit un TirageRecord complet."""
    jp = _journal_path(tmp_path)
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(jp))
    rec = pig._log_tirage_safe(lane=LANE, candidates=[11, 12], retained=11,
                               urn="belt", mode="belt")
    assert rec is not None and rec.draw_id, (
        "le helper rend l'enregistrement ecrit -- le tirage est traçable"
    )
    rows = tirage_journal.read_journal(jp)
    assert len(rows) == 1
    assert rows[0].lane == LANE
    assert rows[0].candidates == [11, 12]
    assert rows[0].retained == 11
    assert rows[0].urn == "belt"
    assert rows[0].mode == "belt"


def test_helper_is_inert_under_pytest_without_env(monkeypatch, tmp_path,
                                                  capsys):
    """Sous pytest sans TIRAGE_JOURNAL_PATH : INERT, pas un echec bavard.

    Meme commutateur d'environnement que le cache et la sonde delivered :
    un test unitaire n'ecrit pas dans le state dir machine, et stderr
    reste propre -- l'inertie n'est pas une panne.
    """
    monkeypatch.delenv("TIRAGE_JOURNAL_PATH", raising=False)
    rec = pig._log_tirage_safe(lane=LANE, candidates=[1], retained=1,
                               urn="belt", mode="belt")
    assert rec is None
    captured = capsys.readouterr()
    assert "journal" not in captured.err.lower(), (
        f"inertie bavarde sur stderr : {captured.err!r}"
    )
    assert not _journal_path(tmp_path).exists()


def test_helper_swallows_journal_failure(monkeypatch, tmp_path, capsys):
    """Un defaut d'ecriture ne lève PAS : stderr une ligne, grain rendu.

    Le journal est une couche d'observabilite, jamais un gate -- un
    disque plein ne doit pas priver la lane de son tirage.
    """
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(_journal_path(tmp_path)))

    def boom(**kwargs):
        raise OSError("disque plein")

    monkeypatch.setattr(pig.tirage_journal, "log_tirage", boom)
    rec = pig._log_tirage_safe(lane=LANE, candidates=[5], retained=None,
                               urn="belt", mode="belt")
    assert rec is None
    assert "NON ECRIT" in capsys.readouterr().err


def test_helper_survives_absent_module(monkeypatch, capsys):
    """Clone sans le module : le picker tire SANS journal, en le disant.

    L'import best-effort met ``tirage_journal = None`` ; le helper rend
    None avec une ligne stderr -- jamais une exception.
    """
    monkeypatch.setattr(pig, "tirage_journal", None)
    rec = pig._log_tirage_safe(lane=LANE, candidates=[5], retained=5,
                               urn="belt", mode="belt")
    assert rec is None
    assert "indisponible" in capsys.readouterr().err


# ==================================================================
# Fixtures reseau : neutralisation hermetique (doctrine #19913 -- un
# test n'atteint JAMAIS le reseau par defaut)
# ==================================================================


def _make_item(number, created, klass="grain", genre="docs"):
    return {"number": number, "klass": klass, "age": 200, "idle": 10,
            "genre": genre, "labels": [], "title": f"issue #{number}",
            "created_at": created, "last_delivery_stamp": None,
            "updated_at": created, "weight": 1.0}


def _state_red(number):
    """Etat GraphQL d'une PR rouge, forme rendue par fetch_pr_states.

    Forme NESTEE complete (reviews.nodes, commits.nodes ->
    statusCheckRollup.contexts.nodes) : une forme aplatie est silencieusement
    illisible par ``blocking_causes`` -- le garde rouge ne declenche pas et
    le test sort sur le reseau reel (mesure pendant l'ecriture de ce test).
    """
    return {
        "number": number, "mergeable": "MERGEABLE",
        "reviews": {"nodes": []},
        "commits": {"nodes": [{"commit": {"statusCheckRollup": {"contexts": {"nodes": [
            {"name": "PR gate", "conclusion": "FAILURE", "isRequired": True,
             "completedAt": "2026-10-08T00:00:00Z"}
        ]}}}}]},
    }


def _patch_common_network(monkeypatch):
    """Le socle commun a tous les chemins de main() hors reseau."""
    monkeypatch.setattr(pig.gh_identity, "pin_gh_token",
                        lambda *a, **k: None)
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: [])
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {})
    monkeypatch.setattr(pig, "unaddressed_review_points", lambda nums: {})
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **k: ([], None))
    monkeypatch.setattr(pig, "fetch_main_head_probe", lambda *a, **k: None)
    monkeypatch.setattr(pig, "fetch_visits", lambda *a, **k: ({}, None))
    monkeypatch.setattr(pig, "fetch_series_visits",
                        lambda **k: ({}, {}, None))
    monkeypatch.setattr(pig, "fetch_merged", lambda *a, **k: ([], None))
    # Doctrine #19913 : main() injecte les sondes REELLES au tapis
    # (delivered_probe=has_delivered_signal) -- on les remplace par les
    # inertes pour que la boucle ne sorte jamais sur un vrai gh.
    monkeypatch.setattr(pig, "has_delivered_signal",
                        pig.delivered_probe_inert)
    monkeypatch.setattr(pig, "merged_pr_signal", pig.merged_pr_probe_inert)


# ==================================================================
# Chemin REPARATION : le plus frequent pour une lane chargee -- sans
# cette entree, le journal sur-estimerait la part du pool proposee.
# ==================================================================


def test_repair_path_journals_the_assignment(monkeypatch, tmp_path):
    jp = _journal_path(tmp_path)
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(jp))
    _patch_common_network(monkeypatch)
    red = _state_red(0)
    created = (pig.NOW
               - pig.dt.timedelta(hours=30)).strftime("%Y-%m-%dT%H:%M:%SZ")
    prs = [{"number": 401, "title": "pr 401",
            "body": f"Grain: MED/guard -- lane {LANE}",
            "createdAt": created, "isDraft": False}]
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    monkeypatch.setattr(pig, "fetch_pr_states",
                        lambda nums: {n: red for n in nums})

    rc = pig.main(["--lane", LANE])

    assert rc == 0
    rows = tirage_journal.read_journal(jp)
    assert len(rows) == 1, "une invocation = une entree"
    assert rows[0].mode == "repair"
    assert rows[0].urn == "repair"
    assert rows[0].candidates == [401]
    assert rows[0].retained == 401, (
        "le grain journalise est la PR a reparer, pas un numero de pool"
    )


def test_repair_json_path_also_journals(monkeypatch, tmp_path, capsys):
    """Le consommateur --json a la meme trace que la sortie texte."""
    jp = _journal_path(tmp_path)
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(jp))
    _patch_common_network(monkeypatch)
    red = _state_red(0)
    created = (pig.NOW
               - pig.dt.timedelta(hours=30)).strftime("%Y-%m-%dT%H:%M:%SZ")
    prs = [{"number": 402, "title": "pr 402",
            "body": f"Grain: MED/guard -- lane {LANE}",
            "createdAt": created, "isDraft": False}]
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    monkeypatch.setattr(pig, "fetch_pr_states",
                        lambda nums: {n: red for n in nums})

    rc = pig.main(["--lane", LANE, "--json"])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "repair"
    rows = tirage_journal.read_journal(jp)
    assert len(rows) == 1
    assert rows[0].mode == "repair"
    assert rows[0].retained == 402


# ==================================================================
# Chemin TAPIS (--belt) : candidats servis + tete retenue
# ==================================================================


def test_belt_path_journals_head_of_queue(monkeypatch, tmp_path, capsys):
    jp = _journal_path(tmp_path)
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(jp))
    _patch_common_network(monkeypatch)
    pool = [
        _make_item(7001, "2025-01-01T00:00:00Z"),
        _make_item(7002, "2025-02-01T00:00:00Z"),
        _make_item(7003, "2025-03-01T00:00:00Z"),
    ]
    monkeypatch.setattr(pig, "fetch_pool", lambda **k: (pool, None))
    monkeypatch.setattr(pig, "check_claims",
                        lambda nums, lane: {n: (pig.CLAIM_CODE_FREE, "libre")
                                            for n in nums})
    monkeypatch.setattr(pig, "latest_claim_stamp", lambda n: None)

    rc = pig.main(["--lane", LANE, "--belt", "--json"])

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["mode"] == "belt"
    picks = [p["number"] for p in payload["picks"]]
    rows = tirage_journal.read_journal(jp)
    assert len(rows) == 1, "une invocation = une entree, garde rouge ou non"
    assert rows[0].mode == "belt"
    assert rows[0].urn == "belt"
    assert rows[0].candidates == picks, (
        "les candidats journalises sont les picks servis, pas la file entiere"
    )
    assert rows[0].retained == picks[0]
    assert rows[0].retained == 7001, (
        "jamais servie et la plus ancienne : la tete du tapis doit etre 7001"
    )


def test_belt_with_red_guard_journals_once(monkeypatch, tmp_path):
    """Garde rouge + tapis : UNE entree belt, pas une repair + une belt.

    Une invocation = une entree : le rappel rouge est fusionne dans la
    sortie du tapis, sa consigne l'est aussi.
    """
    jp = _journal_path(tmp_path)
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(jp))
    _patch_common_network(monkeypatch)
    red = _state_red(0)
    created = (pig.NOW
               - pig.dt.timedelta(hours=30)).strftime("%Y-%m-%dT%H:%M:%SZ")
    prs = [{"number": 403, "title": "pr 403",
            "body": f"Grain: MED/guard -- lane {LANE}",
            "createdAt": created, "isDraft": False}]
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: prs)
    monkeypatch.setattr(pig, "fetch_pr_states",
                        lambda nums: {n: red for n in nums})
    pool = [_make_item(7011, "2025-01-01T00:00:00Z")]
    monkeypatch.setattr(pig, "fetch_pool", lambda **k: (pool, None))
    monkeypatch.setattr(pig, "check_claims",
                        lambda nums, lane: {n: (pig.CLAIM_CODE_FREE, "libre")
                                            for n in nums})
    monkeypatch.setattr(pig, "latest_claim_stamp", lambda n: None)

    rc = pig.main(["--lane", LANE, "--belt", "--json"])

    assert rc == 0
    rows = tirage_journal.read_journal(jp)
    assert len(rows) == 1, (
        f"une invocation belt avec garde rouge doit produire UNE entree, "
        f"got {[r.mode for r in rows]}"
    )
    assert rows[0].mode == "belt"


# ==================================================================
# Chemin PONDERE : la poignee servie et sa tete
# ==================================================================


def test_weighted_path_journals_picks(monkeypatch, tmp_path, capsys):
    jp = _journal_path(tmp_path)
    monkeypatch.setenv("TIRAGE_JOURNAL_PATH", str(jp))
    _patch_common_network(monkeypatch)
    pool = [_make_item(7101, "2025-01-01T00:00:00Z"),
            _make_item(7102, "2025-02-01T00:00:00Z")]
    monkeypatch.setattr(pig, "fetch_pool", lambda **k: (pool, None))
    # La machinerie de tirage elle-meme est couverte par les tests
    # existants ; ici on borne la poignee rendue pour verifier la
    # CONSIGNE, pas la ponderation.
    drawn = [
        {"number": 7101, "klass": "grain", "age": 200, "idle": 10,
         "genre": "docs", "weight": 1.0, "title": "issue #7101",
         "visits": 0},
        {"number": 7102, "klass": "grain", "age": 190, "idle": 10,
         "genre": "docs", "weight": 1.0, "title": "issue #7102",
         "visits": 0},
    ]
    monkeypatch.setattr(pig, "fetch_merged_grains", lambda: ([], None))
    monkeypatch.setattr(pig, "draw_unclaimed",
                        lambda *a, **k: (drawn, {}, []))
    monkeypatch.setattr(pig, "recent_delivery", lambda picks: {})

    rc = pig.main(["--lane", LANE, "--json"])

    assert rc == 0
    rows = tirage_journal.read_journal(jp)
    assert len(rows) == 1
    assert rows[0].mode == "weighted"
    assert rows[0].candidates == [7101, 7102]
    assert rows[0].retained == 7101
    assert rows[0].urn == "grain", (
        "l'urne journalisee est celle du grain retenu"
    )
    # La sortie machine reste du JSON pur : la confirmation journal va sur
    # stderr, jamais sur stdout.
    captured = capsys.readouterr()
    json.loads(captured.out)
    assert "journal de tirage" in captured.err
