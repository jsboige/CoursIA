"""Tests du tableau du tapis partage -- producteur / consommateur (#20053).

Acceptance (issue #20053, body) :
2. mode producteur : classement versionne, horodate UTC, < 10 Ko ;
3. mode consommateur : UN controle vivant du claim sur le candidat retenu,
   retour au calcul local au-dela de la periode de validite ;
4. tests hors ligne : instantane frais, perime, malforme, candidat claime
   entre-temps.

Le point 1 (profil du --belt chaud) est une mesure, pas un test : ses chiffres
vivent dans le corps de la PR.

Tout est hors ligne. `check_claims` est monkeypatche pour compter les appels --
c'est ce compteur qui porte l'acceptance « UN seul controle vivant » -- et le
chemin de consommation ne touche ni `subprocess.run` ni le pool.
"""

import json
import sys
import types
from datetime import datetime, timedelta, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


def _item(number, age_days=10, idle=2, klass="grain", genre="docs",
          last=None, title=None, labels=None, created_at=None):
    """Un item tel que le tapis le produit (cf test_pick_idle_grain_belt)."""
    return {
        "number": number,
        "klass": klass,
        "age": age_days,
        "idle": idle,
        "genre": genre,
        "labels": labels if labels is not None else [],
        "title": title if title is not None else f"issue #{number}",
        "created_at": created_at or "2026-09-01T00:00:00Z",
        "last_delivery_stamp": last,
    }


def _args(**over):
    base = {
        "exclude_issue": [], "require_label": [], "exclude_label": [],
        "min_age_days": None, "max_age_days": None,
        "min_idle_days": None, "max_idle_days": None,
        "urns": "grain,umbrella,delivered", "grains": 4,
        "lane": "myia-po-2026:CoursIA", "check_claims": True, "json": False,
    }
    base.update(over)
    return types.SimpleNamespace(**base)


def _snapshot(items, *, withheld=(), computed_at=None, lane="myia-po-2026:CoursIA"):
    return pig.build_board_snapshot(
        items, list(withheld), lane=lane,
        computed_at=computed_at or pig.board_utcnow(), head=len(items))


# --- Producteur : forme et transport -------------------------------------


def test_item_roundtrip_preserves_the_fields_the_belt_reads():
    """Le consommateur doit pouvoir rejouer `belt_filter` et `belt_sort_key`."""
    source = _item(42, age_days=7, idle=3, klass="umbrella", genre="lean",
                   last="2026-09-20T00:00:00Z", title="un titre",
                   labels=["a", "b"])
    compact = pig.board_item_encode(source)
    back = pig.board_item_decode(compact)
    for key in ("number", "klass", "age", "idle", "genre", "title",
                "created_at", "last_delivery_stamp"):
        assert back[key] == source[key], key
    assert sorted(back["labels"]) == ["a", "b"]


def test_item_encode_omits_empty_fields():
    """Un `labels` vide sur ~50 items coute cher pour rien."""
    compact = pig.board_item_encode(_item(7, idle=0))
    assert "l" not in compact      # labels vide omis
    assert "i" not in compact      # idle == 0 omis
    assert compact["n"] == 7       # le numero, jamais omis


def test_snapshot_is_versioned_and_utc_stamped():
    snap = _snapshot([_item(1)])
    assert snap["schema"] == pig.BOARD_SCHEMA
    assert snap["computed_at"].endswith("Z")
    parsed = datetime.fromisoformat(snap["computed_at"].replace("Z", "+00:00"))
    assert parsed.tzinfo is not None, "un horodatage naif serait relu en heure locale"


def test_snapshot_head_is_bounded():
    pool = [_item(n) for n in range(1, 101)]
    snap = pig.build_board_snapshot(pool, [], lane="l", computed_at="2026-10-09T00:00:00Z",
                                    head=50)
    assert len(snap["items"]) == 50
    assert snap["pool_size"] == 100
    assert snap["head_size"] == 50


def test_withheld_causes_are_reduced_to_codes():
    """Les causes du tapis sont des phrases ; on transporte un code."""
    phrase = ("LIVRAISON : SIGNAL LIVRAISON (commentaire `[INFO] "
              "candidate-delivered`) : une lane a deja rendu la main sur cette "
              "issue en la refutant. La re-servir comme grain de production "
              "fait bruler un cycle.")
    snap = _snapshot([_item(1)], withheld=[(_item(2), phrase)])
    assert snap["withheld"] == [{"n": 2, "c": "LIVRAISON"}]


def test_snapshot_stays_under_the_transport_budget():
    """Acceptance 2 : < 10 Ko pour une tete pleine, sans perdre d'item."""
    pool = [_item(n, title="t" * 200) for n in range(1, 101)]
    snap = pig.build_board_snapshot(pool, [], lane="l",
                                    computed_at="2026-10-09T00:00:00Z", head=50)
    text, written, policy = pig.encode_board_snapshot(snap)
    assert len(text.encode("utf-8")) <= pig.BOARD_MAX_BYTES
    assert policy in ("full", "short", "none")
    assert len(written["items"]) == 50, "le plafond ne se tient pas en vidant la tete"


def test_budget_is_held_by_degrading_titles_not_by_dropping_items():
    """Un plafond tenu en vidant la tete serait un classement qui ment.

    Budget volontairement serre pour forcer la degradation : c'est la seule
    facon de rendre le test deterministe, la tete reelle tenant sous 10 Ko.
    """
    pool = [_item(n, title="t" * 200) for n in range(1, 61)]
    snap = pig.build_board_snapshot(pool, [], lane="l",
                                    computed_at="2026-10-09T00:00:00Z", head=50)
    _text, written, policy = pig.encode_board_snapshot(snap, max_bytes=2000)
    assert len(written["items"]) == 50, "aucun item ne doit disparaitre"
    assert policy == "none", "un budget serre doit retirer les titres"
    assert all("t" not in row for row in written["items"])


def test_writer_emits_utf8_without_bom(tmp_path):
    """Un BOM casserait tout lecteur JSON non-Windows."""
    snap = _snapshot([_item(1, title="accents : ete, cle, controle")])
    target = tmp_path / "belt-board.json"
    written = pig.write_board_snapshot(str(target), snap)
    raw = target.read_bytes()
    assert not raw.startswith(b"\xef\xbb\xbf")
    assert "ete" in raw.decode("utf-8")
    assert written["bytes"] == len(raw)
    assert written["within_budget"] is True


# --- La tete publiee doit etre servable ----------------------------------


def test_board_head_withholds_verdicts_the_consumer_would_refuse(monkeypatch):
    """Une tete IMPLICIT defaisait le chemin rapide : elle doit etre ecartee.

    Mesure du 2026-10-09 : le tapis ne met dans `belt_withheld` que les BLOCKED
    explicites, un candidat IMPLICIT passe donc dans la tete publiee. Le
    consommateur, lui, tient IMPLICIT pour non consommable et fait UN SEUL
    controle vivant, sur cette tete : il la tenait, et retombait sur le calcul
    local. Le chemin rapide ne servait donc JAMAIS, et son repli coute le calcul
    complet. Cas reel mesure le 2026-10-09 : tete `#10355` (EPIC detection de
    sophismes), tenue par la PR ouverte `#20036` de la lane `myia-po-2023:CoursIA`
    (verdict `IMPLICIT`, `blocking_lanes` vide).
    """
    _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    items = [_item(11), _item(12), _item(13)]
    claims = {
        11: (pig.CLAIM_CODE_IMPLICIT, "PR ouverte d'une autre lane : #999"),
        12: (pig.CLAIM_CODE_FREE, "libre"),
    }
    extended = pig.board_withheld_from_claims(items, [], claims, depth=3)
    assert [it["number"] for it, _ in extended] == [11]

    snap = _snapshot(items, withheld=extended)
    picks, meta = pig.consume_board(snap, _args(), urns={"grain"})
    assert meta["retained"] == 12, "la tete tenue doit etre ecartee, pas servie"
    # Le premier retenu est servi, les suivants viennent de l'instantane ; ce qui
    # compte ici est que le candidat ECARTE (11) ne soit pas dans la tete servie.
    assert [it["number"] for it in picks] == [12, 13]


def test_board_withholding_leaves_consumable_verdicts_alone():
    """Un verdict que le consommateur ACCEPTE ne doit pas etre ecarte."""
    items = [_item(11), _item(12)]
    claims = {
        11: (pig.CLAIM_CODE_FREE, "libre"),
        12: (pig.CLAIM_CODE_OWNED_BY_ME, "deja claim par cette lane"),
    }
    assert pig.board_withheld_from_claims(items, [], claims, depth=2) == []


def test_board_withholding_does_not_duplicate_the_belts_own_skips():
    """Le tapis a deja ecarte ce candidat : ne pas le compter deux fois."""
    items = [_item(11)]
    claims = {11: (pig.CLAIM_CODE_BLOCKED, "BLOQUE par une autre lane")}
    existing = [(items[0], "BLOQUE par une autre lane")]
    extended = pig.board_withheld_from_claims(items, existing, claims, depth=1)
    assert len(extended) == 1


def test_board_withholding_leaves_an_unprobed_item_alone():
    """Sans verdict du tapis, on n'invente pas d'ecarte."""
    items = [_item(n) for n in (11, 12, 13)]
    claims = {13: (pig.CLAIM_CODE_ERROR, "sonde en echec")}
    assert pig.board_withheld_from_claims(items, [], claims, depth=2) == []


def test_board_withholding_reaches_the_rank_the_consumer_retains(monkeypatch):
    """Le defaut mesure : le candidat retenu etait au RANG 16 de la tete.

    29 ecartes sur 50 publies, donc le premier candidat non ecarte tombe loin.
    Une extension bornee a la fenetre de sonde (8) ne le voyait pas : le
    consommateur le tenait, et retombait sur le calcul local -- mesure du
    2026-10-09, deux passes, deux replis de 330 s. La profondeur doit donc etre
    celle de la tete PUBLIEE.
    """
    _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    items = [_item(n) for n in range(100, 150)]
    claims = {116: (pig.CLAIM_CODE_IMPLICIT, "PR ouverte d'une autre lane : #999")}
    extended = pig.board_withheld_from_claims(items, [], claims, depth=50)
    assert [it["number"] for it, _ in extended] == [116]
    # Controle negatif : la meme extension bornee a la fenetre de sonde rate le rang.
    assert pig.board_withheld_from_claims(items, [], claims, depth=8) == []


# --- Lecteur : validation stricte ----------------------------------------


def _write(tmp_path, payload):
    target = tmp_path / "board.json"
    target.write_text(payload, encoding="utf-8")
    return str(target)


def test_read_rejects_malformed_json(tmp_path):
    import pytest
    with pytest.raises(pig.BoardSnapshotError):
        pig.read_board_snapshot(_write(tmp_path, "{ ceci n'est pas du json"))


def test_read_rejects_unknown_schema(tmp_path):
    import pytest
    payload = json.dumps({"schema": "belt-board/v2", "computed_at": "2026-10-09T00:00:00Z",
                          "items": []})
    with pytest.raises(pig.BoardSnapshotError, match="schema inconnu"):
        pig.read_board_snapshot(_write(tmp_path, payload))


def test_read_rejects_missing_stamp(tmp_path):
    import pytest
    payload = json.dumps({"schema": pig.BOARD_SCHEMA, "items": []})
    with pytest.raises(pig.BoardSnapshotError, match="computed_at"):
        pig.read_board_snapshot(_write(tmp_path, payload))


def test_read_rejects_item_without_number(tmp_path):
    import pytest
    payload = json.dumps({"schema": pig.BOARD_SCHEMA,
                          "computed_at": "2026-10-09T00:00:00Z",
                          "items": [{"t": "sans numero"}]})
    with pytest.raises(pig.BoardSnapshotError, match="numero"):
        pig.read_board_snapshot(_write(tmp_path, payload))


def test_read_rejects_non_object_root(tmp_path):
    import pytest
    with pytest.raises(pig.BoardSnapshotError):
        pig.read_board_snapshot(_write(tmp_path, "[1, 2, 3]"))


def test_read_accepts_a_fresh_snapshot(tmp_path):
    snap = _snapshot([_item(1)])
    text, written, _policy = pig.encode_board_snapshot(snap)
    target = tmp_path / "board.json"
    target.write_text(text, encoding="utf-8")
    back = pig.read_board_snapshot(str(target))
    assert back["schema"] == pig.BOARD_SCHEMA
    assert len(back["items"]) == len(written["items"])


def test_read_reports_a_missing_file():
    import pytest
    with pytest.raises(pig.BoardSnapshotError, match="illisible"):
        pig.read_board_snapshot("Z:/aucun/dossier/board.json")


# --- Fraicheur -----------------------------------------------------------


def test_fresh_and_stale_are_decided_by_the_configured_window():
    now = datetime(2026, 10, 9, 12, 0, 0, tzinfo=timezone.utc)
    fresh = {"computed_at": "2026-10-09T11:30:00Z"}
    stale = {"computed_at": "2026-10-09T10:00:00Z"}
    assert pig.board_is_fresh(fresh, 60, now=now) is True
    assert pig.board_is_fresh(stale, 60, now=now) is False
    assert pig.board_age_minutes(stale, now=now) == 120.0


def test_naive_timestamp_is_read_as_utc():
    """Le producteur emet un `Z` ; un `Z` retire ne doit pas valoir 2 h d'ecart."""
    aware = {"computed_at": "2026-10-09T10:00:00Z"}
    naive = {"computed_at": "2026-10-09T10:00:00"}
    at = datetime(2026, 10, 9, 12, 0, 0, tzinfo=timezone.utc)
    assert pig.board_age_minutes(aware, now=at) == pig.board_age_minutes(naive, now=at)


def test_unparsable_timestamp_raises():
    import pytest
    with pytest.raises(pig.BoardSnapshotError, match="computed_at illisible"):
        pig.board_age_minutes({"computed_at": "hier soir"})


def test_expiry_boundary_is_inclusive():
    """A l'age exact de la fenetre, l'instantane est encore utilisable."""
    at = datetime(2026, 10, 9, 12, 0, 0, tzinfo=timezone.utc)
    edge = {"computed_at": (at - timedelta(minutes=60)).strftime("%Y-%m-%dT%H:%M:%SZ")}
    assert pig.board_is_fresh(edge, 60, now=at) is True


# --- Consommateur : UN seul controle vivant ------------------------------


def _counting_claims(monkeypatch, verdict):
    """Remplace `check_claims` et rend la liste des appels (nombres demandes)."""
    calls = []

    def fake(numbers, lane):
        calls.append((list(numbers), lane))
        return {n: verdict for n in numbers}

    monkeypatch.setattr(pig, "check_claims", fake)
    return calls


def test_consumer_checks_exactly_one_claim(monkeypatch):
    """Acceptance 3 : UN seul controle vivant, sur le seul candidat retenu."""
    calls = _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    snap = _snapshot([_item(11), _item(12), _item(13), _item(14)])
    picks, meta = pig.consume_board(snap, _args(), urns={"grain"})
    assert len(calls) == 1, "un seul appel gh est le contrat du chemin"
    assert calls[0][0] == [11], "et il porte sur le candidat retenu"
    assert calls[0][1] == "myia-po-2026:CoursIA"
    assert meta["live_check"]["code"] == pig.CLAIM_CODE_FREE
    assert picks, "un candidat libre est servi"
    assert picks[0]["number"] == 11


def test_consumer_preserves_the_belt_order(monkeypatch):
    """La tete du consommateur est celle du tapis, au meme tri pres.

    Une issue jamais servie est classee par sa CREATION (`belt_sort_key`), pas
    mise d'office en tete : c'est la regle du tapis. Le consommateur doit la
    rendre identique -- deux lanes qui liraient deux tetes differentes se
    departageraient sur un ordre, pas sur le claim.
    """
    _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    recent = _item(21, last="2026-10-01T00:00:00Z")
    ancient = _item(22, last="2026-08-01T00:00:00Z")
    never = _item(23, last=None, created_at="2026-06-01T00:00:00Z")
    expected = [it["number"] for it in
                sorted([recent, ancient, never], key=pig.belt_sort_key)]
    snap = _snapshot([recent, ancient, never])
    picks, _meta = pig.consume_board(snap, _args(), urns={"grain"})
    assert [it["number"] for it in picks] == expected == [23, 22, 21]


def test_consumer_falls_back_when_the_retained_candidate_is_held(monkeypatch):
    """Candidat claime entre-temps : picks vide, le caller calcule en local."""
    calls = _counting_claims(
        monkeypatch, (pig.CLAIM_CODE_BLOCKED, "BLOQUE par myia-po-2024:CoursIA-2"))
    snap = _snapshot([_item(11), _item(12)])
    picks, meta = pig.consume_board(snap, _args(), urns={"grain"})
    assert picks == []
    assert len(calls) == 1
    assert "tenu" in meta["reason"] and pig.CLAIM_CODE_BLOCKED in meta["reason"]


def test_consumer_accepts_its_own_claim(monkeypatch):
    """Un claim pose par MA lane est celui que je viens travailler."""
    _counting_claims(monkeypatch, (pig.CLAIM_CODE_OWNED_BY_ME, "deja claim par cette lane"))
    snap = _snapshot([_item(11)])
    picks, _meta = pig.consume_board(snap, _args(), urns={"grain"})
    assert [it["number"] for it in picks] == [11]


def test_consumer_skips_candidates_the_producer_withheld(monkeypatch):
    """Sans `withheld`, le consommateur re-servirait ce que le tapis a ecarte."""
    calls = _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    snap = _snapshot([_item(11), _item(12)],
                     withheld=[(_item(11), "BLOQUE par une autre lane")])
    picks, meta = pig.consume_board(snap, _args(), urns={"grain"})
    assert calls[0][0] == [12], "le candidat ecarte ne doit pas etre re-propose"
    assert meta["withheld_skipped"] == 1
    assert picks[0]["number"] == 12


def test_consumer_does_no_live_check_when_disabled(monkeypatch):
    calls = _counting_claims(monkeypatch, (pig.CLAIM_CODE_BLOCKED, "bloque"))
    snap = _snapshot([_item(11)])
    picks, meta = pig.consume_board(snap, _args(check_claims=False), urns={"grain"},
                                    live_check=False)
    assert calls == []
    assert [it["number"] for it in picks] == [11]
    assert "--no-check-claims" in meta["reason"]


def test_consumer_applies_the_lane_filters(monkeypatch):
    """Le filtre de lane reste applique : c'est le seul ecart entre lanes."""
    _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    snap = _snapshot([_item(11), _item(12, klass="umbrella")])
    picks, _meta = pig.consume_board(snap, _args(), urns={"umbrella"})
    assert [it["number"] for it in picks] == [12]


def test_consumer_reports_an_empty_snapshot_without_calling_gh(monkeypatch):
    calls = _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    snap = _snapshot([_item(11, klass="umbrella")])
    picks, meta = pig.consume_board(snap, _args(), urns={"grain"})
    assert picks == []
    assert calls == [], "rien a verifier : aucun appel ne doit partir"
    assert "vide" in meta["reason"]


# --- Cablage CLI ---------------------------------------------------------


def _stub_head_of_main(monkeypatch):
    """Neutralise tout ce qui, dans `main`, touche le reseau ou le cache."""
    monkeypatch.setattr(pig.gh_identity, "pin_gh_token", lambda: None)

    def boom(*a, **kw):
        raise AssertionError("le chemin consommateur ne doit pas atteindre le pool")

    for name in ("fetch_pool", "fetch_visits", "red_backlog",
                 "fetch_lane_record_prs"):
        if hasattr(pig, name):
            monkeypatch.setattr(pig, name, boom)


def test_consumer_cli_never_fetches_the_pool(monkeypatch, tmp_path, capsys):
    """Le seul interet du chemin : pas de sondes de pool du tout."""
    _stub_head_of_main(monkeypatch)
    _counting_claims(monkeypatch, (pig.CLAIM_CODE_FREE, "libre"))
    snap = _snapshot([_item(11), _item(12)])
    text, _written, _policy = pig.encode_board_snapshot(snap)
    board = tmp_path / "board.json"
    board.write_text(text, encoding="utf-8")

    rc = pig.main(["--belt", "--board-export", str(board),
                   "--lane", "myia-po-2026:CoursIA"])
    assert rc == 0
    out = capsys.readouterr().out
    assert "#20053" in out
    assert "garde rouge NON evalue" in out
    assert "#11" in out


class _LeftTheFastPath(Exception):
    """Sentinelle : le calcul local a repris la main."""


def test_consumer_cli_falls_back_on_a_stale_snapshot(monkeypatch, tmp_path, capsys):
    """Acceptance 3 : au-dela de la validite, on recalcule -- et on republie.

    La sentinelle est levee par le garde rouge, premier calcul de pool rencontre
    apres le court-circuit : la lever prouve qu'on a bien quitte le chemin
    rapide, sans laisser filer une seule requete reseau. La fenetre de 1 min
    rend l'instantane perime sans dependre de l'horloge (l'age ne fait que
    croitre).
    """
    import pytest

    monkeypatch.setattr(pig.gh_identity, "pin_gh_token", lambda: None)
    monkeypatch.setattr(pig, "fetch_lane_record_prs", lambda **kw: ([], None))

    def left_the_fast_path(*a, **kw):
        raise _LeftTheFastPath

    monkeypatch.setattr(pig, "red_backlog", left_the_fast_path)
    stale = _snapshot([_item(11)], computed_at="2026-10-09T00:00:00Z")
    text, _written, _policy = pig.encode_board_snapshot(stale)
    board = tmp_path / "board.json"
    board.write_text(text, encoding="utf-8")

    with pytest.raises(_LeftTheFastPath):
        pig.main(["--belt", "--board-export", str(board), "--board-max-age", "1",
                  "--lane", "myia-po-2026:CoursIA"])
    assert "perime" in capsys.readouterr().err


def test_board_export_requires_belt(tmp_path):
    """Sans --belt, le repli tomberait dans le tirage pondere : un autre resultat."""
    import pytest
    board = tmp_path / "board.json"
    board.write_text("{}", encoding="utf-8")
    with pytest.raises(SystemExit):
        pig.main(["--board-export", str(board), "--lane", "myia-po-2026:CoursIA"])


def test_board_write_requires_belt(tmp_path):
    import pytest
    with pytest.raises(SystemExit):
        pig.main(["--board-write", str(tmp_path / "b.json"),
                  "--lane", "myia-po-2026:CoursIA"])


def test_publish_call_names_the_dedicated_dashboard():
    call = pig.board_publish_call()
    assert pig.BOARD_WORKSPACE in call
    assert 'section:"status"' in call
    assert "roosync_dashboard" in call
