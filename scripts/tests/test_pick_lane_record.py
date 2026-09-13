"""Tests de l'ardoise de lane du picker (L721).

Fondation (mesure du 2026-09-12) : la lane myia-po-2023:CoursIA-2 a envoye
une escalation URGENT claimant « x22 cycles, rien livre par ma lane, pool
tari structurellement » alors qu'elle avait cree 8 PRs DEEP de genre
CONTENU dans les 48 h precedentes (#15662, #15607, #15595, #15582, #15542,
#15540, #15537, #15519), la plus recente 10 h avant l'alerte, 337 issues
etant ouvertes. La regle L721 etait correcte, aucun organe ne la faisait
mordre : l'ardoise rend la mesure visible au moment ou la decision se
prend -- dans la sortie du picker, premier geste de chaque cycle.

Un detecteur se valide par ses faux negatifs ET ses sur-accusations. La
sur-accusation ici serait double : compter les PRs d'une AUTRE lane sous
l'identite de poussee partagee (le defaut structurel que L721 nomme), ou
transformer l'ardoise en garde -- elle est INFORMATIONNELLE, un gate sur
une ardoise vide reproduirait l'incident des « lanes 2 » (un garde qui
drainait les lanes actives). Les tests ci-dessous sont ordonnes par
gravite du degat si ils cassent.
"""

import datetime as dt
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402


LANE = "myia-po-2023:CoursIA-2"          # la lane de l'incident fondateur
OTHER_LANE = "myia-po-2026:CoursIA"      # une autre lane, meme poussee
NOW_FIXED = dt.datetime(2026, 9, 12, 12, 0, tzinfo=dt.timezone.utc)


def _merged_at(hours_ago: float) -> str:
    return (NOW_FIXED - dt.timedelta(hours=hours_ago)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")


def _pr(number, lane, tier, genre, hours_ago, *, author="jsboige",
        body=None):
    """PR mergee telle que fetch_lane_record_prs la rend (author present
    pour pinner qu'il n'est JAMAIS lu)."""
    return {"number": number,
            "body": body if body is not None
            else f"Grain: {tier}/{genre} -- lane {lane}\n",
            "mergedAt": _merged_at(hours_ago),
            "author": {"login": author}}


# Les 8 PRs de l'incident : 5 mergees dans les 24 h, 3 entre 24 et 48 h.
# Genres tous CONTENU, tiers tous DEEP -- le profil exact de la livraison
# que l'escalation claimait inexistante.
FOUNDING = [
    _pr(15662, LANE, "DEEP", "genai", 4),
    _pr(15607, LANE, "DEEP", "lean", 8),
    _pr(15595, LANE, "DEEP", "notebook-python", 13),
    _pr(15582, LANE, "DEEP", "qc", 18),
    _pr(15542, LANE, "DEEP", "training", 22),
    _pr(15540, LANE, "DEEP", "slides", 30),
    _pr(15537, LANE, "DEEP", "research-code", 38),
    _pr(15519, LANE, "DEEP", "notebook-lean", 45),
]
FOUNDING_NUMBERS = {15662, 15607, 15595, 15582, 15542, 15540, 15537, 15519}


# --- CONTROLE POSITIF : le replay exact de l'incident ----------------------

def test_founding_case_replay_renders_the_eight_content_prs():
    """Le replay du 2026-09-12 : la lane qui claimait « rien livre » avait
    8 DEEP CONTENU mergees en 48 h. L'ardoise doit rendre 5 CONTENU sur
    24 h et 8 sur 7 j, en NOMMANT les numeros -- un constat sans preuve
    nommee se discute, un constat qui cite #15662 se verifie."""
    rec = pig.lane_delivery_record(LANE, FOUNDING, now=NOW_FIXED)
    assert rec["measured"] is True
    w24, w7 = rec["windows"]["24h"], rec["windows"]["7d"]
    assert w24["contenu"] == 5 and w24["total"] == 5
    assert w24["by_tier"]["DEEP"] == 5
    assert w7["contenu"] == 8 and w7["total"] == 8
    assert w7["meta"] == 0
    assert {p["number"] for p in w7["prs"]} == FOUNDING_NUMBERS


def test_negative_control_no_content_renders_zero_contenu():
    """Controle NEGATIF du precedent : meme forme, genres tous META ->
    contenu == 0 et meta > 0. Sans ce temoin, un compteur « toujours
    non-zero » passerait le test fondateur en comptant n'importe quoi."""
    prs = [_pr(15662, LANE, "LIGHT", "guard", 4),
           _pr(15607, LANE, "MED", "tooling", 8),
           _pr(15595, LANE, "LIGHT", "docs", 13)]
    rec = pig.lane_delivery_record(LANE, prs, now=NOW_FIXED)
    w24, w7 = rec["windows"]["24h"], rec["windows"]["7d"]
    assert w24["contenu"] == 0 and w7["contenu"] == 0
    assert w24["meta"] == 3 and w7["meta"] == 3
    assert w24["by_tier"] == {"DEEP": 0, "MED": 1, "LIGHT": 2}


# --- ATTRIBUTION : le tag de lane, jamais l'identite de poussee -----------

def test_attribution_follows_the_lane_tag_never_the_push_identity():
    """L721, le coeur : toutes les PRs sont poussees sous le compte partage
    `jsboige` ; seules celles dont le TAG dit cette lane comptent. Compter
    par --author attribuerait a la lane les livraisons de toute la flotte
    -- ou l'inverse, et c'est l'inverse qui a produit le faux « rien
    livre » : la lane ne se reconnaissait pas dans `gh pr list --author`."""
    prs = [
        _pr(1, LANE, "DEEP", "lean", 5),
        _pr(2, OTHER_LANE, "DEEP", "lean", 5),      # autre lane, meme poussee
        _pr(3, "myia-po-2024:CoursIA-2", "MED", "genai", 5),
    ]
    rec = pig.lane_delivery_record(LANE, prs, now=NOW_FIXED)
    assert rec["windows"]["7d"]["total"] == 1
    assert [p["number"] for p in rec["windows"]["7d"]["prs"]] == [1]
    # Et la reciproque : la lane voisine voit ses PRs, pas les notres.
    other = pig.lane_delivery_record(OTHER_LANE, prs, now=NOW_FIXED)
    assert other["windows"]["7d"]["total"] == 1
    assert other["windows"]["7d"]["prs"][0]["number"] == 2


def test_untagged_pr_is_never_attributed():
    """Une PR sans tag lisible n'est comptee NULLE part -- deviner sa lane
    serait pire (meme arithmetique que red_backlog / unattributed_blocked).
    Le defaut a attraper : la compter partout « par defaut », ce qui
    fabriquerait des ardoises identiques pour toutes les lanes."""
    prs = [_pr(1, LANE, "DEEP", "lean", 5),
           _pr(2, None, "DEEP", "lean", 5, body="pas de tag\n")]
    rec = pig.lane_delivery_record(LANE, prs, now=NOW_FIXED)
    assert rec["windows"]["7d"]["total"] == 1
    other = pig.lane_delivery_record(OTHER_LANE, prs, now=NOW_FIXED)
    assert other["windows"]["7d"]["total"] == 0


def test_loose_tag_forms_are_parsed_like_the_guard():
    """Requirement de parite : l'ardoise herite de l'extracteur PARTAGE
    (grain_tag.parse_grain_tag, celui de variation-tag-guard.yml), pas
    d'un regex plus strict. Les formes documentees -- gras, titre `##
    Grain` + ligne suivante, casse inferieure -- doivent compter ; un
    lecteur plus strict sous-compterait des livraisons reelles et
    retiendrait le faux « rien livre » par la bande."""
    prs = [
        _pr(1, LANE, "DEEP", "lean", 5,
            body="**Grain** : DEEP/lean -- lane %s\n" % LANE),
        _pr(2, LANE, "DEEP", "lean", 5,
            body="## Grain\n\nDEEP/lean - lane %s\n" % LANE),
        _pr(3, LANE, "deep", "Lean", 5,
            body="grain: deep/Lean -- lane %s\n" % LANE),
    ]
    rec = pig.lane_delivery_record(LANE, prs, now=NOW_FIXED)
    assert rec["windows"]["24h"]["total"] == 3
    # L'extracteur normalise casse et tier : deep/Lean reste DEEP/lean.
    assert rec["windows"]["24h"]["by_tier"]["DEEP"] == 3


# --- FENETRES ET HONNETETE DES COMPTES ------------------------------------

def test_window_bucketing_30h_counts_in_7d_only():
    """Une merge a 30 h est dans la fenetre 7 j, pas dans la 24 h -- les
    deux fenetres repondent a deux questions differentes ( rythme du jour
    vs trajectoire de la semaine) et doivent rester distinguees."""
    rec = pig.lane_delivery_record(LANE, [_pr(1, LANE, "DEEP", "lean", 30)],
                                   now=NOW_FIXED)
    assert rec["windows"]["24h"]["total"] == 0
    assert rec["windows"]["7d"]["total"] == 1


def test_offlist_tier_and_genre_are_kept_not_silently_dropped():
    """Un tier hors enumeration garde sa propre cle et un genre non resolu
    compte hors_enumeration -- un compte qui somme a moins que le total
    sans le dire est un sous-compte, et un sous-compte ici dirait « moins
    de contenu » a une lane qui en a livre (fail-CLOSED mais NOMME, meme
    politique que substance_drought)."""
    rec = pig.lane_delivery_record(
        LANE, [_pr(1, LANE, "ULTRA", "diagnostic", 5)], now=NOW_FIXED)
    b = rec["windows"]["24h"]
    assert b["total"] == 1
    assert b["by_tier"].get("ULTRA") == 1
    assert b["by_tier"]["DEEP"] == 0 and b["by_tier"]["LIGHT"] == 0
    assert b["hors_enumeration"] == 1
    assert b["contenu"] == 0 and b["meta"] == 0


def test_alias_genres_canonicalize_to_contenu():
    """Un alias (translation -> docs, notebook-genai-python ->
    notebook-python) se canonicalise AVANT classification : compter les
    alias bruts classerait du CONTENU reel en META et gonflerait le
    diagnostic de secheresse d'une lane qui livre (mesure 2026-08-31 : la
    canonicalisation resout 8 des 11 genres hors-enumeration du corpus)."""
    prs = [_pr(1, LANE, "DEEP", "notebook-genai-python", 5),
           _pr(2, LANE, "MED", "translation", 5)]
    rec = pig.lane_delivery_record(LANE, prs, now=NOW_FIXED)
    b = rec["windows"]["24h"]
    assert b["contenu"] == 1 and b["meta"] == 1


# --- LECTURE RATEE : jamais un zero d'absence de mesure --------------------

def test_unreadable_record_announces_never_renders_zero(capsys):
    """Requirement fail-OPEN explicite : une ardoise illisible (gh down,
    403, reseau) doit se DIRE, pas rendre un zero -- un zero silencieux
    fabriquerait exactement le faux « rien livre » que l'organe existe
    pour refuter. Le print porte le rappel L721 et la commande manuelle."""
    rec = pig.lane_delivery_record(LANE, [], now=NOW_FIXED,
                                   error="CalledProcessError: gh exit 1")
    assert rec["measured"] is False
    assert rec["error"] == "CalledProcessError: gh exit 1"
    assert rec["windows"]["24h"]["total"] == 0  # mais NON MESURE le dit
    pig.print_lane_record(rec)
    out = capsys.readouterr().out
    assert "NON MESUREE" in out
    assert "ne serait pas une mesure" in out
    assert "gh pr list" in out  # la voie de verification manuelle


def test_fetch_failure_returns_named_error(monkeypatch):
    """Le fetch lui-meme : echec gh -> ([], erreur nommee), pas d'exception
    qui tuerait le tirage entier (l'ardoise ne doit jamais empecher de
    tirer -- parite avec le fail-open de red_backlog)."""
    def boom(cmd, **kwargs):
        raise pig.subprocess.TimeoutExpired(cmd, 60)
    monkeypatch.setattr(pig.subprocess, "run", boom)
    prs, err = pig.fetch_lane_record_prs()
    assert prs == []
    assert err and "TimeoutExpired" in err


def test_fetch_filters_dates_server_side(monkeypatch):
    """La requete DOIT porter --search merged:>= : gh pr list trie par date
    de CREATION, et la mesure fondatrice de fetch_visits (2026-08-23) est
    de 44 % de population perdue sur une fenetre de 24 h par un filtre
    cote client. Une ardoise amputee consentirait le faux constat d'idle
    au lieu de le refuter."""
    seen = {}

    class _R:
        stdout = "[]"
        returncode = 0

    def fake_run(cmd, **kwargs):
        seen["cmd"] = cmd
        return _R()

    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    prs, err = pig.fetch_lane_record_prs()
    assert err is None and prs == []
    cmd = seen["cmd"]
    assert any(a.startswith("merged:>=") for a in cmd), cmd
    assert "--state" in cmd and "merged" in cmd
    assert "--json" in cmd


# --- INFORMATIONNELLE : aucun gate, aucune mutation ------------------------

def test_record_is_informational_pure_and_ungated(capsys):
    """L'ardoise ne gate RIEN : pas de cle de verdict bloquant dans le
    record, pas de mutation du corpus (parite avec recent_delivery /
    test_candidate_stays_drawable), pas de mot de refus dans le print.
    Un gate sur une ardoise vide reproduirait l'incident « lanes 2 »."""
    prs = [dict(p) for p in FOUNDING]
    snapshot = [dict(p) for p in prs]
    rec = pig.lane_delivery_record(LANE, prs, now=NOW_FIXED)
    assert prs == snapshot
    assert set(rec) == {"lane", "measured", "error", "truncated",
                        "windows", "undated"}
    pig.print_lane_record(rec)
    out = capsys.readouterr().out
    assert "REFUS" not in out.upper()
    assert "Ardoise de la lane" in out


def test_zero_record_print_names_the_tag_hypothesis(capsys):
    """Un zero PEUT etre vrai ; le print doit alors orienter vers la cause
    la plus frequente d'un faux zero (des PRs sans tag lisible) plutot que
    de laisser le zero se lire comme une preuve d'idle."""
    rec = pig.lane_delivery_record(LANE, [], now=NOW_FIXED)
    pig.print_lane_record(rec)
    out = capsys.readouterr().out
    assert "0 merge" in out
    assert "sans tag lisible" in out


def test_truncated_corpus_surfaced_as_lower_bound(capsys):
    """Corpus tronque a la limite de fetch : les comptes restent rendus
    mais declares BORNES INFERIEURES -- convention POOL_FETCH_LIMIT, le
    plafond se fait franchir en silence par construction sinon."""
    rec = pig.lane_delivery_record(LANE, FOUNDING, now=NOW_FIXED,
                                   truncated=True)
    assert rec["truncated"] is True
    pig.print_lane_record(rec)
    out = capsys.readouterr().out
    assert "bornes INFERIEURES" in out


# --- INTEGRATION main() : l'ardoise atteint les deux chemins ---------------

def _red_state():
    """Etat GraphQL d'une PR rouge (check requis en echec), forme
    fetch_pr_states -- declencheur `aged` du garde reparer-son-rouge."""
    return {
        "number": 1, "mergeable": "MERGEABLE",
        "reviews": {"nodes": []},
        "commits": {"nodes": [{"commit": {"statusCheckRollup": {"contexts": {"nodes": [
            {"name": "PR gate", "conclusion": "FAILURE", "isRequired": True,
             "completedAt": "2026-09-12T00:00:00Z"}
        ]}}}}]},
    }


def _patch_repair(monkeypatch, record_prs):
    """main() sur le chemin REPARATION : garde rouge declenche (PR de la
    lane, 30 h, rouge requis), organes externes neutralises, ardoise
    injectee -- le payload exact du fetch de l'ardoise."""
    created = (pig.NOW - pig.dt.timedelta(hours=30)).strftime("%Y-%m-%dT%H:%M:%SZ")
    pr = {"number": 1, "title": "pr 1",
          "body": f"Grain: MED/guard -- lane {LANE}\n",
          "createdAt": created, "isDraft": False}
    monkeypatch.setattr(pig, "fetch_open_prs", lambda: [pr])
    monkeypatch.setattr(pig, "fetch_pr_states", lambda nums: {1: _red_state()})
    monkeypatch.setattr(pig, "unaddressed_review_points", lambda nums: {})
    monkeypatch.setattr(pig, "fetch_lane_record_prs",
                        lambda **k: (record_prs, None))


def test_main_repair_path_prints_the_record(monkeypatch, capsys):
    """Le chemin reparation porte AUSSI l'ardoise : une lane en cycles de
    reparation est precisement celle qui peut ecrire « rien livre » -- la
    mesure doit etre sous ses yeux sur TOUT chemin de sortie du picker,
    apres l'assignation (l'en-tete GRAIN DU CYCLE reste la premiere ligne)."""
    _patch_repair(monkeypatch, FOUNDING)
    rc = pig.main(["--lane", LANE])
    out = capsys.readouterr().out
    assert rc == 0
    assert out.splitlines()[0].startswith("GRAIN DU CYCLE")
    assert "Ardoise de la lane" in out
    assert "#15662" in out  # la PR de l'incident, nommee dans la sortie


def test_main_repair_json_carries_the_record(monkeypatch, capsys):
    """Les deux canaux disent la meme chose : sans cette cle, la sortie
    humaine pourrait porter l'ardoise pendant que --json la tait -- deux
    canaux, deux verites (parite avec test_repair_json_carries_a_grain_field)."""
    _patch_repair(monkeypatch, [])
    rc = pig.main(["--lane", LANE, "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0 and payload["mode"] == "repair"
    assert payload["lane_record"]["measured"] is True
    assert payload["lane_record"]["windows"]["7d"]["total"] == 0


def test_main_draw_json_carries_the_record(monkeypatch, capsys):
    """Chemin de TIRAGE : le payload --json porte l'ardoise. Le mock
    minimal coupe le garde rouge (aucune PR ouverte) et sert un pool vide
    -- le tirage rend 0 candidat mais rend TOUTE sa sortie, record inclus.
    NOW est fige a NOW_FIXED : les fenetres de l'ardoise se ferment sur
    l'horloge REELLE du module, la fixture est relative a NOW_FIXED."""
    monkeypatch.setattr(pig, "NOW", NOW_FIXED)
    monkeypatch.setattr(pig, "red_backlog",
                        lambda *a, **k: {"red": [], "triggers": []})
    monkeypatch.setattr(pig, "fetch_lane_record_prs",
                        lambda **k: (FOUNDING, None))

    class _R:
        stdout = "[]"
        returncode = 0

    monkeypatch.setattr(pig.subprocess, "run", lambda *a, **k: _R())
    rc = pig.main(["--lane", LANE, "--json", "--no-check-claims"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    assert payload["lane_record"]["windows"]["24h"]["contenu"] == 5
