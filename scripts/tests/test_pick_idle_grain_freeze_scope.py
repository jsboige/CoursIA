"""Le GEL est transversal : toutes les classes, pas seulement l'urne grain.

Contexte (#19309) : le gel est une decision explicite du coordinateur.
Deux regles le portent -- regle A (ligne `[FROZEN] ...` dans le CORPS de
l'issue) et regle B (en-tete `[FROZEN]` dans le FIL). `_issue_is_frozen`
les lisait deja, mais elle n'etait cablee que DERRIERE
`has_recent_delivery_marker`, lui-meme cable sur l'urne `grain` SEULE.

Mesure du 2026-11-05 (#19309) : l'EPIC etait gelee par le body ET par le
fil, et le tapis l'a servie 7 fois dans la journee -- 7 `[RELEASED]` sans
travail. Le gel est donc became une sonde A PART ENTIERE : distincte de la
sonde de livraison (elle ne lit QUE le gel -- un parapluie n'herite pas de
la livraison de ses enfants) et valable pour TOUTES les classes.

Les temoins ci-dessous sont les deux formes de gel (body, fil) sur une
EPIC, plus les garde-fous : controle negatif, lecture en echec, et
`--include-delivered` qui ne contourne pas le gel.

Convention du dossier : `main()` n'est appele qu'a pool vide ; les tests
portent sur les boucles extrait (`belt_pick_with_replacements`,
`draw_unclaimed`), comme les autres tests du picker.
"""

import random
import re
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402


class _RealGhReached(BaseException):
    """Un test a atteint un `gh` reel.

    Derive de `BaseException` : le picker attrape large sur ses chemins de
    fetch, un garde derive d'`Exception` serait avale par ces `except` --
    exactement le silence qu'il doit casser.
    """


@pytest.fixture(autouse=True)
def _no_real_gh(monkeypatch, request):
    """Aucun test de ce fichier n'emet un appel `gh` (doctrine #19913)."""
    if request.node.get_closest_marker("real_gh"):
        return
    real_run = pig.subprocess.run

    def guarded_run(argv, *args, **kwargs):
        cmd = argv if isinstance(argv, (list, tuple)) else [argv]
        joined = " ".join(str(part) for part in cmd)
        if re.search(r"(^|[\\/ ])gh(\.exe)?($|\s)", joined):
            raise _RealGhReached("appel gh reel depuis un test : " + joined[:160])
        return real_run(argv, *args, **kwargs)

    monkeypatch.setattr(pig.subprocess, "run", guarded_run)


@pytest.fixture(autouse=True)
def _pool_vide(monkeypatch):
    """Le cache des corps est vide entre deux tests."""
    monkeypatch.setattr(pig, "_POOL_BODIES", {})


def _make_item(number, age_days=100, idle=10, klass="grain", last=None,
               genre="docs"):
    return {
        "number": number,
        "klass": klass,
        "age": age_days,
        "idle": idle,
        "genre": genre,
        "labels": [],
        "title": f"issue #{number}",
        "created_at": "2026-01-01T00:00:00Z",
        "last_delivery_stamp": last,
    }


def _belt_args(grains=2, include_delivered=False):
    import types
    return types.SimpleNamespace(
        grains=grains, include_delivered=include_delivered,
        lane="myia-ai-01:CoursIA-2")


def _free_claims(items):
    return {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in items}


def _install_issues(monkeypatch, issues):
    """Stubbe la lecture de PLUSIEURS issues : corps + fil, sans reseau.

    Le corps passe par le cache du pool (`_POOL_BODIES`) -- c'est le chemin
    que le pool paie deja -- et le fil par `_issue_comments`, qui est ensuite
    lu par `_issue_is_frozen`. Une issue absente du registre se lit comme une
    LECTURE RATEE (`(None, None)`) : c'est le fail-OPEN de la sonde.
    """
    registry = {}
    for number, spec in issues.items():
        body = spec.get("body", "")
        comments = spec.get("comments") or []
        registry[int(number)] = (body, comments)
        pig._POOL_BODIES[int(number)] = body

    def _fake_comments(issue_number):
        found = registry.get(int(issue_number))
        if found is None:
            return None, None
        body, comments = found
        return list(comments), body

    monkeypatch.setattr(pig, "_issue_comments", _fake_comments)


# --------------------------------------------------------------------------
# La sonde de gel elle-meme : source du gel, et echec distingue.
# --------------------------------------------------------------------------


def test_has_frozen_marker_dit_la_source_du_gel(monkeypatch):
    """Regle A (body) et regle B (fil) : la source est nommee, pas devinee."""
    _install_issues(monkeypatch, {
        19309: {"body": "[FROZEN] EPIC gelee sous le veto user "
                       "-- coordinateur, 2026-11-05"},
        19310: {"body": "EPIC de suivi",
                "comments": [{"body": "[FROZEN] gel pose en fil "
                                      "-- coordinateur"}]},
    })
    assert pig.has_frozen_marker(19309) == "body"
    assert pig.has_frozen_marker(19310) == "comment"


def test_has_frozen_marker_ne_gele_pas(monkeypatch):
    """Controle negatif : ni le corps ni le fil ne portent de gel."""
    _install_issues(monkeypatch, {
        19311: {"body": "EPIC de suivi",
                "comments": [{"body": "[RELEASED] lane x -- fin de cycle"}]},
    })
    assert pig.has_frozen_marker(19311) is False


def test_has_frozen_marker_lecture_echouee_rend_none(monkeypatch):
    """Lecture ratee -> None (fail-OPEN signale), pas False."""
    monkeypatch.setattr(pig, "_issue_comments", lambda n: (None, None))
    assert pig.has_frozen_marker(19312) is None


def test_has_frozen_marker_ne_lit_pas_les_marqueurs_de_livraison(monkeypatch):
    """Separation des deux notions : une livraison n'est PAS un gel.

    Un item livre (marqueur `[DELIVERED]`) n'est pas gele : la sonde de gel
    ne doit pas confondre les deux, sinon un parapluie heriterait de la
    livraison de ses enfants.
    """
    _install_issues(monkeypatch, {
        19313: {"body": "EPIC de suivi",
                "comments": [{"body": "[DELIVERED] lane x -- PR #1"}]},
    })
    assert pig.has_frozen_marker(19313) is False


# --------------------------------------------------------------------------
# Temoin 1 : l'EPIC gelee par le BODY est ecartee du tapis.
# --------------------------------------------------------------------------


def test_belt_epic_gelee_par_le_body_est_ecartee(monkeypatch):
    """TEMOIN 1 -- regle A : une EPIC gelee par son corps n'est pas servie.

    C'est le cas fondateur de #19309 : l'EPIC etait gelee depuis le
    2026-11-05 17:38Z (ligne `[FROZEN]` dans le corps) et le tapis l'a
    servie 7 fois dans la journee, parce que la sonde de gel n'etait cablee
    que sur l'urne `grain`.
    """
    epic = _make_item(19309, klass="umbrella")
    clean = _make_item(19320, klass="umbrella")
    _install_issues(monkeypatch, {
        19309: {"body": "[FROZEN] EPIC gelee sous le veto user "
                       "« carnets neufs » -- coordinateur "
                       "myia-ai-01:CoursIA, 2026-11-05"},
        19320: {"body": "EPIC libre"},
    })

    pool = [epic, clean]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=2), probe_budget=8,
        frozen_probe=pig.has_frozen_marker)

    assert [p["number"] for p in picks] == [19320], (
        "une EPIC gelee par son corps ne doit pas etre servie")
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[19309].startswith("GEL (body)"), causes[19309]
    assert state["frozen_filtered"] == 1


# --------------------------------------------------------------------------
# Temoin 2 : l'EPIC gelee par le FIL est ecartee du tapis.
# --------------------------------------------------------------------------


def test_belt_epic_gelee_par_le_fil_est_ecartee(monkeypatch):
    """TEMOIN 2 -- regle B : le gel pose en fil ecarte aussi l'EPIC.

    Le gel de #19309 existe dans les DEUX formes ; une EPIC peut aussi
    n'etre gelee que par le fil (le filet des gels deja poses en
    commentaire, en attendant leur migration vers le body).
    """
    epic = _make_item(19309, klass="umbrella")
    clean = _make_item(19320, klass="umbrella")
    _install_issues(monkeypatch, {
        19309: {"body": "EPIC de suivi",
                "comments": [
                    {"body": "[FROZEN] gel pose en fil "
                             "-- coordinateur, 2026-11-05"},
                    {"body": "[RELEASED] lane autre -- fin de cycle"},
                ]},
        19320: {"body": "EPIC libre"},
    })

    pool = [epic, clean]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=2), probe_budget=8,
        frozen_probe=pig.has_frozen_marker)

    assert [p["number"] for p in picks] == [19320]
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[19309].startswith("GEL (comment)"), causes[19309]
    assert state["frozen_filtered"] == 1


# --------------------------------------------------------------------------
# Garde-fous.
# --------------------------------------------------------------------------


def test_belt_epic_non_gelee_est_servie(monkeypatch):
    """Controle negatif : la porte de gel n'ecarte pas tout."""
    epic = _make_item(19320, klass="umbrella")
    _install_issues(monkeypatch, {
        19320: {"body": "EPIC libre",
                "comments": [{"body": "[RELEASED] lane x -- fin de cycle"}]},
    })
    pool = [epic]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=1), probe_budget=8,
        frozen_probe=pig.has_frozen_marker)
    assert [p["number"] for p in picks] == [19320]
    assert state["frozen_filtered"] == 0


def test_belt_gel_s_applique_a_toutes_les_classes(monkeypatch):
    """Le gel est transversal : grain, umbrella ET delivered.

    L'urne `delivered` sert precisement les issues livrees aux lanes
    habilitees (#15069) ; un gel reste un gel.
    """
    grain = _make_item(101, klass="grain")
    delivered = _make_item(102, klass="delivered")
    clean = _make_item(103, klass="grain")
    _install_issues(monkeypatch, {
        101: {"body": "[FROZEN] gele par le coordinateur -- 2026-11-05"},
        102: {"body": "[FROZEN] gele par le coordinateur -- 2026-11-05"},
        103: {"body": "grain libre"},
    })

    pool = [grain, delivered, clean]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=3), probe_budget=8,
        frozen_probe=pig.has_frozen_marker)

    assert [p["number"] for p in picks] == [103]
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert causes[101].startswith("GEL (body)")
    assert causes[102].startswith("GEL (body)")
    assert state["frozen_filtered"] == 2


def test_belt_include_delivered_ne_contourne_pas_le_gel(monkeypatch):
    """`--include-delivered` ne desarme pas le gel.

    L'echappatoire de `--include-delivered` porte sur les MARQUEURS DE
    LIVRAISON ; le gel est une decision du coordinateur, pas un fait de
    livraison.
    """
    epic = _make_item(19309, klass="umbrella")
    _install_issues(monkeypatch, {
        19309: {"body": "[FROZEN] gelee par le coordinateur -- 2026-11-05"},
    })
    pool = [epic]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=1, include_delivered=True),
        probe_budget=8, frozen_probe=pig.has_frozen_marker)
    assert picks == []
    assert withheld[0][1].startswith("GEL (body)")
    assert state["frozen_filtered"] == 1


def test_belt_lecture_de_gel_echouee_fail_open_et_signalee(monkeypatch):
    """Lecture ratee -> fail-OPEN, mais DIT (`frozen_unread`).

    Meme doctrine que `claim_unread` / `marker_unread` : le silence n'est
    pas un fail-OPEN, c'est un trou.
    """
    epic = _make_item(19320, klass="umbrella")
    pool = [epic]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=1), probe_budget=8,
        frozen_probe=lambda n: None)
    assert [p["number"] for p in picks] == [19320], (
        "une lecture de gel ratee ne doit pas ecarter le candidat")
    assert state["frozen_unread"] == [19320]
    assert state["frozen_filtered"] == 0


def test_belt_sans_sonde_injectee_ne_measure_rien(monkeypatch):
    """Le defaut inerte ne fait rien de plus que la sonde de gel.

    Sans sonde injectee, la porte de gel est NEUTRE (le defaut inerte rend
    `False`) : la boucle ne lit rien de plus, et ne signale aucune lecture
    ratee. Un test qui n'injecte pas de sonde ne sort jamais sur le reseau.
    """
    epic = _make_item(19320, klass="umbrella")
    pool = [epic]
    picks, withheld, state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=1), probe_budget=8)
    assert [p["number"] for p in picks] == [19320]
    assert state["frozen_unread"] == []
    assert state["frozen_filtered"] == 0


# --------------------------------------------------------------------------
# La voie PONDEREE : meme porte, meme grammaire.
# --------------------------------------------------------------------------


def test_draw_unclaimed_epic_gelee_est_ecartee(monkeypatch):
    """La voie ponderee applique la meme porte de gel.

    Sans cela, le tapis ecarterait l'EPIC mais le tirage pondere la
    resservirait -- deux urnes, une seule regle.
    """
    class _A:
        grains = 0
        umbrellas = 1
        delivered = 0
        prev_genre = None
        lane = "myia-ai-01:CoursIA-2"
        check_claims = False

    candidate = {"number": 19309, "title": "EPIC gelee",
                 "age": 30, "idle": 1, "idle_since_delivery": 1,
                 "genre": "guard"}
    by_class = {"grain": [], "umbrella": [candidate], "delivered": []}
    state = {"failures": [], "budget_hit": False, "recent_filtered": 0}

    picks, claims, conflicts = pig.draw_unclaimed(
        by_class, _A(), random.Random(42), {}, {}, {},
        delivered_state=state, frozen_probe=lambda n: "body")

    assert picks == []
    assert len(conflicts) == 1
    assert conflicts[0][1].startswith("GEL (body)"), conflicts[0][1]
    assert state["frozen_filtered"] == 1


def test_draw_unclaimed_lecture_de_gel_echouee_fail_open(monkeypatch):
    """Lecture ratee sur la voie ponderee : fail-OPEN signale."""
    class _A:
        grains = 1
        umbrellas = 0
        delivered = 0
        prev_genre = None
        lane = "myia-ai-01:CoursIA-2"
        check_claims = False

    candidate = {"number": 101, "title": "candidat", "age": 30, "idle": 1,
                 "idle_since_delivery": 1, "genre": "guard"}
    by_class = {"grain": [candidate], "umbrella": [], "delivered": []}
    state = {"failures": [], "budget_hit": False, "recent_filtered": 0}
    # Le filtre RECENT reste cable sur la sonde reelle : on le neutralise
    # ici, le scope du test etant la porte de GEL.
    monkeypatch.setattr(pig, "has_recent_delivery_marker", lambda n: False)

    picks, claims, conflicts = pig.draw_unclaimed(
        by_class, _A(), random.Random(42), {}, {}, {},
        delivered_state=state, frozen_probe=lambda n: None)

    assert [p["number"] for p in picks] == [101]
    assert state["frozen_unread"] == [101]


# --------------------------------------------------------------------------
# Le mode `--admissible` : il rendait ADMISSIBLE sur un item gele.
# --------------------------------------------------------------------------


def test_gel_cause_text_nomme_le_gel():
    """La cause du gel est dite dans la sortie de `--admissible`."""
    assert pig.gel_cause_text("body").startswith("GEL (body)")
    assert pig.gel_cause_text("comment").startswith("GEL (comment)")
    assert pig.gel_cause_text(False) is None
    assert "NON MESURE" in pig.gel_cause_text(None)


def test_admissible_refuse_un_item_gele(monkeypatch, capsys, tmp_path):
    """`--admissible` rend REFUS sur un item gele (#19309, point 3).

    Le mode repondait « ce grain-ci est-il consommable maintenant ? » : un
    item gele ne l'est pas. Le filtre est branche, et la sortie le dit.

    `--cache-dir` est fourni pour que la sonde de gel soit la VRAIE (sous
    pytest, la sonde par defaut est inerte -- cf `main`) ; la sonde elle-meme
    est stubbee, donc aucune requete `gh` n'est emise.
    """
    pool_item = {
        "number": 19309, "title": "EPIC gelee", "genre": "docs",
        "polarity": "neutre", "created_at": "2026-01-01T00:00:00Z",
        "age": 100, "idle": 10, "idle_since_delivery": 10,
        "labels": [], "klass": "umbrella",
    }

    monkeypatch.setattr(pig, "fetch_pool", lambda **kwargs: ([pool_item], None))
    monkeypatch.setattr(pig, "fetch_series_visits",
                        lambda **kwargs: ({}, {}, None))
    monkeypatch.setattr(pig, "zone_balance",
                        lambda series, issue_to_family, pool: {})
    monkeypatch.setattr(pig, "has_frozen_marker", lambda n: "body")
    # `main` epingle le jeton avant tout appel `gh` : un jeton de presence
    # court-circuite l'appel, sans quoi le test toucherait le reseau.
    monkeypatch.setenv("GH_TOKEN", "jeton-de-test")

    rc = pig.main(["--admissible", "19309", "--cache-dir", str(tmp_path)])
    out = capsys.readouterr().out
    assert rc == 1
    assert "REFUS" in out
    assert "GEL (body)" in out
