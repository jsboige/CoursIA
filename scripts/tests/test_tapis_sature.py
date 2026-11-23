"""Tests de `coordination/tapis_sature.py` : les conteneurs que le tapis ne
sert plus (#26973, ligne 4).

Deux ecarteurs :

- **EPAISSE** -- le fil du conteneur declare que sa part deleguable est
  epuisee (attestation, ou `[RELEASED]` qui le dit) ;
- **SATURE** -- tous les enfants du conteneur sont fermes.

Aucun test ne touche le reseau : la mesure des enfants est injectee.
"""
import json
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk
from coordination import gh_recherche
from coordination import tapis_rapide as tr
from coordination import tapis_sature as ts

NOW = datetime(2026, 11, 16, 18, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
AUTRE = "myia-po-2027:CoursIA"


def _h(heures: float) -> str:
    return tr._iso(NOW - timedelta(hours=heures))


def issue(n: int, titre: str = "", body: str = "", labels=(), comments=()) -> dict:
    return {"number": n, "title": titre or f"Grain {n}", "body": body,
            "labels": list(labels), "created_at": "2026-10-01T00:00:00Z",
            "comments": list(comments), "comments_total": len(comments)}


def com(heures: float, body: str) -> dict:
    return {"created_at": _h(heures), "author": "jsboige", "body": body}


def lecture(issues, prs=(), citations=None) -> gh_bulk.Lecture:
    return gh_bulk.Lecture(issues=list(issues), prs=list(prs), citations=citations or {})


def etat(lec: gh_bulk.Lecture, n: int, lane: str = LANE) -> tr.Etat:
    return next(e for e in tr.etats(lec, lane, NOW) if e.numero == n)


def faux_etat(conteneur: bool = True) -> tr.Etat:
    return tr.Etat(numero=900, titre="EPIC", labels=[], cree_le="", parent=None,
                   famille=900, conteneur=conteneur, consolidation=False)


# --- la filiation ------------------------------------------------------------

@pytest.mark.parametrize("corps", [
    "Part of #11698",
    "Part of #11698 (moissonnage QC)",
    "Sous-grain de #11698 (Phase 2)",
    "Sous-grain de l'EPIC #11698 (moissonnage)",
    "Sous-issue de #11698",
    "Fille de #11698",
    "Enfant de #11698",
    "Petite-fille de l'EPIC #11698",
    "parent: #11698",
    "Child of #11698",
])
def test_les_formes_de_filiation_sont_reconnues(corps):
    assert ts.declare_filiation(corps, 11698) is True


@pytest.mark.parametrize("corps", [
    "Voir #11698 pour le contexte",
    "Un lien transversal vers #11698",
    "Le grain #11698 est cite, sans filiation",
    "",
])
def test_une_reference_sans_filiation_nest_pas_un_enfant(corps):
    assert ts.declare_filiation(corps, 11698) is False


def test_une_filiation_vers_un_autre_numero_ne_compte_pas():
    assert ts.declare_filiation("Part of #11699", 11698) is False


# --- la saturation ------------------------------------------------------------

def _candidat(numero: int, etat_: str, corps: str = "", pr: bool = False) -> dict:
    return {"number": numero, "state": etat_, "body": corps, "pr": pr}


def test_un_conteneur_dont_tous_les_enfants_sont_fermes_est_sature():
    candidats = [_candidat(10, "closed", "Part of #900"),
                 _candidat(11, "closed", "Sous-grain de #900 (Phase 2)"),
                 _candidat(12, "open", "rien a voir")]
    motif = ts.sature(900, candidats, True)
    assert motif is not None
    assert "2 enfant(s)" in motif and "aucun ouvert" in motif


def test_un_enfant_ouvert_empeche_la_saturation():
    candidats = [_candidat(10, "closed", "Part of #900"),
                 _candidat(11, "open", "Part of #900")]
    assert ts.sature(900, candidats, True) is None


def test_un_conteneur_sans_enfant_declere_nest_pas_sature():
    """Aucun enfant declare : le conteneur peut garder du travail en prose."""
    candidats = [_candidat(10, "closed", "voir #900 pour le contexte")]
    assert ts.sature(900, candidats, True) is None


def test_une_mesure_incomplete_ne_conclut_pas():
    """fail-OPEN : des enfants non vus ne prouvent pas que les autres sont fermes."""
    candidats = [_candidat(10, "closed", "Part of #900")]
    assert ts.sature(900, candidats, False) is None


def test_une_pr_citee_n_est_pas_un_enfant():
    candidats = [{"number": 10, "state": "closed", "body": "Part of #900", "pr": True}]
    assert ts.sature(900, candidats, True) is None


# --- l'epuisement declare par le fil -----------------------------------------

def test_le_conteneur_atteste_comme_livre_est_epuise():
    e = faux_etat()
    corps = [com(3, "[INFO] candidate-delivered -- le conteneur est livre")]
    motif = ts.epuise(e, [{"body": corps[0]["body"]}])
    assert motif is not None and "atteste" in motif


def test_le_released_qui_declare_l_epuisement_epuise_le_conteneur():
    """#18258 : « la part deleguable de l'issue est epuisee »."""
    e = faux_etat()
    corps = ("[RELEASED] lane myia-po-2028:CoursIA-2 -- barriere reelle : "
             "la part deleguable de l'issue est epuisee, le reste est reserve "
             "au coordinateur")
    motif = ts.epuise(e, [{"body": corps}])
    assert motif is not None and "epuisee" in motif


def test_le_released_qui_pose_une_barriere_epuise_nothing():
    """« barriere reelle » n'est pas un épuisement : l'item reste servi."""
    e = faux_etat()
    corps = f"[RELEASED] lane {AUTRE} -- barriere reelle, mesuree"
    assert ts.epuise(e, [{"body": corps}]) is None


def test_un_epuisement_sans_contexte_ne_parle_pas_de_l_item():
    """« le credit de la lane est epuise » ne parle pas du conteneur."""
    e = faux_etat()
    corps = f"[RELEASED] lane {AUTRE} -- le credit de la lane est epuise"
    assert ts.epuise(e, [{"body": corps}]) is None


def test_un_grain_simple_est_pour_autant_epuise():
    """#18258 n'est PAS un conteneur : la forme visee n'est pas liee au label.

    Le gate EPIC etait trop etroit : l'item que le coordinateur cite (#18258)
    n'a pas le label EPIC, et le tapis le resservait quand meme.
    """
    e = faux_etat(conteneur=False)
    corps = "[RELEASED] lane x -- la part deleguable de l'issue est epuisee"
    motif = ts.epuise(e, [{"body": corps}])
    assert motif is not None and "epuisee" in motif


def test_un_claimed_posterieur_ne_annule_pas_l_epuisement():
    """Une PRISE n'est pas une fin de tour : le cycle fautif est precisely
    un item epuise que le tapis ressert (reclaim le 14/11 par une autre lane,
    epuisement declare le 10/11 -- cas #18258)."""
    e = faux_etat()
    corps = "[RELEASED] lane x -- la part deleguable de l'issue est epuisee"
    reprise = "[CLAIMED] lane y -- dispatch coordinateur du 14/11"
    motif = ts.epuise(e, [{"body": corps}, {"body": reprise}])
    assert motif is not None and "epuisee" in motif


def test_une_negation_ne_declenche_pas_l_epuisement():
    """« l'acceptance n'est pas epuisee » n'est pas un épuisement."""
    e = faux_etat()
    corps = "[RELEASED] lane x -- l'acceptance de l'issue n'est pas epuisee"
    assert ts.epuise(e, [{"body": corps}]) is None


def test_le_delivered_posterieur_ne_signifie_plus():
    """Un [DELIVERED] posterieur au [RELEASED] : l'item a ete livre.

    Le marqueur de fin le plus RECENT l'emporte : une livraison dit ou en
    est l'item, un epuisement anterieur ne le ressuscite pas.
    """
    e = faux_etat()
    corps = "[RELEASED] lane x -- la part deleguable de l'issue est epuisee"
    apres = "[DELIVERED] lane y -- PR #26980 (ligne 2)"
    assert ts.epuise(e, [{"body": corps}, {"body": apres}]) is None


def test_un_delivered_qui_parle_d_epuisement_ne_declenche_pas_l_epuisement():
    """Meme ligne, marqueur de fin different : la DELIVRAISON gagne."""
    e = faux_etat()
    corps = "[RELEASED] lane x -- la part deleguable de l'issue est epuisee"
    apres = "[DELIVERED] lane y -- la part deleguable est epuisee, livree ici"
    assert ts.epuise(e, [{"body": corps}, {"body": apres}]) is None


def test_le_delivered_sans_paths_ne_livre_pas_le_conteneur():
    """Sur un conteneur, `[DELIVERED] lane` livre une TRANCHE : la grammaire
    unique (`delivery_grammar`) l'exclut du marqueur de conteneur."""
    e = faux_etat()
    corps = "[DELIVERED] lane myia-po-2025:CoursIA-2 -- PR #26980 (ligne 2)"
    assert ts.epuise(e, [{"body": corps}]) is None


# --- l'ecart dans le tapis ----------------------------------------------------

def test_le_code_epaisse_apparait_dans_le_tapis():
    corps = ("[RELEASED] lane myia-po-2028:CoursIA-2 -- la part deleguable de "
             "l'issue est epuisee")
    lec = lecture([issue(1, labels=["EPIC"], comments=[com(3, corps)])])
    e = etat(lec, 1)
    assert e.ecart == "EPAISSE"
    assert "EPAISSE" in tr.CODES


def test_un_conteneur_non_epuise_nest_pas_ecarte():
    lec = lecture([issue(1, labels=["EPIC"], comments=[com(3, "[CLAIMED] lane x")])])
    assert etat(lec, 1).ecart is None


# --- le post-pass de saturation ------------------------------------------------

def test_le_post_pass_ecarte_le_conteneur_sature_et_retire_le_tirage():
    conteneur = faux_etat()
    mesure = lambda n: ([{"number": 1, "state": "closed", "body": "Part of #900",
                           "pr": False}], True)
    file = [conteneur]
    tirages = []

    def rebuild():
        tirages.append(len(file))
        return []

    resultat = ts.ecarter_satures([conteneur], file, mesure, rebuild)
    assert conteneur.ecart == "SATURE"
    assert "enfant(s)" in conteneur.motif
    assert resultat == []
    assert tirages == [1]  # le tirage est refait une fois


def test_le_post_pass_laisse_passer_un_conteneur_non_sature():
    conteneur = faux_etat()
    mesure = lambda n: ([{"number": 1, "state": "open", "body": "Part of #900",
                           "pr": False}], True)
    resultat = ts.ecarter_satures([conteneur], [conteneur], mesure, lambda: [])
    assert conteneur.ecart is None
    assert resultat == [conteneur]


def test_le_post_pass_est_fail_open_sur_une_panne_de_mesure():
    conteneur = faux_etat()

    def mesure(n):
        raise RuntimeError("gh muet")

    resultat = ts.ecarter_satures([conteneur], [conteneur], mesure, lambda: [])
    assert conteneur.ecart is None
    assert resultat == [conteneur]


def test_le_post_pass_ignore_les_grains_simples():
    grain = faux_etat(conteneur=False)
    mesure = lambda n: ([{"number": 1, "state": "closed", "body": "Part of #900",
                           "pr": False}], True)
    resultat = ts.ecarter_satures([grain], [grain], mesure, lambda: [])
    assert grain.ecart is None
    assert resultat == [grain]


# --- le transport : la recherche des enfants ------------------------------------

def test_chercher_enfants_lit_la_recherche_et_annonce_la_completude():
    payloads = [
        json.dumps({"total_count": 1, "items": [
            {"number": 5, "state": "OPEN", "body": "Part of #900"},
            {"number": 6, "state": "CLOSED", "body": "x", "pull_request": {"url": "u"}}]}),
    ]
    argv_vus = []

    def run(argv, timeout):
        argv_vus.append(argv)
        return payloads.pop(0)

    candidats, complet = gh_recherche.chercher_enfants(run, "jsboige/CoursIA", 900)
    assert complet is True
    assert [c["number"] for c in candidats] == [5, 6]
    assert candidats[0]["state"] == "open" and candidats[0]["pr"] is False
    assert candidats[1]["pr"] is True
    assert any("search/issues?q=repo:jsboige/CoursIA+is:issue+900" in a for a in argv_vus[0])


def test_chercher_enfants_annonce_une_mesure_incomplete():
    def run(argv, timeout):
        return json.dumps({"total_count": 500, "items": [
            {"number": 5, "state": "CLOSED", "body": "Part of #900"}]})

    candidats, complet = gh_recherche.chercher_enfants(run, "jsboige/CoursIA", 900)
    assert complet is False  # 500 references, 3 pages lues : la mesure est partielle


def test_le_transport_de_la_recherche_ne_lance_aucun_processus():
    """Comme `gh_bulk`, le module appelle le `run` injecte : il n'importe pas
    `subprocess` et ne nomme pas le lanceur par defaut."""
    source = (Path(__file__).resolve().parents[1] / "coordination"
              / "gh_recherche.py").read_text(encoding="utf-8")
    assert "subprocess" not in source
    assert "run_defaut" not in source


# --- l'urne de cloture : les items ETEINTS sont nommes -----------------------

def _rapport(lec, lane: str = LANE) -> dict:
    tous = tr.etats(lec, lane, NOW)
    return tr.rapport(lec, tous, [], lane, NOW, "graine")


def test_le_rapport_nomme_les_items_eteints_et_rien_d_autre():
    """Un item eteint par une barriere de FOND est nomme, avec son motif.

    Les ecarts administratifs (gel, reclamee) ne sont PAS dans l'urne : ils se
    resorbent, l'item revient au tour suivant."""
    corps = ("[RELEASED] lane myia-po-2028:CoursIA-2 -- la part deleguable de "
             "l'issue est epuisee")
    lec = lecture([issue(1, labels=["EPIC"], comments=[com(3, corps)])])
    epaisse = etat(lec, 1)
    administratif = faux_etat()
    administratif.ecart = "GEL"
    administratif.motif = "un gel de sept jours"
    r = tr.rapport(lec, [epaisse, administratif], [], LANE, NOW, "graine")
    eteints = r["eteints"]
    assert [e["numero"] for e in eteints] == [1]
    assert eteints[0]["code"] == "EPAISSE"
    assert "epuise" in eteints[0]["motif"]


def test_un_conteneur_sature_eteint_parait_dans_l_urne():
    conteneur = faux_etat()
    mesure = lambda n: ([{"number": 1, "state": "closed", "body": "Part of #900",
                           "pr": False}], True)
    ts.ecarter_satures([conteneur], [conteneur], mesure, lambda: [])
    r = tr.rapport(gh_bulk.Lecture(issues=[], prs=[], citations={}),
                   [conteneur], [], LANE, NOW, "graine")
    eteints = r["eteints"]
    assert [e["code"] for e in eteints] == ["SATURE"]
    assert eteints[0]["numero"] == 900
    assert "enfant(s)" in eteints[0]["motif"]


def test_la_sortie_texte_nomme_les_items_eteints():
    """La liste n'est pas seulement dans le JSON : elle est DANS la sortie
    texte -- c'est elle que le coordinateur lit."""
    corps = ("[RELEASED] lane myia-po-2028:CoursIA-2 -- la part deleguable de "
             "l'issue est epuisee")
    lec = lecture([issue(1, labels=["EPIC"], comments=[com(3, corps)])])
    sortie = tr.texte(_rapport(lec), "test")
    assert "urne de cloture" in sortie
    assert "#1" in sortie
    assert "EPAISSE" in sortie


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
