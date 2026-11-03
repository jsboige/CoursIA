"""Tests pour la regle de la REOUVERTURE (#24250, suite de #24172/#24173).

Un dossier `[CLOSURE PREFLIGHT]` de verdict CLOSE ecarte une issue du tapis
**sans limite d'age** : il est terminal. Mais une decision de cloture prise
sur une issue que le USER rouvre ensuite n'est plus la decision finale -- et
le tapis, qui ne lit que le fil, ne voyait pas la reouverture : l'issue
restait ecartee du tapis POUR TOUJOURS.

Le predicat : **une reouverture POSTERIEURE a la decision de cloture**. Pas
« une annonce de fermeture presente ET issue ouverte » : ce predicat
ressortirait toute issue livree et non closee, et le filtre de livraison du
tapis s'effondrerait.

Aucun appel reseau : la lecture du timeline est injectee (monkeypatch de
`_reopen_events`), les commentaires viennent de l'instantane local
(`_snapshot_comments`), et les dates sont relatives au NOW du module.
"""
import sys
from datetime import timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig

NOW = pig.NOW
ISSUE = 24250


def _iso(hours_ago: float) -> str:
    return (NOW - timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")


# --- le corps reel d'un dossier de cloture (extrait, champs complets) -------

DOSSIER_CLOSE = """[CLOSURE PREFLIGHT]
schema: 1
lane: myia-po-2025:CoursIA
issue: 19253
verdict: CLOSE
acceptance:
  - "Applications/ ne joue plus le role d'une partie 3 muette -> ABSENT de l'arbre"
  - "la carte de reorganisation est en place -> Part1..Part5 presents"
residue: none
open-prs: 0
comments-reviewed: 14
[/CLOSURE PREFLIGHT]"""

ANNONCE = ("Fermeture sur dossier `[CLOSURE PREFLIGHT]` (verdict CLOSE, "
           "gate `check_closure_dossier.py` rc=0, commentaire 6572592182 "
           "ci-dessus).")

MARQUEUR = "[INFO] candidate-delivered -- lane myia-po-2028:CoursIA-2"


def _c(body, hours_ago):
    return {"body": body, "createdAt": _iso(hours_ago)}


def _install(monkeypatch, comments, reopens):
    """Injecte le fil (instantane local) et la lecture du timeline.

    REND la liste des numeros d'issue dont le timeline a ete lu : c'est la
    mesure du COUT (un marqueur ordinaire ne doit declencher aucune lecture).
    """
    lus = []

    def fake_reopen_events(issue_number):
        lus.append(issue_number)
        return list(reopens)

    monkeypatch.setattr(pig, "_reopen_events", fake_reopen_events)
    monkeypatch.setattr(pig, "_snapshot_comments",
                        lambda n: [dict(c) for c in comments])
    return lus


def _verdicts(monkeypatch, comments, reopens):
    """Les TROIS surfaces qui ecartent un candidat, sur le meme fil.

    - la sonde RECENTE (`has_recent_delivery_marker`) ;
    - la sonde PLEINE (`has_delivered_signal`) ;
    - le reducteur d'evenement (`delivery_event`, surface des consolidations).

    Elles doivent rendre le MEME verdict : sinon le tapis ecarte par une
    surface ce que l'autre surface sert.
    """
    lus = _install(monkeypatch, comments, reopens)
    recent = pig.has_recent_delivery_marker(ISSUE)
    plein = pig.has_delivered_signal(ISSUE)
    evenement = pig.delivery_event(ISSUE)
    servable = bool(
        recent is not True
        and plein is not True
        and not (isinstance(evenement, tuple)
                 and (evenement[0] or evenement[1]))
    )
    return {"recent": recent, "plein": plein, "evenement": evenement,
            "servable": servable, "lus": lus}


# --- la regle : une reouverture POSTERIEURE a la decision ------------------

def test_le_dossier_repris_par_une_reouverture_redonne_l_issue_au_tapis(
        monkeypatch):
    """LE CONTROLE POSITIF : dossier a T-10 h, reouverture a T-5 h.

    La reouverture est posterieure a la decision : elle la reprend, et
    l'issue redevient servable.
    """
    v = _verdicts(monkeypatch, [_c(MARQUEUR, 20), _c(DOSSIER_CLOSE, 10)],
                  [_iso(5)])
    assert v["servable"] is True, (
        "une issue rouverte apres son dossier de cloture doit redevenir "
        "servable, verdict=%r" % (v,))
    assert v["recent"] is False
    assert v["plein"] is False
    assert v["evenement"] == (False, False, None)


def test_les_trois_surfaces_rendent_le_meme_verdict(monkeypatch):
    """INVARIANT : sonde RECENTE, sonde PLEINE et reducteur ne peuvent pas
    diverger sur un fil qui change entre deux lectures."""
    cas = [
        ("reprise", [_c(MARQUEUR, 20), _c(DOSSIER_CLOSE, 10)], [_iso(5)], True),
        ("anterieure", [_c(MARQUEUR, 20), _c(DOSSIER_CLOSE, 10)],
         [_iso(30)], False),
        ("rearmement", [_c(DOSSIER_CLOSE, 10), _c(MARQUEUR, 1)], [_iso(5)],
         False),
        ("aucune", [_c(MARQUEUR, 20), _c(DOSSIER_CLOSE, 10)], [], False),
    ]
    for nom, comments, reopens, attendu in cas:
        v = _verdicts(monkeypatch, comments, reopens)
        assert v["servable"] is attendu, (
            "cas %s : verdict %r, attendu %r" % (nom, v, attendu))
        # La coherence des surfaces : RECENT et PLEINE doivent s'accorder.
        assert bool(v["recent"]) == bool(v["plein"]), (
            "cas %s : sonde RECENTE %r et sonde PLEINE %r divergent"
            % (nom, v["recent"], v["plein"]))


def test_une_reouverture_ANTERIEURE_au_dossier_ne_reprend_pas_la_decision(
        monkeypatch):
    """CONTROLE NEGATIF : le dossier reste la derniere decision."""
    v = _verdicts(monkeypatch, [_c(MARQUEUR, 20), _c(DOSSIER_CLOSE, 10)],
                  [_iso(30)])
    assert v["servable"] is False
    assert v["plein"] is True


def test_un_marqueur_posterior_a_la_reouverture_rearme_le_signal(monkeypatch):
    """Le dossier a T-10 h, reouverture a T-5 h, marqueur a T-1 h : le
    marqueur est la derniere decision, l'issue reste ecartee."""
    v = _verdicts(monkeypatch, [_c(DOSSIER_CLOSE, 10), _c(MARQUEUR, 1)],
                  [_iso(5)])
    assert v["servable"] is False
    assert v["plein"] is True


def test_le_dossier_sans_reouverture_reste_terminal(monkeypatch):
    """LE CONTROLE DU CARACTERE CIBLE : le comportement de #24172/#24173 est
    preserve -- un dossier CLOSE ecarte l'issue SANS limite d'age."""
    v = _verdicts(monkeypatch, [_c(MARQUEUR, 20), _c(DOSSIER_CLOSE, 10)], [])
    assert v["servable"] is False
    assert v["plein"] is True
    assert v["evenement"][2] is None, (
        "le dossier reste terminal : il ne porte pas d'heure, donc la regle "
        "des 48 h ne peut pas l'expirer")


def test_l_annonce_de_cloture_est_reprise_elle_aussi(monkeypatch):
    """L'annonce en prose est la meme decision que le dossier."""
    v = _verdicts(monkeypatch, [_c(DOSSIER_CLOSE, 10), _c(ANNONCE, 9)],
                  [_iso(5)])
    assert v["servable"] is True


# --- le cout : la lecture du timeline est rare -----------------------------

def test_un_marqueur_ordinaire_ne_declenche_aucune_lecture_de_timeline(
        monkeypatch):
    """Un marqueur ordinaire expire a 48 h : il n'a pas besoin de la
    reouverture, et le tapis ne doit donc pas payer une lecture de plus."""
    lus = _install(monkeypatch, [_c(MARQUEUR, 3)], [])
    assert pig.has_recent_delivery_marker(ISSUE) is True
    assert pig.has_delivered_signal(ISSUE) is True
    assert lus == [], (
        "aucune lecture de timeline ne doit avoir eu lieu, lus=%r" % (lus,))


def test_un_dossier_declenche_la_lecture_du_timeline(monkeypatch):
    """Le dossier, lui, doit etre confronte a la reouverture."""
    lus = _install(monkeypatch, [_c(DOSSIER_CLOSE, 10)], [])
    pig.has_recent_delivery_marker(ISSUE)
    assert lus == [ISSUE]


# --- la lecture du timeline elle-meme -------------------------------------

def test_la_lecture_du_timeline_ne_garde_que_des_horodatages_iso(monkeypatch):
    """Une sortie inattendue de `gh` ne doit pas pouvoir fabriquer une
    reouverture : seules les chaines ISO strictes sont retenues."""
    sortie = ('{"event": "reopened", "created_at": "2026-11-02T08:29:00Z"}\n'
              "2026-11-02T09:00:00Z\n"
              "pas une date\n")

    class _Res:
        stdout = sortie

    monkeypatch.setattr(pig, "_REOPEN_CACHE", {})
    monkeypatch.setattr(pig.subprocess, "run", lambda *a, **k: _Res())
    events = pig._reopen_events(ISSUE)
    assert events == ["2026-11-02T09:00:00Z"], events


def test_une_lecture_en_echec_laisse_la_decision_de_cloture_intacte(
        monkeypatch):
    """Fail-OPEN : pas de reouverture lue -> le dossier garde sa terminalite."""
    monkeypatch.setattr(pig, "_REOPEN_CACHE", {})

    def _boom(*a, **k):
        raise OSError("reseau")

    monkeypatch.setattr(pig.subprocess, "run", _boom)
    assert pig._reopen_events(ISSUE) == []

    v = _verdicts(monkeypatch, [_c(MARQUEUR, 20), _c(DOSSIER_CLOSE, 10)], [])
    assert v["servable"] is False
    assert v["plein"] is True


def test_le_timeline_est_lu_une_seule_fois_par_issue(monkeypatch):
    """Les trois surfaces consultent le meme predicat : le timeline ne doit
    pas etre lu trois fois pour la meme issue."""
    appels = []

    class _Res:
        stdout = ""

    def fake_run(argv, **kwargs):
        appels.append(argv)
        return _Res()

    monkeypatch.setattr(pig, "_REOPEN_CACHE", {})
    monkeypatch.setattr(pig.subprocess, "run", fake_run)
    monkeypatch.setattr(pig, "_snapshot_comments",
                        lambda n: [_c(DOSSIER_CLOSE, 10)])

    pig.has_recent_delivery_marker(ISSUE)
    pig.has_delivered_signal(ISSUE)
    pig.delivery_event(ISSUE)
    assert len(appels) == 1, (
        "la lecture est memorisee par issue : une seule requete pour les "
        "trois surfaces, appels=%r" % (appels,))
