"""Tests du garde de lane sur l'urne `delivered` (#15069).

Mandat user 2026-09-07 : « je ne veux pas que Minimax, notre plus petit
modele, soit en charge ni de merger, ni de fermer des issues ». L'urne
`delivered` prescrit une fermeture -- fermer remonte au coordinateur,
la verification pre-fermeture se delegue a l'adjoint, jamais aux
workers.

Un detecteur se valide par ses faux negatifs : le controle positif
(lane habilitee -> urne servie) est AUSSI obligatoire que le negatif
(lane worker -> jamais servie), sinon le garde pourrait refuser tout
le monde et paraitrait vert.

Cas fondateur : #13903, fermee par myia-po-2024:CoursIA-2 (lane MiniMax)
qui appliquait la regle R5 telle qu'elle etait lisible -- urne
`delivered` servie par le picker sans garde de lane.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from pick_idle_grain import (  # noqa: E402
    DELIVERED_COMMENT_MARKER,
    DELIVERED_LABEL,
    DELIVERED_SIGNAL_MAX_PROBES,
    DELIVERED_URN_LANES,
    URN_NAMES,
    apply_delivered_urn_gate,
    delivered_signal_reason,
    delivered_urn_allowed,
    draw_unclaimed,
    has_delivered_signal,
    print_delivered_signal_report,
)

DEFAULT_URNS = "grain,umbrella,delivered"


def test_entitled_lanes_are_exactly_the_short_list():
    """Liste explicite et courte, par conception (#15069) : le
    coordinateur (deux dashboards) et l'adjoint. Rien d'autre."""
    assert DELIVERED_URN_LANES == frozenset({
        "myia-ai-01:CoursIA",
        "myia-ai-01:CoursIA-2",
        "myia-po-2025:CoursIA-2",
    })


@pytest.mark.parametrize("lane", sorted(DELIVERED_URN_LANES))
def test_positive_control_entitled_lane_receives_delivered(lane):
    """Controle POSITIF exige par #15069 : une lane habilitee recoit
    toujours l'urne, par defaut comme en demande explicite -- le garde
    ne doit pas refuser tout le monde."""
    urns, notice = apply_delivered_urn_gate(
        lane, DEFAULT_URNS, DEFAULT_URNS, set(URN_NAMES))
    assert "delivered" in urns
    assert notice is None
    urns, notice = apply_delivered_urn_gate(
        lane, "grain,delivered", DEFAULT_URNS, {"grain", "delivered"})
    assert "delivered" in urns
    assert notice is None
    assert delivered_urn_allowed(lane)


WORKER_LANES = [
    "myia-po-2024:CoursIA-2",  # cas fondateur #13903 (lane MiniMax)
    "myia-po-2023:CoursIA-2",
    "myia-po-2026:CoursIA-2",
    "myia-po-2027:CoursIA-2",
    "myia-po-2025:CoursIA-2-x",  # prefixe de l'adjoint != adjoint
    "myia-po-2026:CoursIA",
    "myia-po-2023:CoursIA",
    "myia-po-2024:CoursIA",
    "myia-po-2025:CoursIA",
    "myia-po-2027:CoursIA",
    None,  # pas de lane = pas d'identite habilitee
]


@pytest.mark.parametrize("lane", WORKER_LANES)
def test_negative_control_worker_never_receives_delivered(lane):
    """Controle NEGATIF exige par #15069 : une lane worker ne recoit
    JAMAIS l'urne, quel que soit le chemin (defaut ou explicite)."""
    assert not delivered_urn_allowed(lane)
    # Defaut : retiree avec un avis, sans echec (le defaut ne doit pas
    # faire echouer chaque worker a chaque tirage).
    urns, notice = apply_delivered_urn_gate(
        lane, DEFAULT_URNS, DEFAULT_URNS, set(URN_NAMES))
    assert "delivered" not in urns
    assert "grain" in urns and "umbrella" in urns
    assert notice is not None and "#15069" in notice
    # Explicite : refus (la demande explicite porte l'intention de fermer).
    with pytest.raises(ValueError, match="reservee aux lanes habilitees"):
        apply_delivered_urn_gate(
            lane, "grain,delivered", DEFAULT_URNS, {"grain", "delivered"})


def test_gate_inactive_when_delivered_not_selected():
    """--urns grain,umbrella : le garde ne fait rien (rien a retirer,
    aucun avis parasite)."""
    urns, notice = apply_delivered_urn_gate(
        "myia-po-2024:CoursIA-2", "grain,umbrella", DEFAULT_URNS,
        {"grain", "umbrella"})
    assert urns == {"grain", "umbrella"}
    assert notice is None


def test_filter_candidates_excludes_delivered_for_worker_urns():
    """Bout en bout du cote selection : une fois l'urne retiree, la
    machinerie existuelle (check `urns` de filter_candidates) exclut
    toute candidate-delivered du tirage d'une lane worker."""
    from pick_idle_grain import filter_candidates

    items = [
        {"number": 1, "klass": "grain", "age": 10, "idle": 1},
        {"number": 2, "klass": "delivered", "age": 10, "idle": 1},
    ]
    lane = "myia-po-2024:CoursIA-2"
    urns, _ = apply_delivered_urn_gate(
        lane, DEFAULT_URNS, DEFAULT_URNS, set(URN_NAMES))
    kept, funnel = filter_candidates(items, urns=urns)
    assert [it["number"] for it in kept] == [1]
    assert funnel["by_urn"]["delivered"] == 0


# --- Signal de livraison : le LABEL *ou* le COMMENTAIRE (#15809) ------------
#
# Defaut mesure le 2026-09-12 : 18 grains dont le travail etait DEJA livre ont
# ete servis a une seule lane (myia-po-2023:CoursIA-2) en 2 cycles. La lane a
# du les refuter au lieu de produire, et restait a `R1 NOT HELD` pour la 9e
# fois. Le picker classait le LABEL `candidate-delivered` (klass `delivered`,
# urne reservee #15069) mais etait AVEUGLE au COMMENTAIRE
# `[INFO] candidate-delivered` -- le marqueur que le protocole demande
# pourtant nommement a une lane worker de poster en rendant la main.
#
# Les deux tests qui portent l'invariant vont par PAIRE : un controle negatif
# (le signale est ecarte) et un controle positif (le non-signale est
# conserve). Sans le second, un filtre qui exclut TOUT le monde passerait --
# c'est exactement le piege que le fichier voisin (#15069) documente deja.

import argparse  # noqa: E402
import json  # noqa: E402
import random  # noqa: E402

import pick_idle_grain as pig  # noqa: E402


def _item(n, *, labels=(), klass="grain"):
    """Candidat synthetique, forme minimale attendue par draw_unclaimed."""
    return {"number": n, "title": f"issue {n}", "labels": list(labels),
            "klass": klass, "genre": "docs", "age": 30, "idle": 10,
            "parent": None, "polarity": "neutral",
            "created_at": "2026-07-01T00:00:00Z", "body": "",
            "updated_at": "2026-08-01T00:00:00Z"}


def _args(**kw):
    base = dict(grains=1, umbrellas=0, delivered=0, prev_genre=None,
                lane="myia-po-2023:CoursIA-2", check_claims=False,
                include_delivered=False)
    base.update(kw)
    return argparse.Namespace(**base)


def _by(grain=(), umbrella=(), delivered=()):
    return {"grain": list(grain), "umbrella": list(umbrella),
            "delivered": list(delivered)}


def _probe(*signalled):
    """Sonde synthetique : True pour les numeros listes, False sinon."""
    def probe(number, lane=None):
        return number in signalled
    return probe


def _patch_draw(monkeypatch, order):
    """Force l'ORDRE du tirage.

    Les tests portent sur le FILTRE, pas sur la ponderation : laisser le
    tirage Efraimidis-Spirakis choisir rendrait chaque assertion dependante du
    bruit d'echantillonnage. On fixe donc l'ordre, et le remplacement se
    mesure sur la liste restante -- le pool retreci par draw_unclaimed suffit
    a faire avancer la sequence.
    """
    seq = list(order)

    def fake_draw(items, n, rng, prev_genre=None, visits=None, series=None,
                  issue_to_family=None, delivery=None):
        by_num = {it["number"]: it for it in items}
        out = []
        for num in seq:
            if num in by_num and len(out) < n:
                it = dict(by_num[num])
                it.pop("body", None)
                it["weight"] = 1.0
                it.setdefault("visits", 0)
                it.setdefault("family", None)
                it.setdefault("family_new_notebooks", 0)
                it.setdefault("polarity", "neutral")
                out.append(it)
        return out

    monkeypatch.setattr(pig, "draw", fake_draw)


# --- surface 1 : le LABEL, gratuit (deja dans le payload du pool) ----------

def test_le_label_ecarte_sans_un_seul_appel_reseau():
    """Le label vient de `gh issue list --json labels`, deja paye pour tout le
    pool : l'ecarter doit couter ZERO appel supplementaire. Une sonde appelee
    sur un candidat labellise signalerait une regression de cout."""
    calls = []

    def probe(number, lane=None):
        calls.append(number)
        return False

    reason = delivered_signal_reason(
        _item(1, labels=(DELIVERED_LABEL,)), "myia-po-2023:CoursIA-2", probe)
    assert reason is not None
    assert "label" in reason
    assert calls == [], f"le label ne doit couter aucun appel, or {calls}"


def test_label_ecarte_le_grain_meme_si_klass_ne_l_a_pas_classe(monkeypatch):
    """Defense en profondeur : le `klass` du pool route deja les labellisees
    vers l'urne `delivered`, donc ce candidat ne devrait PAS se trouver dans
    l'urne `grain`. Le garde est teste ici sur cet etat impossible-par-
    construction, precisement pour qu'il survive a un changement du ternaire
    `klass` -- un garde se valide par ce qu'il attrape, pas par ce qui arrive
    aujourd'hui."""
    _patch_draw(monkeypatch, [1, 2])
    by = _by(grain=[_item(1, labels=(DELIVERED_LABEL,)), _item(2)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None)
    assert [p["number"] for p in picks] == [2]
    assert len(conflicts) == 1
    assert conflicts[0][1].startswith("LIVRAISON")


# --- surface 2 : le COMMENTAIRE, une requete par candidat TIRE -------------

def test_commentaire_marqueur_ecarte_le_grain(monkeypatch):
    _patch_draw(monkeypatch, [1, 2])
    by = _by(grain=[_item(1), _item(2)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        delivered_probe=_probe(1))
    assert [p["number"] for p in picks] == [2]
    assert len(conflicts) == 1
    assert DELIVERED_COMMENT_MARKER in conflicts[0][1]


def test_le_remplacant_est_bien_rendu_le_controle_positif_qui_compte(monkeypatch):
    """Le meme point de doctrine que #13310 : exclure SANS remplacer
    fabriquerait de l'idle. Le candidat signale est remplace DANS SA PROPRE
    urne -- un test qui ne compterait que le retrait ne le verrait pas."""
    _patch_draw(monkeypatch, [1, 2])
    by = _by(grain=[_item(1), _item(2)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        delivered_probe=_probe(1))
    assert len(picks) == 1, "un remplacant doit etre rendu, pas zero grain"
    assert [p["number"] for p in picks] == [2]


def test_controle_positif_un_grain_sans_signal_est_conserve(monkeypatch):
    """Sans ce cas, un filtre qui exclut TOUT serait vert sur le negatif."""
    _patch_draw(monkeypatch, [1])
    by = _by(grain=[_item(1)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        delivered_probe=_probe())
    assert [p["number"] for p in picks] == [1]
    assert conflicts == []


# --- l'urne `delivered` ne doit PAS etre cassee (#15069) -------------------

@pytest.mark.parametrize("lane", sorted(DELIVERED_URN_LANES))
def test_urne_delivered_toujours_servie_a_une_lane_habilitee(lane, monkeypatch):
    """Controle positif de non-regression : l'urne `delivered` sert
    precisement a remettre ces issues aux lanes habilitees. Un filtre qui la
    traverserait la viderait de son sens -- et le modele est signale par la
    sonde la plus agressive possible (elle dit True partout)."""
    _patch_draw(monkeypatch, [300])
    by = _by(delivered=[_item(300, labels=(DELIVERED_LABEL,),
                              klass="delivered")])
    picks, _, conflicts = draw_unclaimed(
        by, _args(lane=lane, grains=0, delivered=1), random.Random(7),
        None, None, None, delivered_probe=_probe(300))
    assert [p["number"] for p in picks] == [300]
    assert conflicts == []


def test_une_lane_worker_ne_recoit_pas_l_urne_delivered_mais_le_grain_reste(monkeypatch):
    """Symetrie : sous une lane worker, l'urne `delivered` est retiree en
    amont (#15069) -- le filtre de livraison ne fait que rendre la meme
    garantie au niveau du grain, il ne remplace pas le garde de lane."""
    _patch_draw(monkeypatch, [300])
    by = _by(delivered=[_item(300, klass="delivered")])
    picks, _, _ = draw_unclaimed(
        by, _args(lane="myia-po-2023:CoursIA-2", grains=0, delivered=0),
        random.Random(7), None, None, None, delivered_probe=_probe(300))
    assert picks == []


# --- echappatoire nommee --------------------------------------------------

@pytest.mark.parametrize("labels,probe_signals", [
    ((DELIVERED_LABEL,), ()),
    ((), (1,)),
])
def test_include_delivered_rend_le_grain_signale(monkeypatch, labels,
                                                 probe_signals):
    """--include-delivered : l'echappatoire de la lane habilitee qui veut
    malgre tout tirer ces issues du vivier ordinaire. Les DEUX surfaces
    doivent se desactiver ensemble."""
    _patch_draw(monkeypatch, [1])
    by = _by(grain=[_item(1, labels=labels)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1, include_delivered=True), random.Random(7),
        None, None, None, delivered_probe=_probe(*probe_signals))
    assert [p["number"] for p in picks] == [1]
    assert conflicts == []


# --- fail-OPEN, et DIT (jamais un echec lu comme une absence) --------------

def test_lecture_en_echec_tirage_maintenu_et_avertissement_emis(monkeypatch,
                                                               capsys):
    """Un 403 / un reseau mort n'est PAS << pas de signal >>. Le grain est
    conserve (fail-open) ET le picker le dit -- le contraire exact du defaut
    d'origine, qui confondait silence et couverture."""
    _patch_draw(monkeypatch, [1])
    state = {"failures": [], "budget_hit": False}
    by = _by(grain=[_item(1)])

    def failing_probe(number, lane=None):
        return None

    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        delivered_probe=failing_probe, delivered_state=state)
    assert [p["number"] for p in picks] == [1], "fail-open : le grain reste"
    assert conflicts == []
    assert state["failures"] == [1]

    print_delivered_signal_report([], state, False)
    out = capsys.readouterr().out
    assert "NON LU" in out
    assert "#1" in out
    assert "MAINTENU" in out
    assert "n'est PAS une absence de signal" in out


def test_plafond_de_sondes_fail_open_et_signale(monkeypatch, capsys):
    """Le plafond borne le cout ; il ne doit pas se lire comme un echec de
    lecture. Les candidats non sondes sont CONSERVES, et le message est
    distinct de celui de l'echec de lecture."""
    monkeypatch.setattr(pig, "DELIVERED_SIGNAL_MAX_PROBES", 1)
    _patch_draw(monkeypatch, [1, 2, 3])
    calls = []

    def counting_probe(number, lane=None):
        calls.append(number)
        return False

    state = {"failures": [], "budget_hit": False}
    by = _by(grain=[_item(1), _item(2), _item(3)])
    picks, _, _ = draw_unclaimed(
        by, _args(grains=3), random.Random(7), None, None, None,
        delivered_probe=counting_probe, delivered_state=state)
    assert calls == [1], f"plafond de 1 : une seule sonde, or {calls}"
    assert len(picks) == 3, "les non sondes sont CONSERVES (fail-open)"
    assert state["budget_hit"] is True
    assert state["failures"] == [], (
        "un candidat NON SONDE n'est pas un echec de lecture -- les confondre "
        "ferait afficher une panne reseau sur une economie voulue")

    print_delivered_signal_report([], state, False)
    out = capsys.readouterr().out
    assert "NON SONDE" in out
    assert "fail-open" in out
    assert "NON LU" not in out


def test_has_delivered_signal_est_tri_etat(monkeypatch):
    """La sonde elle-meme : True / False / None. C'est le seul endroit ou
    l'echec de lecture est distingue du silence, et tout le fail-open en
    depend."""
    class _Proc:
        def __init__(self, payload):
            self.stdout = payload

    marked = json.dumps({"comments": [
        {"body": "rien"}, {"body": DELIVERED_COMMENT_MARKER + " -- preuve"}]})
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **kw: _Proc(marked))
    assert has_delivered_signal(1, "myia-po-2023:CoursIA-2") is True

    clean = json.dumps({"comments": [{"body": "aucun marqueur"}]})
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **kw: _Proc(clean))
    assert has_delivered_signal(1) is False

    def boom(*a, **kw):
        raise OSError("403")

    monkeypatch.setattr(pig.subprocess, "run", boom)
    assert has_delivered_signal(1) is None
