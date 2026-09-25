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
    open_cover_signal,
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

def test_umbrella_portant_le_marqueur_reste_tiree_controle_positif(monkeypatch):
    """Controle POSITIF (review #15809) : l'urne `umbrella` n'est PAS filtree.

    Deux raisons, toutes deux mesurees :
    - le canal label ne marque JAMAIS un EPIC -- decision ecrite dans
      `.github/workflows/candidate-delivered-advisory.yml` (« EPICs are
      excluded ... the checkbox heuristic suggested in #10466 was measured
      firsthand and is UNRELIABLE »). Filtrer l'umbrella par la porte du
      commentaire serait un comportement neuf sans precedent dans l'organe ;
    - le marqueur de #12208, l'exhibit lui-meme, dit « candidate-delivered
      PARTIEL » et conclut « L'EPIC reste vivante comme parapluie de
      tracking ». Une lane n'y claime jamais l'EPIC entier, elle y pioche ou
      y cree un sous-grain (proactive-coordination R5) : servir une umbrella
      partiellement livree est le MODE D'EMPLOI de l'urne, pas un cycle
      brule. Ce test est ce qui distingue « les umbrellas sont protegees »
      de « le filtre ne mord nulle part »."""
    _patch_draw(monkeypatch, [200])
    by = _by(umbrella=[_item(200, klass="umbrella")])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=0, umbrellas=1), random.Random(7), None, None,
        None, delivered_probe=_probe(200))
    assert [p["number"] for p in picks] == [200]
    assert conflicts == []


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


# --- surface 3 : la PR OUVERTE couvrante, meme rang (#16589) ---------------

def _cover_probe(*covered):
    """Sonde de couverture synthetique : descriptor pour les numeros listes,
    chaine vide sinon. Retourne le descripteur « PR #<9000+n> » pour rendre
    l'assertion lisible dans le message de conflit."""
    covered = set(covered)

    def probe(number):
        return f"PR #{9000 + number}" if number in covered else ""
    return probe


def test_pr_ouverte_ecarte_le_grain_et_le_remplace(monkeypatch):
    """Arbitrage #16589 : le candidat couvert par une PR OUVERTE est ecarte
    ET remplace dans son urne -- au meme rang que candidate-delivered, pas
    une annotation de plus. C'est le differenciateur du precedent #12504 :
    le signal existait (annotation recent_delivery), il manquait la
    sanction."""
    _patch_draw(monkeypatch, [1, 2])
    by = _by(grain=[_item(1), _item(2)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        cover_probe=_cover_probe(1))
    assert [p["number"] for p in picks] == [2], (
        "un remplacant doit etre rendu, pas zero grain")
    assert len(conflicts) == 1
    assert conflicts[0][1].startswith("EN COURS")
    assert "PR #9001" in conflicts[0][1]


def test_controle_positif_grain_non_couvert_est_conserve(monkeypatch):
    """Sans ce cas, un garde qui ecarterait TOUT serait vert sur le negatif."""
    _patch_draw(monkeypatch, [1])
    by = _by(grain=[_item(1)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        cover_probe=_cover_probe())
    assert [p["number"] for p in picks] == [1]
    assert conflicts == []


def test_umbrella_pas_filtree_par_la_couverture(monkeypatch):
    """Meme protection que la surface livraison : l'urne `umbrella` n'est pas
    filtree par la couverture -- une PR ouverte sur un VOLET d'EPIC n'epuise
    pas le parapluie (R5 : on y pioche un autre sous-grain, on ne ferme pas
    l'EPIC sur une livraison partielle)."""
    _patch_draw(monkeypatch, [200])
    by = _by(umbrella=[_item(200, klass="umbrella")])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=0, umbrellas=1), random.Random(7), None, None,
        None, cover_probe=_cover_probe(200))
    assert [p["number"] for p in picks] == [200]
    assert conflicts == []


def test_livraison_premiere_le_label_ne_paie_pas_la_couverture(monkeypatch):
    """Le filtre de livraison reste PREMIER : un candidat labelise part en
    LIVRAISON sans jamais atteindre la sonde de couverture (un travail deja
    livre prime sur un travail en cours)."""
    _patch_draw(monkeypatch, [1, 2])
    calls = []

    def probe(number):
        calls.append(number)
        return "PR #9001" if number == 1 else ""

    by = _by(grain=[_item(1, labels=(DELIVERED_LABEL,)), _item(2)])
    picks, _, conflicts = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        cover_probe=probe)
    assert [p["number"] for p in picks] == [2]
    assert conflicts[0][1].startswith("LIVRAISON")
    assert calls == [2], (
        "le candidat labelise ne doit jamais atteindre la sonde de "
        f"couverture, or appels={calls}")


def test_sonde_couverture_en_echec_fail_open_et_dite(monkeypatch, capsys):
    """Echec de requete != absence de PR couvrante : candidat CONSERVE,
    echec rapporte (cover_failures), message distinct du NON SONDE."""
    _patch_draw(monkeypatch, [1])
    by = _by(grain=[_item(1)])

    def failing(number):
        return None

    state = {"failures": [], "budget_hit": False}
    picks, _, _ = draw_unclaimed(
        by, _args(grains=1), random.Random(7), None, None, None,
        cover_probe=failing, delivered_state=state)
    assert [p["number"] for p in picks] == [1], "fail-OPEN : candidat garde"
    assert state["cover_failures"] == [1]
    print_delivered_signal_report([], state, False)
    out = capsys.readouterr().out
    assert "sonde de couverture NON LUE" in out
    assert "NON SONDE" not in out


def test_plafond_partage_entre_sondes_livraison_et_couverture(monkeypatch):
    """« Au meme rang » (#16589) = AUSSI au meme cout : les deux sondes
    parent le MEME budget de DELIVERED_SIGNAL_MAX_PROBES, pas un plafond
    double. Avec un plafond de 2 et deux candidats, exactement deux sondes
    reelles partent (livraison du 1er, couverture du 1er) -- le 2e candidat
    n'en a plus aucune."""
    monkeypatch.setattr(pig, "DELIVERED_SIGNAL_MAX_PROBES", 2)
    _patch_draw(monkeypatch, [1, 2])
    delivered_calls = []
    cover_calls = []

    def counting_delivered(number, lane=None):
        delivered_calls.append(number)
        return False

    def counting_cover(number):
        cover_calls.append(number)
        return ""

    state = {"failures": [], "budget_hit": False}
    by = _by(grain=[_item(1), _item(2)])
    picks, _, _ = draw_unclaimed(
        by, _args(grains=2), random.Random(7), None, None, None,
        delivered_probe=counting_delivered,
        cover_probe=counting_cover, delivered_state=state)
    assert delivered_calls == [1], (
        f"plafond partage : une seule sonde livraison, or {delivered_calls}")
    assert cover_calls == [1], (
        f"plafond partage : une seule sonde couverture, or {cover_calls}")
    assert state["budget_hit"] is True
    assert len(picks) == 2, "les non sondes sont CONSERVES (fail-open)"


def test_open_cover_signal_est_tri_etat(monkeypatch):
    """La sonde elle-meme : descriptor / chaine vide / None. Le meme tri-etat
    que has_delivered_signal -- un echec de requete n'est pas une absence de
    PR couvrante."""
    class _Proc:
        def __init__(self, payload):
            self.stdout = payload

    opened = json.dumps([
        {"number": 12530, "state": "OPEN", "isDraft": False,
         "title": "fix(knot): L576", "body": "See #12504."},
        {"number": 12519, "state": "OPEN", "isDraft": True,
         "title": "#12504 patrol", "body": ""},
        {"number": 12400, "state": "CLOSED", "isDraft": False,
         "title": " vieux sujet 12504", "body": ""}])
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **kw: _Proc(opened))
    assert open_cover_signal(12504) == (
        "PR #12519 [draft] (+1 autre(s) : #12530)")

    clean = json.dumps([{"number": 12400, "state": "CLOSED",
                         "isDraft": False}])
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **kw: _Proc(clean))
    assert open_cover_signal(12504) == ""

    def boom(*a, **kw):
        raise OSError("403")

    monkeypatch.setattr(pig.subprocess, "run", boom)
    assert open_cover_signal(12504) is None


def test_open_cover_signal_exige_l_ancre_diese(monkeypatch):
    """#17760 : la recherche GitHub rend un NOMBRE NU en sous-chaine. Une PR
    ouverte qui ne cite pas `#N` borne par un mot ne couvre PAS -- le
    candidat est conserve. Controles de l'arbitrage ai-01 : le positif
    (ancre presente -> descriptor) et le negatif (sous-chaine seule -> vide).
    """
    class _Proc:
        def __init__(self, payload):
            self.stdout = payload

    # Cas mesure (classe dominante : EPICs au petit numero) : le numero
    # n'apparait qu'en sous-chaine d'identifiants plus grands, jamais ancre.
    bare = json.dumps([
        {"number": 17428, "state": "OPEN", "isDraft": False,
         "title": "fix(knot): patrol L576 branches orphelines",
         "body": "mesures c.1170301 et #1170391 citees pour contexte"}])
    monkeypatch.setattr(pig.subprocess, "run", lambda *a, **kw: _Proc(bare))
    assert open_cover_signal(11703) == ""

    # Nombre nu dans le titre : pas plus couvrant que dans le body.
    title_bare = json.dumps([
        {"number": 17428, "state": "OPEN", "isDraft": False,
         "title": "fix 11703 patrol", "body": ""}])
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **kw: _Proc(title_bare))
    assert open_cover_signal(11703) == ""

    # Controle positif : l'ancre bornee couvre, et seul le PR ancre compte
    # dans le descriptor (le voisin sous-chaine est ecarte du compte).
    anchored = json.dumps([
        {"number": 17428, "state": "OPEN", "isDraft": False,
         "title": "fix(knot): patrol L576",
         "body": "mesure c.1668201 pour contexte"},
        {"number": 17452, "state": "OPEN", "isDraft": False,
         "title": "feat(picker)", "body": "See #16682."}])
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **kw: _Proc(anchored))
    assert open_cover_signal(16682) == "PR #17452"
