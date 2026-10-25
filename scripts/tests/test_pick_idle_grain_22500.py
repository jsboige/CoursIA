"""Tests pour #22500 -- la classe de priorite du tapis roulant.

Mandat user du 2026-10-25, deux phrases qui disent la meme chose par les
deux bouts : une issue de consolidation « merite d'etre visitee plusieurs
fois par semaine » ; un EPIC ordinaire « ne devrait pas etre visite plus
d'une fois par tapis roulant, c'est-a-dire plus d'une fois par semaine au
grand max ».

Un test par point de l'acceptance, sur pool synthetique :

1. classe `consolidation` (titre ou label) : remonte en tete des qu'elle est
   due (derniere visite il y a au moins 48 h) ;
2. urne `umbrella` : un EPIC hors consolidation n'est pas repropose si un
   sous-grain y a ete cree ou claimé dans les 7 jours ;
3. les EPICs de consolidation sont exempts du plafond ;
4. `--belt --report` dit la duree d'une passe complete.

Aucun appel reseau : la boucle du tapis prend ses sondes inertes par
defaut (#19913), et les dates sont injectees par `now=`.
"""
import sys
import types
from datetime import UTC, datetime, timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig

NOW = datetime(2026, 10, 25, 12, 0, 0, tzinfo=UTC)


def _iso(hours_ago: float) -> str:
    return (NOW - timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")


def _item(number, *, title=None, klass="grain", visit_h=None,
          labels=None, **extra):
    """Item de pool minimal : les seules cles que `belt_sort_key` et
    `umbrella_visit_cause` lisent."""
    it = {
        "number": number,
        "klass": klass,
        "title": title if title is not None else f"issue #{number}",
        "labels": labels or [],
        "created_at": _iso(24 * 400),
    }
    if visit_h is not None:
        it["last_delivery_stamp"] = _iso(visit_h)
    it.update(extra)
    return it


def _belt_args(grains=2):
    return types.SimpleNamespace(grains=grains, include_delivered=False,
                                 lane="myia-ai-01:CoursIA-2")


def _free_claims(items):
    return {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in items}


# --- point 1 : la classe `consolidation` remonte en tete ------------------

def test_consolidation_due_passe_devant_un_grain_plus_recent():
    """Consolidation visitee il y a 72 h vs grain ordinaire visite il y a
    30 h : sans classe de priorite, le grain ordinaire passait devant."""
    consolid = _item(1001, title="Consolidation de la serie Search", visit_h=72)
    ordinaire = _item(1002, visit_h=30)
    ordered = sorted([ordinaire, consolid], key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert [it["number"] for it in ordered] == [1001, 1002]


def test_consolidation_due_double_un_grain_plus_ancien_qu_elle():
    """Le cas que la classe existe pour couvrir, et le seul qui la distingue
    du tapis d'origine : un grain ordinaire attend depuis 10 jours, une
    consolidation visitee il y a 49 h est due. Sans classe (#18832), la plus
    ancienne visite passe devant, donc le grain ; avec la classe, la
    consolidation due le double. Un test ou la consolidation serait deja la
    plus ancienne ne prouverait rien."""
    consolid = _item(1001, title="Consolidation de la serie Search", visit_h=49)
    ordinaire = _item(1002, visit_h=24 * 10)
    ordered = sorted([ordinaire, consolid], key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert [it["number"] for it in ordered] == [1001, 1002]


def test_consolidation_pas_due_reste_a_sa_place():
    """Visitee il y a 2 h, elle n'est pas due : elle ne double pas un grain
    qui attend depuis 30 h."""
    consolid = _item(1001, title="Consolidation de la serie Search", visit_h=2)
    ordinaire = _item(1002, visit_h=30)
    ordered = sorted([consolid, ordinaire], key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert [it["number"] for it in ordered] == [1002, 1001]


def test_consolidation_par_label_autant_que_par_titre():
    """Le label n'existe pas encore dans le depot : le motif doit marcher
    des deux facons, sinon la classe depend de sa creation."""
    par_label = _item(1001, title="B.0 : le mot ne dit pas la mesure",
                      labels=[{"name": "consolidation"}], visit_h=72)
    par_titre = _item(1002, title="Consolidation des lectures scindees", visit_h=72)
    ordinaire = _item(1003, visit_h=10)
    ordered = sorted([ordinaire, par_titre, par_label],
                     key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert ordered[-1]["number"] == 1003, "les deux consolidations passent devant"
    assert {it["number"] for it in ordered[:2]} == {1001, 1002}


def test_un_titre_qui_ne_nomme_pas_la_consolidation_ne_suffit_pas():
    """Garde contre l'elargissement : « consolidation » doit etre un mot du
    titre, pas une sous-chaine quelconque."""
    assert pig.is_consolidation(_item(1, title="Consolidation de X")) is True
    assert pig.is_consolidation(_item(2, title="deconsolidation des stocks")) is False
    assert pig.is_consolidation(_item(3, title="[Audit #17073] Serie X -- partition")) is False


def test_consolidations_dues_entre_elles_gardent_l_ordre_de_visite():
    """Aucune consolidation due ne peut attendre plus qu'un tour : entre
    elles, la plus ancienne visite passe d'abord."""
    vieille = _item(2001, title="Consolidation A", visit_h=24 * 5)
    moins_vieille = _item(2002, title="Consolidation B", visit_h=24 * 3)
    ordered = sorted([moins_vieille, vieille], key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert [it["number"] for it in ordered] == [2001, 2002]


# --- points 2 et 3 : plafond hebdomadaire de l'urne `umbrella` ------------

def test_epic_hors_consolidation_sous_plafond_est_ecarte():
    """Un sous-grain cree il y a 2 jours : l'EPIC n'est pas repropose."""
    epic = _item(3001, klass="umbrella", title="[EPIC] Serie Serre100",
                 last_child_stamp=_iso(48))
    cause = pig.umbrella_visit_cause(epic, now=NOW)
    assert cause is not None
    assert cause.startswith("PLAFOND EPIC")
    assert "sous-issue creee" in cause


def test_epic_au_dela_de_sept_jours_redevient_servable():
    """Un EPIC vu il y a 8 jours n'est plus sous plafond : la borne est
    hebdomadaire, pas un gel."""
    epic = _item(3001, klass="umbrella", last_child_stamp=_iso(24 * 8))
    assert pig.umbrella_visit_cause(epic, now=NOW) is None


def test_un_claim_sur_l_epic_compte_comme_une_visite():
    """C'est le geste mesure du 25/10 : quatre lanes ont claimé le meme EPIC
    le meme jour. Le plafond doit voir le claim, pas seulement la creation
    d'une sous-issue."""
    epic = _item(3001, klass="umbrella", last_claim_stamp=_iso(6))
    cause = pig.umbrella_visit_cause(epic, now=NOW)
    assert cause is not None
    assert "claim pose sur l'EPIC" in cause


def test_epic_de_consolidation_est_exempt():
    """La classe consolidation est precisement celle qui doit revenir
    souvent : le plafond ne s'y applique pas."""
    epic = _item(3001, klass="umbrella", title="Consolidation de la serie",
                 last_child_stamp=_iso(2))
    assert pig.umbrella_visit_cause(epic, now=NOW) is None


def test_un_grain_ordinaire_n_est_jamais_sous_plafond_epic():
    """Le plafond porte sur l'urne `umbrella` : un grain n'a pas de
    sous-grains a creer, il ne doit pas etre ecarte par cette regle."""
    grain = _item(3002, last_child_stamp=_iso(1))
    assert pig.umbrella_visit_cause(grain, now=NOW) is None


def test_la_boucle_ecarte_l_epic_et_sert_le_suivant():
    """Bout en bout sur la boucle du tapis : l'EPIC sous plafond part en
    `withheld` avec sa cause, le candidat suivant est servi, et un
    sous-grain ouvert de l'EPIC est nomme pour que la lane sache ou aller."""
    epic = _item(4001, klass="umbrella", title="[EPIC] Serre100",
                 last_child_stamp=_iso(24))
    enfant = _item(4002, title="[#4001 - carnet 29] suite",
                   body="Part of #4001")
    autre = _item(4003, visit_h=24 * 30)
    pool = sorted([epic, enfant, autre], key=lambda it: pig.belt_sort_key(it, now=NOW))
    picks, withheld, _state = pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=3), probe_budget=8)
    servis = [p["number"] for p in picks]
    assert 4001 not in servis, "un EPIC sous plafond n'est pas servi"
    assert 4003 in servis
    causes = {w[0]["number"]: w[1] for w in withheld}
    assert 4001 in causes
    assert causes[4001].startswith("PLAFOND EPIC")
    assert "#4002" in causes[4001], "un sous-grain ouvert est nomme"


# --- point 4 : la duree d'une passe complete ------------------------------

def test_le_rapport_dit_la_duree_d_une_passe(capsys):
    pig.print_belt_report((2.5, 7, 120), elapsed_s=123.4)
    out = capsys.readouterr().out
    assert "duree d'une passe complete" in out
    assert "123.4 s" in out
    assert "2.1 min" in out


def test_le_rapport_ne_fabrique_pas_une_duree_absente(capsys):
    """Une duree non mesuree s'ecrit « non mesuree », jamais un zero."""
    pig.print_belt_report((2.5, 7, 120))
    out = capsys.readouterr().out
    assert "non mesuree" in out
    assert "0.0 s" not in out
