"""Tests pour la seconde passe de #22500 (points 1 et 2).

Le mandat du 2026-10-26 (coordinateur, sur le pool reel mesure) :

1. une issue de la classe `consolidation` livree par un marqueur de cloture
   n'est ecartee du tapis que pendant `CONSOLIDATION_LAG_H` (48 h) ; apres,
   elle redevient DUE ;
2. dans la classe 0, un GRAIN borne passe devant un EPIC de consolidation --
   une lane en cycle de 30 minutes ne sait pas servir un EPIC.

Mesure de reference (26/10, 48 issues ouvertes label `consolidation`) : 15
consolidations bornees ecartees par un marqueur de moins de 48 h (exclusion
normale) et 10 ecartees par un marqueur de PLUS de 48 h, dont #20381
(Dynamics, citee par le user depuis le 23/10).

Aucun appel reseau : la boucle du tapis prend ses sondes inertes par
defaut (#19913) ; la lecture d'evenement est injectee, ou simulee.
"""
import sys
import types
from datetime import timedelta
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig

# Le NOW du module : la boucle mesure l'age du marqueur contre LUI, et les
# horodatages injectes doivent etre relatifs a la meme reference.
NOW = pig.NOW


def _iso(hours_ago: float) -> str:
    return (NOW - timedelta(hours=hours_ago)).strftime("%Y-%m-%dT%H:%M:%SZ")


def _item(number, *, title=None, klass="grain", visit_h=None,
          labels=None, **extra):
    """Item de pool minimal : les seules cles que `belt_sort_key` et la
    boucle du tapis lisent."""
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


def _consol(number, *, visit_h=None, **extra):
    """Item de la classe `consolidation` : la classe se lit au LABEL et a lui
    seul (arbitrage coordinateur 2026-10-25T17:37Z)."""
    return _item(number, labels=[{"name": "consolidation"}], visit_h=visit_h,
                 **extra)


def _belt_args(grains=2):
    return types.SimpleNamespace(grains=grains, include_delivered=False,
                                 lane="myia-ai-01:CoursIA-2")


def _free_claims(items):
    return {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in items}


def _run(pool, *, event_probe=None, probe_budget=8, **kw):
    return pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _belt_args(grains=len(pool) + 2),
        probe_budget=probe_budget, delivery_event_probe=event_probe, **kw)


# --- point 1 : une consolidation livree n'ecarte que 48 h ------------------

def test_consolidation_livree_depuis_plus_de_48h_est_servie():
    """Le cas que le mandat decrit : #20381 (Dynamics) porte un marqueur de
    cloture vieux de cinq jours et le tapis l'ecartait quand meme. Elle est
    DUE : elle doit etre servie, pas ecartee."""
    item = _consol(5001, visit_h=72)
    picks, withheld, _state = _run([item], event_probe=lambda n: (True, True, _iso(72)))
    assert [p["number"] for p in picks] == [5001], (
        f"une consolidation dont le marqueur a plus de 48 h doit etre servie, "
        f"withheld={[w[1] for w in withheld]}")
    assert withheld == []


def test_consolidation_livree_depuis_moins_de_48h_est_ecartee():
    """Le controle : livree a l'instant, elle reste ecartee. La regle des
    48 h ne doit pas rendre une consolidation visible pendant qu'une lane
    travaille dessus."""
    item = _consol(5002, visit_h=2)
    picks, withheld, _state = _run([item], event_probe=lambda n: (True, True, _iso(2)))
    assert picks == []
    assert withheld and withheld[0][1].startswith("LIVRAISON (recent)")


def test_grain_ordinaire_livree_depuis_plus_de_48h_est_ecartee():
    """La regle des 48 h est propre a la classe `consolidation` : un grain
    ordinaire porte par le meme marqueur reste ecarte (c'est le comportement
    d'avant, et il est le bon : une issue livree est livree).

    Le grain ordinaire passe par le filtre recent (le marqueur sur le dernier
    commentaire) ; c'est la consolidation qui passe par la lecture
    d'evenement. Les deux sondes sont injectees ici."""
    item = _item(5003, visit_h=72)
    picks, withheld, _state = _run(
        [item], event_probe=lambda n: (True, True, _iso(72)),
        recent_marker_probe=lambda n: True)
    assert picks == []
    assert withheld and withheld[0][1].startswith("LIVRAISON (recent)")


def test_le_marqueur_neutralise_ne_touche_pas_le_label():
    """Une consolidation dont le marqueur a plus de 48 h n'est plus ecartee
    par le MARQUEUR -- mais le LABEL `candidate-delivered` reste un verdict :
    il est pose par le workflow advisory, et la regle des 48 h ne le touche
    pas."""
    # Les labels du pool reel sont des CHAINES (`fetch_pool` :
    # `[lb["name"] for lb in ...]`) -- c'est la forme que le filtre label
    # (`delivered_signal_reason`) sait lire.
    item = _item(5004, visit_h=72,
                  labels=["consolidation", "candidate-delivered"])
    picks, withheld, _state = _run([item], event_probe=lambda n: (True, True, _iso(72)))
    assert picks == []
    assert withheld and "candidate-delivered" in withheld[0][1]


def test_consolidation_pr_mergee_72h_est_servie():
    """Une consolidation dont la derniere livraison par PR a plus de 48 h
    n'est plus ecartee par la surface « PR MERGEE < 90 j » : une tranche
    mergee depuis 72 h ne dit pas « la consolidation est finie ».

    L'age se lit sur `last_delivery_stamp`, deja calcule en amont par le
    corpus `fetch_merged` partage : la sonde PR n'a alors plus rien a
    mesurer, et elle ne doit meme pas etre appelee (une requete `gh` de
    moins, et aucune consommation du budget de sonde). La sonde ci-dessous
    rend True, c'est-a-dire le veto historique des 90 jours : sur la version
    anterieure, elle etait appelee et la consolidation restait invisible."""
    item = _consol(5005, visit_h=72)
    appels = []

    def _sonde_pr(n, lane=None):
        appels.append(n)
        return True

    picks, withheld, _state = _run(
        [item], event_probe=lambda n: (True, True, _iso(72)),
        merged_pr_probe=_sonde_pr)
    assert [p["number"] for p in picks] == [5005], (
        "la consolidation doit etre servie, "
        f"withheld={[w[1] for w in withheld]}")
    assert withheld == []
    assert appels == [], (
        "la sonde PR ne doit pas etre appelee pour une consolidation dont "
        "la derniere livraison par PR depasse 48 h")


def test_consolidation_pr_mergee_2h_est_retenue():
    """Le veto « PR MERGEE » joue encore tant que la derniere livraison par
    PR a moins de 48 h : une tranche vient d'etre mergee, la consolidation
    n'est pas a re-servir.

    La lecture d'evenement rend ici un marqueur ANCIEN (72 h) alors que la
    derniere PR date de 2 h : le filtre recent ne retient donc pas l'issue,
    et c'est bien la surface PR seule qui est mesuree. Le grain libre en
    second sert de temoin : la consolidation retenue est remplacee, et elle
    n'est PAS re-servie derriere -- « retenue » veut dire qu'elle reste
    invisible pour CE tirage, pas seulement qu'un motif est affiche."""
    item = _consol(5008, visit_h=2)
    libre = _item(5011, visit_h=24 * 40)
    pool = sorted([libre, item], key=lambda it: pig.belt_sort_key(it, now=NOW))
    picks, withheld, _state = _run(
        pool, event_probe=lambda n: (True, True, _iso(72)),
        merged_pr_probe=lambda n, lane=None: n == 5008, probe_budget=12)
    assert [p["number"] for p in picks] == [5011], (
        "seul le grain libre doit etre servi ; la consolidation retenue ne "
        "doit pas revenir comme remplacement")
    reasons = [w[1] for w in withheld if w[0]["number"] == 5008]
    assert reasons and all("PR MERGEE" in r for r in reasons), (
        f"la consolidation doit etre retenue par le veto PR : {reasons}")


def test_grain_ordinaire_pr_mergee_72h_est_toujours_retenu():
    """La regle des 90 jours ne change pas pour un grain ordinaire : une PR
    mergee il y a 72 h reste un veto, meme quand le marqueur de commentaire
    est ancien. La neutralisation des 48 h est propre a la consolidation.

    Le grain libre en second sert de temoin : le grain ordinaire retenu est
    remplace sans etre re-servi derriere, exactement comme avant."""
    item = _item(5009, visit_h=72)
    libre = _item(5012, visit_h=24 * 40)
    pool = sorted([libre, item], key=lambda it: pig.belt_sort_key(it, now=NOW))
    picks, withheld, _state = _run(
        pool, recent_marker_probe=lambda n: False,
        merged_pr_probe=lambda n, lane=None: n == 5009, probe_budget=12)
    assert [p["number"] for p in picks] == [5012]
    reasons = [w[1] for w in withheld if w[0]["number"] == 5009]
    assert reasons and all("PR MERGEE" in r for r in reasons)


def test_label_candidate_delivered_retenu_quel_que_soit_l_age():
    """Le label `candidate-delivered` n'est pas touche par la regle des 48 h :
    il continue d'ecarter l'issue, quel que soit l'age de la derniere
    livraison par PR, et sans qu'aucune sonde soit necessaire. Le grain
    libre en second sert de temoin : l'issue labellisee est remplacee sans
    etre re-servie derriere, a 2 h comme a 72 h."""
    for age in (2, 72):
        item = _item(5010 + age, visit_h=age,
                     labels=["consolidation", "candidate-delivered"])
        libre = _item(5100 + age, visit_h=24 * 40)
        pool = sorted([libre, item],
                      key=lambda it: pig.belt_sort_key(it, now=NOW))
        picks, withheld, _state = _run(
            pool, event_probe=lambda n, a=age: (True, True, _iso(a)),
            merged_pr_probe=lambda n, lane=None, a=age: n == 5010 + a,
            probe_budget=12)
        assert [p["number"] for p in picks] == [5100 + age], (
            f"age={age} h : le label doit retenir l'issue")
        reasons = [w[1] for w in withheld if w[0]["number"] == 5010 + age]
        assert reasons and all("candidate-delivered" in r for r in reasons)


def test_une_lecture_en_echec_ne_neutralise_aucun_marqueur():
    """fail-OPEN : une lecture ratee ne prouve rien, donc rien n'est
    neutralise. L'item passe par les filtres habituels -- c'est la sonde
    pleine, elle aussi fail-OPEN, qui decide."""
    item = _consol(5006, visit_h=72)
    picks, _withheld, _state = _run([item], event_probe=lambda n: None)
    assert [p["number"] for p in picks] == [5006]


def test_le_rang_ne_depend_pas_du_dernier_commentaire():
    """Le filtre recent ne regarde que le DERNIER commentaire ; la lecture
    d'evenement, elle, donne l'HEURE du dernier evenement de cloture. Une
    consolidation dont le dernier commentaire n'est PAS un marqueur, mais
    dont le fil en porte un vieux, est donc DUE elle aussi."""
    item = _consol(5007, visit_h=72)
    picks, _withheld, _state = _run(
        [item], event_probe=lambda n: (False, True, _iso(96)))
    assert [p["number"] for p in picks] == [5007]


# --- point 2 : dans la classe 0, le grain borne passe devant l'EPIC -------

def test_grain_borne_passe_devant_un_epic_de_consolidation():
    """Les EPICs de consolidation sont les plus anciens : ils passaient
    devant les grains bornes. Une lane en cycle de 30 minutes ne sait pas
    les servir (« le belt offre 4 umbrellas toutes bloquees », quatre cycles
    de suite) -- donc le grain passe devant."""
    grain = _consol(6001, visit_h=72)
    epic = _consol(6002, klass="umbrella", title="[EPIC] Consolidation globale",
                   visit_h=24 * 30)
    ordered = sorted([epic, grain], key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert [it["number"] for it in ordered] == [6001, 6002]


def test_epic_de_consolidation_arrive_quand_plus_aucun_grain_ne_reste():
    """Le grain d'abord, l'EPIC ensuite : l'EPIC n'arrive en tete que
    lorsque plus aucun grain borne n'est due."""
    grain = _consol(6003, visit_h=72)
    epic = _consol(6004, klass="umbrella", title="[EPIC] Consolidation globale",
                   visit_h=24 * 30)
    pool = sorted([epic, grain], key=lambda it: pig.belt_sort_key(it, now=NOW))
    picks, _withheld, _state = _run(pool)
    assert [p["number"] for p in picks] == [6003, 6004]


def test_le_rang_ne_change_l_ordre_de_la_classe_1():
    """Le rang ne sert qu'A L'INTERIEUR de la classe 0 : la classe 1 garde
    exactement son ordre d'avant (le plus ancien en tete)."""
    ancien = _item(6005, visit_h=24 * 30)
    recent = _item(6006, visit_h=24 * 2)
    ordered = sorted([recent, ancien], key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert [it["number"] for it in ordered] == [6005, 6006]


def test_un_grain_borne_non_consolidation_garde_sa_place():
    """Le rang ne concerne que la classe `consolidation` : un grain ordinaire
    n'est ni promu ni retrograde. La CLASSE prime sur le rang (comportement
    de #22504) : une consolidation due passe devant tout, et le rang ne
    sert qu'a ordonner les membres d'une meme classe."""
    grain = _item(6007, visit_h=24 * 30)
    epic = _consol(6008, klass="umbrella", visit_h=24 * 40)
    ordered = sorted([grain, epic], key=lambda it: pig.belt_sort_key(it, now=NOW))
    assert [it["number"] for it in ordered] == [6008, 6007], (
        "la consolidation due (classe 0) passe avant le grain ordinaire "
        "(classe 1) : le rang ne sert qu'en SON SEIN")


# --- la lecture d'evenement, elle-meme -------------------------------------

class _FakeCompleted:
    def __init__(self, stdout):
        self.stdout = stdout


def test_delivery_event_rend_le_marqueur_et_son_heure(monkeypatch):
    """Une lecture : le DERNIER commentaire porte-t-il un marqueur, le fil
    est-il livre, et QUAND. C'est l'heure qui manque a tous les filtres
    existants -- c'est elle que la regle des 48 h consomme."""
    payload = ('{"comments": ['
               '{"body": "une tranche livree", "createdAt": "2026-10-20T10:00:00Z"},'
               '{"body": "[DELIVERED] lane myia-po-2025:CoursIA -- PR #1234",'
               ' "createdAt": "2026-10-21T22:16:00Z"}]}')
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: _FakeCompleted(payload))
    recent, state, stamp = pig.delivery_event(5001)
    assert recent is True, "le dernier commentaire porte le marqueur"
    assert state is True, "le fil est livre"
    assert stamp == "2026-10-21T22:16:00Z"


def test_delivery_event_ne_confond_pas_une_retractation(monkeypatch):
    """Une retraction posteriore desarme l'etat ET l'heure : l'issue n'est
    plus livree, donc aucune echeance ne court."""
    payload = ('{"comments": ['
               '{"body": "[DELIVERED] lane x -- PR #1",'
               ' "createdAt": "2026-10-20T10:00:00Z"},'
               '{"body": "[NOT-DELIVERED] la tranche n etait pas complete",'
               ' "createdAt": "2026-10-21T10:00:00Z"}]}')
    monkeypatch.setattr(pig.subprocess, "run",
                        lambda *a, **k: _FakeCompleted(payload))
    recent, state, stamp = pig.delivery_event(5002)
    assert state is False
    assert stamp is None
    assert recent is False, "une retraction n'est pas un marqueur de cloture"


def test_delivery_event_rend_none_quand_la_lecture_echoue(monkeypatch):
    """TRI-ETAT : une lecture ratee n'est PAS « pas de marqueur »."""
    def _boom(*a, **k):
        raise RuntimeError("reseau")
    monkeypatch.setattr(pig.subprocess, "run", _boom)
    assert pig.delivery_event(5003) is None


# --- le mur de temps ne doit pas faire tomber le tapis ----------------------

def test_le_mur_de_temps_ne_tombe_pas_sur_une_consolidation():
    """REGRESSION (26/10, tire reel) : le budget de temps de la boucle etait
    epuise AVANT la boucle de service (`settle_belt_head` 341 s + claims 38 s
    pour 240 s de budget). Le code de la consolidation formait alors le
    verdict `False` -- un booleen nu -- et le decomposait en trois :
    `TypeError: cannot unpack non-iterable bool object`.

    Consequence mesuree : le tirage entier rendait ZERO grain, et la
    classe `consolidation` (le mandat user du 25/10) n'etait jamais servie.

    Le comportement attendu quand le temps est epuise : fail-OPEN -- aucune
    sonde lue, AUCUN marqueur neutralise, le candidat reste servable."""
    item = _consol(7001, visit_h=72)
    picks, withheld, _state = _run(
        [item], event_probe=lambda n: (True, True, _iso(72)),
        time_budget_s=0)
    assert [p["number"] for p in picks] == [7001], (
        "mur de temps atteint : rien n'est neutralise, le candidat reste "
        f"servable (withheld={[w[1] for w in withheld]})")


def test_le_mur_de_temps_ne_tombe_pas_non_plus_sur_un_grain_ordinaire():
    """Le meme mur, hors classe consolidation : le filtre recent ne doit pas
    non plus lever une exception (il renvoie un booleen, il le decompose
    normalement -- le test verrouille le voisinage)."""
    item = _item(7002, visit_h=72)
    picks, withheld, _state = _run(
        [item], recent_marker_probe=lambda n: True, time_budget_s=0)
    assert [p["number"] for p in picks] == [7002], (
        f"mur de temps atteint sur un grain ordinaire (withheld="
        f"{[w[1] for w in withheld]})")
