"""La repondersion du tapis : recompense de fermeture et prior de
consolidation (issue #25082, points A et B).

Le mandat user du 2026-11-07 (session directe avec ai-01) demande que le
tapis serve la CLOTURE : « L'objectif est de cloturer le max d'issues en
les visitant de facon intelligente (bandit manchots?) ».

Deux mecanismes, distincts et mesurables :

A -- la RECOMPENSE est la fermeture, pas la visite. Le bras est la zone
(chemin de serie), le genre servant de repli quand la zone n'est pas
resolue. Le tirage est un echantillon de Thompson sur
Beta(fermees + 1, visitees_sans_fermeture + 1).

B -- le PRIOR de consolidation est independant de la zone : le label
`consolidation`, l'urne `delivered`, les partitions d'audit `[Audit #17073]`.

Contrainte du mandat (decision user du 12/10) : des POIDS SEULEMENT. Aucun
refus de tirage, aucun plafond. Ces tests le verifient : la repondersion
reordonne, elle ne retire rien.

Aucun appel reseau : les fermetures et les PRs mergees sont injectes.
"""

import random
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import pick_idle_grain as pig  # noqa: E402

NOW = datetime(2026, 11, 7, 18, 0, tzinfo=timezone.utc)
ZONE_A = "MyIA.AI.Notebooks/GenAI/Texte"
ZONE_B = "MyIA.AI.Notebooks/GameTheory/Chaines"


def _item(number, *, title="un grain", labels=(), klass="grain",
          family=None, genre="notebook-python", polarity="neutral",
          created="2026-01-01T00:00:00Z", last_visit=None):
    it = {"number": number, "title": title, "labels": list(labels),
          "klass": klass, "genre": genre, "polarity": polarity,
          "created_at": created, "last_delivery_stamp": last_visit,
          "last_claim_stamp": None, "last_child_stamp": None}
    if family is not None:
        it["family"] = family
    return it


# --- A : le bras -------------------------------------------------------------


def test_le_bras_est_la_zone_quand_elle_est_resolue():
    assert pig.bandit_arm(_item(1, family=ZONE_A)) == "zone:" + ZONE_A


def test_le_bras_replie_sur_le_genre_quand_la_zone_est_absente():
    it = _item(1, genre="guard")
    assert "family" not in it
    assert pig.bandit_arm(it) == "genre:guard"


def test_une_zone_non_resolue_ne_porte_pas_le_bras_dune_autre():
    """Le repli est le GENRE, jamais la zone d'un autre grain : un grain
    sans zone ne doit pas hériter du credit d'une zone qui ferme."""
    assert pig.bandit_arm(_item(1, genre="docs")) != "zone:" + ZONE_B


# --- A : la recompense et l'echec --------------------------------------------


def test_chaque_bras_compte_fermees_et_visitees_sans_fermeture():
    arms = pig.arm_outcomes({"zone:A": 3}, {"zone:B": 2})
    assert arms == {"zone:A": (3, 0), "zone:B": (0, 2)}


def test_une_issue_fermee_est_la_recompense_de_son_bras():
    pool = [_item(25100, family=ZONE_A)]
    closed = [{"number": 25190, "title": "GenAI/Texte : fin de serie",
               "body": "", "labels": []}]
    arms = pig.arm_outcomes_from_pool(pool, closed, [], series=[ZONE_A])
    assert arms["zone:" + ZONE_A][0] == 1
    assert arms["zone:" + ZONE_A][1] == 0


def test_une_issue_ouverte_visitee_est_un_echec_de_son_bras():
    pool = [_item(25100, family=ZONE_A)]
    prs = [{"number": 500, "title": "Fix(x): y", "body": "Closes #25100"}]
    arms = pig.arm_outcomes_from_pool(pool, [], prs, series=[ZONE_A])
    assert arms["zone:" + ZONE_A] == (0, 1)


def test_une_pr_qui_cite_une_issue_hors_pool_ne_compte_pas():
    """Le corpus de visites ne compte que les issues ENCORE OUVERTES : une
    issue fermee est une recompense, pas un echec."""
    pool = [_item(25100, family=ZONE_A)]
    prs = [{"number": 500, "title": "Fix(x): y", "body": "Closes #25101"}]
    arms = pig.arm_outcomes_from_pool(pool, [], prs, series=[ZONE_A])
    assert arms == {}


def test_une_pr_sans_declaration_ne_compte_pas_comme_une_visite():
    """`cited_issues` ne lit que les DECLARATIONS : un renvoi de contexte
    n'est pas une visite (cf #13435)."""
    pool = [_item(25100, family=ZONE_A)]
    prs = [{"number": 500, "title": "Fix(x): y", "body": "voir #25100"}]
    arms = pig.arm_outcomes_from_pool(pool, [], prs, series=[ZONE_A])
    assert arms == {}


def test_une_issue_fermee_sans_zone_ne_tue_pas_le_tirage():
    """`gh issue list` rend des labels OBJETS (`{name: ...}`), la ou le pool
    du picker porte des chaines. `infer_genre` concatene les labels : sans
    normalisation, une seule issue fermee sans zone faisait echouer le
    tirage entier (mesure du 07/11, rejeu du bandit)."""
    issue = {"number": 25190, "title": "un titre sans zone", "body": "",
             "labels": [{"name": "audit"}]}
    assert pig._arm_of_issue(issue, {}, [], None).startswith("genre:")


# --- A : l'echantillon de Thompson -------------------------------------------


def test_un_bras_sans_donnee_a_un_prior_uniforme():
    """Beta(1, 1) : le bras n'est ni favorise ni ecarte. C'est ce qui
    evite qu'une zone jamais mesuree herite du credit d'une zone qui
    ferme."""
    rng = random.Random(7)
    thetas = pig.sample_arm_thetas({"zone:A": (0, 0)}, rng)
    assert 0.0 < thetas["zone:A"] < 1.0


def test_un_bras_qui_ferme_vite_a_un_theta_plus_eleve():
    """Le bras qui ferme a un theta plus eleve en moyenne -- c'est la
    RECOMPENSE qui fait la loi, pas le hasard du tirage."""
    rng = random.Random(11)
    ferme = pig.sample_arm_thetas({"zone:A": (9, 1)}, rng)["zone:A"]
    sterile = pig.sample_arm_thetas({"zone:B": (0, 10)}, rng)["zone:B"]
    assert ferme > sterile


def test_le_prior_reste_uniforme_sur_un_bras_sans_recompense():
    rng = random.Random(3)
    echantillons = [pig.sample_arm_thetas({"zone:A": (0, 0)}, rng)["zone:A"]
                    for _ in range(200)]
    assert 0.3 < sum(echantillons) / len(echantillons) < 0.7


# --- B : le prior de consolidation -------------------------------------------


def test_le_label_de_consolidation_porte_le_prior():
    facteur, classe = pig.consolidation_prior(
        _item(1, labels=["consolidation"]))
    assert classe == "consolidation"
    assert facteur == pig.CONSOLIDATION_PRIOR


def test_l_urne_delivered_porte_le_prior():
    facteur, classe = pig.consolidation_prior(_item(1, klass="delivered"))
    assert classe == "delivered"
    assert facteur == pig.DELIVERED_URN_PRIOR


def test_les_partitions_d_audit_17073_portent_le_prior():
    facteur, classe = pig.consolidation_prior(
        _item(1, title="[Audit #17073] 02-5 LTX2 -- la sortie annonce"))
    assert classe == "audit_17073"
    assert facteur == pig.AUDIT_17073_PRIOR


def test_un_grain_ne_portant_none_des_trois_classes_n_a_pas_de_prior():
    assert pig.consolidation_prior(_item(1, labels=["bug"])) == (1.0, "")


def test_le_prior_le_plus_fort_gagne_quand_plusieurs_classes_se_superposent():
    facteur, classe = pig.consolidation_prior(
        _item(1, labels=["consolidation"], klass="delivered",
              title="[Audit #17073] une partition"))
    assert facteur == pig.CONSOLIDATION_PRIOR
    assert classe == "consolidation"


# --- B : le grain d'expansion ------------------------------------------------


def test_sous_le_seuil_du_veto_le_grain_d_expansion_n_est_penalise():
    assert pig.expansion_factor(400) == 1.0
    assert pig.expansion_factor(200) == 1.0


def test_au_dessus_du_seuil_le_grain_d_expansion_est_streme():
    facteur = pig.expansion_factor(574)
    assert 0.0 < facteur < 1.0


def test_le_poids_d_expansion_ne_devient_jamais_nul():
    """Un poids nul serait un REFUS de tirage, et le mandat du 12/10
    l'interdit."""
    assert pig.expansion_factor(100000) == pig.EXPANSION_FACTOR_FLOOR
    assert pig.EXPANSION_FACTOR_FLOOR > 0.0


def test_le_score_du_grain_d_expansion_porte_le_facteur():
    thetas = {"zone:" + ZONE_A: 0.5}
    neutre = pig.belt_score(_item(1, family=ZONE_A), thetas, 0.5, 574)
    expansion = pig.belt_score(
        _item(2, family=ZONE_A, polarity="expansion"), thetas, 0.5, 574)
    assert expansion["score"] < neutre["score"]


# --- la repondersion ---------------------------------------------------------


def test_la_repondersion_ne_retire_aucun_grain():
    """Des POIDS SEULEMENT : rien n'est ecarte, rien n'est refuse."""
    pool = [_item(i, family=ZONE_A) for i in range(1, 6)]
    avant = sorted(it["number"] for it in pool)
    pig.apply_belt_weights(pool, rng=random.Random(1), closed_issues=[],
                           now=NOW)
    assert sorted(it["number"] for it in pool) == avant


def test_la_repondersion_ordonne_le_pool_sans_le_desordonner():
    pool = [_item(1, family=ZONE_A), _item(2, family=ZONE_B)]
    ordre_avant = [it["number"] for it in pool]
    pig.apply_belt_weights(pool, rng=random.Random(1), closed_issues=[],
                           now=NOW)
    assert sorted(it["number"] for it in pool) == sorted(ordre_avant)


def test_une_erreur_de_lecture_est_reportee_comme_non_mesuree():
    """Une recompense non lue n'est pas un zero de fermeture : elle est
    NON MESUREE, et le rapport le dit."""
    pool = [_item(1, family=ZONE_A)]
    signal = pig.apply_belt_weights(pool, rng=random.Random(1),
                                    closed_error="gh a echoue", now=NOW)
    assert signal["measured"] is False
    assert signal["error"] == "gh a echoue"


def test_le_prior_de_consolidation_s_applique_meme_sans_lecture():
    """Le prior ne depend d'aucune lecture reseau : il s'applique quand
    meme quand le bandit ne peut pas jouer."""
    pool = [_item(1, family=ZONE_A, labels=["consolidation"])]
    signal = pig.apply_belt_weights(pool, rng=random.Random(1),
                                    closed_error="gh a echoue", now=NOW)
    assert signal["classes"]["consolidation"] == 1
    assert pool[0]["belt_score_class"] == "consolidation"


def test_le_score_est_publie_sur_le_grain():
    pool = [_item(1, family=ZONE_A)]
    pig.apply_belt_weights(pool, rng=random.Random(1), closed_issues=[],
                           now=NOW)
    assert pool[0]["bandit_arm"] == "zone:" + ZONE_A
    assert pool[0]["belt_score"] > 0


# --- la cle de tri -----------------------------------------------------------


def _detail(item, thetas=None, mean=0.5, open_count=0):
    return pig.belt_score(item, thetas or {"zone:" + ZONE_A: mean}, mean,
                           open_count)


def test_le_grain_de_consolidation_passe_devant_un_grain_neutre():
    """Le prior de consolidation doit etre VISIBLE dans l'ordre : c'est la
    demande du mandat, et la mesure 3 du 07/11 (0 issue de consolidation
    sur 50 tirages) en montrait l'absence."""
    neutre = _item(1, family=ZONE_A, created="2020-01-01T00:00:00Z")
    consolidation = _item(2, family=ZONE_A, labels=["consolidation"],
                          created="2026-11-01T00:00:00Z")
    assert pig.belt_weight_key(consolidation, _detail(consolidation), now=NOW) < \
        pig.belt_weight_key(neutre, _detail(neutre), now=NOW)


def test_le_prior_ne_se_laisse_pas_annuler_par_une_zone_sterile():
    """Le prior pese en POTS, pas en rang dur (#25082, revue du 07/11) : a
    zone egale, un grain de consolidation passe devant un grain neutre
    (l'assertion de la cle ci-dessous), mais une zone qui ferme nettement
    mieux fait passer SES neutres devant la consolidation d'une zone
    sterile -- c'est le bandit qui fait son travail, et c'est voulu. Un
    rang lexicographique (tout prioritaire devant tout neutre) vidait la
    tete de sa variete : 45/50 grains de tier 0 au rejeu du 07/11."""
    sterile = _item(1, family=ZONE_A)
    neutre_bon = _item(2, family=ZONE_B,
                       last_visit="2026-11-06T00:00:00Z")
    # visites recentes (< 48 h) : NON dues, la garde legacy[0] ne tranche
    # pas -- c'est le POT qui decide, sinon le test mesurerait #22500.
    consolidation_sterile = _item(3, family=ZONE_A, labels=["consolidation"],
                                  last_visit="2026-11-07T00:00:00Z")
    neutre_meme_zone = _item(4, family=ZONE_A, created="2020-01-01T00:00:00Z",
                             last_visit="2026-11-07T00:00:00Z")
    consolidation_egale = _item(5, family=ZONE_A,
                                labels=["consolidation"],
                                last_visit="2026-11-07T00:00:00Z")
    thetas = {"zone:" + ZONE_A: 0.05, "zone:" + ZONE_B: 0.9}
    assert pig.belt_sort_key(neutre_bon, now=NOW)[0] == \
        pig.belt_sort_key(consolidation_sterile, now=NOW)[0] == 2
    # (a) la zone qui ferme 18x mieux fait passer son neutre devant la
    # consolidation sterile : le pot (log2 rel + log2 prior) le permet.
    assert pig.belt_weight_key(neutre_bon, _detail(neutre_bon, thetas),
                               now=NOW) < \
        pig.belt_weight_key(consolidation_sterile,
                            _detail(consolidation_sterile, thetas), now=NOW)
    assert _detail(sterile, thetas)["bucket"] < _detail(neutre_bon, thetas)["bucket"]
    # (b) a zone EGALE, le prior de consolidation reste visible dans l'ordre.
    assert pig.belt_weight_key(consolidation_egale,
                               _detail(consolidation_egale, thetas),
                               now=NOW) < \
        pig.belt_weight_key(neutre_meme_zone,
                            _detail(neutre_meme_zone, thetas), now=NOW)


def test_changer_le_facteur_change_l_ordre():
    """Le facteur du prior PESE dans l'ordre (revue du 07/11, test (c)) :
    x3 met la consolidation devant un neutre deux fois mieux servi par sa
    zone ; a x2 les pots s'egalisent et c'est la ligne de temps qui
    tranche. Si le facteur ne changeait plus l'ordre, il serait decoratif."""
    consolidation = _item(1, family=ZONE_A, labels=["consolidation"],
                          last_visit="2026-11-07T00:00:00Z")
    neutre = _item(2, family=ZONE_B,
                   last_visit="2026-11-06T00:00:00Z")
    thetas = {"zone:" + ZONE_A: 0.25, "zone:" + ZONE_B: 0.5}
    assert pig.belt_sort_key(neutre, now=NOW)[0] == \
        pig.belt_sort_key(consolidation, now=NOW)[0] == 2
    # rel_A/rel_B = 0.5 : le neutre vaut +1 pot de zone ; le prior x3
    # (~+1,58 pot) met la consolidation devant.
    assert pig.belt_weight_key(consolidation, _detail(consolidation, thetas),
                               now=NOW) < \
        pig.belt_weight_key(neutre, _detail(neutre, thetas), now=NOW)
    # Le meme pool sous un prior x2 : +1 pot exactement, l'egalite rend la
    # main a la ligne de temps -- le neutre, visite plus anciennement, passe.
    orig = pig.CONSOLIDATION_PRIOR
    try:
        pig.CONSOLIDATION_PRIOR = 2.0
        assert pig.belt_weight_key(neutre, _detail(neutre, thetas),
                                   now=NOW) < \
            pig.belt_weight_key(consolidation, _detail(consolidation, thetas),
                                now=NOW)
    finally:
        pig.CONSOLIDATION_PRIOR = orig


def test_entre_deux_grains_de_meme_pot_la_ligne_du_temps_tranche():
    """Le pot est un entier de log2 : a pot egal, c'est le MOINS visite qui
    passe en tete. Le tapis garde sa ligne de temps."""
    ancien = _item(1, family=ZONE_A, last_visit="2026-01-01T00:00:00Z")
    recent = _item(2, family=ZONE_A, last_visit="2026-11-07T00:00:00Z")
    assert pig.belt_weight_key(ancien, _detail(ancien), now=NOW) < \
        pig.belt_weight_key(recent, _detail(recent), now=NOW)


def test_le_grain_borne_passe_devant_le_conteneur_dans_la_classe_dues():
    """La regle #22500 point 2 tient : dans la classe des consolidations
    dues, un grain borne passe devant un EPIC."""
    grain = _item(1, family=ZONE_A, labels=["consolidation"], klass="grain",
                  created="2026-01-01T00:00:00Z")
    conteneur = _item(2, family=ZONE_A, labels=["consolidation"],
                       klass="umbrella", created="2026-01-01T00:00:00Z")
    assert pig.belt_weight_key(grain, _detail(grain), now=NOW) < \
        pig.belt_weight_key(conteneur, _detail(conteneur), now=NOW)


# --- la composition mesuree --------------------------------------------------


def test_la_composition_compte_les_trois_classes():
    items = [_item(1, labels=["consolidation"]), _item(2, klass="delivered"),
             _item(3, title="[Audit #17073] une partition"),
             _item(4, labels=["bug"])]
    composition = pig.belt_order_composition(items)
    assert composition["consolidation"] == 1
    assert composition["delivered"] == 1
    assert composition["audit_17073"] == 1
    assert composition["priority"] == 2
    assert composition["ratio"] == 0.5


def test_la_composition_d_une_tete_vide_ne_donne_pas_de_ratio():
    composition = pig.belt_order_composition([])
    assert composition["ratio"] is None


def test_la_tete_ponderee_contient_plus_de_grains_prioritaires():
    """Le rejeu de l'acceptance 2, sur un vivier factories : la tete
    ponderee doit porter plus de grains prioritaires que la tete d'avant."""
    pool = []
    for i in range(20):
        pool.append(_item(100 + i, family=ZONE_A,
                          created=f"2026-01-{i + 1:02d}T00:00:00Z"))
    for i in range(6):
        pool.append(_item(200 + i, family=ZONE_B, labels=["consolidation"],
                          created=f"2026-01-{i + 1:02d}T00:00:00Z"))
    signal = pig.apply_belt_weights(pool, rng=random.Random(5),
                                    closed_issues=[], head=10, now=NOW)
    assert signal["weighted_head"]["priority"] > \
        signal["legacy_head"]["priority"]


def test_la_tete_contient_les_neutres_de_la_zone_qui_ferme():
    """Revue du 07/11, test (a) : pool de 100 consolidations et 400 neutres,
    dont une zone qui ferme bien -- la tete de 50 doit contenir des neutres
    de cette zone ET rester majoritairement prioritaire. Sous le rang dur
    (tier 0 = tout grain prioritaire devant tout neutre), les 100
    consolidations occupaient la tete entiere et les neutres disparaissaient
    (45/50 au rejeu du 07/11) : plus de variete, plus de bandit."""
    pool = []
    for i in range(100):  # consolidations d'une zone sterile, non dues
        pool.append(_item(1000 + i, family=ZONE_A,
                          labels=["consolidation"],
                          last_visit="2026-11-07T00:00:00Z"))
    for i in range(380):  # neutres de la meme zone sterile
        pool.append(_item(2000 + i, family=ZONE_A,
                          last_visit="2026-11-07T00:00:00Z"))
    for i in range(20):   # neutres de la zone qui ferme
        pool.append(_item(3000 + i, family=ZONE_B,
                          last_visit="2026-11-07T00:00:00Z"))
    outcomes = {"zone:" + ZONE_A: (0, 6), "zone:" + ZONE_B: (8, 0)}
    with pytest.MonkeyPatch.context() as mp:
        mp.setattr(pig, "arm_outcomes_from_pool", lambda *a, **k: outcomes)
        signal = pig.apply_belt_weights(pool, rng=random.Random(7),
                                        closed_issues=[], head=50, now=NOW)
    head = pool[:50]
    zones_b = [it for it in head if it.get("family") == ZONE_B]
    consolidations = [it for it in head
                      if "consolidation" in it.get("labels", [])]
    assert zones_b, "la tete doit contenir les neutres de la zone qui ferme"
    assert consolidations, "et la consolidation reste servie (pot favorable)"
    assert signal["weighted_head"]["arms"] >= 2


def test_les_classes_de_fraicheur_priment_sur_les_poids():
    """Un poids extreme ne change pas l'ordre des classes de visite.

    Relecture du 11/11 (#24373) : la classe 3 a disparu. L'issue ancienne
    jamais visitee est desormais en classe 2 -- meleee aux items visites.
    La classe reste prioritaire sur le poids (l'item frais de classe 1
    passe devant les deux autres quel que soit le pot) ; a l'interieur de
    la classe 2, c'est le POT qui tranche, comme entre deux items visites.
    """
    recent = _item(1, family=ZONE_A, created="2026-11-06T00:00:00Z")
    visite = _item(2, family=ZONE_A, last_visit="2026-11-07T00:00:00Z")
    ancien = _item(3, family=ZONE_B, created="2020-01-01T00:00:00Z")
    thetas = {"zone:" + ZONE_A: 0.05, "zone:" + ZONE_B: 0.9}
    keys = [pig.belt_weight_key(item, _detail(item, thetas), now=NOW)
            for item in (recent, visite, ancien)]
    assert [key[0] for key in keys] == [1, 2, 2]
    # La classe prime sur le poids : le frais de classe 1 passe devant.
    assert keys[0] < keys[1] and keys[0] < keys[2]
    # Dans la classe 2, le pot tranche : l'ancien, au meilleur pot, passe
    # devant l'item visite.
    assert keys[2] < keys[1]
    assert _detail(ancien, thetas)["bucket"] > _detail(visite, thetas)["bucket"]
