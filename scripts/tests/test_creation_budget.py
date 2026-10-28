#!/usr/bin/env python3
"""Tests du budget de creation (#23174).

Le regime : tant qu'il tient, un grain de CREATION ne peut pas etre servi
quand le compteur de carnets neufs demarres par la flotte sur 7 jours
glissants depasse un budget DERIVE d'une mesure. Un grain de REPARATION
n'est jamais ecarte : c'est la borne de securite du regime.

Ce que ces tests verrouillent, par ordre d'importance :

  1. **un grain de REPARATION n'est jamais ecarte** — sauter un grain de
     consolidation ferait perdre le travail que le regime demande ;
  2. la **derive** du budget (part de creation du pool x grains livres) et
     son plancher de 1 : le regime ralentit, il n'arrete pas ;
  3. le **fail-OPEN** : un etat absent, illisible ou mal forme n'ecarte
     personne ;
  4. l'**EPIC est un conteneur** : un EPIC qui a une fille de reparation
     n'est jamais ecarte, meme si toutes les autres creent ;
  5. les cas **indetermines** ne sont PAS ecartes (le module ne devine pas).

Les cas sont des MESURES (issues et PRs reelles du 2026-10-28) : chaque
test porte le numero d'origine, pour qu'une regression puisse etre relue
contre la realite et non contre une invention.
"""

import pytest

import creation_budget as cb


# --- catalogue de test : trois series, quatre carnets ------------------------
CATALOG_PATHS = [
    "MyIA.AI.Notebooks/NLP/01-Introduction-Python.ipynb",
    "MyIA.AI.Notebooks/NLP/02-Ngrammes-Python.ipynb",
    "MyIA.AI.Notebooks/NLP/06-BM25-Python.ipynb",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/20b-groupes-abeliens.ipynb",
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/28-mobius-inversion.ipynb",
    "MyIA.AI.Notebooks/GameTheory/GameTheory-11b-Jeux-Iteres-Python.ipynb",
    "MyIA.AI.Notebooks/Search/Part1-Foundations/03-Informed-Python.ipynb",
    "MyIA.AI.Notebooks/Archive/07-ancien-carnet.ipynb",
]


@pytest.fixture
def catalog():
    return cb.NotebookCatalog(CATALOG_PATHS)


def issue(number=1, title="", body="", labels=None, parent=None):
    return {"number": number, "title": title, "body": body,
            "labels": labels or [], "parent": parent}


# --- la livraison : le depot contre l'issue -----------------------------------

def test_rang_deja_livre_vient_existant(catalog):
    """Le rang 28 de Serre 100 est livre : le grain parle d'un carnet
    EXISTANT, il ne doit pas etre ecarte."""
    verdict, why = cb.classify_delivery(
        issue(title="Serre 100 — carnet 28 : inversion de Möbius"), catalog)
    assert verdict == cb.DELIVERY_EXISTING
    assert "28" in why


def test_rang_absent_vient_neuf(catalog):
    """#23123 — « NLP — carnet 07 » : le rang n'existe pas sur main."""
    verdict, why = cb.classify_delivery(
        issue(title="NLP — carnet 07 : classification de texte Naive Bayes"), catalog)
    assert verdict == cb.DELIVERY_NEW
    assert "07" in why


def test_rang_a_serie_inconnue_ne_dit_rien(catalog):
    verdict, _ = cb.classify_delivery(
        issue(title="Serie-Inconnue -- carnet 07 : x"), catalog)
    assert verdict == cb.DELIVERY_UNKNOWN


def test_fichier_cite_absent_vient_neuf(catalog):
    """#22704 — le titre annonce la creation, le corps nomme le fichier a
    creer : le fichier n'existe pas dans le depot -> creation."""
    verdict, why = cb.classify_delivery(
        issue(title="Add(nlp,#22704): carnet 08 — word2vec from scratch",
              body="Livrable : `MyIA.AI.Notebooks/NLP/08-Word2Vec-CBOW-SkipGram.ipynb`"),
        catalog)
    assert verdict == cb.DELIVERY_NEW
    assert "08-Word2Vec-CBOW-SkipGram.ipynb" in why


def test_fichier_cite_absent_sans_intention_de_creation_nest_pas_saute(catalog):
    """#14926 — un issue d'outillage cite un carnet au nom approximatif : ce
    n'est pas une creation, et l'issue ne doit pas disparaitre du tapis."""
    verdict, _ = cb.classify_delivery(
        issue(title="claudish: la cle cliente du proxy n'a aucun organe de propagation",
              body="Voir `MyIA.AI.Notebooks/GameTheory/GameTheory-03c-Le-Joueur-LLM.ipynb`"),
        catalog)
    assert verdict != cb.DELIVERY_NEW


def test_fichier_cite_avec_suffixe_vient_existant(catalog):
    """Le nom cite est approximatif : le depot porte `02-Ngrammes-Python.ipynb`
    et l'issue cite `02-Ngrammes.ipynb`. Ce n'est PAS une creation."""
    verdict, _ = cb.classify_delivery(
        issue(body="Le carnet `MyIA.AI.Notebooks/NLP/02-Ngrammes.ipynb` est vise."),
        catalog)
    assert verdict != cb.DELIVERY_NEW


def test_audit_qui_cite_un_carnet_absent_nest_pas_saute(catalog):
    """#18556 — « [Audit #17073] Serie Infer — partition Hermes » cite un
    carnet dont le nom ne correspond a aucun fichier du depot : c'est un
    audit, pas une creation. Le veto l'emporte."""
    verdict, _ = cb.classify_delivery(
        issue(title="[Audit #17073] Serie Infer — partition Hermes",
              body="`MyIA.AI.Notebooks/Probas/Infer/Infer-1-Setup.ipynb` est cite."),
        catalog)
    assert verdict == cb.DELIVERY_EXISTING


def test_correction_de_prose_nest_pas_saute(catalog):
    verdict, _ = cb.classify_delivery(
        issue(title="Fix(lean,#18408): aligner la prose de ANALYSE-04"), catalog)
    assert verdict == cb.DELIVERY_EXISTING


def test_phrase_de_creation_sans_rang_vient_neuf(catalog):
    """Sans serie ni rang resolvable, la phrase de creation est le seul
    indice : elle suffit (#17883 — « Decisions typees systeme 1 »)."""
    verdict, why = cb.classify_delivery(
        issue(title="[GenAI/Texte] Decisions typees « systeme 1 »",
              body="Livrable : un carnet neuf de distillation."), catalog)
    assert verdict == cb.DELIVERY_NEW
    assert "declare" in why


def test_le_depot_prime_sur_une_prose_perimee(catalog):
    """#21799 — « [GameTheory] 11c » : le rang 11c est desormais LIVRE sur
    `main`, le grain n'est plus une creation meme si son corps date d'une
    annonce de creation. Le depot est l'etat courant, la prose est datee de
    sa redaction."""
    verdict, why = cb.classify_delivery(
        issue(title="Serre 100 — carnet 28 : inversion de Mobius",
              body="Slot: palier 28 — premier numero libre de la serie."), catalog)
    assert verdict == cb.DELIVERY_EXISTING
    assert "28" in why


def test_collision_d_identifiant_nest_pas_saute(catalog):
    """#22056 — « Collision d'identifiant 04-17 dans GenAI/Audio » : la
    livraison est une RENUMEROTATION de carnets existants, c'est un grain
    de consolidation. Le veto l'emporte sur la phrase « Slot: » du corps,
    qui decrit la cause de la collision et non l'intention du grain."""
    verdict, _ = cb.classify_delivery(
        issue(title="Collision d'identifiant 04-17 dans GenAI/Audio/04-Applications",
              body="Le corps de #21441 dit « Slot: palier 17 ... max+1 de la serie »."),
        catalog)
    assert verdict == cb.DELIVERY_EXISTING


def test_accretion_d_un_carnet_existant_vient_neuf(catalog):
    """#22125 — « Search-03g » : l'accretion EST une creation (le fichier
    03g n'existe pas) ; le veto « reparation » ne doit pas la capturer."""
    verdict, why = cb.classify_delivery(
        issue(title="Search-03g : la memoire n'est jamais mesuree dans la serie Search",
              body="`Search-03g` (accretion de Search-03) mesure le pic de frontiere."),
        catalog)
    assert verdict == cb.DELIVERY_NEW
    assert "03g" in why


def test_une_quantite_en_prose_nest_pas_un_rang(catalog):
    """#21871 — « ... le PDF archive, et le PDF a ete archive 11 jours apres
    la PR » : le « 11 » est une DUREE, pas un rang de carnet. Sans la garde
    d'unite, la serie « archive » et le rang « 11 » etaient resolus, et ce
    grain d'AUDIT sur un carnet existant etait ecarte du tapis — un faux
    positif du regime, c'est-a-dire la perte d'un grain de consolidation."""
    verdict, why = cb.classify_delivery(
        issue(title="[Distillation] trefle (#19590) : l'« ancrage theorique "
                    "Milnor » est absent du PDF archive, et le PDF a ete "
                    "archive 11 jours apres la PR"), catalog)
    assert verdict == cb.DELIVERY_UNKNOWN
    assert "livrable non nomme" in why


# --- le grain de creation ----------------------------------------------------

def test_un_grain_neuf_est_un_grain_de_creation(catalog):
    verdict, _ = cb.classify_grain(
        issue(title="NLP — carnet 07 : classification de texte"), catalog, [])
    assert verdict == cb.VERDICT_CREATION


def test_un_grain_de_reparation_nest_jamais_un_grain_de_creation(catalog):
    verdict, _ = cb.classify_grain(
        issue(title="Fix(lean,#18408): aligner la prose de ANALYSE-04"), catalog, [])
    assert verdict != cb.VERDICT_CREATION


def test_umbrella_sans_fille_nest_ecartee(catalog):
    """Un conteneur sans fille ouverte n'a rien a servir : il n'est ni de
    creation ni de reparation."""
    verdict, _ = cb.classify_grain(
        issue(number=900, title="[EPIC] Serie Physique numerique — distillations"),
        catalog, [])
    assert verdict == cb.VERDICT_NEUTRAL


def test_umbrella_a_fille_de_reparation_nest_jamais_ecarte(catalog):
    """#23161 et ses voisines : un EPIC qui a UNE fille de reparation ne
    peut pas etre ecarte — le servir ne sert QUE de la reparation. C'est la
    regle de l'issue portee au sous-grain effectif."""
    fille_reparation = issue(number=901, title="Fix(lean,#18408): corriger la prose",
                             parent=900)
    epic = issue(number=900, title="[EPIC] Serie Physique numerique — distillations")
    verdict, why = cb.classify_grain(epic, catalog, [epic, fille_reparation])
    assert verdict != cb.VERDICT_CREATION
    assert "reparation" in why


def test_umbrella_a_filles_toutes_creatrices_est_un_grain_de_creation(catalog):
    fille1 = issue(number=901, title="NLP — carnet 07 : classification", parent=900)
    fille2 = issue(number=902, title="NLP — carnet 08 : regression logistique", parent=900)
    epic = issue(number=900, title="[EPIC] Serie NLP — extensions")
    verdict, why = cb.classify_grain(epic, catalog, [epic, fille1, fille2])
    assert verdict == cb.VERDICT_CREATION
    assert "2 fille(s) de creation" in why


def test_une_proposition_compte_meme_si_l_epic_a_une_fille_de_reparation(catalog):
    """La PROPOSITION (ce que le pool propose) et la PORTE (ce que servir
    produirait) ne sont pas la meme chose. Un EPIC qui propose de la
    creation reste une proposition de creation — meme si une de ses filles
    est une reparation : c'est cette seconde mesure qui regit la porte."""
    epic = issue(number=900, title="[EPIC] Serie NLP — extensions")
    fille = issue(number=901, title="Fix(lean,#18408): corriger la prose", parent=900)
    pool = [epic, fille]
    propositions = cb.creation_proposals(pool, catalog)
    assert [it["number"] for it in propositions] == [900]
    assert cb.classify_grain(epic, catalog, pool)[0] == cb.VERDICT_REPAIR


def test_un_epic_consolidation_ne_propose_pas_de_creation(catalog):
    """Un EPIC porte le label `consolidation` : il ne propose pas de
    creation, quelle que soit sa fille."""
    epic = issue(number=900, title="[EPIC] Serie NLP — extensions",
                 labels=["epic", "consolidation"])
    fille = issue(number=901, title="NLP — carnet 07 : classification", parent=900)
    pool = [epic, fille]
    propositions = [it["number"] for it in cb.creation_proposals(pool, catalog)]
    assert 900 not in propositions  # l'EPIC consolide ne propose pas de creation
    assert cb.classify_grain(epic, catalog, pool)[0] != cb.VERDICT_CREATION


def test_un_grain_consolidation_nest_jamais_ecarte(catalog):
    """#23175 — le CONTROLE NEGATIF de l'issue : « aucune issue de
    `consolidation` ou de correction ne peut etre ecarte ». Le label
    `consolidation` l'emporte donc sur la phrase de creation : ce grain
    cree un ORGANE, pas un carnet, et son corps parle de « carnet »."""
    grain = issue(number=23175, labels=["consolidation"],
                  title="Registre anti-entropie : les issues qui gardent le "
                        "depot digerable",
                  body="Le registre suit les carnets et leur derivance.")
    verdict, why = cb.classify_grain(grain, catalog, [grain])
    assert verdict != cb.VERDICT_CREATION
    assert "consolidation" in why
    assert [it["number"] for it in cb.creation_proposals([grain], catalog)] == []


def test_un_cycle_de_rattachement_ne_boucle_pas(catalog):
    """Le graphe des parents est declare par les issues : il peut contenir
    une boucle. Sans garde, la recursion ne s'arrete jamais."""
    a = issue(number=1, title="[EPIC] Conteneur A")
    b = issue(number=2, title="[EPIC] Conteneur B")
    a["parent"] = 2
    b["parent"] = 1
    verdict, _ = cb.classify_grain(a, catalog, [a, b])
    assert verdict in (cb.VERDICT_CREATION, cb.VERDICT_REPAIR, cb.VERDICT_NEUTRAL)


# --- la derive du budget -----------------------------------------------------

def test_le_budget_se_derive_de_la_part_de_creation(catalog):
    """budget = part_creation x grains livres la semaine ecoulee."""
    pool = [
        issue(number=10, title="NLP — carnet 07 : classification de texte"),
        issue(number=11, title="Fix(lean,#18408): aligner la prose de ANALYSE-04"),
        issue(number=12, title="NLP — carnet 08 : regression logistique"),
    ]
    budget, preuve = cb.derive_budget(pool, 100, catalog)
    assert preuve["pool_ouvert"] == 3
    assert preuve["propositions_creation"] == 2
    assert preuve["part_creation"] == pytest.approx(2 / 3, abs=1e-3)
    assert budget == 67  # round(2/3 * 100)


def test_le_budget_a_un_plancher_de_un(catalog):
    """Le regime RALENTIT la creation, il ne l'ARRETE pas : meme sans aucun
    grain de creation propose, le budget ne descend pas sous 1."""
    pool = [issue(number=11, title="Fix(lean,#18408): aligner la prose")]
    budget, preuve = cb.derive_budget(pool, 100, catalog)
    assert budget == 1
    assert preuve["budget_brut"] == 0
    assert preuve["plancher_applique"] is True


# --- l'etat et le fail-OPEN --------------------------------------------------

def test_sans_etat_personne_n_est_ecarte():
    """Un compteur qui n'a pas tourne ne doit pas vider le tapis."""
    trop, why = cb.over_budget(None)
    assert trop is False
    assert "indisponible" in why


def test_un_etat_mal_forme_n_ecarte_personne():
    trop, why = cb.over_budget({"carnets_neufs_demarres": "beaucoup"})
    assert trop is False
    assert "illisible" in why


def test_le_budget_dependant_de_l_etat():
    trop, why = cb.over_budget({"carnets_neufs_demarres": 125, "budget": 50})
    assert trop is True
    assert "125" in why and "50" in why
    trop, why = cb.over_budget({"carnets_neufs_demarres": 40, "budget": 50})
    assert trop is False


def test_l_etat_est_absent_par_defaut(monkeypatch):
    """La variable d'environnement n'est pas posee par defaut : aucune lane
    n'ecarte rien tant que le coordinateur n'a pas pose l'etat."""
    monkeypatch.delenv(cb.ENV_STATE, raising=False)
    assert cb.state_path() is None
    assert cb.load_state() is None
