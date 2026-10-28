#!/usr/bin/env python3
"""Tests du regime consolidation (arbitrage user 2026-10-28).

Le regime : tant qu'il tient, un grain tire dont la LIVRAISON est un carnet
neuf se saute ; le plancher G-VAR-1 se tient par une reparation d'un carnet
EXISTANT. Le classement est porte par `scripts/consolidation_regime.py`.

Ce que ces tests verrouillent, dans l'ordre d'importance :

  1. **un grain de REPARATION n'est jamais saute** — c'est la borne de
     securite du regime : sauter un grain de consolidation ferait perdre le
     travail que le regime demande (l'erreur de sens qui coute) ;
  2. un grain de CREATION est saute, avec une preuve citable ;
  3. les cas **indetermines** ne sont PAS sautes (le module ne devine pas) ;
  4. le veto de reparation l'emporte sur l'oracle « fichier absent » — le
     piege mesure : un audit cite un carnet avec un nom approximatif, et
     l'oracle le prendrait pour une creation ;
  5. une umbrella dont une sous-issue est une creation est une creation ;
  6. un catalogue du depot indisponible ne fait sauter PERSONNE.

Les cas sont des MESURES (issues et PRs reelles du 2026-10-28) : chaque
test porte le numero d'origine, pour qu'une regression puisse etre relue
contre la realite et non contre une invention.
"""

import consolidation_regime as cr
import pytest

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
    return cr.NotebookCatalog(CATALOG_PATHS)


def issue(number=1, title="", body="", labels=None):
    return {"number": number, "title": title, "body": body, "labels": labels or []}


# --- O1 : serie + rang contre l'etat du depot --------------------------------

def test_rang_deja_livre_vient_existant(catalog):
    """Le rang 28 de Serre 100 est livre : le grain parle d'un carnet
    EXISTANT, il ne doit pas etre saute."""
    verdict, why = cr.classify(
        issue(title="Serre 100 — carnet 28 : inversion de Möbius"),
        catalog)
    assert verdict == cr.VERDICT_EXISTING
    assert "28" in why


def test_rang_absent_vient_neuf(catalog):
    """#23123 — « NLP — carnet 07 » : le rang n'existe pas sur main."""
    verdict, why = cr.classify(
        issue(title="NLP — carnet 07 : classification de texte Naive Bayes"),
        catalog)
    assert verdict == cr.VERDICT_NEW
    assert "07" in why


def test_rang_a_serie_inconnue_ne_dit_rien(catalog):
    """Une serie absente du depot ne permet aucune conclusion."""
    verdict, _ = cr.classify(issue(title="Serie-Inconnue -- carnet 07 : x"), catalog)
    assert verdict == cr.VERDICT_UNKNOWN


# --- O2 : fichier cite absent du depot ---------------------------------------

def test_fichier_cite_absent_vient_neuf(catalog):
    """#22704 — le titre annonce la creation, le corps nomme le fichier a
    creer : le fichier n'existe pas dans le depot -> creation."""
    verdict, why = cr.classify(
        issue(title="Add(nlp,#22704): carnet 08 — word2vec from scratch",
              body="Livrable : `MyIA.AI.Notebooks/NLP/08-Word2Vec-CBOW-SkipGram.ipynb`"),
        catalog)
    assert verdict == cr.VERDICT_NEW
    assert "08-Word2Vec-CBOW-SkipGram.ipynb" in why


def test_fichier_cite_absent_sans_intention_de_creation_nest_pas_saute(catalog):
    """#14926 — un issue d'outillage cite un carnet au nom approximatif : ce
    n'est pas une creation, et l'issue ne doit pas disparaitre du tapis."""
    verdict, _ = cr.classify(
        issue(title="claudish: la cle cliente du proxy n'a aucun organe de propagation",
              body="Voir `MyIA.AI.Notebooks/GameTheory/GameTheory-03c-Le-Joueur-LLM.ipynb`"),
        catalog)
    assert verdict != cr.VERDICT_NEW


def test_fichier_cite_avec_suffixe_vient_existant(catalog):
    """Le nom cite est approximatif : le depot porte `02-Ngrammes-Python.ipynb`
    et l'issue cite `02-Ngrammes.ipynb`. Ce n'est PAS une creation."""
    verdict, _ = cr.classify(
        issue(body="Le carnet `MyIA.AI.Notebooks/NLP/02-Ngrammes.ipynb` est vise."),
        catalog)
    assert verdict != cr.VERDICT_NEW


# --- le veto de reparation ---------------------------------------------------

def test_audit_qui_cite_un_carnet_absent_nest_pas_saute(catalog):
    """#18556 — « [Audit #17073] Serie Infer — partition Hermes » cite un
    carnet dont le nom ne correspond a aucun fichier du depot : c'est un
    audit, pas une creation. Le veto l'emporte."""
    verdict, _ = cr.classify(
        issue(title="[Audit #17073] Serie Infer — partition Hermes",
              body="`MyIA.AI.Notebooks/Probas/Infer/Infer-1-Setup.ipynb` est cite."),
        catalog)
    assert verdict == cr.VERDICT_EXISTING


def test_correction_de_prose_nest_pas_saute(catalog):
    verdict, _ = cr.classify(
        issue(title="Fix(lean,#18408): aligner la prose de ANALYSE-04"), catalog)
    assert verdict == cr.VERDICT_EXISTING


# --- O3 : la phrase de creation ----------------------------------------------

def test_phrase_de_creation_vient_neuf(catalog):
    """#22617 — « Serre 100 — carnet 30 » : le rang 30 est absent du depot.

    L'oracle du depot passe AVANT la prose : la raison rendue est celle du
    depot, pas celle de la phrase du corps."""
    verdict, why = cr.classify(
        issue(title="Serre 100 — carnet 30 : fonction de partition p(n)",
              body="Slot: **palier 30** — premier numero libre de la serie."),
        catalog)
    assert verdict == cr.VERDICT_NEW
    assert "30" in why


def test_phrase_de_creation_sans_rang_vient_neuf(catalog):
    """Sans serie ni rang resolvable, la phrase de creation est le seul
    indice : elle suffit (#17883 — « Decisions typees systeme 1 »)."""
    verdict, why = cr.classify(
        issue(title="[GenAI/Texte] Decisions typees « systeme 1 »",
              body="Livrable : un carnet neuf de distillation."),
        catalog)
    assert verdict == cr.VERDICT_NEW
    assert "declare" in why


def test_le_depot_prime_sur_une_prose_perimee(catalog):
    """#21799 — « [GameTheory] 11c » : le rang 11c est desormais LIVRE sur
    `main`, le grain n'est plus une creation meme si son corps date d'une
    annonce de creation. Le depot est l'etat courant, la prose est datee de
    sa redaction."""
    verdict, why = cr.classify(
        issue(title="Serre 100 — carnet 28 : inversion de Mobius",
              body="Slot: palier 28 — premier numero libre de la serie."),
        catalog)
    assert verdict == cr.VERDICT_EXISTING
    assert "28" in why


def test_collision_d_identifiant_nest_pas_saute(catalog):
    """#22056 — « Collision d'identifiant 04-17 dans GenAI/Audio » : la
    livraison est une RENUMEROTATION de carnets existants, c'est un grain
    de consolidation. Le veto l'emporte sur la phrase « Slot: » du corps,
    qui decrit la cause de la collision et non l'intention du grain."""
    verdict, _ = cr.classify(
        issue(title="Collision d'identifiant 04-17 dans GenAI/Audio/04-Applications",
              body="Le corps de #21441 dit « Slot: palier 17 ... max+1 de la serie »."),
        catalog)
    assert verdict == cr.VERDICT_EXISTING


def test_accretion_d_un_carnet_existant_vient_neuf(catalog):
    """#22125 — « Search-03g » : l'accretion EST une creation (le fichier
    03g n'existe pas) ; le veto « reparation » ne doit pas la capturer."""
    verdict, why = cr.classify(
        issue(title="Search-03g : la memoire n'est jamais mesuree dans la serie Search",
              body="`Search-03g` (accretion de Search-03) mesure le pic de frontiere."),
        catalog)
    assert verdict == cr.VERDICT_NEW
    assert "03g" in why


def test_une_quantite_en_prose_nest_pas_un_rang(catalog):
    """#21871 — « ... le PDF archive, et le PDF a ete archive 11 jours apres
    la PR » : le « 11 » est une DUREE, pas un rang de carnet. Sans la garde
    d'unite, la serie « archive » et le rang « 11 » etaient resolus, et ce
    grain d'AUDIT sur un carnet existant etait ecarte du tapis — un faux
    positif du regime, c'est-a-dire la perte d'un grain de consolidation."""
    verdict, why = cr.classify(
        issue(title="[Distillation] trefle (#19590) : l'« ancrage theorique "
                    "Milnor » est absent du PDF archive, et le PDF a ete "
                    "archive 11 jours apres la PR"),
        catalog)
    assert verdict == cr.VERDICT_UNKNOWN
    assert "livrable non nomme" in why


# --- l'umbrella n'est pas un grain -------------------------------------------

def test_umbrella_nest_pas_saute_meme_si_une_sous_issue_cree(catalog):
    """Une EPIC qui cite une sous-issue de creation n'est PAS sajee.

    Mesure du 2026-10-28 : l'oracle d'umbrella a cascade -- l'EPIC qui cite
    une EPIC qui cite une sous-issue de creation herite du classement, et
    **plus de 60 EPIC du depot** ont ete ainsi retournees, dont des EPIC de
    gouvernance (« Les body d'Epic ne sont jamais reecrits »). Une cascade
    est une machine a faux positifs, et l'EPIC n'est pas un grain : la regle
    du tapis dit « un EPIC en tete se sert par un sous-grain ».
    """
    umbrella = issue(number=900, title="[EPIC] Serie Physique numerique — distillations",
                     body="Tranches : #901 (Jauge-01). "
                          "Livrable : `MyIA.AI.Notebooks/Physique/Jauge/Jauge-01-Noether-Python.ipynb`")
    verdict, _ = cr.classify(umbrella, catalog)
    assert verdict != cr.VERDICT_NEW


# --- le filtre de pool -------------------------------------------------------

def test_le_filtre_ecarte_la_creation_et_garde_la_reparation(catalog):
    pool = [
        issue(number=10, title="NLP — carnet 07 : classification de texte"),
        issue(number=11, title="Fix(lean,#18408): aligner la prose de ANALYSE-04"),
        issue(number=12, title="[Audit #17073] Serie Infer — partition Hermes",
             body="`MyIA.AI.Notebooks/Probas/Infer/Infer-1-Setup.ipynb`"),
    ]
    kept, skipped = cr.filter_pool(pool, catalog)
    assert [it["number"] for it in kept] == [11, 12]
    assert [it["number"] for it, _, _ in skipped] == [10]


def test_un_catalogue_inconnu_ne_fait_sauter_personne():
    """Un `git` muet ne doit pas vider le tapis : rien n'est saute, et le
    motif dit pourquoi."""
    vide = cr.NotebookCatalog([])
    pool = [issue(number=20, title="NLP — carnet 07 : classification de texte")]
    kept, skipped = cr.filter_pool(pool, vide)
    assert skipped == []
    assert len(kept) == 1


def test_un_candidat_indetermine_nest_pas_saute(catalog):
    pool = [issue(number=30, title="GameTheory: jeux globaux — selection d'equilibre")]
    kept, skipped = cr.filter_pool(pool, catalog)
    assert skipped == []
    assert len(kept) == 1
