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

import json

import creation_budget as cb
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
    return cb.NotebookCatalog(CATALOG_PATHS)


@pytest.fixture(autouse=True)
def _isoler_l_etat_anti_entropie(monkeypatch, tmp_path):
    """Le cliquet lit un chemin par DEFAUT : l'organe et le tapis sont deux
    processus differents, et un chemin connu les relie.

    Sans cet isolement, un test qui n'ecrit aucun etat lirait l'etat REEL
    de la machine (verdict `RECULE` au 2026-10-28) — et le test passerait
    pour une porte qui n'a rien retenu alors qu'elle en a retenu un.
    `LOCALAPPDATA` isole le chemin par defaut, la variable d'environnement
    surcharge le defaut.
    """
    monkeypatch.delenv(cb.ENV_ANTI_ENTROPY, raising=False)
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))


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
              body="Voir `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-10-Joueur-LLM.ipynb`"),
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


# --- le cliquet anti-entropie (#23175) ---------------------------------------

def _ecrire_etat_anti_entropie(tmp_path, verdict):
    etat = tmp_path / "anti_entropy.json"
    etat.write_text(
        json.dumps({"entrees": {"padding-nommage": {
            "issue": 5081, "valeur": 813, "verdict": verdict}}}),
        encoding="utf-8")
    # L'etat est lu par `cliquet_actif()`, qui fail-OPEN sur un JSON
    # illisible : un etat mal forme ne retient PERSONNE, et le test
    # passerait pour une porte qui n'a rien retenu. On verifie donc que
    # l'etat ecrit est bien lisible par l'organe.
    json.loads(etat.read_text(encoding="utf-8"))
    return etat


def _grain_qui_cree(numeros=1, fichier=None, corps=""):
    """Un grain de CREATION qui nomme le fichier qu'il veut creer."""
    nom = fichier or "MyIA.AI.Notebooks/ML/ML.Net/ML-07-Recommendation.ipynb"
    return issue(number=numeros,
                 title="Add(ml,#19341): carnet ML-07 — systeme de recommandation",
                 body=f"Livrable : `{nom}`\n{corps}")


def test_le_cliquet_retient_un_carnet_au_nom_non_conforme(monkeypatch, catalog,
                                                           tmp_path):
    """Le cliquet de #23175 : quand le chantier de padding RECULE, un
    carnet neuf au nom non conforme est retenu — meme si le budget n'est
    pas depasse.

    Le rang `7` n'est pas zero-pad : la convention du depot est `07`.

    #19341 — `ML-7-Recommendation.ipynb` : c'est le defaut que le renommage
    canonique (`rename_notebooks`) corrigerait — le chantier de padding
    grossirait.
    """
    etat = _ecrire_etat_anti_entropie(tmp_path, "RECULE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None)
    assert 1 in gate
    assert cb.CAUSE_NOM in gate[1]
    assert "zero-pad" in gate[1]


def test_le_cliquet_retient_un_index_en_tete_non_zero_pad(monkeypatch, catalog,
                                                          tmp_path):
    """L'autre moitie du defaut, vue par l'inventaire : un index EN TETE
    a 1 chiffre (`1_OpenAI_Intro`) est `rename_proposed`."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "RECULE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/GenAI/Texte/"
                                       "1_Introduction-OpenAI.ipynb")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None)
    assert 1 in gate
    assert cb.CAUSE_NOM in gate[1]


def test_le_cliquet_ignore_un_nom_conforme(monkeypatch, catalog, tmp_path):
    """Le rang `07` EST conforme : le cliquet ne retient pas ce grain."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "RECULE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-07-Recommendation.ipynb")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None)
    assert gate == {}


def test_le_cliquet_ne_reient_pas_sur_une_ambiguite(monkeypatch, catalog,
                                                     tmp_path):
    """Mesure du 2026-10-28 : 708 des 813 `ambigu` de l'inventaire sont des
    noms a prefixe de serie (`Complexity-02b-...`) que l'inventaire ne sait
    pas lire. Les retenir ecarterait 6 des 11 creations reelles du pool
    pour des noms conformes : l'`ambigu` est une INCERTITUDE, pas un defaut."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "RECULE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(
        fichier="MyIA.AI.Notebooks/Complexity/"
                "Complexity-03e-Barrieres-WordRAM-Python.ipynb")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None)
    assert gate == {}


def test_le_cliquet_ne_juge_pas_sur_un_titre_sans_fichier(monkeypatch, catalog,
                                                           tmp_path):
    """Un issue qui ne nomme pas son fichier ne permet aucun jugement de
    nom : le cliquet ne retient que ce qu'il sait."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "RECULE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [issue(number=1, title="NLP — carnet 7 : classification")]
    gate = cb.creation_gate(pool, catalog=catalog, state=None)
    assert gate == {}


def test_le_cliquet_ignore_un_grain_de_reparation(monkeypatch, catalog, tmp_path):
    """Le cliquet ne retient jamais un grain de reparation."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "RECULE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [issue(number=2, title="Fix(lean,#18408): aligner la prose de ANALYSE-04")]
    assert cb.creation_gate(pool, catalog=catalog, state=None) == {}


def test_sans_etat_anti_entropie_le_cliquet_neretient_rien(catalog):
    """Fail-OPEN : pas de mesure du registre, pas de sanction.

    L'isolement de l'etat par defaut est fait par la fixture
    `_isoler_l_etat_anti_entropie` : ici, aucun etat n'est ecrit.
    """
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    assert cb.creation_gate(pool, catalog=catalog, state=None) == {}


def test_un_verdict_AVANCE_desactive_le_cliquet(monkeypatch, catalog, tmp_path):
    """Quand le chantier avance, le cliquet ne retient plus rien : le
    registre mesure, le cliquet agit sur la mesure."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "AVANCE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    assert cb.creation_gate(pool, catalog=catalog, state=None) == {}


def test_le_cliquet_agit_meme_sans_depassement_de_budget(monkeypatch, catalog,
                                                         tmp_path):
    """Le cliquet est independant du budget : c'est le registre qui
    decide, pas le compteur."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "RECULE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    sous_budget = {"carnets_neufs_demarres": 10, "budget": 50}
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    gate = cb.creation_gate(pool, catalog=catalog, state=sous_budget)
    assert 1 in gate


# --- le cliquet face a une mesure NON COMPARABLE -----------------------------

def test_le_cliquet_suit_le_verdict_de_comparabilite(tmp_path):
    """Le cliquet retient tant qu'on ne peut pas PROUVER que le chantier
    progresse : `RECULE` retient, `STAGNE` retient aussi (rien n'a bouge,
    donc rien n'est prouve), `INSTRUMENT ILLEGIBLE` (mesure non comparable)
    retient, et seul `AVANCE` libere."""
    attendu = {
        "RECULE": True,
        "STAGNE": True,
        "INSTRUMENT ILLEGIBLE": True,
        "PREMIERE MESURE": True,
        "AVANCE": False,
    }
    for verdict, doit_retenir in attendu.items():
        etat = _ecrire_etat_anti_entropie(tmp_path, verdict)
        assert cb.cliquet_actif(str(etat)) is doit_retenir, verdict


def test_une_mesure_non_comparable_retient_un_carnet_au_nom_non_conforme(
        monkeypatch, catalog, tmp_path):
    """Une mesure non comparable retient le carnet neuf non conforme : le
    garde est fail-CLOSED sur la comparabilite, parce que son but est de
    retenir un carnet qui aggrave le chantier."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "INSTRUMENT ILLEGIBLE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    out = cb.creation_gate(pool, catalog=catalog, state=None)
    assert out, "une mesure non comparable doit retenir le carnet"


def test_un_etat_absent_ne_retient_toujours_rien(catalog):
    """L'absence d'etat reste fail-OPEN : le registre n'a rien publie, donc
    il n'a rien a dire sur le chantier."""
    assert cb.cliquet_actif("C:/nonexistent/anti_entropy.json") is False


def test_un_chantier_stagne_retient_un_carnet_au_nom_non_conforme(
        monkeypatch, catalog, tmp_path):
    """`STAGNE` retient aussi : un chantier qui n'a pas bouge n'est pas un
    chantier qui progresse. Un carnet neuf au nom non conforme aggraverait
    une file qui ne recule pas -- c'est exactement ce que le cliquet doit
    retenir."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "STAGNE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    out = cb.creation_gate(pool, catalog=catalog, state=None)
    assert out, "un chantier stagne doit retenir le carnet non conforme"
    assert cb.CAUSE_NOM in out[1]


def test_un_chantier_qui_avance_libere_le_carnet(
        monkeypatch, catalog, tmp_path):
    """Le cliquet ne s'ouvre que sur une preuve : `AVANCE` libere."""
    etat = _ecrire_etat_anti_entropie(tmp_path, "AVANCE")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    out = cb.creation_gate(pool, catalog=catalog, state=None)
    assert not out, "un chantier qui avance ne retient plus personne"


def test_une_comparaison_suspendue_retient_meme_sur_un_verdict_avance(
        monkeypatch, catalog, tmp_path):
    """Le fail-CLOSED doit etre VISIBLE : une comparaison suspendue
    (fenetre de rebasage) ne prouve aucun progres, meme quand le verdict
    affiche dit `AVANCE`. Un lecteur qui ne voit que le verdict doit
    pouvoir constater que rien n'est libere."""
    etat = tmp_path / "anti_entropy.json"
    etat.write_text(
        json.dumps({"entrees": {"padding-nommage": {
            "issue": 5081, "valeur": 38, "verdict": "AVANCE",
            "comparaison_suspendue": True,
            "fenetre": "comparaison de 7 j SUSPENDUE : reference de "
                       "rebasage (2026-10-31) ; elle s'ouvre le 2026-11-07"}}}),
        encoding="utf-8")
    monkeypatch.setenv(cb.ENV_ANTI_ENTROPY, str(etat))
    assert cb.cliquet_actif(str(etat)) is True
    pool = [_grain_qui_cree(fichier="MyIA.AI.Notebooks/ML/ML.Net/"
                                       "ML-7-Recommendation.ipynb")]
    out = cb.creation_gate(pool, catalog=catalog, state=None)
    assert out, "une comparaison suspendue doit retenir le carnet"
