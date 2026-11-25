"""Tests du registre des corpus open access (#26911, tranche 1).

Le registre est un artefact de **droits**, pas de donnees : ces tests
envoient quatre signaux distincts, parce que quatre erreurs sont possibles.

1. Un champ de droits vide : le corpus serait utilise sans etre autorise.
2. Une taille non mesuree : la taille serait une impression.
3. Un echantillon copie dans le depot : le corpus lui-meme n'a pas sa place
   dans un depot public, et la bibliographie_shared interdit la recopie.
4. Un statut pose sans motif : l'ecarte serait inexplique.

Le test ne verifie pas la verite des chiffres — il verifie que chaque chiffre
porte la source d'ou il a ete lu, et que le registre respecte ses regles.
"""

from __future__ import annotations

import dataclasses

import pytest

from ict.corpus_registry import (
    ACCES_TELECHARGEMENT,
    CANDIDATS,
    LONGUEUR_MAX_CHAMP,
    par_cle,
    plan_acces,
    retenus,
)

#: Licences acceptees comme identifiants SPDX par l'hebergeur.
SPDX_ATTENDUS = {
    "cc-by-2.0",
    "cc-by-4.0",
    "cc-by-sa-4.0",
    "apache-2.0",
    "mit",
    "other",
}

#: Champs textuels qui doivent porter l'information de droits.
CHAMPS_DROITS = ("licence", "conditions", "redistribution", "provenance")


def test_le_registre_nest_pas_vide():
    """Le registre doit contenir des candidats reels."""
    assert len(CANDIDATS) >= 5


def test_les_cles_sont_uniques():
    """Deux corpus ne peuvent pas partager la meme cle."""
    cles = [c.cle for c in CANDIDATS]
    assert len(cles) == len(set(cles))


def test_les_quatre_champs_de_droits_sont_renseignes():
    """Chaque corpus porte licence, conditions, redistribution et provenance."""
    for candidat in CANDIDATS:
        for champ in CHAMPS_DROITS:
            valeur = getattr(candidat, champ)
            assert valeur and valeur.strip(), f"{candidat.cle} : {champ} vide"


def test_chaque_droit_porte_une_source():
    """Un fait sans source n'est pas un fait : chaque porte de droit a une source."""
    for candidat in CANDIDATS:
        for champ in ("licence_source", "provenance_source", "taille_source"):
            valeur = getattr(candidat, champ)
            assert valeur and valeur.strip(), f"{candidat.cle} : {champ} vide"
            assert len(valeur) >= 20, f"{candidat.cle} : {champ} trop court pour etre une source"


def test_les_sources_de_licence_et_de_taille_sont_ancrees_sur_une_url():
    """Licence et taille sont lues chez l'hebergeur : leur source est une URL."""
    for candidat in CANDIDATS:
        assert "http" in candidat.licence_source, candidat.cle
        assert "http" in candidat.taille_source, candidat.cle


def test_la_licence_est_un_identifiant_connu():
    """Les licences declarees sont des identifiants SPDX, pas des phrases."""
    for candidat in CANDIDATS:
        assert candidat.licence in SPDX_ATTENDUS, candidat.cle


def test_la_taille_est_uneure_et_mesuree():
    """La taille est un entier positif, mesure et date."""
    for candidat in CANDIDATS:
        assert candidat.taille_lignes > 0, candidat.cle
        assert "2026-11-16" in candidat.taille_source, candidat.cle


def test_un_seul_corpus_est_retenu_et_c_est_un_corpus_d_humour():
    """Le registre designe un corpus de travail unique, pour l'humour."""
    retenus_local = retenus()
    assert len(retenus_local) == 1, [c.cle for c in retenus_local]
    assert "humor" in retenus_local[0].cle.lower()


def test_le_corpus_retenu_publie_une_publication_archivee():
    """Le corpus retenu doit avoir sa publication dans le gisement partage."""
    for candidat in retenus():
        assert candidat.publication_archivee
        assert "Bibliographie IA" in candidat.publication_archivee


def test_chaque_candidat_a_un_motif():
    """Aucun statut n'est pose sans dire pourquoi."""
    for candidat in CANDIDATS:
        assert candidat.motif and candidat.motif.strip(), candidat.cle


def test_les_statuts_sont_dans_l_enumeration():
    """Les statuts restent dans l'enumeration fermee."""
    autorises = {"retenu", "candidat", "a-verifier", "ecarte"}
    for candidat in CANDIDATS:
        assert candidat.statut in autorises, candidat.cle


def test_les_ecartes_ont_un_droit_non_etabli():
    """Un corpus ecarte l'est pour un droit manquant, pas pour un gout."""
    for candidat in CANDIDATS:
        if candidat.statut in {"ecarte", "a-verifier"}:
            assert "non etabli" in candidat.redistribution.lower() or (
                "non etabli" in candidat.conditions.lower()
            ), candidat.cle


def test_aucune_donnee_de_corpus_dans_le_registre():
    """Le registre ne contient que des metadonnees : aucun echantillon.

    Un champ textuel plus long que le seuil ressemble a une ligne de corpus ;
    c'est le garde-fou mecanique contre la recopie d'un dataset dans l'arbre.
    """
    for candidat in CANDIDATS:
        for champ in dataclasses.fields(candidat):
            valeur = getattr(candidat, champ.name)
            if isinstance(valeur, str):
                assert len(valeur) <= LONGUEUR_MAX_CHAMP, (
                    f"{candidat.cle}.{champ.name} depasse "
                    f"{LONGUEUR_MAX_CHAMP} caracteres : resemble a un echantillon"
                )


def test_le_corpus_ne_se_copie_pas_dans_le_depot():
    """L'acces est le telechargement a l'execution, jamais une copie."""
    for candidat in CANDIDATS:
        assert candidat.acces == ACCES_TELECHARGEMENT, candidat.cle
        assert "depot" not in candidat.acces.lower()


def test_le_plan_acces_est_minimal_et_complet():
    """Le plan d'acces dit ou prendre, comment, et sous quelles obligations."""
    plan = plan_acces("CreativeLang/ColBERT_Humor_Detection")
    assert set(plan) == {"url", "mode", "licence", "obligation", "taille_lignes"}
    assert plan["mode"] == ACCES_TELECHARGEMENT
    assert plan["url"].startswith("https://")
    assert plan["licence"] == "cc-by-2.0"


def test_le_plan_acces_refuse_une_cle_inconnue():
    """Une cle inconnue est une erreur franche, pas un corpus vide."""
    with pytest.raises(KeyError):
        par_cle("inexistant/pas-un-corpus")
