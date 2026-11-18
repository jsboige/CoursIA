"""Tests for scripts/audit/check_distillation_archival_order.py (#21858).

L'organe rejoue la partie mecanique de l'audit de #21858 : une distillation est
redigee AVANT que sa source n'arrive dans le gisement bibliographique, et n'est
jamais relue contre elle ensuite. Cas fondateur : ICT-36c committe le
2026-10-14T05:46Z, papier archive a 06:08Z, deux attributions fausses, trois
reviewers verts.

Ce que ces tests protegent, et qui n'est pas evident a la lecture du code :

  - la **tolerance** de 180 s : sur les trois cas ou le commentaire
    ``[INFO] archivage`` et le ``ctime`` coexistent, l'ecart atteint 3 min
    (Subramani : ``ctime`` 06:07:58Z, commentaire 06:08:10Z). Sans elle,
    l'organe accuserait d'ecart d'ordre une lane qui a archive 12 s apres son
    commit, et un faux positif de cette classe tue l'organe a sa premiere
    utilisation ;
  - la **priorite des verdicts** : une source absente prime sur l'ecart
    d'ordre, et reste vraie quand les dates manquent. Inverser cet ordre
    classerait « pas de source du tout » comme un simple probleme de calendrier ;
  - le **refus du fuseau implicite** : une date sans ``Z`` ni decalage n'est
    pas une date. La supposer locale fabrique precisement le faux ecart que
    l'organe est cense mesurer ;
  - la **provenance declaree** : ``CONFORME`` fonde sur un ``ctime`` POSIX (date
    de changement d'inode) n'a pas la meme force que sur un commentaire
    d'archivage. Le rapport doit le dire, sinon le verdict se croit tout seul ;
  - le **repli par titre** : les fils qui ne nomment jamais le fichier ne
    doivent pas produire ``SOURCE_ABSENTE`` par construction. Le repli est
    declare par ``methode``, pour qu'un absence obtenue par repli ne se lise
    pas comme un nom cite introuvable.
"""
import importlib.util
import json
import sys
from datetime import datetime
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
SCRIPT = HERE.parent / "check_distillation_archival_order.py"


def _charger():
    spec = importlib.util.spec_from_file_location("check_distillation_archival_order", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    # `from __future__ import annotations` + @dataclass : le decorateur relit
    # cls.__module__ dans sys.modules, qui doit exister AVANT exec_module.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


org = _charger()


# --------------------------------------------------------------------------
# Normalisation et appariement de titres
# --------------------------------------------------------------------------

def test_normaliser_retire_accents_et_separateurs():
    assert org.normaliser("Trèfle knots in algebraic geometry") == "trefle knots in algebraic geometry"
    assert org.normaliser("a-b_c.d") == "a b c d"
    assert org.normaliser("") == ""


def test_jetons_ignore_les_mots_trop_courts_et_les_connecteurs():
    jetons = org.jetons("The trefoil knots and a to of")
    assert "trefoil" in jetons
    assert "knots" in jetons
    # « the », « and », « to », « of » sont des connecteurs ; « a » est trop court
    assert not jetons & {"the", "and", "to", "of", "a"}


def test_score_titre_trouve_le_titre_dans_un_nom_de_fichier_auteurs_annee():
    nom = "2026 - Michael and Kenta - Trefoil knots in algebraic geometry"
    assert org.score_titre(nom, "Trefoil knots in algebraic geometry") >= org.SEUIL_TITRE


def test_score_titre_ne_confond_pas_deux_papiers_du_meme_gisement():
    autre = "2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015"
    assert org.score_titre(autre, "Trefoil knots in algebraic geometry") < org.SEUIL_TITRE


def test_score_titre_vide_rend_zero_sans_diviser_par_zero():
    assert org.score_titre("n importe quoi", "") == 0.0


# --------------------------------------------------------------------------
# Chemins cites
# --------------------------------------------------------------------------

def test_extraire_chemins_pdf_conserve_les_espaces_du_nom_de_fichier():
    # Regression mesuree : un motif `[^\s]+\.pdf` ne rendait que « Trefoil.pdf »,
    # et l'appariement exact avec le gisement echouait sur tous les noms reels.
    chemins = org.extraire_chemins_pdf([
        "PDF archive `Hidden-Phenomena/2026 - Michael et Kenta - Trefoil knots.pdf` (31 p.)",
    ])
    assert chemins == ["2026 - Michael et Kenta - Trefoil knots.pdf"]


def test_extraire_chemins_pdf_dedoublonne_et_ne_garde_que_le_basename():
    chemins = org.extraire_chemins_pdf([
        "PDF archive `Hidden-Phenomena/2026 - Michael et Kenta - Trefoil.pdf` (31 p.)",
        "seconde mention `2026 - Michael et Kenta - Trefoil.pdf`",
        "et un chemin Windows `C:\\Users\\x\\Bibliographie IA\\Autre Papier.pdf`",
    ])
    assert len(chemins) == 2
    assert "2026 - Michael et Kenta - Trefoil.pdf" in chemins
    assert "Autre Papier.pdf" in chemins


def test_extraire_chemins_pdf_citation_en_prose_nue_garde_son_preambule():
    # L'extraction ne devine pas ou commence le nom : c'est la resolution qui
    # absorbe le preambule, par couverture de jetons.
    chemins = org.extraire_chemins_pdf(["voir Sona Technical Report - arXiv 2608.11015.pdf"])
    assert len(chemins) == 1
    assert chemins[0].endswith("2608.11015.pdf")


def test_extraire_chemins_pdf_sans_pdf_rend_vide():
    assert org.extraire_chemins_pdf(["aucun fichier ici", ""]) == []


# --------------------------------------------------------------------------
# Dates : fuseau explicite obligatoire
# --------------------------------------------------------------------------

def test_date_iso_accepte_z_et_decalage_et_normalise_en_utc():
    a = org.date_iso("2026-10-14T06:08Z")
    b = org.date_iso("2026-10-14T08:08+02:00")
    assert a == b
    assert org._iso(a) == "2026-10-14T06:08:00Z"


def test_date_iso_refuse_une_date_sans_fuseau():
    # Regle dure : supposer le fuseau local fabrique un faux ecart d'ordre.
    assert org.date_iso("2026-10-14 06:08") is None
    assert org.date_iso("2026-10-14T06:08:00") is None


def test_date_iso_illisible_rend_none_sans_lever():
    assert org.date_iso("") is None
    assert org.date_iso("pas une date") is None
    assert org.date_iso("2026-13-45T99:99Z") is None


def test_date_archivage_commentaire_retient_la_date_unique():
    date = org.date_archivage_commentaire([
        "[INFO] archivage du papier fait a 2026-10-14T06:08:10Z, dossier Hidden-Phenomena",
    ])
    assert org._iso(date) == "2026-10-14T06:08:10Z"


def test_date_archivage_commentaire_ne_choisit_pas_entre_deux_dates():
    # Deux dates contradictoires ne se departagent pas mecaniquement : on
    # retombe sur le ctime, et la provenance le dira.
    date = org.date_archivage_commentaire([
        "[INFO] archivage a 2026-10-14T06:08:10Z",
        "[INFO] archivage corrige a 2026-10-15T09:00:00Z",
    ])
    assert date is None


def test_date_archivage_commentaire_ignore_les_commentaires_sans_rapport():
    assert org.date_archivage_commentaire(["rien a voir", ""]) is None


# --------------------------------------------------------------------------
# Classement : les cinq branches, et l'ordre de priorite entre elles
# --------------------------------------------------------------------------

def _d(texte: str) -> datetime:
    return org.date_iso(texte)


def test_classer_ecart_ordre_cas_fondateur_ict36c():
    # Committe 05:46Z, archive 06:08Z : 22 minutes d'ecart.
    assert org.classer(_d("2026-10-14T05:46:00Z"), _d("2026-10-14T06:08:00Z"), True) == org.ECART_ORDRE


def test_classer_conforme_quand_l_archivage_precede_la_redaction():
    assert org.classer(_d("2026-10-18T17:08:00Z"), _d("2026-10-18T13:55:00Z"), True) == org.CONFORME


def test_classer_tolerance_absorbe_un_ecart_de_12_secondes():
    # Subramani : ctime 06:07:58Z, commentaire 06:08:10Z.
    assert org.classer(_d("2026-10-14T06:07:58Z"), _d("2026-10-14T06:08:10Z"), True) == org.CONFORME


def test_classer_tolerance_borne_exacte_incluse_puis_depassee():
    # 180 s pile : absorbe ; 181 s : ecart.
    assert org.classer(_d("2026-10-14T06:05:00Z"), _d("2026-10-14T06:08:00Z"), True) == org.CONFORME
    assert org.classer(_d("2026-10-14T06:04:59Z"), _d("2026-10-14T06:08:00Z"), True) == org.ECART_ORDRE


def test_classer_source_absente_prime_sur_les_dates():
    # Meme avec des dates contradictoires, une source absente est un defaut
    # plus fort qu'un probleme de calendrier.
    assert org.classer(_d("2026-10-14T05:46:00Z"), _d("2026-10-14T06:08:00Z"), False) == org.SOURCE_ABSENTE
    assert org.classer(None, None, False) == org.SOURCE_ABSENTE


def test_classer_date_manquante_rend_indetermine_jamais_conforme():
    # Un CONFORME par defaut serait un acquittement sans mesure.
    assert org.classer(None, _d("2026-10-14T06:08:00Z"), True) == org.INDETERMINE
    assert org.classer(_d("2026-10-14T05:46:00Z"), None, True) == org.INDETERMINE


def test_classer_date_naive_est_traitee_comme_utc_sans_crash():
    naive = datetime(2026, 10, 14, 5, 46)
    assert org.classer(naive, _d("2026-10-14T06:08:00Z"), True) == org.ECART_ORDRE


def test_classer_tolerance_configurable():
    assert org.classer(
        _d("2026-10-14T05:46:00Z"), _d("2026-10-14T06:08:00Z"), True, tolerance_s=3600
    ) == org.CONFORME


# --------------------------------------------------------------------------
# Plusieurs sources : l'ordre doit tenir pour TOUTES
# --------------------------------------------------------------------------

def test_classer_sources_vide_rend_source_absente():
    assert org.classer_sources(_d("2026-10-14T05:46:00Z"), []) == org.SOURCE_ABSENTE


def test_classer_sources_conforme_quand_toutes_les_archives_precedent():
    commit = _d("2026-10-14T12:00:00Z")
    assert org.classer_sources(commit, [
        (_d("2026-10-13T10:00:00Z"), "commentaire"),
        (_d("2026-10-14T09:00:00Z"), "ctime"),
    ]) == org.CONFORME


def test_classer_sources_ecart_des_qu_une_seule_archive_est_tardive():
    # Distillation en deux parties : le second papier arrive apres le commit,
    # donc le livrable a bien ete ecrit sans lui.
    commit = _d("2026-10-14T12:00:00Z")
    assert org.classer_sources(commit, [
        (_d("2026-10-13T10:00:00Z"), "commentaire"),
        (_d("2026-10-15T09:00:00Z"), "ctime"),
    ]) == org.ECART_ORDRE


def test_classer_sources_indetermine_quand_une_date_manque_sans_preuve_d_ecart():
    # Une source non datable n'acquitte pas : sans preuve d'ecart, on ne sait pas.
    commit = _d("2026-10-14T12:00:00Z")
    assert org.classer_sources(commit, [
        (_d("2026-10-13T10:00:00Z"), "commentaire"),
        (None, "aucune"),
    ]) == org.INDETERMINE


def test_classer_sources_ecart_prouve_malgre_une_source_non_datationnee():
    commit = _d("2026-10-14T12:00:00Z")
    assert org.classer_sources(commit, [
        (_d("2026-10-15T09:00:00Z"), "ctime"),
        (None, "aucune"),
    ]) == org.ECART_ORDRE


def test_classer_sources_sans_date_du_tout_rend_indetermine():
    assert org.classer_sources(_d("2026-10-14T12:00:00Z"), [(None, "aucune")]) == org.INDETERMINE


# --------------------------------------------------------------------------
# Resolution de la source sur un gisement synthetique
# --------------------------------------------------------------------------

@pytest.fixture
def gisement(tmp_path):
    (tmp_path / "MachineLearning").mkdir()
    (tmp_path / "Hidden-Phenomena").mkdir()
    (tmp_path / "SocialChoice").mkdir()
    (tmp_path / "MachineLearning" / "2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015.pdf").write_bytes(b"%PDF-1.4")
    (tmp_path / "Hidden-Phenomena" / "2026 - Michael and Kenta - Trefoil knots in algebraic geometry.pdf").write_bytes(b"%PDF-1.4")
    (tmp_path / "SocialChoice" / "2026 - Becker Greger Peters - committee elections approval core (arXiv 2609.11912).pdf").write_bytes(b"%PDF-1.4")
    return tmp_path


def test_indexer_gisement_trouve_les_pdf_en_profondeur(gisement):
    index = org.indexer_gisement(gisement)
    assert len(index) == 3


def test_indexer_gisement_sur_chemin_absent_rend_vide(tmp_path):
    assert org.indexer_gisement(tmp_path / "nexiste-pas") == {}


def test_resoudre_source_par_nom_cite_prime_sur_le_titre(gisement):
    index = org.indexer_gisement(gisement)
    res = org.resoudre_source(
        index,
        ["Sona Technical Report - arXiv 2608.11015.pdf"],
        titre="Trefoil knots in algebraic geometry",
    )
    assert res["trouvee"] is True
    assert res["methode"] == "nom_cite"
    assert "Sona" in res["chemin"]


def test_resoudre_source_par_titre_quand_le_fil_ne_nomme_pas_le_fichier(gisement):
    index = org.indexer_gisement(gisement)
    res = org.resoudre_source(index, [], titre="Trefoil knots in algebraic geometry")
    assert res["trouvee"] is True
    assert res["methode"] == "titre"
    assert res["score"] >= org.SEUIL_TITRE


def test_resoudre_source_absente_quand_ni_nom_ni_titre_ne_correspondent(gisement):
    index = org.indexer_gisement(gisement)
    res = org.resoudre_source(index, ["papier jamais depose.pdf"], titre="Un titre sans rapport aucun")
    assert res["trouvee"] is False
    # Le repli est declare : une absence par titre ne se lit pas comme un nom cite introuvable.
    assert res["methode"] == "titre"


def test_resoudre_source_rattrape_un_chemin_absolu_cite_en_entier(gisement):
    # Sens inverse de la couverture : le nom du fichier est DANS le chemin.
    index = org.indexer_gisement(gisement)
    chemin = gisement / "MachineLearning" / "2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015.pdf"
    res = org.resoudre_source(index, [str(chemin)])
    assert res["trouvee"] is True
    assert res["methode"] == "nom_cite"


def test_resoudre_source_rattrape_une_citation_qui_a_laisse_l_annee_et_les_auteurs(gisement):
    index = org.indexer_gisement(gisement)
    res = org.resoudre_source(index, ["Sona Technical Report - arXiv 2608.11015.pdf"])
    assert res["trouvee"] is True
    assert "Sona" in res["chemin"]


def test_resoudre_source_refuse_une_citation_d_un_seul_jeton(gisement):
    # Sans ce garde-fou, un « report.pdf » generique apparierait n'importe quel
    # rapport du gisement — et un SOURCE_ABSENTE deviendrait un CONFORME faux.
    index = org.indexer_gisement(gisement)
    assert org.resoudre_source(index, ["report.pdf"])["trouvee"] is False


def test_resoudre_source_sans_nom_ni_titre_ne_prétend_rien(gisement):
    res = org.resoudre_source(org.indexer_gisement(gisement), [])
    assert res["trouvee"] is False
    assert res["methode"] == "aucune"


# --------------------------------------------------------------------------
# Mesure complete d'une paire
# --------------------------------------------------------------------------

def test_mesurer_paire_ecart_ordre_avec_archivage_par_commentaire(gisement):
    mesure = org.mesurer_paire(
        issue=19438, pr=19438,
        texte_fil=["voir Sona Technical Report - arXiv 2608.11015.pdf"],
        premier_commit=org.date_iso("2026-10-06T05:34:00Z"),
        index=org.indexer_gisement(gisement),
        commentaires=["[INFO] archivage a 2026-10-06T10:27:00Z"],
    )
    assert mesure.verdict == org.ECART_ORDRE
    assert mesure.archivage_provenance == "commentaire"
    assert org._iso(mesure.archivage) == "2026-10-06T10:27:00Z"


def test_mesurer_paire_retombe_sur_le_ctime_et_le_declare(gisement):
    mesure = org.mesurer_paire(
        issue=19438, pr=19438,
        texte_fil=["voir Sona Technical Report - arXiv 2608.11015.pdf"],
        premier_commit=org.date_iso("2026-10-06T05:34:00Z"),
        index=org.indexer_gisement(gisement),
        commentaires=[],
    )
    # Sans commentaire d'archivage, le fichier existe : le ctime prend le relais.
    assert mesure.archivage_provenance == "ctime"
    assert mesure.archivage is not None
    assert mesure.verdict in {org.CONFORME, org.ECART_ORDRE}


def test_mesurer_paire_source_absente_ne_datationne_pas(gisement):
    mesure = org.mesurer_paire(
        issue=1, pr=2,
        texte_fil=["aucun pdf cite"],
        premier_commit=org.date_iso("2026-10-06T05:34:00Z"),
        index=org.indexer_gisement(gisement),
        commentaires=["[INFO] archivage a 2026-10-06T10:27:00Z"],
    )
    assert mesure.verdict == org.SOURCE_ABSENTE
    assert mesure.archivage_provenance == "aucune"


def test_mesurer_paire_lit_la_source_dans_le_livrable_avant_le_fil(gisement):
    # Mesure du 29/10 sur #21858 : sans cette priorite, les PRs correctes
    # etaient appariees au papier cite par l'issue d'audit — donc a une source
    # qui n'est pas la leur.
    mesure = org.mesurer_paire(
        issue=21858, pr=21888,
        texte_fil=["l'audit cite Sona Technical Report - arXiv 2608.11015.pdf"],
        texte_livrable=[
            "cette PR corrige les renvois au "
            "`SocialChoice/2026 - Becker Greger Peters - committee elections approval core (arXiv 2609.11912).pdf`"
        ],
        premier_commit=org.date_iso("2026-10-21T19:36:36Z"),
        index=org.indexer_gisement(gisement),
        commentaires=[],
        titre="Audit des distillations",
    )
    assert mesure.origine_source == "livrable"
    assert "committee elections" in Path(mesure.sources[0]["chemin"]).name


def test_mesurer_paire_replie_sur_le_fil_quand_le_livrable_ne_cite_rien(gisement):
    mesure = org.mesurer_paire(
        issue=21901, pr=21901,
        texte_fil=["voir 2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015.pdf"],
        texte_livrable=["fix(notebook): corriger la citation Sona"],
        premier_commit=org.date_iso("2026-10-24T20:13:32Z"),
        index=org.indexer_gisement(gisement),
        commentaires=[],
    )
    assert mesure.origine_source == "fil"
    assert "Sona" in Path(mesure.sources[0]["chemin"]).name


def test_mesurer_paire_deux_papiers_et_l_un_archive_apres_le_commit(gisement):
    mesure = org.mesurer_paire(
        issue=21875, pr=21893,
        texte_fil=[
            "PDFs `MachineLearning/2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015.pdf` "
            "et `Hidden-Phenomena/2026 - Michael and Kenta - Trefoil knots in algebraic geometry.pdf`"
        ],
        premier_commit=org.date_iso("2026-10-21T20:08:34Z"),
        index=org.indexer_gisement(gisement),
        commentaires=[],
    )
    assert len(mesure.sources) == 2
    # Les deux fichiers viennent d'etre crees dans tmp_path : leur ctime est
    # posterieur au commit, donc au moins une archive est tardive.
    assert mesure.verdict == org.ECART_ORDRE


def test_mesurer_paire_declare_un_conteneur_umbrella_au_lieu_de_le_mesurer(tmp_path):
    # Un audit ou un EPIC cite une foule de papiers : mesurer « l'ordre » d'un
    # conteneur n'a pas de sens, et ses lignes fausseraient le decompte.
    for i in range(org.MAX_SOURCES_LIVRABLE + 2):
        (tmp_path / f"2026 - Auteur {i} - Papier numero {i} sur un sujet.pdf").write_bytes(b"%PDF-1.4")
    index = org.indexer_gisement(tmp_path)
    citations = [f"2026 - Auteur {i} - Papier numero {i} sur un sujet.pdf" for i in range(len(index))]
    mesure = org.mesurer_paire(
        issue=21858, pr=22896,
        texte_fil=citations,
        premier_commit=org.date_iso("2026-10-27T06:32:57Z"),
        index=index,
        commentaires=[],
    )
    assert mesure.verdict == org.UMBRELLE
    # La liste est tronquee pour rester lisible, mais le verdict est declare.
    assert len(mesure.sources) == org.MAX_SOURCES_LIVRABLE


def test_mesurer_paire_ne_prend_pas_une_distillation_en_deux_parties_pour_un_conteneur(gisement):
    # Garde-fou du garde-fou : deux papiers restent un livrable mesurable.
    mesure = org.mesurer_paire(
        issue=21875, pr=21893,
        texte_fil=[
            "`MachineLearning/2026 - Sona Team et al - Sona Technical Report - arXiv 2608.11015.pdf` "
            "et `Hidden-Phenomena/2026 - Michael and Kenta - Trefoil knots in algebraic geometry.pdf`"
        ],
        premier_commit=org.date_iso("2026-10-21T20:08:34Z"),
        index=org.indexer_gisement(gisement),
        commentaires=[],
    )
    assert mesure.verdict != org.UMBRELLE


def test_mesure_as_dict_est_serialisable_et_porte_la_provenance(gisement):
    mesure = org.mesurer_paire(
        issue=19438, pr=19438,
        texte_fil=["Sona Technical Report - arXiv 2608.11015.pdf"],
        premier_commit=org.date_iso("2026-10-06T05:34:00Z"),
        index=org.indexer_gisement(gisement),
        commentaires=["[INFO] archivage a 2026-10-06T10:27:00Z"],
        titre="Sona Technical Report",
    )
    charge = json.loads(json.dumps(mesure.as_dict()))
    assert charge["verdict"] == org.ECART_ORDRE
    assert charge["archivage_provenance"] == "commentaire"
    assert charge["source_methode"] == "nom_cite"


# --------------------------------------------------------------------------
# Rapport
# --------------------------------------------------------------------------

def test_rendre_rapport_compte_par_verdict_et_trie_par_severite(gisement):
    index = org.indexer_gisement(gisement)
    mesures = [
        org.mesurer_paire(issue=1, pr=1, texte_fil=[], premier_commit=None, index=index),
        org.mesurer_paire(
            issue=2, pr=2, texte_fil=["Sona Technical Report - arXiv 2608.11015.pdf"],
            premier_commit=org.date_iso("2026-10-06T05:34:00Z"), index=index,
            commentaires=["[INFO] archivage a 2026-10-06T10:27:00Z"],
        ),
    ]
    rapport = org.rendre_rapport(mesures)
    assert "SOURCE_ABSENTE 1" in rapport
    assert "ECART_ORDRE 1" in rapport
    # La source absente est la plus grave : elle passe en tete du tableau.
    assert rapport.index("#1") < rapport.index("#2")


def test_rendre_rapport_vide_ne_leve_pas():
    rapport = org.rendre_rapport([])
    assert "paires mesurees : 0" in rapport


# --------------------------------------------------------------------------
# CLI : self-test et instrument indisponible
# --------------------------------------------------------------------------

def test_self_test_passe():
    assert org.self_test() == 0
    assert org.main(["--self-test"]) == 0


def test_sans_argument_le_parseur_refuse():
    with pytest.raises(SystemExit):
        org.main([])


def test_gisement_absent_rend_3_jamais_0(tmp_path):
    # Un 3 est une question, jamais un « aucune distillation fautive ».
    assert org.main(["--since", "2026-09-01", "--gisement", str(tmp_path / "nexiste-pas")]) == 3


def test_gisement_vide_rend_3_pas_un_rapport_vide(tmp_path):
    assert org.main(["--since", "2026-09-01", "--gisement", str(tmp_path)]) == 3


def test_mode_paires_rejoue_hors_ligne(gisement, tmp_path, capsys):
    paires = tmp_path / "paires.json"
    paires.write_text(json.dumps([{
        "issue": 19438,
        "pr": 19438,
        "textes": ["Sona Technical Report - arXiv 2608.11015.pdf"],
        "premier_commit": "2026-10-06T05:34:00Z",
        "commentaires": ["[INFO] archivage a 2026-10-06T10:27:00Z"],
        "titre": "Sona Technical Report",
    }]), encoding="utf-8")
    code = org.main(["--paires", str(paires), "--gisement", str(gisement), "--json"])
    assert code == 0
    charge = json.loads(capsys.readouterr().out)
    assert len(charge) == 1
    assert charge[0]["verdict"] == org.ECART_ORDRE
