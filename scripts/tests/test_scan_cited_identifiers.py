"""Tests du census de citations `scripts/bibliography/scan_cited_identifiers.py`.

Le correctif porte sur la **population** : le census de reference de l'EPIC
#14407 ne capturait que la forme URL (`arxiv.org/abs/NNNN.NNNNN`) et laissait
echapper la forme tampon (`arXiv:NNNN.NNNNN`), qui est la forme employee par
la majorite des carnets. Ces tests echouent si un scanner se remet a capturer
une seule des deux formes, ou si la forme nue (sur-comptante en masse) revient
par defaut.
"""

import csv
import json

from scan_cited_identifiers import (
    ARXIV_NU_RE,
    charger_catalogue,
    cle_arxiv,
    census,
    extraire,
    normaliser_arxiv,
    table_du_gisement,
    texte_notebook,
)


def _ids(occurrences):
    return {(o.type_id, o.identifiant) for o in occurrences}


class TestFormesCapturees:
    def test_forme_tampon_est_capturee(self):
        trouvees = extraire("Voir arXiv:2401.05375 pour le detail.", "a.ipynb")
        assert ("arxiv", "2401.05375") in _ids(trouvees)

    def test_forme_url_est_capturee(self):
        trouvees = extraire("https://arxiv.org/abs/2401.05375", "a.ipynb")
        assert ("arxiv", "2401.05375") in _ids(trouvees)

    def test_les_deux_formes_donnent_la_meme_entree(self):
        trouvees = extraire("arXiv:2401.05375 (https://arxiv.org/abs/2401.05375)",
                            "a.ipynb")
        formes = {o.forme for o in trouvees if o.identifiant == "2401.05375"}
        assert {"tampon", "url"} <= formes

    def test_forme_legacy_garde_son_prefixe(self):
        trouvees = extraire("Ancient: arXiv:cs/0011047", "a.ipynb")
        assert ("arxiv", "cs/0011047") in _ids(trouvees)

    def test_version_suffixee_normalisee(self):
        trouvees = extraire("arXiv:2401.05375v3", "a.ipynb")
        assert ("arxiv", "2401.05375") in _ids(trouvees)

    def test_doi_marque_et_nu(self):
        trouvees = extraire("DOI: 10.1000/xyz123 puis 10.1000/abc456", "a.md")
        assert ("doi", "10.1000/xyz123") in _ids(trouvees)
        assert ("doi", "10.1000/abc456") in _ids(trouvees)

    def test_doi_a_parentheses_interne_preserve(self):
        # DOI Elsevier : la parenthese appartient a l'identifiant.
        trouvees = extraire("doi:10.1016/0304-4068(74)90217-3", "a.md")
        assert ("doi", "10.1016/0304-4068(74)90217-3") in _ids(trouvees)

    def test_parenthese_fermale_de_punctuation_retiree(self):
        trouvees = extraire("DOI: 10.1073/pnas.1210467109)", "a.md")
        assert ("doi", "10.1073/pnas.1210467109") in _ids(trouvees)

    def test_doi_placeholder_rejete(self):
        # `10.1002/...` et `10.1000/x` circulent dans les docstrings et les
        # fixtures : sans filtre, ils compteraient comme des DOI cites.
        trouvees = extraire("Voir 10.1002/... ou 10.1000/x", "a.md")
        assert _ids(trouvees) == set()

    def test_forme_nue_arxiv_exclue_par_defaut(self):
        trouvees = extraire("Le modele 2401.05375 est rapide.", "a.md")
        assert ("arxiv", "2401.05375") not in _ids(trouvees)

    def test_forme_nue_arxiv_capturee_sur_demande(self):
        trouvees = extraire("Le modele 2401.05375 est rapide.", "a.md",
                            nu_arxiv=True)
        assert ("arxiv", "2401.05375") in _ids(trouvees)

    def test_le_motif_nu_ne_renvoie_que_des_identifiants_arxiv(self):
        # Garde-fou du motif : `NNNN.NNNNN` ne doit pas attraper un DOI.
        assert ARXIV_NU_RE.findall("10.1000/xyz123") == []


class TestNormalisation:
    def test_prefixe_legacy_non_consultable(self):
        assert cle_arxiv("cs/0011047") == "0011047"

    def test_version_retiree(self):
        assert normaliser_arxiv("2401.05375v3") == "2401.05375"


class TestNotebook:
    def test_source_et_sorties_textuelles_relues(self, tmp_path):
        carnet = tmp_path / "n.ipynb"
        carnet.write_text(json.dumps({
            "cells": [
                {"cell_type": "markdown", "source": ["arXiv:2401.05375\n"]},
                {"cell_type": "code", "source": ["print(1)\n"],
                 "outputs": [{"output_type": "stream", "text": ["DOI: 10.1000/xyz\n"]}]},
                {"cell_type": "code", "source": ["x\n"],
                 "outputs": [{"output_type": "display_data",
                              "data": {"image/png": "iVBORw0KGgo="}}]},
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }), encoding="utf-8")
        texte = texte_notebook(carnet)
        assert "arXiv:2401.05375" in texte
        assert "10.1000/xyz" in texte
        assert "iVBORw0KGgo=" not in texte


class TestCensusSurArbre:
    def test_census_aggrege_par_famille(self, tmp_path):
        (tmp_path / "a.ipynb").write_text(json.dumps({
            "cells": [{"cell_type": "markdown", "source": ["arXiv:2401.05375\n"]}],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }), encoding="utf-8")
        (tmp_path / "b.md").write_text("DOI: 10.1000/xyz123\n", encoding="utf-8")
        (tmp_path / "c.py").write_text("x = 1\n", encoding="utf-8")
        entrees = census(tmp_path)
        assert ("arxiv", "2401.05375") in entrees
        assert ("doi", "10.1000/xyz123") in entrees
        assert entrees[("arxiv", "2401.05375")].fichiers == {"a.ipynb"}

    def test_repertoires_exclus_du_perimetre(self, tmp_path):
        (tmp_path / "_archives").mkdir()
        (tmp_path / "_archives" / "vieux.md").write_text(
            "arXiv:1111.11111\n", encoding="utf-8")
        entrees = census(tmp_path)
        assert ("arxiv", "1111.11111") not in entrees
        entrees = census(tmp_path, inclure_archives=True)
        assert ("arxiv", "1111.11111") in entrees


class TestJointureCatalogue:
    def _ecrire_catalogue(self, chemin, lignes):
        with chemin.open("w", encoding="utf-8", newline="") as f:
            redacteur = csv.DictWriter(
                f, fieldnames=["chemin_gisement", "type_id", "id",
                               "source_extraction", "confiance", "contexte"])
            redacteur.writeheader()
            for ligne in lignes:
                redacteur.writerow(ligne)

    def test_ligne_malformee_signalee_et_ignoree(self, tmp_path):
        catalogue = tmp_path / "cat.csv"
        self._ecrire_catalogue(catalogue, [
            {"chemin_gisement": "MachineLearning/x.pdf", "type_id": "arxiv",
             "id": "2401.05375", "source_extraction": "nom_fichier",
             "confiance": "elevee", "contexte": ""},
            {"chemin_gisement": "MachineLearning/y.pdf", "type_id": " OA).pdf",
             "id": "2403.06629", "source_extraction": "2403.06629",
             "confiance": "elevee", "contexte": ""},
        ])
        index, repares, malformees = charger_catalogue([catalogue])
        assert ("arxiv", "2401.05375") in index
        # Aucun type d'identifiant n'est recoverable : la ligne est inexploitable.
        assert repares == []
        assert len(malformees) == 1
        assert malformees[0]["ligne"] == 3

    def test_ligne_decalee_repartee(self, tmp_path):
        # Cas mesure dans le catalogue du 2026-10-25 : le chemin porte une
        # virgule non quotee, toutes les colonnes sont decalees d'un rang.
        catalogue = tmp_path / "cat.csv"
        catalogue.write_text(
            "chemin_gisement,type_id,id,source_extraction,confiance,contexte\n"
            'Consciousness\\2024 - Assembly Theory (arXiv 2403.06629v6, OA).pdf,'
            "arxiv,2403.06629,nom_fichier,elevee,tranche IIT\n",
            encoding="utf-8")
        index, repares, malformees = charger_catalogue([catalogue])
        assert ("arxiv", "2403.06629") in index
        assert index[("arxiv", "2403.06629")]["chemin_gisement"].endswith(
            "(arXiv 2403.06629v6, OA).pdf")
        assert index[("arxiv", "2403.06629")]["source_extraction"] == "nom_fichier"
        assert len(repares) == 1
        assert malformees == []

    def test_table_du_gisement_classe_chaque_identifiant(self, tmp_path):
        catalogue = tmp_path / "cat.csv"
        self._ecrire_catalogue(catalogue, [
            {"chemin_gisement": "MachineLearning/x.pdf", "type_id": "arxiv",
             "id": "2401.05375", "source_extraction": "nom_fichier",
             "confiance": "elevee", "contexte": ""},
        ])
        index, _, _ = charger_catalogue([catalogue])
        entrees = {
            ("arxiv", "2401.05375"): type("E", (), {
                "formes": {"tampon"}, "fichiers": {"a.ipynb"}, "occurrences": 1,
                "exemple_fichier": "a.ipynb", "exemple_contexte": "arXiv:2401.05375"})(),
            ("arxiv", "1706.03762"): type("E", (), {
                "formes": {"url"}, "fichiers": {"b.ipynb"}, "occurrences": 2,
                "exemple_fichier": "b.ipynb", "exemple_contexte": "arxiv.org/abs/1706.03762"})(),
        }
        lignes = table_du_gisement(entrees, index)
        par_id = {l["id"]: l for l in lignes}
        assert par_id["2401.05375"]["statut"] == "DETENU_CATALOGUE"
        assert par_id["2401.05375"]["chemin_gisement"] == "MachineLearning/x.pdf"
        assert par_id["1706.03762"]["statut"] == "ABSENT_CATALOGUE"
        assert par_id["1706.03762"]["chemin_gisement"] == ""
