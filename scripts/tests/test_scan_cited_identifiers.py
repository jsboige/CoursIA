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
from pathlib import Path

from scan_cited_identifiers import (
    ARXIV_NU_RE,
    charger_catalogue,
    cle_arxiv,
    census,
    extraire,
    inventaire_gisement,
    normaliser_arxiv,
    normaliser_texte,
    resoudre_arxiv,
    resoudre_dois,
    statuts_resolus,
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


# ---------------------------------------------------------------------------
# Etape de resolution (A1) : (auteur, titre, annee) + verdict de detention
# ---------------------------------------------------------------------------

ATOM_EXEMPLE = """<?xml version="1.0" encoding="UTF-8"?>
<feed xmlns="http://www.w3.org/2005/Atom"
      xmlns:arxiv="http://arxiv.org/schemas/atom">
  <entry>
    <id>http://arxiv.org/abs/1706.03762v7</id>
    <title>Attention Is All You Need</title>
    <published>2017-06-12T00:00:00Z</published>
    <author><name>Ashish Vaswani</name></author>
    <author><name>Noam Shazeer</name></author>
    <arxiv:doi>10.5555/3295222.3295349</arxiv:doi>
    <arxiv:journal_ref>Advances in Neural Information Processing Systems 30</arxiv:journal_ref>
  </entry>
</feed>
"""


class TestResolutionArxiv:
    def test_reponse_atom_rendue_en_fiche(self):
        from scan_cited_identifiers import _parser_arxiv
        entrees = _parser_arxiv(ATOM_EXEMPLE.encode("utf-8"))
        assert len(entrees) == 1
        identifiant, fiche = entrees[0]
        assert identifiant == "1706.03762"
        assert fiche["titre"] == "Attention Is All You Need"
        assert fiche["auteur"] == "Ashish Vaswani"
        assert fiche["auteurs"] == ["Ashish Vaswani", "Noam Shazeer"]
        assert fiche["annee"] == "2017"
        # Le crosswalk arXiv -> DOI de la version publiee : c'est lui qui
        # manquait au catalogue A5 (#21631).
        assert fiche["doi_publie"] == "10.5555/3295222.3295349"

    def test_lot_resolu_sans_reseau_ne_leve_pas(self):
        def fetcher(url):
            raise OSError("reseau indisponible")

        assert resoudre_arxiv(["1706.03762"], fetcher=fetcher, pause=0) == {}

    def test_identifiant_absent_de_la_reponse_nest_pas_resolu(self):
        def fetcher(url):
            return b"""<?xml version="1.0" encoding="UTF-8"?>
<feed xmlns="http://www.w3.org/2005/Atom"></feed>"""

        assert resoudre_arxiv(["1706.03762"], fetcher=fetcher, pause=0) == {}


class TestResolutionDoi:
    def test_doi_resolu(self):
        def fetcher(url):
            return (b'{"message": {"title": ["Deep Residual Learning"],'
                    b'"author": [{"given": "Kaiming", "family": "He"}],'
                    b'"issued": {"date-parts": [[2015, 12, 10]]}}}')

        resolus = resoudre_dois(["10.1109/cvpr.2016.90"], fetcher=fetcher)
        fiche = resolus["10.1109/cvpr.2016.90"]
        assert fiche["titre"] == "Deep Residual Learning"
        assert fiche["auteur"] == "Kaiming He"
        assert fiche["annee"] == "2015"
        assert fiche["source_api"] == "CROSSREF"

    def test_doi_absent_des_deux_registres_nest_pas_resolu(self):
        def fetcher(url):
            raise OSError("404")

        assert resoudre_dois(["10.9999/inexistant"], fetcher=fetcher) == {}

    def test_doi_absent_de_crossref_est_relance_chez_datacite(self):
        # Mesure du 2026-11-14 : 12 des 46 DOI non resolus par Crossref
        # (Zenodo, DBLP, Dagstuhl, Dataverse) se resolvent chez DataCite.
        def fetcher(url):
            if "crossref" in url:
                raise OSError("404")
            return (b'{"data": {"attributes": {"titles": [{"title": "Un Depot Zenodo"}],'
                    b'"creators": [{"name": "Un Auteur"}], "published": "2026-01-28",'
                    b'"container": {"title": "Zenodo"}}}}')

        resolus = resoudre_dois(["10.5281/zenodo.22737750"], fetcher=fetcher)
        fiche = resolus["10.5281/zenodo.22737750"]
        assert fiche["titre"] == "Un Depot Zenodo"
        assert fiche["auteur"] == "Un Auteur"
        assert fiche["annee"] == "2026"
        assert fiche["source_api"] == "DATACITE"

    def test_doi_avec_residu_markdown_est_nettoye_avant_requete(self):
        # Mesure du 2026-11-14 : 33 des 46 DOI `NON_RESOLU` portaient le
        # residu `](https://doi.org/...)` capture par la regex.
        vues = []

        def fetcher(url):
            vues.append(url)
            return (b'{"message": {"title": ["Dagstuhl"], "author": [],'
                    b'"issued": {"date-parts": [[2015, 1, 1]]}}}')

        brut = "10.4230/dagrep.9.2.27](https://doi.org/10.4230/dagrep.9.2.27)"
        resolus = resoudre_dois([brut], fetcher=fetcher)
        assert "10.4230/dagrep.9.2.27" in resolus
        assert "](https" not in vues[0]


class TestNettoyageDoi:
    def test_residu_markdown_tronque(self):
        from scan_cited_identifiers import _nettoyer_doi
        assert _nettoyer_doi(
            "10.4230/dagrep.9.2.27](https://doi.org/10.4230/dagrep.9.2.27)"
        ) == "10.4230/dagrep.9.2.27"

    def test_parenthese_interne_conservee(self):
        # DOI Elsevier : la parenthese appartient a l'identifiant.
        from scan_cited_identifiers import _nettoyer_doi
        assert _nettoyer_doi("10.1016/0304-4068(74)90217-3") == \
            "10.1016/0304-4068(74)90217-3"

    def test_asterisque_de_markdown_retire(self):
        from scan_cited_identifiers import _nettoyer_doi
        assert _nettoyer_doi("10.64898/2026.01.28.702361*") == \
            "10.64898/2026.01.28.702361"


class TestGisement:
    def test_normalisation_insensible_aux_accents_et_a_la_ponctuation(self):
        assert normaliser_texte("Attention Is All You Need!") == \
            "attention is all you need"
        assert normaliser_texte("Génération  dactylique") == \
            "generation dactylique"

    def test_nom_canonique_decoupe(self, tmp_path):
        from scan_cited_identifiers import _titre_du_fichier
        annee, auteurs, titre = _titre_du_fichier(
            "2017 - Vaswani et al. - Attention is All you need.pdf")
        assert annee == "2017"
        assert auteurs == "Vaswani et al."
        assert titre == "Attention is All you need"

    def test_inventaire_du_gisement(self, tmp_path):
        (tmp_path / "MachineLearning").mkdir()
        (tmp_path / "MachineLearning" /
         "2017 - Vaswani et al. - Attention is All you need.pdf").write_bytes(b"%PDF-")
        inventaire = inventaire_gisement(tmp_path)
        assert len(inventaire) == 1
        assert inventaire[0]["cle"] == "attention is all you need"
        assert inventaire[0]["annee"] == "2017"

    def test_gisement_absent_ne_produit_pas_d_inventaire(self, tmp_path):
        assert inventaire_gisement(tmp_path / "absent") == []


class TestVerdicts:
    def _ligne(self, identifiant, type_id="arxiv", statut="ABSENT_CATALOGUE"):
        return {"type_id": type_id, "id": identifiant, "statut": statut,
                "chemin_gisement": "", "source_extraction": "",
                "confiance_catalogue": "", "nb_fichiers": 1, "nb_occurrences": 1,
                "formes": "tampon", "exemple_fichier": "a.ipynb",
                "exemple_contexte": ""}

    def test_identifiant_au_catalogue_reste_detenu(self):
        lignes = [self._ligne("1706.03762", statut="DETENU_CATALOGUE")]
        enrichies = statuts_resolus(lignes, {}, {}, [])
        assert enrichies[0]["statut"] == "DETENU"
        assert enrichies[0]["preuve"] == "CATALOGUE_ID"

    def test_titre_exact_au_gisement_donne_detenu(self):
        lignes = [self._ligne("1706.03762")]
        resolus = {"1706.03762": {"titre": "Attention Is All You Need",
                                   "auteurs": ["A"], "auteur": "A", "annee": "2017"}}
        inventaire = [{"chemin": "G:/x/2017 - A - Attention is All you need.pdf",
                       "annee": "2017", "auteurs": "A",
                       "titre": "Attention is All you need",
                       "cle": "attention is all you need"}]
        enrichies = statuts_resolus(lignes, resolus, {}, inventaire)
        assert enrichies[0]["statut"] == "DETENU"
        assert enrichies[0]["preuve"] == "TITRE_EXACT"
        assert enrichies[0]["auteur"] == "A"
        assert enrichies[0]["annee"] == "2017"

    def test_identifiant_resolu_mais_non_detenu_donne_absent(self):
        lignes = [self._ligne("2401.05375")]
        resolus = {"2401.05375": {"titre": "Un Papier Inconnu", "auteurs": ["B"],
                                   "auteur": "B", "annee": "2024"}}
        enrichies = statuts_resolus(lignes, resolus, [], [])
        assert enrichies[0]["statut"] == "ABSENT"
        assert enrichies[0]["preuve"] == "RESOLU_NON_DETENU"

    def test_identifiant_non_resolu_est_non_resolu(self):
        lignes = [self._ligne("cs/0011047")]
        enrichies = statuts_resolus(lignes, {}, {}, [])
        assert enrichies[0]["statut"] == "NON_RESOLU"
        assert enrichies[0]["preuve"] == "API_SANS_REPONSE"


class TestSortiesRobustes:
    def test_table_csv_reprend_le_format_du_gisement(self, tmp_path):
        from scan_cited_identifiers import _ecrire_table_csv
        sortie = tmp_path / "table.csv"
        lignes = [{"type_id": "arxiv", "id": "1706.03762", "statut": "DETENU",
                   "chemin_gisement": "MachineLearning/x.pdf",
                   "source_extraction": "nom_fichier",
                   "confiance_catalogue": "", "nb_fichiers": 2,
                   "nb_occurrences": 5, "formes": "tampon",
                   "exemple_fichier": "a.ipynb", "exemple_contexte": "x",
                   "auteur": "Vaswani", "titre": "Attention", "annee": "2017",
                   "revue": "", "doi_publie": "10.1/x", "preuve": "CATALOGUE_ID",
                   "confiance": "HAUTE"}]
        _ecrire_table_csv(sortie, lignes)
        with sortie.open("r", encoding="utf-8", newline="") as f:
            lecteur = csv.DictReader(f)
            entete = lecteur.fieldnames
            ligne = next(lecteur)
        # Les noms de colonnes du gisement sont ceux de ses tables A1.
        for nom in ("id", "verdict", "titre_api", "auteurs", "annee", "score",
                    "chemin_gisement", "citations", "fichiers"):
            assert nom in entete
        assert ligne["verdict"] == "DETENU"
        assert ligne["titre_api"] == "Attention"
        assert ligne["auteurs"] == "Vaswani"
        assert ligne["citations"] == "5"
        assert ligne["fichiers"] == "a.ipynb"

    def test_cache_non_ecrit_ne_leve_pas(self, tmp_path):
        from scan_cited_identifiers import _ecrire_cache
        # Un chemin non inscriptible ne doit pas interrompre la mesure.
        _ecrire_cache(Path("Z:/inexistant/cache.json"), {"arxiv": {}})

    def test_cache_ecrit_puis_relu(self, tmp_path):
        from scan_cited_identifiers import _charger_cache, _ecrire_cache
        chemin = tmp_path / "cache.json"
        _ecrire_cache(chemin, {"arxiv": {"1.2": {"titre": "x"}}})
        assert _charger_cache(chemin)["arxiv"]["1.2"]["titre"] == "x"


class TestCatalogueVide:
    """Un catalogue absent ne doit pas se voir comme une detention vide.

    Mesure fondatrice (2026-11-14, review Hermes sur #26493) : le defaut
    `--travaux` est un chemin Windows. Sur un siege sans le montage, aucun
    catalogue n'est charge, la table sort 100 % `ABSENT_CATALOGUE` — la meme
    sortie qu'un gisement vide, en silence.
    """

    def test_aucun_catalogue_warnit(self):
        from scan_cited_identifiers import avertir_si_catalogues_vides
        message = avertir_si_catalogues_vides([], {}, "G:/Mon Drive/.../travaux")
        assert message
        assert "aucun catalogue" in message.lower()

    def test_catalogue_charge_sans_index_warnit(self, tmp_path):
        from scan_cited_identifiers import avertir_si_catalogues_vides
        vide = tmp_path / "IDENTIFIANTS-catalogue-2026-10-25.csv"
        vide.write_text("chemin_gisement,type_id,id\n", encoding="utf-8")
        message = avertir_si_catalogues_vides([vide], {}, "explicite")
        assert message
        assert "aucun identifiant" in message.lower()

    def test_catalogue_peuple_ne_warnit_pas(self, tmp_path):
        from scan_cited_identifiers import avertir_si_catalogues_vides
        plein = tmp_path / "IDENTIFIANTS-catalogue-2026-10-25.csv"
        plein.write_text("chemin_gisement,type_id,id\nx.pdf,arxiv,2403.06629\n",
                         encoding="utf-8")
        index = {("arxiv", "2403.06629"): {"chemin_gisement": "x.pdf"}}
        assert avertir_si_catalogues_vides([plein], index, "explicite") == ""
