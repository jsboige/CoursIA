"""Tests de la mesure APPROVE -> merge du plan « CI a deux etages » (#25510).

L'instrument ne se teste pas en l'executant contre l'API : ce serait une mesure,
pas un test. Ce qui est teste ici, c'est ce qui **decide** de la mesure :

1. **la population mesuree est celle des PRs approuvees a la tete exacte** --
   une approbation posee sur une tete anterieure, une approbation d'un autre
   compte, ou une revue COMMENTED ne creent pas de point de depart ; ces PRs
   sortent du denominateur et sont comptees a part, jamais comme « lentes » ;
2. **la fenetre se lit sur `merged_at`**, pas sur `updated_at` : une PR fermee
   sans fusion n'entre pas dans la population ;
3. **une part sans denominateur vaut `null`**, jamais 0 % ;
4. **le seuil est inclusif** a 24 h pile, et la troncature par `--max-prs` est
   dite dans le rapport et dans le rendu lisible ;
5. **le releve porte son cote censure** : une PR ouverte qu'une approbation a la
   tete exacte attend depuis plus que le seuil est comptee comme attente, une
   approbation perimee par un push n'attend rien ;
6. **une approbation soumise apres la fusion sort du denominateur** : elle ne
   peut pas etre la cause de la fusion, et le delai negatif qu'elle produisait
   se lisait « sous 24 h » ;
7. **les revues se lisent page par page** : une page unique peut omettre
   l'approbation recente d'une PR tres commentee ;
8. **un plafond de pages atteint sur une page pleine est dit** : la fenetre est
   alors declaree incomplete (`fenetre_complete: false`, `tronquee`), et une PR
   dont les revues ne sont pas lues en entier sort du denominateur
   (`revues_incompletes`) -- jamais classee « sans approbation » alors que
   l'approbation est sur une page non lue ;
9. **une approbation reprise par l'approbateur n'est plus en force** : un
   `CHANGES_REQUESTED` du coordinateur sur la tete approuvee retire son
   approbation. La PR fusionnee sort du denominateur (`approbation_retiree`),
   et une PR ouverte ainsi reprise n'attend pas un merge. Cote ouvert, ce cas
   etait masque par le filtre de recherche `review:approved`, qui suit la
   derniere decision de review ; la regle tient sans ce filtre.
10. **une population ouverte partielle est dite, meme a comptes egaux** : la
    recherche GitHub peut annoncer `incomplete_results: true` en rendant
    autant d'items que de `total_count` annonce, zero compris. Le signal est
    porte a part (`resultats_incomplets`) et nomme dans le rendu, au lieu de
    conclure `tronquee: false` sur une file qu'on n'a pas lue en entier.

Les appels reseau sont remplaces par une fonction `api` factice : les tests ne
dependent ni du reseau ni du quota. La couche de lecture (`api`) a sa
propre suite : `test_measure_approve_to_merge_lecture.py`.
"""

from __future__ import annotations

import json
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import measure_approve_to_merge as m  # noqa: E402


def _pr(numero: int, tete: str, fusionnee_le: str, mise_a_jour: str | None = None) -> dict:
    return {
        "number": numero,
        "head": {"sha": tete},
        "merged_at": fusionnee_le,
        "updated_at": mise_a_jour or fusionnee_le,
    }


def _revue(login: str, etat: str, commit: str, soumise_le: str) -> dict:
    return {
        "user": {"login": login},
        "state": etat,
        "commit_id": commit,
        "submitted_at": soumise_le,
    }


# --- horodatages -----------------------------------------------------------

def test_parse_ts_absent_rend_none():
    assert m.parse_ts(None) is None
    assert m.parse_ts("") is None


def test_parse_ts_z_est_utc():
    moment = m.parse_ts("2026-11-25T22:00:00Z")
    assert moment.tzinfo == timezone.utc
    assert moment.hour == 22


def test_parse_ts_offset_conserve_l_instant():
    assert m.parse_ts("2026-11-25T23:00:00+01:00") == m.parse_ts("2026-11-25T22:00:00Z")


# --- selection de l'approbation --------------------------------------------

def test_approbation_tete_retient_la_derniere_sur_cette_tete():
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-25T10:00:00Z"),
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-25T12:00:00Z"),
    ]
    choisie = m.approbation_tete(revues, "abc", "myia-ai-01")
    assert choisie is not None
    assert choisie["submitted_at"] == "2026-11-25T12:00:00Z"


def test_approbation_d_une_autre_tete_ne_compte_pas():
    revues = [_revue("myia-ai-01", "APPROVED", "ancienne", "2026-11-25T10:00:00Z")]
    assert m.approbation_tete(revues, "nouvelle", "myia-ai-01") is None


def test_revue_commentee_ne_compte_pas():
    revues = [_revue("myia-ai-01", "COMMENTED", "abc", "2026-11-25T10:00:00Z")]
    assert m.approbation_tete(revues, "abc", "myia-ai-01") is None


def test_approbation_d_un_autre_compte_ignoree():
    revues = [_revue("jsboige", "APPROVED", "abc", "2026-11-25T10:00:00Z")]
    assert m.approbation_tete(revues, "abc", "myia-ai-01") is None


def test_approbation_reprise_par_l_approbateur_n_est_plus_en_force():
    """Temoin : l'approbation d'avant la reprise restait le point de depart.

    Lu sur #28327 le 26/11 : APPROVE du coordinateur le 24/11 20:31:58Z, puis
    `CHANGES_REQUESTED` du meme compte le 26/11 10:29:11Z, sur la meme tete.
    La decision de review a change : la PR attend sa lane, pas un merge.
    Compter depuis l'APPROVE la disait en attente de fusion depuis 38 h.
    """
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-24T20:31:58Z"),
        _revue("myia-ai-01", "CHANGES_REQUESTED", "abc", "2026-11-26T10:29:11Z"),
    ]
    assert m.approbation_tete(revues, "abc", "myia-ai-01") is None


def test_reprise_par_un_autre_compte_ne_retire_pas():
    """Seul l'approbateur retire son approbation : la regle de merge est la sienne."""
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T08:00:00Z"),
        _revue("clusterManager-Myia", "CHANGES_REQUESTED", "abc", "2026-11-26T09:00:00Z"),
    ]
    choisie = m.approbation_tete(revues, "abc", "myia-ai-01")
    assert choisie is not None
    assert choisie["submitted_at"] == "2026-11-26T08:00:00Z"


def test_demande_de_changements_anterieure_a_l_approbation_ne_retire_pas():
    """Ordre habituel sur une meme tete : la reprise precede l'approbation."""
    revues = [
        _revue("myia-ai-01", "CHANGES_REQUESTED", "abc", "2026-11-26T08:00:00Z"),
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T09:00:00Z"),
    ]
    choisie = m.approbation_tete(revues, "abc", "myia-ai-01")
    assert choisie is not None
    assert choisie["submitted_at"] == "2026-11-26T09:00:00Z"


def test_approbation_reposee_apres_une_reprise_est_en_force():
    """Lu sur #28373 le 26/11 : approvee, relue en `COMMENTED`, puis re-approuvee."""
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-24T20:34:02Z"),
        _revue("myia-ai-01", "CHANGES_REQUESTED", "abc", "2026-11-26T09:00:00Z"),
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T11:10:24Z"),
    ]
    choisie = m.approbation_tete(revues, "abc", "myia-ai-01")
    assert choisie is not None
    assert choisie["submitted_at"] == "2026-11-26T11:10:24Z"


# --- classement ------------------------------------------------------------

def test_classer_tete_exacte_donne_le_delai():
    pr = _pr(1, "abc", "2026-11-26T10:30:00Z")
    revues = [_revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T08:00:00Z")]
    ligne = m.classer(pr, revues, "myia-ai-01")
    assert ligne["classe"] == "tete_exacte"
    assert ligne["heures"] == 2.5


def test_classer_tete_anterieure_sort_du_denominateur():
    pr = _pr(2, "nouvelle", "2026-11-26T10:30:00Z")
    revues = [_revue("myia-ai-01", "APPROVED", "ancienne", "2026-11-25T08:00:00Z")]
    ligne = m.classer(pr, revues, "myia-ai-01")
    assert ligne["classe"] == "tete_anterieure"
    assert ligne["heures"] is None


def test_classer_sans_approbation():
    pr = _pr(3, "abc", "2026-11-26T10:30:00Z")
    ligne = m.classer(pr, [], "myia-ai-01")
    assert ligne["classe"] == "sans_approbation"
    assert ligne["heures"] is None


def test_classer_approbation_soumise_apres_la_fusion_ne_donne_pas_de_delai():
    """Temoin : une approbation posterieure a la fusion produisait un delai negatif.

    Le delai negatif etait compte « sous 24 h » et gonflait la part mesuree.
    Une approbation qui suit la fusion ne peut pas en etre la cause : elle sort
    du denominateur, comptee a part.
    """
    pr = _pr(4, "abc", "2026-11-26T10:30:00Z")
    revues = [_revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T14:00:00Z")]
    ligne = m.classer(pr, revues, "myia-ai-01")
    assert ligne["classe"] == "approbation_apres_fusion"
    assert ligne["heures"] is None
    agregat = m.resume([ligne])
    assert agregat["tete_exacte"]["n"] == 0
    assert agregat["tete_exacte"]["sous_le_seuil"] == 0
    assert agregat["approbation_apres_fusion"] == 1


def test_classer_retient_l_approbation_anterieure_quand_une_autre_suit_la_fusion():
    """La derniere approbation d'avant la fusion fait foi, pas la plus recente."""
    pr = _pr(5, "abc", "2026-11-26T10:30:00Z")
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T08:00:00Z"),
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T12:00:00Z"),
    ]
    ligne = m.classer(pr, revues, "myia-ai-01")
    assert ligne["classe"] == "tete_exacte"
    assert ligne["heures"] == 2.5


def test_classer_approbation_reprise_avant_la_fusion_sort_du_denominateur():
    """Temoin : la fusion etait datee depuis une approbation que la reprise avait videe.

    Aucune approbation n'etait en force a la fusion : la PR sort du
    denominateur sous sa propre classe. Elle n'est ni « tete anterieure »
    (l'approbation porte bien sur cette tete), ni « sans approbation ».
    """
    pr = _pr(6, "abc", "2026-11-26T10:30:00Z")
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-24T20:00:00Z"),
        _revue("myia-ai-01", "CHANGES_REQUESTED", "abc", "2026-11-26T09:00:00Z"),
    ]
    ligne = m.classer(pr, revues, "myia-ai-01")
    assert ligne["classe"] == "approbation_retiree"
    assert ligne["heures"] is None
    agregat = m.resume([ligne])
    assert agregat["approbation_retiree"] == 1
    assert agregat["tete_exacte"]["n"] == 0
    assert agregat["tete_anterieure"] == 0
    assert agregat["sans_approbation"] == 0


def test_classer_reprise_posterieure_a_la_fusion_ne_retire_pas():
    """La reprise suit la fusion : a la fusion, l'approbation etait en force."""
    pr = _pr(7, "abc", "2026-11-26T10:30:00Z")
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T08:00:00Z"),
        _revue("myia-ai-01", "CHANGES_REQUESTED", "abc", "2026-11-26T11:00:00Z"),
    ]
    ligne = m.classer(pr, revues, "myia-ai-01")
    assert ligne["classe"] == "tete_exacte"
    assert ligne["heures"] == 2.5


def test_classer_approbation_reposee_compte_depuis_la_nouvelle():
    """Reprise puis nouvelle approbation : le point de depart est la nouvelle."""
    pr = _pr(8, "abc", "2026-11-26T10:30:00Z")
    revues = [
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T08:00:00Z"),
        _revue("myia-ai-01", "CHANGES_REQUESTED", "abc", "2026-11-26T09:00:00Z"),
        _revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T10:00:00Z"),
    ]
    ligne = m.classer(pr, revues, "myia-ai-01")
    assert ligne["classe"] == "tete_exacte"
    assert ligne["heures"] == 0.5


def test_revues_suit_les_pages(monkeypatch):
    """Temoin : sur une page unique, l'approbation recente disparaissait.

    Une PR tres commentee porte son approbation sur une page suivante ; le
    lecteur doit la trouver, sinon la PR est classee « tete anterieure » a tort.
    """
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    tete = "abc"
    pages = {
        1: [_revue("autre", "COMMENTED", tete, "2026-11-26T07:00:00Z"),
            _revue("autre", "COMMENTED", tete, "2026-11-26T07:05:00Z")],
        2: [_revue("myia-ai-01", "APPROVED", tete, "2026-11-26T08:00:00Z")],
    }

    def faux_api(chemin: str) -> list[dict]:
        if "/reviews" not in chemin:
            return []
        return pages.get(int(chemin.rsplit("page=", 1)[1]), [])

    monkeypatch.setattr(m, "api", faux_api)
    lues, completes = m.revues(9)
    assert len(lues) == 3
    assert completes is True
    ligne = m.classer(_pr(9, tete, "2026-11-26T10:30:00Z"), lues, "myia-ai-01")
    assert ligne["classe"] == "tete_exacte"
    assert ligne["heures"] == 2.5


def test_revues_page_pleine_au_plafond_n_a_pas_de_preuve_d_exhaustivite(monkeypatch):
    """Temoin : le plafond atteint sur une page pleine ne disait rien.

    Les pages 1 et 2 sont pleines et la page 3 existe : la lecture bornee a
    deux pages rend un prefixe. Rien ne prouve qu'elle a tout vu, et
    `complete` doit le dire. La page 3 n'est pas demandee -- le plafond borne
    la depense.
    """
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    demandees: list[int] = []

    def faux_api(chemin: str) -> list[dict]:
        page = int(chemin.rsplit("page=", 1)[1])
        demandees.append(page)
        return [_revue("autre", "COMMENTED", "abc", f"2026-11-26T0{page}:00:00Z")] * 2

    monkeypatch.setattr(m, "api", faux_api)
    lues, completes = m.revues(9, max_pages=2)
    assert len(lues) == 4
    assert completes is False
    assert demandees == [1, 2]


def test_une_approbation_au_dela_du_plafond_n_est_pas_dite_absente(monkeypatch):
    """Temoin : l'approbation a la tete exacte etait sur la page non lue.

    Le prefixe lu ne contient aucune approbation. Classe tel quel, il
    concluait « sans approbation » : la PR sortait du denominateur alors
    qu'elle est approuvee a sa tete. Une lecture incomplete ne classe pas.
    """
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    pages = {
        1: [_revue("autre", "COMMENTED", "abc", "2026-11-26T06:00:00Z")] * 2,
        2: [_revue("autre", "COMMENTED", "abc", "2026-11-26T07:00:00Z")] * 2,
        3: [_revue("myia-ai-01", "APPROVED", "abc", "2026-11-26T08:00:00Z")],
    }

    def faux_api(chemin: str) -> list[dict]:
        return pages.get(int(chemin.rsplit("page=", 1)[1]), [])

    monkeypatch.setattr(m, "api", faux_api)
    lues, completes = m.revues(9, max_pages=2)
    assert completes is False
    ligne = m.classer(_pr(9, "abc", "2026-11-26T10:30:00Z"), lues, "myia-ai-01",
                      revues_completes=completes)
    assert ligne["classe"] == "revues_incompletes"
    agregat = m.resume([ligne])
    assert agregat["sans_approbation"] == 0
    assert agregat["tete_anterieure"] == 0
    assert agregat["tete_exacte"]["n"] == 0
    assert agregat["revues_incompletes"] == 1


def test_revues_incompletes_ne_classe_pas_meme_avec_une_ancienne_approbation():
    """Le prefixe porte une approbation sur une tete anterieure.

    Les pages non lues peuvent en porter une sur la tete courante : le
    classement « tete anterieure » n'est pas sur non plus.
    """
    pr = _pr(10, "nouvelle", "2026-11-26T10:30:00Z")
    revues = [_revue("myia-ai-01", "APPROVED", "ancienne", "2026-11-25T08:00:00Z")]
    ligne = m.classer(pr, revues, "myia-ai-01", revues_completes=False)
    assert ligne["classe"] == "revues_incompletes"
    assert ligne["heures"] is None


# --- agregats --------------------------------------------------------------

def test_seuil_inclusif_a_24_h():
    lignes = [
        {"numero": 1, "classe": "tete_exacte", "heures": 24.0},
        {"numero": 2, "classe": "tete_exacte", "heures": 24.01},
    ]
    bloc = m.resume(lignes)["tete_exacte"]
    assert bloc["n"] == 2
    assert bloc["sous_le_seuil"] == 1
    assert bloc["part_sous_le_seuil"] == 0.5


def test_part_sans_denominateur_vaut_none():
    lignes = [{"numero": 1, "classe": "sans_approbation", "heures": None}]
    bloc = m.resume(lignes)["tete_exacte"]
    assert bloc["n"] == 0
    assert bloc["part_sous_le_seuil"] is None
    assert bloc["p50_heures"] is None


def test_percentile_rang_le_plus_proche():
    valeurs = [float(n) for n in range(1, 11)]
    assert m.percentile(valeurs, 50) == 5.0
    assert m.percentile(valeurs, 90) == 9.0
    assert m.percentile([], 90) is None


def test_resume_compte_les_classes_hors_denominateur():
    lignes = [
        {"numero": 1, "classe": "tete_exacte", "heures": 3.0},
        {"numero": 2, "classe": "tete_anterieure", "heures": None},
        {"numero": 3, "classe": "sans_approbation", "heures": None},
        {"numero": 4, "classe": "sans_approbation", "heures": None},
        {"numero": 5, "classe": "revues_incompletes", "heures": None},
        {"numero": 6, "classe": "approbation_retiree", "heures": None},
    ]
    agregat = m.resume(lignes)
    assert agregat["tete_exacte"]["n"] == 1
    assert agregat["tete_anterieure"] == 1
    assert agregat["sans_approbation"] == 2
    assert agregat["revues_incompletes"] == 1
    assert agregat["approbation_retiree"] == 1


# --- lecture de la fenetre, borne et bout en bout --------------------------

def _pages_fusionnees() -> dict[int, list[dict]]:
    """Trois pages de deux PRs, toutes fusionnees le 25/11 (dans la fenetre de ces tests)."""
    return {
        1: [_pr(1, "a", "2026-11-25T12:00:00Z"), _pr(2, "b", "2026-11-25T11:00:00Z")],
        2: [_pr(3, "c", "2026-11-25T10:00:00Z"), _pr(4, "d", "2026-11-25T09:00:00Z")],
        3: [_pr(5, "e", "2026-11-25T08:00:00Z")],
    }


def test_fusionnees_filtre_sur_merged_at(monkeypatch):
    depuis = datetime(2026, 11, 25, tzinfo=timezone.utc)
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    page = [
        _pr(1, "a", "2026-11-25T12:00:00Z"),
        _pr(2, "b", "2026-11-20T12:00:00Z"),          # hors fenetre
        {"number": 3, "head": {"sha": "c"}, "merged_at": None,
         "updated_at": "2026-11-25T13:00:00Z"},       # fermee sans fusion
    ]
    monkeypatch.setattr(m, "api", lambda chemin: page if "page=1" in chemin else [])
    trouvees, complete = m.fusionnees(depuis, jusqu_a)
    assert [pr["number"] for pr in trouvees] == [1]
    assert complete is True


def test_fusionnees_page_pleine_au_plafond_dans_la_fenetre_est_incompletee(monkeypatch):
    """Temoin : le plafond atteint sur une page pleine encore dans la fenetre.

    Des fusions de la fenetre existent au-dela (page 3) : la liste rendue est
    un prefixe, et `complete` vaut False -- le rapport declarera la fenetre
    tronquee au lieu de compter 4 fusions pour un total.
    """
    depuis = datetime(2026, 11, 25, tzinfo=timezone.utc)
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    pages = _pages_fusionnees()
    demandees: list[int] = []

    def faux_api(chemin: str) -> list[dict]:
        page = int(chemin.rsplit("page=", 1)[1])
        demandees.append(page)
        return pages.get(page, [])

    monkeypatch.setattr(m, "PAR_PAGE", 2)
    monkeypatch.setattr(m, "api", faux_api)
    trouvees, complete = m.fusionnees(depuis, jusqu_a, max_pages=2)
    assert complete is False
    assert [pr["number"] for pr in trouvees] == [1, 2, 3, 4]
    assert demandees == [1, 2]


def test_fusionnees_plafond_sur_une_page_sortie_de_la_fenetre_est_complete(monkeypatch):
    """Page pleine au plafond, mais sa plus ancienne `updated_at` sort de la fenetre.

    Une fusion de la fenetre est mise a jour au plus tard a sa fusion : rien
    d'elle ne peut etre sur une page plus ancienne. La preuve d'exhaustivite
    existe, `complete` vaut True bien que le plafond soit atteint.
    """
    depuis = datetime(2026, 11, 25, tzinfo=timezone.utc)
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    pages = {
        1: [_pr(1, "a", "2026-11-25T12:00:00Z"), _pr(2, "b", "2026-11-25T11:00:00Z")],
        2: [_pr(3, "c", "2026-11-25T10:00:00Z"),
            _pr(4, "d", "2026-11-20T09:00:00Z", mise_a_jour="2026-11-24T09:00:00Z")],
    }
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    monkeypatch.setattr(m, "api",
                        lambda chemin: pages.get(int(chemin.rsplit("page=", 1)[1]), []))
    trouvees, complete = m.fusionnees(depuis, jusqu_a, max_pages=2)
    assert complete is True
    assert [pr["number"] for pr in trouvees] == [1, 2, 3]


def test_mesurer_borne_la_lecture_et_le_dit(monkeypatch):
    depuis = datetime(2026, 11, 25, tzinfo=timezone.utc)
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    page = [
        _pr(1, "a", "2026-11-25T12:00:00Z"),
        _pr(2, "b", "2026-11-25T11:00:00Z"),
        _pr(3, "c", "2026-11-25T10:00:00Z"),
    ]
    revues = {
        1: [_revue("myia-ai-01", "APPROVED", "a", "2026-11-25T10:00:00Z")],
        2: [_revue("myia-ai-01", "APPROVED", "b", "2026-11-25T10:00:00Z")],
        3: [],
    }

    def faux_api(chemin: str):
        if "/search/" in chemin:
            return {"items": [], "total_count": 0}
        if "/reviews" in chemin:
            numero = int(chemin.split("/pulls/")[1].split("/")[0])
            return revues[numero]
        return page if "page=1" in chemin else []

    monkeypatch.setattr(m, "api", faux_api)
    rapport = m.mesurer(depuis, jusqu_a, max_prs=2)
    assert rapport["fusionnees_dans_la_fenetre"] == 3
    assert rapport["fenetre_complete"] is True
    assert rapport["inspectees"] == 2
    assert rapport["tronquee"] is True
    assert rapport["tete_exacte"]["n"] == 2
    assert rapport["tete_exacte"]["part_sous_le_seuil"] == 1.0


def test_mesurer_dit_une_fenetre_incompletee(monkeypatch):
    """Temoin : au plafond, le rapport affichait encore `tronquee: false`.

    La fenetre lue est un prefixe de deux pages sur trois. Le rapport porte
    `fenetre_complete: false`, `tronquee: true`, et le rendu dit la cause.
    """
    depuis = datetime(2026, 11, 25, tzinfo=timezone.utc)
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    pages = _pages_fusionnees()
    revues = {1: [_revue("myia-ai-01", "APPROVED", "a", "2026-11-25T10:00:00Z")]}

    def faux_api(chemin: str):
        if "/reviews" in chemin:
            return revues.get(int(chemin.split("/pulls/")[1].split("/")[0]), [])
        return pages.get(int(chemin.rsplit("page=", 1)[1]), [])

    monkeypatch.setattr(m, "PAR_PAGE", 2)
    monkeypatch.setattr(m, "api", faux_api)
    rapport = m.mesurer(depuis, jusqu_a, avec_ouvertes=False, max_pages=2)
    assert rapport["fenetre_complete"] is False
    assert rapport["fusionnees_dans_la_fenetre"] == 4
    assert rapport["inspectees"] == 4
    assert rapport["tronquee"] is True
    texte = m.formater(rapport)
    assert "TRONQUEE : plafond de pages atteint sur une page pleine" in texte
    assert "borne basse" in texte


def test_mesurer_sort_une_pr_a_revues_incompletes(monkeypatch):
    """La PR 1 est approuvee a sa tete, sur une page de revues que le plafond omet."""
    depuis = datetime(2026, 11, 25, tzinfo=timezone.utc)
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    page = [_pr(1, "a", "2026-11-25T12:00:00Z")]
    pages_revues = {
        1: [_revue("autre", "COMMENTED", "a", "2026-11-25T10:00:00Z")] * 2,
        2: [_revue("autre", "COMMENTED", "a", "2026-11-25T10:30:00Z")] * 2,
        3: [_revue("myia-ai-01", "APPROVED", "a", "2026-11-25T11:00:00Z")],
    }

    def faux_api(chemin: str):
        if "/reviews" in chemin:
            return pages_revues.get(int(chemin.rsplit("page=", 1)[1]), [])
        return page if "page=1" in chemin else []

    monkeypatch.setattr(m, "PAR_PAGE", 2)
    monkeypatch.setattr(m, "api", faux_api)
    rapport = m.mesurer(depuis, jusqu_a, avec_ouvertes=False, max_pages=2)
    assert rapport["fenetre_complete"] is True
    assert rapport["tronquee"] is False
    assert rapport["lignes"][0]["classe"] == "revues_incompletes"
    assert rapport["revues_incompletes"] == 1
    assert rapport["sans_approbation"] == 0
    assert rapport["tete_exacte"]["n"] == 0
    assert "1 a revues non lues en entier" in m.formater(rapport)


def test_mesurer_sans_ouvertes_n_interroge_pas_la_recherche(monkeypatch):
    depuis = datetime(2026, 11, 25, tzinfo=timezone.utc)
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    appeles: list[str] = []

    def faux_api(chemin: str):
        appeles.append(chemin)
        return [] if "/reviews" not in chemin else []

    monkeypatch.setattr(m, "api", faux_api)
    rapport = m.mesurer(depuis, jusqu_a, avec_ouvertes=False)
    assert rapport["inspectees"] == 0
    assert "ouvertes_approuvees" not in rapport
    assert not any("/search/" in chemin for chemin in appeles)


def test_ouvertes_approuvees_compte_l_attente_a_la_tete_exacte(monkeypatch):
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    tetes = {11: "k1", 12: "k2", 13: "k3"}
    revues = {
        # approuvee a sa tete il y a 30 h : elle attend au-dela du seuil
        11: [_revue("myia-ai-01", "APPROVED", "k1", "2026-11-24T18:00:00Z")],
        # approuvee a sa tete il y a 2 h : elle attend, sous le seuil
        12: [_revue("myia-ai-01", "APPROVED", "k2", "2026-11-25T22:00:00Z")],
        # approuvee sur une tete anterieure, puis poussee : l'approbation est perimee
        13: [_revue("myia-ai-01", "APPROVED", "k0", "2026-11-24T18:00:00Z")],
    }

    def faux_api(chemin: str):
        if "/search/" in chemin:
            return {"total_count": 3, "items": [{"number": n} for n in tetes]}
        numero = int(chemin.split("/pulls/")[1].split("/")[0])
        if "/reviews" in chemin:
            return revues[numero]
        return {"number": numero, "head": {"sha": tetes[numero]}}

    monkeypatch.setattr(m, "api", faux_api)
    ouvertes = m.ouvertes_approuvees(jusqu_a)
    assert ouvertes["trouvees"] == 3
    assert ouvertes["inspectees"] == 3
    assert ouvertes["tronquee"] is False
    assert ouvertes["a_la_tete_exacte"] == 2
    assert ouvertes["au_dela_du_seuil"] == 1
    assert [ligne["numero"] for ligne in ouvertes["au_dela"]] == [11]
    assert ouvertes["plus_ancienne_heures"] == 30.0
    assert ouvertes["revues_incompletes"] == 0
    assert ouvertes["resultats_incomplets"] is False


def test_ouvertes_approuvees_propage_les_resultats_incomplets_a_comptes_egaux(monkeypatch):
    """Temoin : comptes egaux, population pourtant partielle.

    La recherche rend deux items et annonce `total_count: 2`, mais elle porte
    `incomplete_results: true` : la population n'est pas lue en entier.
    Comparer les seuls nombres rendait `tronquee: false` et le rapport pouvait
    sous-estimer la file en attente sans avertissement. Le signal se lit donc
    dans le JSON et se nomme dans le rendu lisible.
    """
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    tetes = {41: "k1", 42: "k2"}

    def faux_api(chemin: str):
        if "/search/" in chemin:
            return {"total_count": 2, "incomplete_results": True,
                    "items": [{"number": n} for n in tetes]}
        numero = int(chemin.split("/pulls/")[1].split("/")[0])
        if "/reviews" in chemin:
            return [_revue("myia-ai-01", "APPROVED", tetes[numero], "2026-11-24T18:00:00Z")]
        return {"number": numero, "head": {"sha": tetes[numero]}}

    monkeypatch.setattr(m, "api", faux_api)
    ouvertes = m.ouvertes_approuvees(jusqu_a)
    assert ouvertes["trouvees"] == 2
    assert ouvertes["inspectees"] == 2
    assert ouvertes["resultats_incomplets"] is True
    assert ouvertes["tronquee"] is True
    rapport = _rapport_echantillon()
    rapport["ouvertes_approuvees"] = ouvertes
    texte = m.formater(rapport)
    assert "resultats incomplets annonces par la recherche GitHub" in texte
    assert "plafond --max-ouvertes" not in texte


def test_formater_nomme_la_cause_du_plafond_des_ouvertes():
    """Le plafond et le signal GitHub sont deux causes, et le rendu les nomme."""
    rapport = _rapport_echantillon()
    rapport["ouvertes_approuvees"] = {
        "trouvees": 9, "inspectees": 2, "tronquee": True,
        "resultats_incomplets": False, "revues_incompletes": 0,
        "approbations_retirees": 0, "a_la_tete_exacte": 2,
        "au_dela_du_seuil": 1, "plus_ancienne_heures": 30.0,
    }
    texte = m.formater(rapport)
    assert "TRONQUEE : plafond --max-ouvertes atteint" in texte


def test_ouvertes_approuvees_compte_les_revues_incompletes(monkeypatch):
    """Temoin : une PR ouverte approuvee etait lue « sans approbation ».

    Sa page de revues 3 porte l'approbation a sa tete ; bornee a deux pages,
    la lecture ne la voit pas. Elle est comptee a part, pas comme une PR
    qu'aucune approbation n'attend.
    """
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    tetes = {21: "k1", 22: "k2"}
    pages_revues = {
        (21, 1): [_revue("myia-ai-01", "APPROVED", "k1", "2026-11-25T22:00:00Z")],
        (22, 1): [_revue("autre", "COMMENTED", "k2", "2026-11-25T21:00:00Z")] * 2,
        (22, 2): [_revue("autre", "COMMENTED", "k2", "2026-11-25T21:30:00Z")] * 2,
        (22, 3): [_revue("myia-ai-01", "APPROVED", "k2", "2026-11-25T22:00:00Z")],
    }

    def faux_api(chemin: str):
        if "/search/" in chemin:
            return {"total_count": 2, "items": [{"number": n} for n in tetes]}
        numero = int(chemin.split("/pulls/")[1].split("/")[0])
        if "/reviews" in chemin:
            return pages_revues.get((numero, int(chemin.rsplit("page=", 1)[1])), [])
        return {"number": numero, "head": {"sha": tetes[numero]}}

    monkeypatch.setattr(m, "api", faux_api)
    monkeypatch.setattr(m, "PAR_PAGE", 2)
    ouvertes = m.ouvertes_approuvees(jusqu_a, max_pages=2)
    assert ouvertes["inspectees"] == 2
    assert ouvertes["revues_incompletes"] == 1
    assert ouvertes["a_la_tete_exacte"] == 1
    assert ouvertes["au_dela_du_seuil"] == 0


def test_ouvertes_une_approbation_reprise_n_attend_pas_un_merge(monkeypatch):
    """Temoin : la regle ne tenait, cote ouvert, que par le filtre de recherche.

    La PR 31 est approuvee a sa tete depuis 30 h, puis le coordinateur
    demande des changements sur cette tete il y a 4 h. La recherche
    `review:approved` ne la liste plus, donc le lecteur ne la voyait pas ;
    lue quand meme (filtre en retard, population elargie), elle etait comptee
    « en attente de fusion depuis 30 h ».
    """
    jusqu_a = datetime(2026, 11, 26, tzinfo=timezone.utc)
    tetes = {31: "k1", 32: "k2"}
    revues = {
        31: [_revue("myia-ai-01", "APPROVED", "k1", "2026-11-24T18:00:00Z"),
             _revue("myia-ai-01", "CHANGES_REQUESTED", "k1", "2026-11-25T20:00:00Z")],
        # approuvee a sa tete il y a 30 h, jamais reprise : elle attend
        32: [_revue("myia-ai-01", "APPROVED", "k2", "2026-11-24T18:00:00Z")],
    }

    def faux_api(chemin: str):
        if "/search/" in chemin:
            return {"total_count": 2, "items": [{"number": n} for n in tetes]}
        numero = int(chemin.split("/pulls/")[1].split("/")[0])
        if "/reviews" in chemin:
            return revues[numero]
        return {"number": numero, "head": {"sha": tetes[numero]}}

    monkeypatch.setattr(m, "api", faux_api)
    ouvertes = m.ouvertes_approuvees(jusqu_a)
    assert ouvertes["a_la_tete_exacte"] == 1
    assert ouvertes["approbations_retirees"] == 1
    assert [ligne["numero"] for ligne in ouvertes["au_dela"]] == [32]
    assert ouvertes["plus_ancienne_heures"] == 30.0


def _rapport_echantillon(fenetre_complete: bool = True) -> dict:
    """Rapport a deux PRs inspectees sur neuf fusions ; la fenetre est complete sauf demande."""
    return {
        "fenetre": {"depuis": "2026-11-19T00:00:00Z", "jusqu_a": "2026-11-26T00:00:00Z"},
        "approuveur": "myia-ai-01",
        "seuil_heures": 24.0,
        "fusionnees_dans_la_fenetre": 9,
        "fenetre_complete": fenetre_complete,
        "inspectees": 2,
        "tronquee": True,
        "tete_exacte": {"n": 2, "sous_le_seuil": 1, "part_sous_le_seuil": 0.5,
                        "p50_heures": 2.0, "p90_heures": 30.0,
                        "min_heures": 1.0, "max_heures": 30.0},
        "tete_anterieure": 0,
        "approbation_retiree": 0,
        "approbation_apres_fusion": 0,
        "revues_incompletes": 0,
        "sans_approbation": 0,
    }


def test_formater_dit_les_approbations_reprises():
    rapport = _rapport_echantillon()
    rapport["approbation_retiree"] = 2
    texte = m.formater(rapport)
    assert "2 reprise(s) sur la tete par l'approbateur" in texte


def test_formater_dit_la_troncature():
    texte = m.formater(_rapport_echantillon())
    assert "TRONQUEE : --max-prs atteint" in texte
    assert "n'est pas lue en entier" not in texte
    assert "borne basse" not in texte
    assert "50.0 %" in texte
    assert "p90 30.00 h" in texte


def test_formater_dit_une_fenetre_incompletee_et_ses_deux_causes():
    texte = m.formater(_rapport_echantillon(fenetre_complete=False))
    assert "9 (borne basse)" in texte
    assert ("TRONQUEE : plafond de pages atteint sur une page pleine,"
            " la fenetre n'est pas lue en entier ; --max-prs atteint") in texte


def test_main_depuis_illisible_rend_2():
    assert m.main(["--depuis", "pas-une-date"]) == 2


def test_main_max_pages_inferieur_a_1_rend_2():
    assert m.main(["--depuis", "2026-11-25T00:00:00Z", "--max-pages", "0"]) == 2


def test_main_ecrit_le_json(monkeypatch, tmp_path, capsys):
    maintenant = datetime.now(timezone.utc)
    fusion = (maintenant - timedelta(hours=1)).isoformat().replace("+00:00", "Z")
    approbation = (maintenant - timedelta(hours=2, minutes=30)).isoformat().replace(
        "+00:00", "Z")
    page = [_pr(1, "a", fusion)]

    def faux_api(chemin: str):
        if "/reviews" in chemin:
            return [_revue("myia-ai-01", "APPROVED", "a", approbation)]
        return page if "page=1" in chemin else []

    monkeypatch.setattr(m, "api", faux_api)
    sortie = tmp_path / "a2m.json"
    depuis = (maintenant - timedelta(hours=3)).isoformat().replace("+00:00", "Z")
    assert m.main(["--depuis", depuis, "--json", "--out", str(sortie), "--sans-ouvertes"]) == 0
    ecrit = json.loads(sortie.read_text(encoding="utf-8"))
    assert ecrit["tete_exacte"]["n"] == 1
    assert ecrit["lignes"][0]["numero"] == 1
    assert json.loads(capsys.readouterr().out)["inspectees"] == 1
