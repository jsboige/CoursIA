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
   approbation perimee par un push n'attend rien.

Les appels reseau sont remplaces par une fonction `api` factice : les tests ne
dependent ni du reseau ni du quota.
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
    ]
    agregat = m.resume(lignes)
    assert agregat["tete_exacte"]["n"] == 1
    assert agregat["tete_anterieure"] == 1
    assert agregat["sans_approbation"] == 2


# --- lecture de la fenetre, borne et bout en bout --------------------------

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
    trouvees = m.fusionnees(depuis, jusqu_a)
    assert [pr["number"] for pr in trouvees] == [1]


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
    assert rapport["inspectees"] == 2
    assert rapport["tronquee"] is True
    assert rapport["tete_exacte"]["n"] == 2
    assert rapport["tete_exacte"]["part_sous_le_seuil"] == 1.0


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
        if chemin.endswith("/reviews?per_page=100"):
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


def test_formater_dit_la_troncature():
    rapport = {
        "fenetre": {"depuis": "2026-11-19T00:00:00Z", "jusqu_a": "2026-11-26T00:00:00Z"},
        "approuveur": "myia-ai-01",
        "seuil_heures": 24.0,
        "fusionnees_dans_la_fenetre": 9,
        "inspectees": 2,
        "tronquee": True,
        "tete_exacte": {"n": 2, "sous_le_seuil": 1, "part_sous_le_seuil": 0.5,
                        "p50_heures": 2.0, "p90_heures": 30.0,
                        "min_heures": 1.0, "max_heures": 30.0},
        "tete_anterieure": 0,
        "sans_approbation": 0,
    }
    texte = m.formater(rapport)
    assert "TRONQUEE" in texte
    assert "50.0 %" in texte
    assert "p90 30.00 h" in texte


def test_main_depuis_illisible_rend_2():
    assert m.main(["--depuis", "pas-une-date"]) == 2


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
