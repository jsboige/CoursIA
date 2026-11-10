"""Tests de l'instrument de mesure de la duree du checkout (P1 du plan).

L'instrument ne se teste pas en l'executant contre l'API -- ce serait une
mesure, pas un test. Ce qui est teste ici, c'est ce qui **decide** de la
mesure :

1. **Le filtre de fenetre est reellement applique.** La forme
   `created%3E={since}` se decode en une cle `created>` que l'API ignore :
   l'instrument mesurait alors n'importe quelle fenetre, pendant que son
   rapport annoncait la fenetre demandee. Mesure du 2026-11-09 : 2 500 runs
   non filtres contre 733 filtres sur la meme fenetre de 2 h. Le test
   verifie la **chaine construite**, decodee par le parseur de requete.
2. **L'etape de heal est reconnue**, et pas seulement celle du checkout :
   c'est l'etape que la phase P1 deplace le cout vers, et un instrument qui
   ne la verrait pas lirait ce deplacement comme un gain.
3. **Les fonctions pures** (percentile, minutes, detection d'etape) ont un
   comportement explicite sur les cas limites.
"""

from __future__ import annotations

import sys
import urllib.parse
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import measure_checkout_p90 as mcp  # noqa: E402


# --- Le filtre de fenetre ---------------------------------------------------


def test_le_filtre_de_fenetre_est_reellement_applique() -> None:
    url = mcp.runs_url("2026-11-09T20:00:00Z", 1)
    params = urllib.parse.parse_qs(urllib.parse.urlparse(url).query)
    # La cle attendue par l'API Actions est `created`, avec l'operateur `>=`
    # dans la valeur. C'est ce qui rend le filtre operant.
    assert params["created"] == [">=2026-11-09T20:00:00Z"]


def test_la_forme_que_l_api_ignore_n_est_plus_utilisee() -> None:
    # `created%3E=` se decode en une cle `created>` : l'API ignore cette
    # cle, et le filtre ne porte alors sur rien.
    url = mcp.runs_url("2026-11-09T20:00:00Z", 1)
    assert "created%3E=" not in url
    assert "created=%3E%3D" in url


def test_l_url_porte_le_declencheur_la_page_et_la_fenetre() -> None:
    url = mcp.runs_url("2026-11-09T20:00:00Z", 3)
    params = urllib.parse.parse_qs(urllib.parse.urlparse(url).query)
    assert params["event"] == ["pull_request"]
    assert params["page"] == ["3"]
    assert params["per_page"] == ["100"]


# --- Les fonctions pures ----------------------------------------------------


def test_percentile_interpole_sur_une_liste_triee() -> None:
    # La regle de l'instrument est `index = int(fraction * (n - 1))`, donc
    # un p90 sur quatre valeurs est la **troisieme** (index 2), et un median
    # la deuxieme (index 1). Elle n'est pas changee ici : la changer
    # rendrait les mesures anterieures non comparables.
    assert mcp.percentile([1.0, 2.0, 3.0, 4.0], 0.9) == 3.0
    assert mcp.percentile([1.0, 2.0, 3.0, 4.0], 0.5) == 2.0


def test_percentile_ordonne_avant_de_prendre() -> None:
    # Sans tri, l'index 1 de [1, 4, 2, 3] rendrait 4.0 ; avec le tri, il
    # rend 2.0. C'est le tri qui rend la mesure juste.
    assert mcp.percentile([1.0, 4.0, 2.0, 3.0], 0.5) == 2.0


def test_percentile_d_une_liste_vide_vaut_zero() -> None:
    assert mcp.percentile([], 0.9) == 0.0


def test_minutes_calcule_la_duree_entre_deux_horodatages() -> None:
    assert mcp.minutes("2026-11-09T20:00:00Z", "2026-11-09T20:01:30Z") == 1.5


def test_minutes_rend_none_si_la_fin_precede_le_debut() -> None:
    assert mcp.minutes("2026-11-09T20:05:00Z", "2026-11-09T20:00:00Z") is None


def test_minutes_rend_none_sans_horodatage() -> None:
    assert mcp.minutes(None, "2026-11-09T20:00:00Z") is None
    assert mcp.minutes("2026-11-09T20:00:00Z", None) is None


# --- La detection des etapes ------------------------------------------------


def _step(name: str, start: str, end: str) -> dict:
    return {"name": name, "started_at": start, "completed_at": end}


def test_l_etape_de_checkout_est_reconnue() -> None:
    steps = [_step("Checkout repository", "2026-11-09T20:00:00Z", "2026-11-09T20:01:00Z")]
    assert mcp.step_minutes(steps, mcp.CHECKOUT_NAMES) == 1.0


def test_l_etape_de_heal_est_reconnue() -> None:
    steps = [
        _step(
            "Purger un work dir reutilise au graphe incomplet (#15387)",
            "2026-11-09T20:00:00Z",
            "2026-11-09T20:02:00Z",
        )
    ]
    assert mcp.step_minutes(steps, mcp.HEAL_NAMES) == 2.0


def test_le_nom_de_heal_sans_son_numero_d_issue_est_reconnu() -> None:
    # le marqueur est le debut du nom : la queue peut changer sans que la
    # mesure perde son objet.
    steps = [
        _step(
            "Purger un work dir reutilise",
            "2026-11-09T20:00:00Z",
            "2026-11-09T20:02:00Z",
        )
    ]
    assert mcp.step_minutes(steps, mcp.HEAL_NAMES) == 2.0


def test_une_etape_inconnue_rend_none() -> None:
    steps = [_step("Set up Python", "2026-11-09T20:00:00Z", "2026-11-09T20:00:30Z")]
    assert mcp.step_minutes(steps, mcp.CHECKOUT_NAMES) is None
    assert mcp.step_minutes(steps, mcp.HEAL_NAMES) is None


def test_une_liste_d_etapes_vide_rend_none() -> None:
    assert mcp.step_minutes([], mcp.CHECKOUT_NAMES) is None
    assert mcp.step_minutes(None, mcp.HEAL_NAMES) is None
