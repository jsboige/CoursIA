"""Tests du garde des quadruplets d'heure de cycle (#22736).

Le garde vit dans `scripts/ci/check_cycle_time_examples.py` : il verifie
les quadruplets `(date, heure UTC, heure locale, decalage)` ecrits dans les
fichiers normatifs, sur DEUX relations -- coherence interne (l'heure locale
est l'heure UTC plus le decalage) et coherence calendaire (le decalage est
celui en vigueur dans le fuseau de reference a CETTE date, heure d'ete
comprise).

L'instance fondatrice est le controle positif : le gabarit du skill
`coordinate` annoncait `2026-10-26 14:37 UTC / 16:37 locale (UTC+02:00)`.
Son arithmetique interne est juste (14:37 + 2 h = 16:37) ; c'est le couple
(date, decalage) qui est faux, parce que le 26/10/2026 est posterieur a la
fin de l'heure d'ete europeenne (25/10) -- Europe/Paris etait a UTC+01:00 ce
jour-la. Un garde qui ne verifie que l'arithmetique interne ne voit rien.

Ces tests prouvent que le garde **peut rougir** : sans quoi il ne serait pas
un garde (cf. `feedback_measured_criteria`).
"""

from __future__ import annotations

import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "coordination"))

from check_cycle_time_examples import (  # noqa: E402
    EXIT_DEFECT,
    EXIT_OK,
    EXIT_UNREACHABLE,
    scanner,
)
from cycle_time import (  # noqa: E402
    decalage_en_minutes,
    formater_decalage,
    rendre,
    rendre_json,
)

GARDE = REPO_ROOT / "scripts" / "ci" / "check_cycle_time_examples.py"
ZONE = "Europe/Paris"


def _arbre(tmp_path: Path, contenu: str, chemin: str = "docs/exemple.md") -> Path:
    """Ecrit un fichier normatif dans un arbre temporaire."""
    cible = tmp_path / chemin
    cible.parent.mkdir(parents=True, exist_ok=True)
    cible.write_text(contenu, encoding="utf-8")
    return cible


# --- l'instance fondatrice : le couple (date, decalage) est faux ---


def test_quadruplet_ete_tardif_rouge(tmp_path: Path) -> None:
    """L'instance mesuree rougit : 26/10/2026 est en UTC+01:00, pas +02:00."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-10-26 14:37 UTC / 16:37 locale (UTC+02:00)\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "DEFECT"
    relations = {a["relation"] for a in rapport["anomalies"]}
    # L'arithmetique interne est JUSTE (14:37 + 2 h = 16:37) : c'est bien la
    # relation calendaire qui tombe. Un garde qui ne verifierait que
    # l'arithmetique interne laisserait passer l'instance.
    assert relations == {"coherence-calendaire"}
    assert rapport["anomalies"][0]["attendu"] == "UTC+01:00"


def test_quadruplet_correct_ete_reste_vert(tmp_path: Path) -> None:
    """Le meme jour, avec le decalage reellement en vigueur : rien a dire."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-10-26 14:37 UTC / 15:37 locale (UTC+01:00)\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "CLEAN"
    assert rapport["anomalies"] == []
    assert len(rapport["quadruplets"]) == 1


def test_decalage_ete_manquant_en_hiver_rouge(tmp_path: Path) -> None:
    """15/07/2026 : Europe/Paris est en UTC+02:00, un decalage d'hiver tombe."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-07-15 14:37 UTC / 15:37 locale (UTC+01:00)\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "DEFECT"
    assert rapport["anomalies"][0]["attendu"] == "UTC+02:00"


def test_decalage_hiver_correct_reste_vert(tmp_path: Path) -> None:
    """15/01/2026 : Europe/Paris est en UTC+01:00 -- le quadruplet est juste."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-01-15 14:37 UTC / 15:37 locale (UTC+01:00)\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "CLEAN"


# --- coherence interne ---


def test_heure_locale_incoherente_rouge(tmp_path: Path) -> None:
    """L'heure locale n'est pas l'heure UTC plus le decalage : rouge."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-01-15 14:37 UTC / 16:37 locale (UTC+01:00)\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "DEFECT"
    assert rapport["anomalies"][0]["relation"] == "coherence-interne"
    assert rapport["anomalies"][0]["attendu"] == "15:37"


def test_date_locale_non_conforme_rouge(tmp_path: Path) -> None:
    """La date locale ecrite doit suivre le decalage (passage de minuit)."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-01-15 23:37 UTC / 2026-01-15 00:37 locale (UTC+01:00)\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "DEFECT"
    assert rapport["anomalies"][0]["attendu"] == "2026-01-16"


def test_passage_de_minuit_correct_vert(tmp_path: Path) -> None:
    """23:37 UTC + 1 h = le lendemain 00:37 : la date locale suit."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-01-15 23:37 UTC / 2026-01-16 00:37 locale (UTC+01:00)\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "CLEAN"


# --- marqueurs ---


def test_marqueur_exemption_saute_la_ligne(tmp_path: Path) -> None:
    """Une ligne qui RECITE un quadruplet faux peut s'exempter par motif."""
    _arbre(
        tmp_path,
        "on citait 2026-10-26 14:37 UTC / 16:37 locale (UTC+02:00) "
        "-- cycle-time-exempt: recitation du defaut\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "CLEAN"
    assert len(rapport["exemptes"]) == 1


def test_marqueur_zone_designe_le_fuseau_de_la_ligne(tmp_path: Path) -> None:
    """Une ligne qui parle d'un autre fuseau le designe elle-meme."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-10-26 14:37 UTC / 23:37 locale (UTC+09:00) "
        "-- cycle-time-zone: Asia/Tokyo\n",
    )
    rapport = scanner(tmp_path, ZONE, arbres=("docs",))
    assert rapport["verdict"] == "CLEAN"


# --- aucun compte fige ---


def test_aucun_compte_fige(tmp_path: Path) -> None:
    """Le garde verifie une RELATION : 0, 1 ou 3 quadruplets corrects restent
    verts, et le verdict ne porte aucun compte attendu."""
    _arbre(tmp_path, "rien ici\n")
    vide = scanner(tmp_path, ZONE, arbres=("docs",))
    assert vide["verdict"] == "CLEAN"
    assert vide["quadruplets"] == []

    _arbre(
        tmp_path,
        "Heure de cycle : 2026-01-15 14:37 UTC / 15:37 locale (UTC+01:00)\n"
        "Heure de cycle : 2026-07-15 14:37 UTC / 16:37 locale (UTC+02:00)\n",
        chemin="docs/autre.md",
    )
    deux = scanner(tmp_path, ZONE, arbres=("docs",))
    assert deux["verdict"] == "CLEAN"
    assert len(deux["quadruplets"]) == 2
    assert "attendu" not in deux


# --- le depot lui-meme ---


def test_depot_propre_est_vert() -> None:
    """Le depot au moment de la livraison ne porte aucun quadruple fautif.

    Ce test ne fige AUCUN compte d'exemples : il verifie qu'aucune
    contradiction n'est trouvee, pas qu'il y en a exactement N.
    """
    rapport = scanner(REPO_ROOT, ZONE)
    assert rapport["verdict"] == "CLEAN", rapport["anomalies"]


# --- CLI ---


def _cli(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(GARDE), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(REPO_ROOT),
        timeout=180,
    )


def test_cli_rc_1_sur_contradiction(tmp_path: Path) -> None:
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-10-26 14:37 UTC / 16:37 locale (UTC+02:00)\n",
    )
    proc = _cli(["--root", str(tmp_path)])
    assert proc.returncode == EXIT_DEFECT, proc.stdout
    assert "coherence-calendaire" in proc.stdout


def test_cli_rc_0_sur_depot_propre() -> None:
    proc = _cli(["--root", str(REPO_ROOT)])
    assert proc.returncode == EXIT_OK, proc.stdout
    assert "CLEAN" in proc.stdout


def test_cli_rc_2_sur_fuseau_inconnu(tmp_path: Path) -> None:
    """Un fuseau inconnu n'est PAS un vert : la mesure est impossible."""
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-01-15 14:37 UTC / 15:37 locale (UTC+01:00)\n",
    )
    proc = _cli(["--root", str(tmp_path), "--zone", "Zone/Inexistante"])
    assert proc.returncode == EXIT_UNREACHABLE, proc.stdout
    # Le motif est sur stderr : l'instrument n'a pas rendu de verdict, il ne
    # doit pas ecrire un rapport de verdict sur stdout.
    assert "UNKNOWN" in proc.stderr


def test_cli_json_reste_parseable(tmp_path: Path) -> None:
    _arbre(
        tmp_path,
        "Heure de cycle : 2026-10-26 14:37 UTC / 16:37 locale (UTC+02:00)\n",
    )
    proc = _cli(["--root", str(tmp_path), "--json"])
    rapport = json.loads(proc.stdout)
    assert rapport["verdict"] == "DEFECT"
    assert proc.returncode == EXIT_DEFECT


# --- l'emetteur (volet 1) ---


def test_emetteur_rend_le_format_prescrit() -> None:
    moment = datetime(2026, 10, 26, 14, 37, 16, tzinfo=timezone.utc)
    entete = rendre(moment, zone=ZONE)
    assert entete == (
        "Heure de cycle : 2026-10-26 14:37:16 UTC / 15:37:16 locale (UTC+01:00)"
    )


def test_emetteur_suit_le_decalage_reel_de_la_machine() -> None:
    """Le decalage sort de la bibliotheque, il n'est pas memore."""
    moment = datetime(2026, 7, 15, 14, 37, 16, tzinfo=timezone.utc)
    entete = rendre(moment, zone=ZONE)
    assert entete.endswith("(UTC+02:00)")  # aout : heure d'ete europeenne
    moment = datetime(2026, 1, 15, 14, 37, 16, tzinfo=timezone.utc)
    assert rendre(moment, zone=ZONE).endswith("(UTC+01:00)")


def test_emetteur_ajoute_la_date_locale_au_passage_de_minuit() -> None:
    moment = datetime(2026, 1, 15, 23, 37, 16, tzinfo=timezone.utc)
    entete = rendre(moment, zone=ZONE)
    assert entete == (
        "Heure de cycle : 2026-01-15 23:37:16 UTC / 2026-01-16 00:37:16 locale "
        "(UTC+01:00)"
    )


def test_emetteur_json_porte_la_meme_information() -> None:
    moment = datetime(2026, 10, 26, 14, 37, 16, tzinfo=timezone.utc)
    payload = rendre_json(moment, zone=ZONE)
    assert payload["offset"] == "+01:00"
    assert payload["header"].startswith("Heure de cycle : ")


def test_formateur_de_decalage() -> None:
    assert formater_decalage("+0100") == "+01:00"
    assert formater_decalage("-0500") == "-05:00"
    assert decalage_en_minutes("+01:00") == 60
    assert decalage_en_minutes("-05:30") == -330
