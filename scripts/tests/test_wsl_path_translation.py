"""Tests de la traduction de chemins Windows -> WSL par wsl_papermill.

Le defaut vise (#11703, mesure 2026-10-08) : un ``--cwd`` pointant sur un lac
vivant sur le disque propre de la VM (ext4, hors /mnt) passe par un chemin UNC
``\\\\wsl.localhost\\<distro>\\...`` ; ``win_to_wsl_path`` ne traduisait que
les lettres de lecteur, donc le chemin UNC arrivait **tel quel** dans bash, ou
aucun lakefile n'est trouve. La re-execution d'un carnet contre un lac ext4
(complet) etait structurellement impossible depuis Windows.

Un motif de traduction se valide par ses formes frontieres : les cas
``unchanged`` ci-dessous sont les faux positifs qui auraient corrompu un
chemin sain (UNC reseau ordinaire, racine de distro, POSIX pur).

Regression #2871 : les cas lettre-de-lecteur (majuscule, minuscule,
separateurs mixtes) doivent continuer de rendre la forme /mnt.
"""

import sys
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[1] / "notebook_tools"
sys.path.insert(0, str(TOOLS))

from wsl_papermill import win_to_wsl_path  # noqa: E402


# --- UNC vers le systeme de fichiers WSL : formes qui DOIVENT traduire ---

def test_unc_wsl_localhost_backslashes():
    assert win_to_wsl_path(
        "\\\\wsl.localhost\\Ubuntu\\home\\jesse\\k26lake\\discrepancy_lean"
    ) == "/home/jesse/k26lake/discrepancy_lean"


def test_unc_legacy_wsl_dollar():
    assert win_to_wsl_path("\\\\wsl$\\Ubuntu\\home\\jesse\\lac") == "/home/jesse/lac"


def test_unc_forward_slashes():
    assert win_to_wsl_path("//wsl.localhost/Ubuntu/home/jesse/lac") == "/home/jesse/lac"


def test_unc_case_insensitive_host():
    assert win_to_wsl_path("\\\\WSL.LOCALHOST\\Ubuntu\\home\\x") == "/home/x"


def test_unc_distro_name_is_dropped_not_kept():
    # la distro nommee dans le partage disparait du resultat : le chemin rendu
    # est le chemin DANS la VM, pas un chemin /mnt de la distro
    out = win_to_wsl_path("\\\\wsl.localhost\\Ubuntu-22.04\\home\\jesse\\lac")
    assert out == "/home/jesse/lac"
    assert "Ubuntu" not in out


# --- Formes frontieres : doivent rester INCHANGEES (faux positifs) ---

def test_posix_path_unchanged():
    assert win_to_wsl_path("/home/jesse/lac") == "/home/jesse/lac"


def test_ordinary_network_unc_unchanged():
    # un UNC reseau ordinaire n'est PAS un partage WSL : le traduire en /
    # fabriquerait un chemin inexistant
    assert win_to_wsl_path("\\\\server\\share\\repo") == "\\\\server\\share\\repo"


def test_distro_root_without_rest_unchanged():
    assert win_to_wsl_path("\\\\wsl.localhost\\Ubuntu") == "\\\\wsl.localhost\\Ubuntu"


def test_bare_host_unchanged():
    assert win_to_wsl_path("\\\\wsl.localhost") == "\\\\wsl.localhost"


# --- Regression #2871 : lettre de lecteur, formes historiques ---

def test_drive_uppercase_backslash():
    assert win_to_wsl_path("D:\\dev\\CoursIA") == "/mnt/d/dev/CoursIA"


def test_drive_lowercase_forward_slash():
    assert win_to_wsl_path("d:/dev/x") == "/mnt/d/dev/x"
