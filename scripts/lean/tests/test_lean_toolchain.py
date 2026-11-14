"""Tests de l'organe d'epinglage de la toolchain Lean (issue #24568).

L'organe ``scripts/lean/lean_toolchain.py`` detient la resolution du pin de
toolchain et la declaration par environnement. Ces tests eprouvent :

* l'ordre de resolution, palier par palier, sans reseau et sans elan reel
  (la mesure du defaut elan est injectee) ;
* que la declaration est lue dans le **fichier** (pas une constante codee) ;
* que le repli n'est plus un tag absent du parc (``v4.27.0``) ;
* que le pin de flotte declare est un tag reellement employe par les lakes du
  depot (temoin externe, independant de l'organe) ;
* que le controle de derive distingue « pin non reproductible » et
  « defaut elan local different de la declaration » ;
* que la mesure du defaut elan est **paresseuse** (aucune quand un palier
  plus haut tranche) et qu'une entree de declaration mal formee est
  signalee.

Convention : import par chemin, comme les autres tests de ``scripts/lean/``.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from lean_toolchain import (  # noqa: E402
    INVENTORY_FILENAME,
    LAST_RESORT_TOOLCHAIN,
    check_drift,
    current_host,
    declared_pin,
    fleet_pin,
    installed_toolchain,
    inventory_path,
    load_inventory,
    repo_root,
    resolve_pin,
    toolchain_from_version,
)

#: Tag du defaut elan simule (le defaut mesure sur ai-01 le 2026-11-10).
FAKE_ELAN_DEFAULT = "leanprover/lean4:v4.11.0"

#: Declaration d'un poste qui n'existe pas dans l'inventaire.
UNKNOWN_HOST = "poste-sans-declaration"


def _inventory(**kwargs) -> dict:
    """Inventaire de test : pin de flotte + une declaration d'hote."""
    base = {
        "schema": 1,
        "fleet_pin": "leanprover/lean4:v4.33.0",
        "environments": {
            "poste-declare": {
                "toolchain": "leanprover/lean4:v4.33.1",
                "elan_default": FAKE_ELAN_DEFAULT,
            }
        },
    }
    base.update(kwargs)
    return base


# -- lecture de la declaration -------------------------------------------------


def test_inventory_file_is_read_by_the_organ():
    """La declaration vient d'un fichier lu, pas d'une constante codee."""
    path = inventory_path()
    assert path.name == INVENTORY_FILENAME
    assert path.exists(), f"declaration absente : {path}"
    inventory = load_inventory()
    assert inventory.get("fleet_pin"), "pin de flotte absent de la declaration"
    assert isinstance(inventory.get("environments"), dict)


def test_declared_pin_is_case_insensitive_on_the_host_key():
    inventory = _inventory()
    assert declared_pin(inventory, "POSTE-DECLARE") == "leanprover/lean4:v4.33.1"
    assert declared_pin(inventory, UNKNOWN_HOST) is None


def test_load_inventory_survives_a_missing_file(tmp_path):
    """Une declaration absente degrade la resolution, elle n'interrompt pas."""
    assert load_inventory(tmp_path) == {}


# -- ordre de resolution --------------------------------------------------------


def test_environment_pin_is_read_verbatim(tmp_path):
    """``ELAN_TOOLCHAIN`` est lu TEL QUEL (jamais reconstruit)."""
    pin = "leanprover/lean4:v4.34.0-rc2"
    tag, provenance = resolve_pin(
        tmp_path,
        env={"ELAN_TOOLCHAIN": pin},
        inventory=_inventory(),
        host=UNKNOWN_HOST,
        installed=FAKE_ELAN_DEFAULT,
    )
    assert (tag, provenance) == (pin, "env")


def test_project_pin_wins_over_the_declaration(tmp_path):
    """Un projet fourni impose son propre pin."""
    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.32.1\n",
                                             encoding="utf-8")
    tag, provenance = resolve_pin(
        tmp_path,
        env={},
        inventory=_inventory(),
        host="poste-declare",
        installed=FAKE_ELAN_DEFAULT,
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.32.1", "projet")


def test_declaration_wins_over_the_resolved_default():
    """La declaration de l'hote prime sur le defaut elan mesure.

    C'est le coeur du correctif : sans declaration, chaque poste suivait son
    propre defaut elan (v4.11.0 sur ai-01, v4.35.0 ailleurs).
    """
    tag, provenance = resolve_pin(
        None,
        env={},
        inventory=_inventory(),
        host="poste-declare",
        installed=FAKE_ELAN_DEFAULT,
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.33.1", "declaration")


def test_fleet_pin_is_used_when_the_host_declares_nothing():
    tag, provenance = resolve_pin(
        None,
        env={},
        inventory=_inventory(),
        host=UNKNOWN_HOST,
        installed=FAKE_ELAN_DEFAULT,
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.33.0", "declaration_flotte")


def test_resolved_default_is_reached_only_without_any_declaration():
    """Le defaut elan reste le palier « non fige », en dernier resort."""
    tag, provenance = resolve_pin(
        None,
        env={},
        inventory={},
        host=UNKNOWN_HOST,
        installed=FAKE_ELAN_DEFAULT,
    )
    assert (tag, provenance) == (FAKE_ELAN_DEFAULT, "default_resolu")


def test_no_project_pin_is_read_when_no_project_is_given(tmp_path, monkeypatch):
    """Sans projet fourni, aucun ``lean-toolchain`` n'est consulte.

    Le squelette gere (``~/.cache/rlvr-lean``) ecrit son propre pin : le
    relire comme un pin de projet masquerait la provenance reelle au second
    lancement.
    """
    monkeypatch.chdir(tmp_path)
    (tmp_path / "lean-toolchain").write_text("leanprover/lean4:v4.99.0\n",
                                             encoding="utf-8")
    tag, provenance = resolve_pin(
        None,
        env={},
        inventory=_inventory(),
        host=UNKNOWN_HOST,
        installed=FAKE_ELAN_DEFAULT,
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.33.0", "declaration_flotte")
    assert tag != "leanprover/lean4:v4.99.0"


def test_fallback_warns_and_uses_a_park_present_tag(caplog):
    """Aucun pin, aucune declaration, defaut elan inmesurable -> repli alerte."""
    import logging

    with caplog.at_level(logging.WARNING):
        tag, provenance = resolve_pin(
            None,
            env={},
            inventory={},
            host=UNKNOWN_HOST,
            installed=None,
        )
    assert provenance == "fallback_averti"
    assert tag == LAST_RESORT_TOOLCHAIN
    assert "téléchargement elan peut être requis" in caplog.text


def test_last_resort_is_not_the_tag_absent_from_the_park():
    """Le repli historique ``v4.27.0`` ne peut plus etre atteint.

    Il n'etait installe sur aucun poste mesure : chaque rollout declenchait
    un telechargement elan.
    """
    assert LAST_RESORT_TOOLCHAIN != "leanprover/lean4:v4.27.0"
    assert LAST_RESORT_TOOLCHAIN.startswith("leanprover/lean4:v")


def test_inventory_fleet_pin_agrees_with_the_last_resort_constant():
    """La declaration et la constante de repli ne peuvent pas diverger."""
    assert fleet_pin(load_inventory()) == LAST_RESORT_TOOLCHAIN


def test_fleet_pin_is_a_tag_the_repo_lakes_actually_use():
    """Temoin externe : le pin de flotte est employe par les lakes du depot.

    Le calcul est fait sur les fichiers ``lean-toolchain`` versionnes (via
    ``git ls-files``), donc sur l'etat commite — pas sur l'arbre de travail.
    """
    root = repo_root()
    try:
        completed = subprocess.run(
            ["git", "ls-files", "*lean-toolchain"],
            cwd=str(root), capture_output=True, text=True,
            encoding="utf-8", errors="replace", check=True,
        )
    except (OSError, subprocess.SubprocessError):  # pragma: no cover
        pytest.skip("git indisponible : temoin externe non mesurable")
    pins = set()
    for relative in completed.stdout.split():
        first = (root / relative).read_text(encoding="utf-8").splitlines()[:1]
        if first:
            pins.add(first[0].strip())
    declared = fleet_pin(load_inventory())
    assert declared in pins, (
        f"pin de flotte {declared} absent des lean-toolchain du depot "
        f"({sorted(pins)})")


# -- mesure du defaut elan ------------------------------------------------------


def _fake_lean(tmp_path, monkeypatch, version="4.11.0"):
    """Binaire ``lean`` factice, executable sur la plateforme du runner.

    Windows execute un ``.bat`` via PATHEXT ; POSIX execute un script ``sh``.
    Le contenu est identique : la mesure de l'organe doit lire la version
    rapportee, pas la plateforme.
    """
    bindir = tmp_path / "bin"
    bindir.mkdir()
    if os.name == "nt":
        lean = bindir / "lean.bat"
        lean.write_text(f'@echo Lean (version {version}, fake)\n', encoding="utf-8")
    else:
        lean = bindir / "lean"
        lean.write_text(f'#!/bin/sh\necho "Lean (version {version}, fake)"\n',
                        encoding="utf-8")
        lean.chmod(0o755)
    monkeypatch.setenv("PATH", str(bindir))
    monkeypatch.setenv("HOME", str(tmp_path))
    # elan respecte ELAN_HOME : on le pointe vers un repertoire vide pour
    # que le proxy elan du poste n'ecrase pas le faux binaire (le proxy
    # echoue au lieu de repondre quand il ne trouve aucune toolchain).
    monkeypatch.setenv("ELAN_HOME", str(tmp_path / "elan"))
    (tmp_path / "elan" / "bin").mkdir(parents=True)
    (tmp_path / ".elan" / "bin").mkdir(parents=True)


def test_version_is_reconstructed_into_an_elan_tag():
    """La reconstruction est une fonction pure : aucun processus, meme OS."""
    assert toolchain_from_version(
        "Lean (version 4.11.0, x86_64-w64-windows-gnu, commit abc, Release)"
    ) == "leanprover/lean4:v4.11.0"
    assert toolchain_from_version("Lean (version 4.35.0, fake)") == (
        "leanprover/lean4:v4.35.0")
    assert toolchain_from_version("command not found") is None
    assert toolchain_from_version("") is None


@pytest.mark.skipif(
    os.name == "nt",
    reason=("Windows : CreateProcess resout 'lean' dans le PATH du processus "
            "parent et n'essaie que '.exe' — un faux binaire script ne peut "
            "pas etre declenche. La reconstruction pure est couverte par le "
            "test precedent ; la mesure complete est exercee par la CI Linux."))
def test_installed_toolchain_is_measured_from_the_binary_on_the_path(
        tmp_path, monkeypatch):
    _fake_lean(tmp_path, monkeypatch, version="4.11.0")
    assert installed_toolchain() == "leanprover/lean4:v4.11.0"


def test_installed_toolchain_is_none_when_no_binary_answers(tmp_path, monkeypatch):
    monkeypatch.setenv("PATH", str(tmp_path / "vide"))
    monkeypatch.setenv("HOME", str(tmp_path))
    monkeypatch.setenv("ELAN_HOME", str(tmp_path / "elan"))
    assert installed_toolchain() is None


def test_current_host_is_a_lowercase_key():
    host = current_host()
    assert host == host.lower()
    assert host


# -- controle de derive ---------------------------------------------------------


def test_check_drift_is_not_flagged_when_the_fleet_pin_applies():
    """Un hote sans declaration propre suit le pin de flotte : reproductible."""
    report = check_drift(
        env={}, inventory=_inventory(), host=UNKNOWN_HOST,
        installed=FAKE_ELAN_DEFAULT,
    )
    assert report["drift"] is False
    assert report["effective"] == "leanprover/lean4:v4.33.0"
    assert report["provenance"] == "declaration_flotte"
    assert report["local_default_drift"] is True


def test_check_drift_flags_a_host_without_any_declaration():
    """Sans declaration ni pin de flotte, le pin effectif suit l'hote : derive."""
    report = check_drift(
        env={}, inventory={}, host=UNKNOWN_HOST,
        installed=FAKE_ELAN_DEFAULT,
    )
    assert report["drift"] is True
    assert report["provenance"] == "default_resolu"


def test_check_drift_flags_the_last_resort_fallback():
    report = check_drift(
        env={}, inventory={}, host=UNKNOWN_HOST, installed=None,
    )
    assert report["drift"] is True
    assert report["provenance"] == "fallback_averti"
    assert report["effective"] == LAST_RESORT_TOOLCHAIN


def test_check_drift_is_silent_when_the_host_declares_its_pin():
    report = check_drift(
        env={}, inventory=_inventory(), host="poste-declare",
        installed=FAKE_ELAN_DEFAULT,
    )
    assert report["drift"] is False
    assert report["effective"] == "leanprover/lean4:v4.33.1"
    assert report["local_default_drift"] is True
    assert report["elan_default"] == FAKE_ELAN_DEFAULT


def test_check_drift_reports_the_environments_that_diverge_from_the_fleet():
    inventory = _inventory()
    inventory["environments"]["poste-divergent"] = {
        "toolchain": "leanprover/lean4:v4.35.0",
    }
    report = check_drift(
        env={}, inventory=inventory, host="poste-declare",
        installed=FAKE_ELAN_DEFAULT,
    )
    divergents = {entry["host"]: entry["toolchain"] for entry in report["fleet_drift"]}
    assert divergents["poste-divergent"] == "leanprover/lean4:v4.35.0"
    assert "poste-declare" in divergents, (
        "une declaration differente du pin de flotte est aussi une derive")


def test_check_drift_reports_a_local_default_that_differs_from_the_declaration():
    """Le defaut elan local n'est pas le pin : il est signale, sans etre fatal."""
    report = check_drift(
        env={}, inventory=_inventory(), host="poste-declare",
        installed="leanprover/lean4:v4.11.0",
    )
    assert report["declared"] == "leanprover/lean4:v4.33.1"
    assert report["local_default_drift"] is True


def test_inventory_is_valid_json():
    """Le fichier de declaration est du JSON valide et son schema est declare."""
    raw = inventory_path().read_text(encoding="utf-8")
    data = json.loads(raw)
    assert data["schema"] == 1
    for host, entry in data["environments"].items():
        assert isinstance(entry.get("toolchain"), str), host
        assert entry["toolchain"].startswith("leanprover/lean4:"), host


# -- mesure paresseuse du defaut elan -------------------------------------------
#
# Une mesure lance un ``lean --version`` par le proxy elan : sur un poste ou
# le defaut n'est pas installe, elle peut declencher un telechargement. Elle
# ne doit donc avoir lieu qu'au palier 5, quand aucun palier plus haut ne
# tranche.


def _forbidden_loader():
    """Loader qui echoue si la mesure a lieu."""

    def loader():
        raise AssertionError("le defaut elan n'aurait pas du etre mesure")

    return loader


def test_no_measurement_when_the_environment_pin_decides(tmp_path):
    """``ELAN_TOOLCHAIN`` posee : aucun ``lean --version`` n'est lance."""
    tag, provenance = resolve_pin(
        tmp_path,
        env={"ELAN_TOOLCHAIN": "leanprover/lean4:v4.34.0"},
        inventory=_inventory(),
        host=UNKNOWN_HOST,
        loader=_forbidden_loader(),
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.34.0", "env")


def test_no_measurement_when_the_declaration_decides(tmp_path):
    """Une declaration d'hote suffit : le defaut elan n'est pas mesure."""
    tag, provenance = resolve_pin(
        tmp_path,
        env={},
        inventory=_inventory(),
        host="poste-declare",
        loader=_forbidden_loader(),
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.33.1", "declaration")


def test_no_measurement_when_the_fleet_pin_decides(tmp_path):
    """Le pin de flotte suffit : le defaut elan n'est pas mesure."""
    tag, provenance = resolve_pin(
        tmp_path,
        env={},
        inventory=_inventory(),
        host=UNKNOWN_HOST,
        loader=_forbidden_loader(),
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.33.0", "declaration_flotte")


def test_measurement_happens_once_and_only_at_the_last_stage(tmp_path):
    """Le defaut elan n'est mesure qu'au palier 5, et une seule fois."""
    calls: list[int] = []

    def loader():
        calls.append(1)
        return FAKE_ELAN_DEFAULT

    tag, provenance = resolve_pin(
        tmp_path,
        env={},
        inventory={},
        host=UNKNOWN_HOST,
        loader=loader,
    )
    assert (tag, provenance) == (FAKE_ELAN_DEFAULT, "default_resolu")
    assert len(calls) == 1


def test_check_drift_measures_the_default_only_once():
    """Le controle de derive et la resolution partagent une seule mesure."""
    calls: list[int] = []

    def loader():
        calls.append(1)
        return FAKE_ELAN_DEFAULT

    report = check_drift(env={}, inventory={}, host=UNKNOWN_HOST, loader=loader)
    assert report["elan_default"] == FAKE_ELAN_DEFAULT
    assert len(calls) == 1


# -- entrees mal formees et lectures non UTF-8 -----------------------------------


def test_malformed_host_entry_is_reported_and_ignored(caplog):
    """Une entree d'hote mal formee est signalee, pas silencieusement ignoree."""
    import logging

    inventory = _inventory()
    inventory["environments"]["poste-malforme"] = "leanprover/lean4:v4.33.0"
    with caplog.at_level(logging.WARNING):
        assert declared_pin(inventory, "poste-malforme") is None
    assert "mal formee" in caplog.text


def test_malformed_toolchain_field_is_reported_and_ignored(caplog):
    """Un ``toolchain`` qui n'est pas une chaine est signale puis ignore."""
    import logging

    inventory = _inventory()
    inventory["environments"]["poste-bad-type"] = {"toolchain": 42}
    with caplog.at_level(logging.WARNING):
        assert declared_pin(inventory, "poste-bad-type") is None
    assert "mal formee" in caplog.text


def test_an_absent_declaration_is_not_reported_as_malformed(caplog):
    """Une entree sans ``toolchain`` n'est pas une malformation : rien n'est dit."""
    import logging

    inventory = _inventory()
    inventory["environments"]["poste-sans-pin"] = {"elan_default": FAKE_ELAN_DEFAULT}
    with caplog.at_level(logging.WARNING):
        assert declared_pin(inventory, "poste-sans-pin") is None
    assert "mal formee" not in caplog.text


def test_project_pin_that_is_not_utf8_is_ignored(tmp_path):
    """Un ``lean-toolchain`` non UTF-8 ne casse pas le constructeur."""
    (tmp_path / "lean-toolchain").write_bytes(b"leanprover/lean4:v4.32.1\n\xff\xfe")
    tag, provenance = resolve_pin(
        tmp_path,
        env={},
        inventory=_inventory(),
        host="poste-declare",
        installed=FAKE_ELAN_DEFAULT,
    )
    assert (tag, provenance) == ("leanprover/lean4:v4.33.1", "declaration")


def test_load_inventory_survives_a_non_utf8_file(tmp_path):
    """Une declaration illisible degrade la resolution, elle n'interrompt pas."""
    path = tmp_path / "scripts" / "lean" / INVENTORY_FILENAME
    path.parent.mkdir(parents=True)
    path.write_bytes(b'{"fleet_pin": "\xff"}')
    assert load_inventory(tmp_path) == {}
