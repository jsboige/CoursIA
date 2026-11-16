"""#26926 : le tapis lourd refuse de servir des grains hors diagnostic.

Le tapis lourd (``pick_idle_grain.py --belt``) mettait ~240 s a rendre des
grains non verifies. La consigne ecrite ne suffisait pas : une lane qui le
tirait de memoire repartait pour quatre minutes. Le refus vit dans l'organe,
et ces tests le tiennent : il rend la main tout de suite, sans aucun appel
sortant, et nomme le tapis rapide.
"""
from __future__ import annotations

import json
import subprocess

import pytest

import pick_idle_grain as pig

LANE = "myia-po-2025:CoursIA"


@pytest.fixture
def sans_diagnostic(monkeypatch):
    monkeypatch.delenv(pig.HEAVY_BELT_DIAGNOSTIC_ENV, raising=False)

    def _refuse(*args, **kwargs):
        raise AssertionError("le refus du tapis lourd ne doit lancer aucun processus")

    monkeypatch.setattr(subprocess, "run", _refuse)
    monkeypatch.setattr(subprocess, "Popen", _refuse)


def test_belt_sans_diagnostic_refuse_et_nomme_le_tapis_rapide(sans_diagnostic, capsys):
    rc = pig.main(["--lane", LANE, "--belt", "--json"])
    assert rc == 2
    refus = json.loads(capsys.readouterr().out)
    assert refus["mode"] == "tapis-lourd-refuse"
    assert refus["issue"] == 26926
    assert "tapis_rapide.py" in refus["commande"]
    assert LANE in refus["commande"]


def test_belt_sans_diagnostic_en_texte(sans_diagnostic, capsys):
    rc = pig.main(["--lane", LANE, "--belt"])
    assert rc == 2
    out = capsys.readouterr().out
    assert out.startswith("REFUS (#26926)")
    assert f'tapis_rapide.py --lane "{LANE}" --json' in out


def test_belt_sans_lane_donne_le_gabarit(sans_diagnostic, capsys):
    rc = pig.main(["--belt", "--json"])
    assert rc == 2
    assert "<machine:workspace>" in json.loads(capsys.readouterr().out)["commande"]


def test_le_refus_ne_touche_pas_les_autres_modes(sans_diagnostic, capsys):
    # Controle negatif : sans --belt, le refus ne s'applique pas. L'erreur
    # d'argument vient de la validation ordinaire, pas du refus du tapis.
    with pytest.raises(SystemExit):
        pig.main([])
    assert "tapis-lourd-refuse" not in capsys.readouterr().out
