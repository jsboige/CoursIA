# -*- coding: utf-8 -*-
"""Tests de check_companion_coverage.py (#10643, criteres 2-3).

Les fonctions pures (perimetre, appariement, classification bi-OS) sont
testees ici ; la passe git (``git ls-files``) reste au main, couvert par
l'execution CI du garde lui-meme sur le corpus reel.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

MODULE_PATH = (Path(__file__).resolve().parents[1] / "ci"
               / "check_companion_coverage.py")
spec = importlib.util.spec_from_file_location(
    "check_companion_coverage", MODULE_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_companion_coverage"] = mod
spec.loader.exec_module(mod)


class TestInScope:
    def test_vibe_coding_hors_scope(self):
        assert not mod.in_scope(
            "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Scripts/clean.ps1")

    def test_docs_archive_hors_scope(self):
        assert not mod.in_scope("docs/archive/suivis/x/legacy.ps1")

    def test_archive_interne_hors_scope(self):
        assert not mod.in_scope("scripts/genai-stack/_archive/manage.ps1")

    def test_windows_par_nature_exempt(self):
        assert not mod.in_scope(
            "docker-configurations/services/tts-multi/"
            "setup-iis-reverse-proxy.ps1")

    def test_infra_reelle_in_scope(self):
        assert mod.in_scope("scripts/environment/setup_environment.ps1")


class TestCompanionOf:
    def test_meme_stem(self):
        sh = {"scripts/environment/setup_environment.sh"}
        assert mod.companion_of(
            "scripts/environment/setup_environment.ps1", sh) == \
            "scripts/environment/setup_environment.sh"

    def test_stem_absent(self):
        assert mod.companion_of("a/b/seul.ps1", {"a/b/autre.sh"}) is None

    def test_split_naming_mappe(self):
        sh = {"MyIA.AI.Notebooks/GameTheory/scripts/setup_lean4_native.sh"}
        assert mod.companion_of(
            "MyIA.AI.Notebooks/GameTheory/scripts/setup_lean4_kernel.ps1",
            sh) == "MyIA.AI.Notebooks/GameTheory/scripts/setup_lean4_native.sh"

    def test_split_naming_sans_compagnon(self):
        # le mapping split-naming ne pardonne pas : le compagnon nomme
        # doit exister, aucun fallback par stem.
        assert mod.companion_of(
            "MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_kernel.ps1",
            {"MyIA.AI.Notebooks/GameTheory/scripts/setup_wsl_kernel.sh"}) \
            is None


class TestBiosState:
    def test_windows_only(self):
        nb = {"cells": [
            {"cell_type": "code", "source": ["powershell -File run.ps1"]},
            {"cell_type": "markdown", "source": ["# Intro"]},
        ]}
        assert mod.bios_state(nb) == "windows-only"

    def test_les_deux_chemins(self):
        nb = {"cells": [
            {"cell_type": "code", "source": ["powershell -File run.ps1"]},
            {"cell_type": "code", "source": ["bash run.sh"]},
        ]}
        assert mod.bios_state(nb) == "ok"

    def test_geste_cs_isosplatform_compte_comme_unix(self):
        # faux positif calibre sur Infer-1-Setup : la cellule C# gere
        # deja les deux OS -- ce n'est PAS un carnet windows-only.
        nb = {"cells": [
            {"cell_type": "code", "source": [
                "// winget install graphviz\n",
                "var p = RuntimeInformation.IsOSPlatform(OSPlatform.OSX)",
            ]},
        ]}
        assert mod.bios_state(nb) == "ok"

    def test_prose_seule_pas_windows_only(self):
        # une mention en prose ("sous Windows") n'est pas une invocation.
        nb = {"cells": [
            {"cell_type": "markdown", "source": [
                "Sous Windows, utiliser winget pour Graphviz."]},
            {"cell_type": "code", "source": ["!pip install pyphi"]},
        ]}
        assert mod.bios_state(nb) == "ok"

    def test_os_neutre_ok(self):
        nb = {"cells": [
            {"cell_type": "code", "source": ["!pip install infer-ui"]},
        ]}
        assert mod.bios_state(nb) == "ok"


class TestIsSetupNotebook:
    @pytest.mark.parametrize("name", [
        "Probas/Infer/Infer-1-Setup.ipynb",
        "GenAI/00-GenAI-Environment/00-1-Environment-Setup.ipynb",
        "Sudoku/Sudoku-00-Environment-CSharp.ipynb",
        "Planners/00-Environment/Planners-0-Setup.ipynb",
    ])
    def test_noms_setup(self, name):
        assert mod.is_setup_notebook(name)

    def test_cours_ordinaire_hors_champ(self):
        assert not mod.is_setup_notebook("Search/Search-03-LDS.ipynb")


class TestAnalyse:
    def test_uncovered_echoue_et_xref_warn(self, tmp_path, monkeypatch):
        # arbre synthetique : un .ps1 couvert sans README, un decouvert,
        # un carnet Setup windows-only -- et les exemptions respectees.
        (tmp_path / "README.md").write_text("rien d'utile", encoding="utf-8")
        monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

        def fake_git(pattern):
            if pattern == "*.ps1":
                return ["scripts/environment/ok.ps1",
                        "scripts/environment/nu.ps1",
                        "MyIA.AI.Notebooks/GenAI/Vibe-Coding/Skip/x.ps1"]
            if pattern == "*.sh":
                return ["scripts/environment/ok.sh"]
            if pattern == "*.ipynb":
                return ["Serie/serie-1-Setup.ipynb"]
            return []

        monkeypatch.setattr(mod, "git_tracked", fake_git)
        nb_path = tmp_path / "Serie/serie-1-Setup.ipynb"
        nb_path.parent.mkdir(parents=True)
        nb_path.write_text(json.dumps({"cells": [
            {"cell_type": "code", "source": ["powershell run.ps1"]}]}),
            encoding="utf-8")

        report = mod.analyse(
            fake_git("*.ps1"), fake_git("*.sh"), fake_git("*.ipynb"))

        kinds_f = {f["kind"] for f in report["findings"]}
        kinds_w = {w["kind"] for w in report["warnings"]}
        assert kinds_f == {"uncovered_companion"}
        assert kinds_w == {"missing_readme_xref", "setup_windows_only"}
        assert report["in_scope_ps1"] == 2  # Vibe-Coding exempt

    def test_corpus_propre_sortie_zero(self, tmp_path, monkeypatch):
        monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)
        (tmp_path / "README.md").write_text(
            "compagnon : env.sh", encoding="utf-8")

        def fake_git(pattern):
            table = {
                "*.ps1": ["scripts/environment/env.ps1"],
                "*.sh": ["scripts/environment/env.sh"],
                "*.ipynb": ["Serie/cours.ipynb"],
            }
            return table.get(pattern, [])

        monkeypatch.setattr(mod, "git_tracked", fake_git)
        report = mod.analyse(
            fake_git("*.ps1"), fake_git("*.sh"), fake_git("*.ipynb"))
        assert report["findings"] == []
        assert report["warnings"] == []


def test_main_exit_codes(tmp_path, monkeypatch, capsys):
    """Le main traduit le rapport : findings -> 1, propre -> 0."""
    monkeypatch.setattr(mod, "REPO_ROOT", tmp_path)

    def fake_git(pattern):
        return {"*.ps1": ["a/x.ps1"], "*.sh": [], "*.ipynb": []}.get(
            pattern, [])

    monkeypatch.setattr(mod, "git_tracked", fake_git)
    assert mod.main([]) == 1
    out = capsys.readouterr().out
    assert "uncovered_companion" in out

    monkeypatch.setattr(mod, "git_tracked",
                        lambda p: {"*.ps1": ["a/x.ps1"],
                                   "*.sh": ["a/x.sh"]}.get(p, []))
    (tmp_path / "a").mkdir()
    (tmp_path / "a" / "README.md").write_text("voici x.sh", encoding="utf-8")
    assert mod.main([]) == 0
