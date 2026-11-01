# -*- coding: utf-8 -*-
"""Tests de check_readme_notebook_coverage.py (organe du critere 3 de #13504).

Ce qui est couvert ici : la classification (les cinq classes de verdict), le
contrat « le stock ne rougit personne », le delta, et la surface CLI
(``--json``, ``--strict``, code retour). La passe git de ``--diff-base`` est
testee par son echec d'entree ; son succes se mesure en CI sur le corpus reel.
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

MODULE_PATH = (Path(__file__).resolve().parents[1] / "ci"
               / "check_readme_notebook_coverage.py")
spec = importlib.util.spec_from_file_location(
    "check_readme_notebook_coverage", MODULE_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_readme_notebook_coverage"] = mod
spec.loader.exec_module(mod)

ROOT_REL = "MyIA.AI.Notebooks"


def make_tree(tmp_path: Path, files: dict[str, str]) -> Path:
    """Ecrit un faux depot : ``{chemin relatif: contenu}``."""

    for rel, content in files.items():
        target = tmp_path / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8")
    return tmp_path


def nb(name: str) -> str:
    """Contenu minimal d'un carnet : le nom suffit a la detection."""

    return json.dumps({"cells": [], "metadata": {}, "nbformat": 4,
                       "nbformat_minor": 5})


def kinds(report) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for finding in report.findings:
        out.setdefault(finding.kind, []).append(finding.path)
    return out


class TestClassification:
    def test_carnet_liste_est_couvert(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
        })
        report = mod.scan(tmp_path)
        assert report.findings == []
        assert report.totals["covered"] == 1

    def test_carnet_absent_du_readme_est_manquant(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/b.ipynb": nb("b"),
        })
        report = mod.scan(tmp_path)
        assert kinds(report)[mod.MISSING] == [f"{ROOT_REL}/Serie/b.ipynb"]

    def test_jumeau_en_est_advisory(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/a_en.ipynb": nb("a_en"),
        })
        report = mod.scan(tmp_path)
        found = kinds(report)
        assert mod.MISSING not in found
        assert found[mod.EN_SIBLING] == [f"{ROOT_REL}/Serie/a_en.ipynb"]

    def test_dossier_sans_readme_est_advisory(self, tmp_path):
        make_tree(tmp_path, {f"{ROOT_REL}/Orphelin/a.ipynb": nb("a")})
        report = mod.scan(tmp_path)
        found = kinds(report)
        assert found[mod.NO_README] == [f"{ROOT_REL}/Orphelin/a.ipynb"]
        assert mod.MISSING not in found

    def test_readme_ne_listant_aucun_carnet_est_convention_off(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "# Serie\n\nVoir le cours.\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
        })
        report = mod.scan(tmp_path)
        found = kinds(report)
        assert found[mod.CONVENTION_OFF] == [f"{ROOT_REL}/Serie/a.ipynb"]
        assert mod.MISSING not in found

    def test_readme_multiple_concatene(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/README.en.md": "- [b](b.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/b.ipynb": nb("b"),
        })
        report = mod.scan(tmp_path)
        assert report.findings == []

    def test_archive_et_checkpoints_ecartes(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/_archive/3.9d.ipynb": nb("3.9d"),
            f"{ROOT_REL}/Serie/.ipynb_checkpoints/a-checkpoint.ipynb": nb("x"),
        })
        report = mod.scan(tmp_path)
        assert report.findings == []
        assert report.totals["notebooks"] == 1

    def test_racine_absente_rend_un_rapport_vide(self, tmp_path):
        report = mod.scan(tmp_path)
        assert report.totals == {"notebooks": 0}
        assert report.findings == []


class TestStockNeRougitPersonne:
    def test_scan_complet_ne_bloque_jamais(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/b.ipynb": nb("b"),
        })
        report = mod.scan(tmp_path)
        assert len(kinds(report)[mod.MISSING]) == 1
        assert report.blocking() == []

    def test_delta_ne_bloque_que_les_ajoutes(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/ancien.ipynb": nb("ancien"),
            f"{ROOT_REL}/Serie/nouveau.ipynb": nb("nouveau"),
        })
        report = mod.scan(tmp_path)
        report.delta = True
        report.added = [f"{ROOT_REL}/Serie/nouveau.ipynb"]
        blocking = [f.path for f in report.blocking()]
        assert blocking == [f"{ROOT_REL}/Serie/nouveau.ipynb"]

    def test_delta_vide_ne_bloque_pas_le_stock(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/ancien.ipynb": nb("ancien"),
        })
        report = mod.scan(tmp_path)
        report.delta = True
        report.added = []
        assert report.blocking() == []


class TestAddedNotebooks:
    def test_ref_inconnue_leve_un_incident(self, tmp_path):
        make_tree(tmp_path, {})
        with pytest.raises(RuntimeError):
            mod.added_notebooks(tmp_path, "ref-qui-nexiste-pas")


class TestMain:
    def _tree(self, tmp_path: Path) -> Path:
        return make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
            f"{ROOT_REL}/Serie/b.ipynb": nb("b"),
        })

    def test_scan_complet_rc0(self, tmp_path, capsys):
        root = self._tree(tmp_path)
        rc = mod.main(["--repo-root", str(root)])
        out = capsys.readouterr().out
        assert rc == 0
        assert "1 carnet(s) sans ligne au README" in out

    def test_json_porte_le_verdict(self, tmp_path, capsys):
        root = self._tree(tmp_path)
        rc = mod.main(["--repo-root", str(root), "--json"])
        payload = json.loads(capsys.readouterr().out)
        assert rc == 0
        assert payload["verdict"] == "OK"
        assert payload["blocking"] == []
        assert payload["totals"][mod.MISSING] == 1
        assert [f["path"] for f in payload["findings"]] == [
            f"{ROOT_REL}/Serie/b.ipynb"]

    def test_strict_promeut_les_advisory(self, tmp_path, capsys):
        make_tree(tmp_path, {f"{ROOT_REL}/Orphelin/a.ipynb": nb("a")})
        rc = mod.main(["--repo-root", str(tmp_path), "--strict"])
        assert rc == 1

    def test_strict_sans_advisory_reste_vert(self, tmp_path):
        make_tree(tmp_path, {
            f"{ROOT_REL}/Serie/README.md": "- [a](a.ipynb)\n",
            f"{ROOT_REL}/Serie/a.ipynb": nb("a"),
        })
        assert mod.main(["--repo-root", str(tmp_path), "--strict"]) == 0

    def test_diff_base_en_echec_rend_rc2(self, tmp_path, capsys):
        root = self._tree(tmp_path)
        rc = mod.main(["--repo-root", str(root),
                       "--diff-base", "ref-absente"])
        assert rc == 2
        assert "incident d'entree" in capsys.readouterr().err
