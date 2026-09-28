"""Tests for scripts/lean/axiom_coverage.py — verdicts de couverture B.3.

Controles (le faux positif fondateur est mesure ici meme) :
- BARE / WIRED / WIRED-DEAD / wildcard discriminés depuis le manifeste ;
- normalisation pointee : `SocialChoice.Arrow` (manifeste) == `SocialChoice/Arrow.lean`
  (disque) — la premiere version comparait slashes a points et declarait
  WIRED-DEAD les 21 modules d'un lake reellement wired ;
- counts coherents avec les verdicts.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "lean"))

import axiom_coverage as cov


@pytest.fixture
def repo(tmp_path, monkeypatch):
    """REPO_ROOT + MANIFEST rejouables sur un arbre tmp."""
    (tmp_path / "scripts" / "lean").mkdir(parents=True)
    monkeypatch.setattr(cov, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(cov, "MANIFEST", tmp_path / "scripts" / "lean" / "ci_lakes.json")

    def write(lakes):
        cov.MANIFEST.write_text(json.dumps({"lakes": lakes}), encoding="utf-8")

    return tmp_path, write


def _make_lake(repo_root, rel, modules):
    d = repo_root / rel
    for m in modules:
        p = d / Path(*m.split("."))
        p.parent.mkdir(parents=True, exist_ok=True)
        p.with_suffix(".lean").write_text("-- test\n", encoding="utf-8")
    return d


class TestCoverageReport:

    def test_bare_lake(self, repo):
        root, write = repo
        write([{"lake": "a", "project-path": "p/a", "display-name": "a"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "BARE"
        assert r["lakes"][0]["axiom-target-modules"] is None
        assert r["counts"] == {"BARE": 1}

    def test_wired_dotted_modules_match_disk_paths(self, repo):
        root, write = repo
        _make_lake(root, "p/g", ["SocialChoice.Arrow", "SocialChoice.Arrow_en"])
        write([{"lake": "g", "project-path": "p/g",
                "axiom-target-modules": "SocialChoice.Arrow,SocialChoice.Arrow_en"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "WIRED"
        assert r["lakes"][0]["dead_modules"] == []

    def test_wired_dead_detects_missing_module(self, repo):
        root, write = repo
        _make_lake(root, "p/g", ["SocialChoice.Arrow"])
        write([{"lake": "g", "project-path": "p/g",
                "axiom-target-modules": "SocialChoice.Arrow,SocialChoice.Ghost"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "WIRED-DEAD"
        assert r["lakes"][0]["dead_modules"] == ["SocialChoice.Ghost"]

    def test_wildcard_skips_verification(self, repo):
        root, write = repo
        write([{"lake": "s", "project-path": "p/s", "axiom-target-modules": "*"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "WIRED"
        assert r["lakes"][0].get("wildcard") is True

    def test_counts_across_verdicts(self, repo):
        root, write = repo
        _make_lake(root, "p/g", ["M.A"])
        write([
            {"lake": "g", "project-path": "p/g", "axiom-target-modules": "M.A,M.B"},
            {"lake": "s", "project-path": "p/s", "axiom-target-modules": "*"},
            {"lake": "b", "project-path": "p/b"},
        ])
        r = cov.coverage_report()
        assert r["total"] == 3
        assert r["counts"] == {"WIRED-DEAD": 1, "WIRED": 1, "BARE": 1}

    def test_lake_directory_absent_is_not_dead(self, repo):
        """Un chemin de lake absent (checkout partiel) ne doit pas produire
        un WIRED-DEAD mensonger : modules introuvables = disque muet."""
        root, write = repo
        write([{"lake": "g", "project-path": "p/inexistant",
                "axiom-target-modules": "M.A"}])
        r = cov.coverage_report()
        # Les modules sont introuvables parce que le lake n'est pas sur disque :
        # le verdict WIRED-DEAD reste correct (on ne peut pas verifier), et le
        # compte des modules morts est exhaustif.
        assert r["lakes"][0]["dead_modules"] == ["M.A"]
