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


def _write_lean(repo_root, rel, name, body):
    d = repo_root / rel
    d.mkdir(parents=True, exist_ok=True)
    (d / name).write_text(body, encoding="utf-8")
    return d


class TestDeclarationFreeLakes:
    """`conway_cgt_lean` (#24092, 2026-11-02) : un carnet de visite dont tous
    les `theorem` vivent dans des blocs `/-! ... -/`. Le cabler fait echouer le
    gate sur sa non-vacuite (« the gate inspected nothing »), et la jambe
    resterait rouge a perpetuite. Le census doit le dire, pas le compter BARE.

    Le verdict se mesure avec l'enumerateur du GATE, jamais avec un lexique
    local : la premiere version de `axiom_coverage.py` comptait les `example`
    et rendait `mathlib_examples` cablable la ou le gate enumere zero.
    """

    def test_comment_only_lake_is_not_applicable(self, repo):
        root, write = repo
        _write_lean(root, "p/c", "Tour.lean",
                    "/-! un carnet\ntheorem x : True := trivial\n-/\n"
                    "import Foo\n#check @Foo.x\n")
        write([{"lake": "c", "project-path": "p/c", "display-name": "c"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "NOT-APPLICABLE"
        assert r["lakes"][0]["declaration_count"] == 0
        assert r["lakes"][0]["declaration_reason"] == "declaration_free_module"
        assert r["counts"] == {"NOT-APPLICABLE": 1}

    def test_anonymous_examples_are_not_declarations(self, repo):
        """Le cas `mathlib_examples` : des `example` sont du code reel, mais
        anonymes — le gate ne peut pas les interroger par nom."""
        root, write = repo
        _write_lean(root, "p/e", "Basic.lean",
                    "import Mathlib\nexample : 1 + 1 = 2 := rfl\n")
        write([{"lake": "e", "project-path": "p/e", "display-name": "e"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "NOT-APPLICABLE"

    def test_lake_with_one_declaration_stays_bare(self, repo):
        """Un lake qui declare reste un cable MANQUANT : le verdict ne doit
        pas blanchir ce qui est gateable."""
        root, write = repo
        _write_lean(root, "p/d", "A.lean", "theorem t : True := trivial\n")
        write([{"lake": "d", "project-path": "p/d", "display-name": "d"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "BARE"
        assert r["lakes"][0]["declaration_count"] == 1

    def test_partial_checkout_is_not_excused(self, repo):
        """Disque muet != « declare rien » : un chemin absent reste BARE, sinon
        un checkout partiel blanchirait silencieusement le census."""
        root, write = repo
        write([{"lake": "z", "project-path": "p/absent", "display-name": "z"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "BARE"
        assert r["lakes"][0]["declaration_count"] == -1
        assert r["lakes"][0]["declaration_reason"] == "source_not_found"

    def test_source_not_found_never_reads_as_declaration_free(self, repo):
        """Le discriminant est la RAISON, pas le compte : `source_not_found`
        et `all_private_declarations` restent a instruire."""
        root, write = repo
        _write_lean(root, "p/p", "A.lean", "private theorem t : True := trivial\n")
        write([{"lake": "p", "project-path": "p/p", "display-name": "p"}])
        r = cov.coverage_report()
        assert r["lakes"][0]["verdict"] == "BARE"
        assert r["lakes"][0]["declaration_count"] == 0
        assert r["lakes"][0]["declaration_reason"] == "all_private_declarations"

    def test_require_covered_fails_on_bare_but_not_on_not_applicable(self, repo):
        root, write = repo
        _write_lean(root, "p/c", "Tour.lean", "import Foo\n")
        write([{"lake": "c", "project-path": "p/c", "display-name": "c"}])
        assert cov.main(["--require-covered"]) == 0

        _write_lean(root, "p/d", "A.lean", "def x := 1\n")
        write([
            {"lake": "c", "project-path": "p/c", "display-name": "c"},
            {"lake": "d", "project-path": "p/d", "display-name": "d"},
        ])
        assert cov.main(["--require-covered"]) == 1

    def test_real_manifest_matches_the_written_decision(self):
        """Controle positif sur l'arbre reel : les deux lakes declares « sans
        gate » par #22519 §4.1 sont exactement ceux que le census mesure
        NOT-APPLICABLE, et aucun autre."""
        r = cov.coverage_report()
        by_name = {row["display-name"]: row for row in r["lakes"]}
        assert by_name["conway_cgt_lean"]["verdict"] == "NOT-APPLICABLE"
        assert by_name["mathlib_examples"]["verdict"] == "NOT-APPLICABLE"
        assert r["counts"].get("NOT-APPLICABLE") == 2
        assert r["counts"].get("BARE", 0) == 0

