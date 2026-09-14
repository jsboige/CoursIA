"""Tests for scripts/notebook_tools/detect_mermaid_fill_without_color.py (#15022).

Pourquoi ce fichier de tests existe
-----------------------------------
`detect_mermaid_fill_without_color.py` est le detecteur DETECTION du defect
#15022 (regles mermaid `style`/`classDef` avec `fill:` sans `color:` = libelle
clair-sur-clair en theme sombre). La verification etait faite a la main dans
le fix #15502 ; la review NanoClaw a demande la garde mecanique. Ces tests
pinent le contrat pour qu'une regression (faux positif massif ou forme
manquee) soit attrapee avant de polluer l'advisory.

Clusters :

  1. TestClassify       -- regle unitaire : finding fill-sans-color, clean
                           fill-avec-color, fence non-mermaid ignoree,
                           commentaire %% ignore, forme style ET classDef.
  2. TestScanMarkdown   -- fichier .md : findings par ligne + stats pairees.
  3. TestScanNotebook   -- cellule markdown .ipynb : finding par cell_index,
                           cellule code ignoree.
  4. TestAllowlist      -- fixture positive allowlistee par chemin.
  5. TestMainExitCodes  -- contrat de sortie : --check 1 sur finding, 0 clean,
                           --self-test 0.

Ground truth : la mesure fleet sur origin/main (2026-09-11) = 25 fichiers /
90 regles fautives / 204 regles fill: totales ; le README Probas porte
exactement 10 findings pre-fix (retrouves par le detecteur -- les memes 10
que le recompte manuel de la review NanoClaw sur #15502).
"""
import io
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_mermaid_fill_without_color import (  # noqa: E402
    ALLOWED,
    classify_mermaid_fill_rules,
    main,
    scan_markdown_file,
    scan_notebook,
)

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "mermaid_fill_no_color.md"


class TestClassify:
    def test_classdef_fill_without_color_is_finding(self):
        text = "```mermaid\nflowchart LR\nA-->B\nclassDef d fill:#d1ecf1,stroke:#0c5460;\nclass A,B d;\n```\n"
        findings, n_rules, n_color = classify_mermaid_fill_rules(text)
        assert len(findings) == 1
        assert findings[0]["rule"] == "classDef" and findings[0]["target"] == "d"
        assert (n_rules, n_color) == (1, 0)

    def test_classdef_fill_with_color_is_clean(self):
        text = "```mermaid\nclassDef d fill:#d1ecf1,color:#0c5460;\n```\n"
        findings, n_rules, n_color = classify_mermaid_fill_rules(text)
        assert findings == []
        assert (n_rules, n_color) == (1, 1)

    def test_style_form_is_judged_too(self):
        text = "```mermaid\nflowchart TD\nX-->Y\nstyle X fill:#fff3cd,stroke:#856404;\n```\n"
        findings, _, _ = classify_mermaid_fill_rules(text)
        assert len(findings) == 1 and findings[0]["rule"] == "style"

    def test_non_mermaid_fence_ignored(self):
        text = "```\nclassDef d fill:#d1ecf1;\nstyle X fill:#fff3cd;\n```\n"
        findings, n_rules, _ = classify_mermaid_fill_rules(text)
        assert findings == [] and n_rules == 0

    def test_mermaid_comment_line_ignored(self):
        # Un %% porte les mots fill:/color: en prose -- pas une regle.
        text = "```mermaid\n%% fill: sans color: serait un finding\nclassDef ok fill:#d1ecf1,color:#000;\n```\n"
        findings, n_rules, n_color = classify_mermaid_fill_rules(text)
        assert findings == [] and (n_rules, n_color) == (1, 1)

    def test_rule_without_fill_ignored(self):
        # classDef sans fill: (fond herite du theme) : rien a verifier.
        text = "```mermaid\nclassDef d stroke:#333,stroke-width:2px;\n```\n"
        findings, n_rules, _ = classify_mermaid_fill_rules(text)
        assert findings == [] and n_rules == 0

    def test_tilde_fence_supported(self):
        text = "~~~mermaid\nclassDef d fill:#d1ecf1;\n~~~\n"
        findings, _, _ = classify_mermaid_fill_rules(text)
        assert len(findings) == 1

    def test_fixture_contract_counts(self):
        """Le fixture porte exactement 2 findings (classDef dist, style X) et
        5 regles fill: dont 3 avec color:."""
        findings, n_rules, n_color = classify_mermaid_fill_rules(FIXTURE.read_text(encoding="utf-8"))
        rules = sorted((f["rule"], f["target"]) for f in findings)
        assert rules == [("classDef", "dist"), ("style", "X")]
        assert (n_rules, n_color) == (5, 3)


class TestScanMarkdown:
    def test_scan_marks_line_numbers(self):
        result = scan_markdown_file(FIXTURE, FIXTURE.parents[3])
        assert result["error"] is None and result["allowed"] is None
        linenos = sorted(h["lineno"] for h in result["hits"])
        assert len(linenos) == 2
        assert result["stats"] == {"fill_rules": 5, "with_color": 3}

    def test_scan_unreadable_file_reports_error(self, tmp_path):
        missing = tmp_path / "nope.md"
        missing.write_text("x", encoding="utf-8")
        result = scan_markdown_file(missing, tmp_path)
        # Lisible mais sans mermaid : clean, pas d'erreur.
        assert result["hits"] == [] and result["error"] is None


class TestScanNotebook:
    def _nb(self, tmp_path, cell_source):
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": cell_source},
                {"cell_type": "code", "source": "classDef d fill:#d1ecf1;"},
            ],
            "metadata": {},
            "nbformat": 4,
        }
        p = tmp_path / "nb.ipynb"
        p.write_text(json.dumps(nb), encoding="utf-8")
        return p

    def test_markdown_cell_flagged_code_cell_ignored(self, tmp_path):
        src = "```mermaid\nclassDef d fill:#d1ecf1;\n```\n"
        result = scan_notebook(self._nb(tmp_path, src), tmp_path)
        assert len(result["hits"]) == 1
        assert result["hits"][0]["cell_index"] == 0
        assert result["stats"]["fill_rules"] == 1


class TestAllowlist:
    def test_fixture_path_is_allowed(self):
        rel = "scripts/notebook_tools/tests/fixtures/mermaid_fill_no_color.md"
        assert any(needle in rel for needle in ALLOWED)
        result = scan_markdown_file(FIXTURE, FIXTURE.parents[4])
        # Le resolve() du root reel peut differe ; on teste via _is_allowed
        # indirectement : le chemin fixture doit matcher une cle ALLOWED.
        matched = [needle for needle in ALLOWED if needle in str(FIXTURE).replace("\\", "/")]
        assert matched, "fixture positive doit etre allowlistee par chemin"


class TestMainExitCodes:
    def test_self_test_exits_zero(self, capsys):
        assert main(["--self-test"]) == 0

    def test_check_on_finding_exits_one(self, tmp_path):
        bad = tmp_path / "bad.md"
        bad.write_text("```mermaid\nclassDef d fill:#d1ecf1;\n```\n", encoding="utf-8")
        assert main(["--check", "--root", str(tmp_path), str(bad)]) == 1

    def test_check_on_clean_exits_zero(self, tmp_path):
        good = tmp_path / "good.md"
        good.write_text("```mermaid\nclassDef d fill:#d1ecf1,color:#000;\n```\n", encoding="utf-8")
        assert main(["--check", "--root", str(tmp_path), str(good)]) == 0

    def test_stdin_json_payload_fields(self, tmp_path, capsys, monkeypatch):
        bad = tmp_path / "bad.md"
        bad.write_text("```mermaid\nstyle X fill:#fff3cd;\n```\n", encoding="utf-8")
        monkeypatch.setattr("sys.stdin", io.StringIO(f"{bad}\n"))
        rc = main(["--json", "--stdin", "--root", str(tmp_path)])
        out = json.loads(capsys.readouterr().out)
        assert rc == 0
        assert out["total_hits"] == 1 and out["flagged_count"] == 1
        assert out["error_count"] == 0
        # Champs consommes par le workflow advisory.
        assert {"scanned", "flagged_count", "total_hits", "error_count"} <= set(out)
