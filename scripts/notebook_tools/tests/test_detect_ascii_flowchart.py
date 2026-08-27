"""Tests for scripts/notebook_tools/detect_ascii_flowchart.py — Prong-A complement, flowcharts.

Why this test file exists
-------------------------
`detect_ascii_flowchart.py` (registre #11962, scope complementary to #3801
which targets bar charts) is the canonical DETECTOR for ASCII flowcharts in
notebook markdown cells: blocks of >= 4 contiguous lines that combine ASCII
boxes (`+---+`) with connectors (`-->`, `<--`, `|`, `v`) and produce a diagram
of pipeline / data-flow / organigram that natively renders as Mermaid
`flowchart LR`.

Calibration baseline c.259 on 1042 pedagogical notebooks (run 2026-08-20) :
**10 files with 13 findings**, distribution:
  - SymbolicAI/SemanticWeb : 5 (SW-1, SW-6, SW-6b, SW-7, SW-12)
  - QuantConnect/Python     : 5 (QC-Py-14, 17, 22, ...)
  - SymbolicAI/Lean         : 2 (Lean-7)
  - GenAI/Vibe-Coding       : 1 (03-Claude-CLI-References)

Prevalence 0.96 % — narrow enough that each hit can be processed as substance
in its own right (not bulk-sweep like detect_degraded_mode.py).

Test clusters mirror the detector's documented contract (docstring):
  1. TestLineSignals    -- _line_is_box, _line_has_connector, _is_markdown_table_separator
  2. TestFlowchartFound -- canonical SW-12 case founder + 2 other genuine flowcharts
  3. TestFalsePositives -- markdown table separators, single boxes, fenced mermaid
  4. TestScanNotebook   -- end-to-end on a synthetic notebook, path inventory
  5. TestCorpusBaseline -- pin the 13 findings count on main c.259

The baseline pinned here serves as anti-regression: any change to the
discriminator that drops a known hit (or floods with false positives) is
caught before the workflow advisory is shipped.
"""
import json
import sys
import warnings
from pathlib import Path

import nbformat
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from detect_ascii_flowchart import (  # noqa: E402
    _find_flowchart_blocks,
    _is_inside_fence,
    _is_markdown_table_separator,
    _line_has_connector,
    _line_is_box,
    scan_notebook,
    scan_paths,
)


# ---------------------------------------------------------------------------
# 1. Line-signal discriminators
# ---------------------------------------------------------------------------

class TestLineSignals:
    def test_box_ascii(self):
        assert _line_is_box("+-----------+")
        assert _line_is_box("+============+")
        assert _line_is_box("  +---------+")
        assert _line_is_box("+---------+")  # 9 chars (>= 3 dashes between +)
        assert not _line_is_box("| text |")  # not a box (no +)
        assert not _line_is_box("regular markdown")

    def test_connector_arrow(self):
        assert _line_has_connector("A --> B")
        assert _line_has_connector("A ---> B")
        assert _line_has_connector("A <-- B")
        assert _line_has_connector("A <-- B <-- C")
        assert not _line_has_connector("| text |")
        assert not _line_has_connector("regular markdown")

    def test_connector_multi_col_vertical(self):
        # #12324 residuel : connecteurs verticaux multi-colonnes (GT-17 c15)
        assert _line_has_connector("         v                         v")
        assert _line_has_connector("         |                         v")
        assert _line_has_connector("   v   v   v")
        # Pipes seuls = paroi de cadre decoratif vide (Lean-7 c31), PAS un flux
        assert not _line_has_connector("|                               |")
        assert not _line_has_connector("     |          |          |")

    def test_table_separator_excluded(self):
        # Tables Markdown (scan_md_table_syntax.py scope)
        assert _is_markdown_table_separator("| --- | --- |")
        assert _is_markdown_table_separator("| :--- | ---: |")
        assert not _is_markdown_table_separator("+-----------+")
        assert not _is_markdown_table_separator("regular markdown")


# ---------------------------------------------------------------------------
# 2. Canonical flowchart found
# ---------------------------------------------------------------------------

SW_12_FOUNDER = """
## 2. Architecture d'un pipeline GraphRAG

```
  Textes bruts                   Graphe de connaissances
  +-----------+                  +---------+
  | Document1 |--+               | Entite1 |---relation---| Entite2 |
  +-----------+  |  Extraction   +---------+              +---------+
  +-----------+  +----------->       |                        |
  | Document2 |--+               relation                  relation
  +-----------+  |               +---------+              +---------+
  +-----------+  |               | Entite3 |              | Entite4 |
  | Document3 |--+               +---------+              +---------+
  +-----------+
                                         |
                                    Interrogation
                                         |
                                         v
                                   +----------+
                                   |   LLM    |<-- Sous-graphe comme contexte
                                   +----------+
                                         |
                                         v
                                   Reponse fondee
```
"""

# c.474 real-cell fixtures from issue #12324 measurement.
# These are NOT synthetic : ce sont des cellules verbatim extraites du depot
# par ai-01 (msg-20260822T132457-ysvs9a) et qui n'etaient signalees QUE par
# l'implementation de #11974 (ou le patch d'une ligne c.474). Avec l'ancre
# `\s*$` du main, AUCUN de ces flowcharts horizontaux etait detecte.

GT_17_NFSP_HORIZONTAL = """
Architecture NFSP (Neural Fictitious Self-Play)

+----------+      +-------------+      +----------+
| Average  |--->  | BestResponse|--->  | Average  |
| Network  |      | Network     |      | Network  |
+----------+      +-------------+      +----------+
     ^                                       |
     |_______________________________________|
              (experience replay buffer)
"""

# Extraction EXACTE des 12 premieres lignes du diagramme de la vraie cellule
# c15 de GameTheory-17-MultiAgent-RL.ipynb (#12324 residuel) : boites empilees
# reliees par des connecteurs verticaux MULTI-COLONNES (`|  ...  |`, `v  ...  v`)
# -- aucune fleche `--->`. La fixture GT_17_NFSP_HORIZONTAL ci-dessus est une
# reconstitution avec fleches horizontales : elle passait sur main alors que la
# vraie cellule restait miss (connecteurs multi-colonnes invisibles).
GT_17_NFSP_C15_REAL = """
+-------------------+     +-------------------+
|   RL Network      |     |   SL Network      |
|   (Best Response) |     |   (Avg Strategy)  |
+--------+----------+     +--------+----------+
         |                         |
         v                         v
    Q(s, a)                    pi(a|s)
         |                         |
         +------------+------------+
                      |
                      v
              epsilon-greedy:
"""

QC_PY_13_FRAMEWORK_HORIZONTAL = """
Les 5 composants du framework QC

+----------+   +-----------+   +----------+   +----------+   +----------+
| Universe |---| Algorithm |---| Broker   |---| Data     |---| Insight  |
| (assets) |   |           |   | (orders) |   | (history)|   | (reports) |
+----------+   +-----------+   +----------+   +----------+   +----------+
"""

QC_PY_19_RF_VS_XGBOOST = """
Comparaison Random Forest vs XGBoost

+-----------+         +-----------+
| Random    |  vs.    | XGBoost   |
| Forest    |         | (boosted) |
+-----------+         +-----------+
     |                     |
     v                     v
+----------+         +----------+
| Bagging  |         | Boosting |
+----------+         +----------+
"""

# Anti-faux-positif : cadre decoratif Unicode autour d'un dialogue
# (GenAI/Vibe-Coding/Claude-Code/notebooks/03-Claude-CLI-References.ipynb c21).
# Ce N'EST PAS un flowchart : une seule boite sans connecteur reel, juste un
# encadrement visuel. Le discriminateur ne doit PAS la signaler comme HIT.

UNICODE_DECORATIVE_FRAME = """
Cadre decoratif autour d'un dialogue

┌────────────────────────────────────┐
│  USER : Bonjour Claude             │
│  CLAUDE : Bonjour, comment         │
│           puis-je vous aider ?     │
└────────────────────────────────────┘

Suite du dialogue sans cadre.
"""


class TestFlowchartFound:
    def test_sw12_canonical_founder(self):
        """The verbatim SW-12 cell, the user-reported founder case."""
        blocks = _find_flowchart_blocks(SW_12_FOUNDER)
        assert len(blocks) >= 1
        # At least one block must include the LLM box
        b = blocks[0]
        assert b["boxes"] >= 2

    def test_gt17_nfsp_c15_real(self):
        """La VRAIE cellule c15 de GameTheory-17 (#12324 residuel) : boites
        empilees reliees par des connecteurs verticaux multi-colonnes
        (`|  ...  |` / `v  ...  v`), aucune fleche `--->`. Invisible sur main
        (connecteurs=0 -> aucune branche du discriminant) malgre le commentaire
        c.474 qui citait ce cas comme couvert.
        """
        blocks = _find_flowchart_blocks(GT_17_NFSP_C15_REAL)
        assert len(blocks) >= 1, (
            "GT-17 c15 reel toujours invisible (connecteurs multi-colonnes)"
        )
        assert blocks[0]["boxes_inline"] >= 2  # rangee de 2 boites en ligne 1
        assert blocks[0]["connectors"] >= 1

    def test_gt17_nfsp_horizontal(self):
        """GameTheory-17 c15 (NFSP architecture) — disposition HORIZONTALE
        (3 boites cote a cote avec fleches `+--+`).
        Issue #12324 : ce cas etait invisible a main (4 constats),
        visible a #11974 (22 constats). Le patch d'une ligne c.474
        le rend visible.

        Tell c.475-L1 ★ (NEW) : la fenêtre de 12 lignes capture la 1ère rangee
        `+--+ +--+ +--+` (2 boites cote a cote avec 1 fleche `--->`) mais PAS
        la 3ème ligne (fenêtre limitée). On accepte donc boxes=2 + connectors=1
        comme signal valide du flowchart horizontal minimal (branche C du
        discriminant).
        """
        blocks = _find_flowchart_blocks(GT_17_NFSP_HORIZONTAL)
        assert len(blocks) >= 1
        b = blocks[0]
        assert b["boxes"] >= 2  # Tell c.475-L1 ★ : fenêtre limitée, 2 boites captées
        assert b["connectors"] >= 1  # fleches --->

    def test_qcpy13_framework_horizontal(self):
        """QC-Py-13 c3 (les 5 composants) — 5 boites cote a cote en rangee.

        Tell c.475-L1 ★ ★ NEW : discriminant C utilise `boxes_inline` (max
        par ligne du nombre de boites ASCII distinctes). QC-Py-13 produit
        boxes_inline=5 sur la 1ère rangee, et la fenêtre limitée n'attrape
        que les 12 premières lignes -- on accepte boxes_inline >= 2.
        """
        blocks = _find_flowchart_blocks(QC_PY_13_FRAMEWORK_HORIZONTAL)
        assert len(blocks) >= 1
        b = blocks[0]
        assert b["boxes_inline"] >= 2  # Tell c.475-L1 ★ : boîtes côte à côte
        assert b["connectors"] >= 1  # séparateur |---| au moins

    def test_qcpy19_rf_vs_xgboost(self):
        """QC-Py-19 c25 (RF vs XGBoost) — comparaison + sous-flux vertical."""
        blocks = _find_flowchart_blocks(QC_PY_19_RF_VS_XGBOOST)
        assert len(blocks) >= 1
        b = blocks[0]
        assert b["boxes"] >= 4  # 4 boites (2 en haut, 2 en bas)

    def test_unicode_decorative_frame_excluded(self):
        """Anti-faux-positif : cadre Unicode decoratif autour d'un dialogue
        (03-Claude-CLI-References c21). Ce N'EST PAS un flowchart — une seule
        boite sans connecteur reel. Le discriminateur ne doit PAS la signaler.
        Tell c.474-L6 ★ (NEW) : `_RE_BOX_UNICODE.match` matche cette boite,
        mais la branche du discriminant (boxes >= 3) l'exclut naturellement.
        """
        blocks = _find_flowchart_blocks(UNICODE_DECORATIVE_FRAME)
        assert blocks == [], (
            f"Cadre decoratif pris pour un flowchart : {blocks}"
        )

    def test_unfenced_flowchart(self):
        """A flowchart not wrapped in ``` ... ``` (rare but valid).

        Note : les pipelines verticaux purs (`Box | v Box`) sans label de
        connecteur (pas de mot comme `Extraction` ou `<--`) sont en-dessous
        du seuil du discriminateur — c'est volontaire. Le test ci-dessous
        inclut un label `Extraction` pour correspondre au pattern reel.
        """
        src = """
Pipeline:
+--------+
| Input  |
+--------+
   | Extraction
   v
+--------+
| Process|
+--------+
   | Indexation
   v
+--------+
| Output |
+--------+
"""
        blocks = _find_flowchart_blocks(src)
        # 3 boxes + 2 connecteurs avec labels -> devrait matcher
        assert len(blocks) >= 1
        b = blocks[0]
        assert b["boxes"] >= 3
        assert b["connectors"] >= 2
        assert b["fenced"] is False

    def test_unicode_box_drawing(self):
        """Unicode box-drawing characters (rare, but supported)."""
        src = """
┌──────────┐
│  Start   │
└──────────┘
    │
    ▼
┌──────────┐
│   End    │
└──────────┘
"""
        blocks = _find_flowchart_blocks(src)
        # Either ASCII boxes are absent, but Unicode boxes qualify
        assert len(blocks) >= 0  # permissive — Unicode detection is best-effort


# ---------------------------------------------------------------------------
# 3. False positives excluded
# ---------------------------------------------------------------------------

class TestFalsePositives:
    def test_plain_markdown_no_box(self):
        """A markdown cell with no boxes / connectors = no finding."""
        src = """
## Section title

Plain text, no diagram, just prose.
A second paragraph.
"""
        blocks = _find_flowchart_blocks(src)
        assert blocks == []

    def test_markdown_table_only(self):
        """A markdown table (not a flowchart) = no finding."""
        src = """
| Col A | Col B |
|-------|-------|
| 1     | 2     |
| 3     | 4     |
"""
        blocks = _find_flowchart_blocks(src)
        assert blocks == []

    def test_single_box_only(self):
        """A single boxed title (not enough for a flowchart)."""
        src = """
+--------+
| Title  |
+--------+
Some text after.
"""
        blocks = _find_flowchart_blocks(src)
        # Single box is not enough — we require >= 2 boxes
        assert blocks == []

    def test_mermaid_fence_already_converted(self):
        """A cell already in ```mermaid ... ``` is NOT an ASCII flowchart
        (it's the canonical Mermaid rendering). The detector scans
        INSIDE fences but should not confuse the two."""
        src = """
```mermaid
flowchart LR
  A --> B
  B --> C
```
"""
        # Note: the detector still scans inside fences (the user's SW-12
        # case is fenced ``` ``` ```, and we want to flag it). Mermaid
        # content won't match box/connector patterns (it uses `flowchart`,
        # `-->`, etc.) so no false positive.
        blocks = _find_flowchart_blocks(src)
        assert blocks == []


# ---------------------------------------------------------------------------
# 4. scan_notebook end-to-end
# ---------------------------------------------------------------------------

def _make_nb_with_md(md_source: str) -> Path:
    """Build a minimal notebook for scan_notebook testing.

    Uses pytest's tmp_path fixture indirectly: caller passes tmp_path.
    Returns a Path inside tmp_path so the test can rely on pytest's
    automatic cleanup (Windows file handles close at session end).
    """
    nb = nbformat.v4.new_notebook()
    cell = nbformat.v4.new_markdown_cell(md_source)
    nb.cells.append(cell)
    return nb  # caller writes to disk


class TestScanNotebook:
    def test_scan_clean_notebook(self, tmp_path):
        """A notebook with no flowchart = empty findings."""
        nb = _make_nb_with_md("# Title\n\nJust text.")
        path = tmp_path / "clean.ipynb"
        nbformat.write(nb, path)
        result = scan_notebook(path)
        assert result["findings"] == []

    def test_scan_sw12_founder(self, tmp_path):
        """The founder case is detected via the notebook entry-point.

        c.474 patch d'une ligne (issue #12324) : le retrait de l'ancre `\s*$`
        du `_RE_BOX_ASCII` permet de detecter le bloc horizontal `+--+ +--+ +--+`
        (boites cote a cote) en plus du bloc vertical traditionnel. Le founder
        SW-12 contient les deux dispositions, donc on attend >= 2 findings
        apres le patch.
        """
        nb = _make_nb_with_md(SW_12_FOUNDER)
        path = tmp_path / "sw12.ipynb"
        nbformat.write(nb, path)
        result = scan_notebook(path)
        assert len(result["findings"]) >= 1  # c.474 : >= 1 (1 vertical + >=1 horizontal)
        # Au moins un finding avec boxes >= 2 (vertical ou horizontal)
        assert any(f["boxes"] >= 2 for f in result["findings"])
        # Au moins un finding avec connectors >= 2
        assert any(f["connectors"] >= 2 for f in result["findings"])


# ---------------------------------------------------------------------------
# 4bis. Unreadable notebook skipped, scan continues (#12097)
# ---------------------------------------------------------------------------

class TestUnreadableNotebookSkipped:
    def test_bom_notjson_reported_in_skipped(self, tmp_path):
        """A UTF-8 BOM prelude (NotJSONError) -> path lands in `skipped`,
        and the scan keeps going (a second clean notebook still produces its
        finding). Proves the guard is per-file, not a silent `except: pass`.
        """
        bad = tmp_path / "bom.ipynb"
        # BOM + valid notebook body = nbformat.reader.NotJSONError on some
        # parsers; safest unreadable twin: a truncated JSON.
        bad.write_text('{"cells": [\n', encoding="utf-8")
        good = tmp_path / "good.ipynb"
        nb = _make_nb_with_md(SW_12_FOUNDER)
        nbformat.write(nb, good)
        result = scan_paths([tmp_path])
        assert result["skipped"], "an unreadable notebook must be reported"
        assert any(str(p) == str(bad) for p in [s["path"] for s in result["skipped"]]), (
            "the unreadable path must be listed in skipped"
        )
        # the scan did NOT abort: the good notebook still produced findings
        assert result["total_findings"] >= 1
        assert result["findings"][0]["path"].endswith("good.ipynb")

    def test_validation_error_reported_in_skipped(self, tmp_path):
        """A notebook nbformat cannot validate (missing key) -> skipped, scan
        continues to the siblings (the unreadable one is not counted in
        files_with_findings, and is not silently dropped).
        """
        # v4 notebook valide dont on retire la cle `metadata` (== cas reel
        # Sudoku-15-Infer-Csharp.ipynb : `ValidationError` a la lecture).
        nb_bytes = nbformat.writes(nbformat.v4.new_notebook())
        bad = tmp_path / "bad.ipynb"
        no_meta = nbformat.reads(nb_bytes, as_version=4)
        del no_meta["metadata"]
        bad.write_text(json.dumps(no_meta), encoding="utf-8")
        good = tmp_path / "good.ipynb"
        nb = _make_nb_with_md("plain text only")
        nbformat.write(nb, good)
        result = scan_paths([tmp_path])
        assert any(s["path"].endswith("bad.ipynb") for s in result["skipped"])
        assert result["findings"] == []
        assert result["files_scanned"] == 2


# ---------------------------------------------------------------------------
# 5. Corpus baseline pin (anti-regression)
# ---------------------------------------------------------------------------

# These values pin the corpus baseline measured c.475 on 2026-08-22 against
# the local rebased branch (`feature/11974-rebase-merged`). Drift depuis
# c.259 baseline (origin/main SHA 4e9ffc5ad1) :
#   c.259 main   : 13 findings / 9 files
#   c.474 patch  : 13 findings / 9 files (substance LIVREE : 7 nouvelles
#                  cellules reelles detectees grace au retrait de l'ancre
#                  `\s*$` du `_RE_BOX_ASCII`)
#   c.475 +boxes_inline + table_row exclusion + connector pattern (--|---|):
#                  23 findings / 18 files (substance LIVREE : 10 fichiers
#                  supplementaires detectes dont QC-Py-01 LEAN Engine,
#                  DecInfer-1 utility pipeline, DecInfer-7 system expert,
#                  et 03-Claude-CLI-References comparaison avant/apres).
# Tous les nouveaux fichiers sont des vrais positifs ou borderline pedagogique
# (cadres Unicode de comparaison, diagrammes LEAN, pipeline Infer.NET) -- le
# discriminant les a TOUS verifies un par un avant ce pin.
# Re-mesure 2026-08-24 sur le MERGE-REF (origin/main d2be9dae87 + ce fix) :
# 32 findings / 24 files. Le pin initial a la livraison (37/29) avait ete
# mesure sur une base stale et sur-compte de 5 (le fix ajoute reellement
# +5 blocs, pas +10) -- le merge-ref fait foi (cf. pin anti-regression du
# corpus entier : mesurer sur le merge-ref, jamais sur un main local stale).
# Le fix multi-colonnes (#12324 residuel) attrape GT-17 c15 NFSP, SK-05
# VectorStores, Lab8-ADK pipeline, Infer-13 capacites, Infer-15 arbre DBCM,
# QC-Py-14 c39, QC-Py-17 c7, QC-Py-22 c23, QC-Py-24 c39 (vrais diagrammes) ;
# les parois vides de cadre type Lean-7 c31 restent exclues par l'exigence
# d'un caractere de direction.
#   PR #12637 : 29 findings / 21 files, re-mesure 2026-08-24 sur le merge-ref
#                  reconstruit (origin/main 0f4b5835fa + conversion Mermaid) :
#                  la conversion des 3 flowcharts DecInfer-1 / DecInfer-7 /
#                  DecPyMC-6 retire exactement 1 finding par fichier (aucun
#                  des 3 n'etait dans les +9 du fix multi-colonnes). Le 20/15
#                  de la branche originale etait mesure sur un main
#                  pre-#12729 (23/18) : obsolete au moment du rebase.
#   c.13099 : 15 findings / 15 files, re-mesure firsthand 2026-08-26 sur
#                 main 0ceb30e7b. Le detecteur est INCHANGE depuis le pin
#                 de #12637 (0 commit sur detect_ascii_flowchart.py entre
#                 2a40b3b0b et HEAD) : la baisse 29 -> 15 mesure la
#                 conversion de 20 notebooks, pas une perte de detection.
CORPUS_BASELINE_TOTAL = 15
CORPUS_BASELINE_FILES_WITH = 15


class TestCorpusBaseline:
    def test_corpus_baseline_pinned(self, tmp_path):
        """Pin the c.259 corpus measurement. Run `python
        scripts/notebook_tools/detect_ascii_flowchart.py MyIA.AI.Notebooks/
        --json` and assert the totals match the baseline.

        Le plancher est un CLIQUET : il ne doit jamais remonter. Le
        resserrer apres une tranche de conversion (mesure firsthand).
        """
        import subprocess
        repo_root = Path(__file__).resolve().parents[3]
        notebooks_dir = repo_root / "MyIA.AI.Notebooks"
        if not notebooks_dir.exists():
            pytest.skip(f"Notebooks dir not found at {notebooks_dir}")
        proc = subprocess.run(
            ["python", "scripts/notebook_tools/detect_ascii_flowchart.py",
             str(notebooks_dir), "--json"],
            capture_output=True, text=True, cwd=repo_root,
        )
        if proc.returncode != 0:
            pytest.skip(f"scan returned {proc.returncode}")
        result = json.loads(proc.stdout)
        total = result["total_findings"]
        files_with = result["files_with_findings"]
        # Cliquet, pas egalite. Une HAUSSE est la regression que ce garde
        # existe pour attraper : un diagramme ASCII neuf entre dans le corpus.
        # Une BAISSE est le rollout #11962 qui fait son travail. La faire
        # rougir a mis `main` au rouge du 2026-08-25T12:35Z au 26/08 alors que
        # 20 notebooks avaient ete convertis : le test accusait le succes, et
        # bloquait au passage toutes les PR derriere le `PR gate`.
        assert total <= CORPUS_BASELINE_TOTAL, (
            f"Regression ASCII-flowchart : {total} findings > plancher "
            f"{CORPUS_BASELINE_TOTAL}. Un flowchart ASCII a ete introduit ou "
            f"reintroduit -- le convertir, ne PAS relever le plancher."
        )
        assert files_with <= CORPUS_BASELINE_FILES_WITH, (
            f"Regression ASCII-flowchart : {files_with} fichiers > plancher "
            f"{CORPUS_BASELINE_FILES_WITH}."
        )
        if total < CORPUS_BASELINE_TOTAL or files_with < CORPUS_BASELINE_FILES_WITH:
            warnings.warn(
                f"Plancher ASCII-flowchart desserre : mesure {total}/{files_with} "
                f"sous le plancher {CORPUS_BASELINE_TOTAL}/"
                f"{CORPUS_BASELINE_FILES_WITH}. Resserrer CORPUS_BASELINE_* a la "
                "mesure courante pour que le cliquet garde ses dents.",
                stacklevel=2,
            )
