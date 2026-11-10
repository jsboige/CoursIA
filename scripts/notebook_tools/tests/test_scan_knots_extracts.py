"""Tests for scripts/notebook_tools/scan_knots_extracts.py -- voie (B) #21007.

Ce fichier consolide deux generations de tests (c.478) :

  - la premiere (16 tests) couvrait la v1 de l'organe, qui cablait les deux
    instances fondatrices en dur (``FIGURE_EIGHT_FILE``, ``LIDMAN_FILE``).
    Ses tests sont CONSERVES, avec une seule adaptation : le 4e argument de
    ``scan_classe2`` / ``scan_classe3`` / ``scan_notebook`` est desormais une
    ``LeanTruth`` derivee de l'arbre, plus un ``repo_root``. Aucun cas n'a
    ete retire ; les deux helpers qui posaient les fichiers de verite a leur
    chemin canonique sont conserves et servent a construire la ``LeanTruth``.
  - la seconde ajoute les controles qui manquaient : positifs fondateurs,
    negatifs mesures (les faux positifs qui ont dicte les deux
    discriminants), la verite du depot, l'orchestration (rc 0/1/2) et le
    caractere read-only du scan.

Les deux discriminants sont MESURES, chacun a son test de non-regression :
  - classe 3 : une regle acceptant n'importe quel identifiant declare rend
    2 faux positifs sur 2 candidats sur le corpus reel (``existe`` et
    ``trefoil`` sont des mots ordinaires ET des noms de ``def`` des 47
    modules) -> discriminant underscore.
  - classe 2 : un cadrage CELLULE rend un faux positif sur la cellule 16 de
    KNOTS-01 (arbre d'architecture) -> cadrage ligne.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_knots_extracts import (  # noqa: E402
    LeanTruth,
    _filter_knots,
    iter_notebook_cells,
    main,
    scan_classe2,
    scan_classe3,
    scan_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

KNOTS_REL = Path("MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS")


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source if isinstance(source, list) else [source]}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": source if isinstance(source, list) else [source]}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


def _write_ground_truth_files(repo_root: Path) -> None:
    """Pose les 2 fichiers .lean de verite a leur chemin canonique.

    Conserve de la premiere generation : les chemins sont ceux du depot
    (``.../KNOTS/knot_lean/Knots/<Module>.lean``), ce qui donne a
    ``LeanTruth.build`` les memes cles de module que sur le vrai arbre.
    """
    lean_dir = repo_root / KNOTS_REL / "knot_lean" / "Knots"
    lean_dir.mkdir(parents=True, exist_ok=True)
    # Le header du module declare explicitement 4_1
    (lean_dir / "FigureEight.lean").write_text(
        "/-- Knots.FigureEight -- Invariants du noeud 4_1 sur son code PD plan -/\n"
        "namespace Knots\n"
        "def FigureEight : Knot where\n"
        "  pd_code := [[4,2,5,1], [8,6,1,3], [6,4,7,5], [2,8,3,7]]\n",
        encoding="utf-8",
    )
    (lean_dir / "Lidman.lean").write_text(
        "/-- Knots.Lidman -- 11-crossing knots (subset) -/\n"
        "namespace Knots\n"
        "def knot_11n102_diagram : PDCode where\n"
        "  numEdges := 22\n"
        "def knot_11n102 : Knot where\n"
        "  diagram := knot_11n102_diagram\n",
        encoding="utf-8",
    )


def _truth(repo_root: Path) -> LeanTruth:
    """Verite du depot pour un repo_root de fixture."""
    return LeanTruth.build(repo_root / KNOTS_REL / "knot_lean")


def _bare_truth(nodes: dict[str, set[str]] | None = None) -> LeanTruth:
    """Verite minimale en memoire (pas de disque)."""
    return LeanTruth(defs={k: set() for k in (nodes or {})},
                     nodes=dict(nodes or {}),
                     all_defs=set(),
                     modules_read=len(nodes or {}))


def _truth_from_disk(tmp_path: Path, files: dict[str, str], subdir: str = "knot_lean") -> LeanTruth:
    root = tmp_path / subdir
    for name, content in files.items():
        f = root / f"{name}.lean"
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(content, encoding="utf-8")
    return LeanTruth.build(root)


FIGURE_EIGHT_LEAN = """\
/-- Knots.FigureEight -- Invariants du noeud en huit (4_1) sur son code PD plan. -/
def figureEightInvariant : Nat := 3
"""

LIDMAN_LEAN = """\
/-- Knots.Lidman -- 11n102, unknotting number 2. -/
def knot_11n102_diagram : PDCode :=
  [ .X 0 1 2 3 ]

def knot_11n102 : Knot := { diagram := knot_11n102_diagram }
"""


# ---------------------------------------------------------------------------
# iter_notebook_cells : smoke test (premiere generation, conserve)
# ---------------------------------------------------------------------------

class TestIterNotebookCells:
    def test_yields_all_cells(self, tmp_path: Path):
        nb = tmp_path / "demo.ipynb"
        _write_nb(nb, [_md("a"), _code("b"), _md("c")])
        cells = list(iter_notebook_cells(nb))
        assert len(cells) == 3
        assert [c[0] for c in cells] == [0, 1, 2]
        assert [c[1] for c in cells] == ["markdown", "code", "markdown"]

    def test_skips_empty_cells(self, tmp_path: Path):
        nb = tmp_path / "demo.ipynb"
        _write_nb(nb, [_md("a"), _md("   \n  "), _md("c")])
        cells = list(iter_notebook_cells(nb))
        assert len(cells) == 2

    def test_handles_source_as_list(self, tmp_path: Path):
        # ipynb stores source as a list of strings (one per line)
        nb = tmp_path / "demo.ipynb"
        _write_nb(nb, [{"cell_type": "markdown", "source": ["line1\n", "line2\n"]}])
        cells = list(iter_notebook_cells(nb))
        assert len(cells) == 1
        assert "line1" in cells[0][2]
        assert "line2" in cells[0][2]


# ---------------------------------------------------------------------------
# Classe 2 -- cas de la premiere generation (conserve, adapte a LeanTruth)
# ---------------------------------------------------------------------------

class TestScanClasse2Heritage:
    def test_fresh_4_1_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "FigureEight.lean modelise le noeud 4_1 (quatre-un)."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert findings == []

    def test_stale_8_1_yields_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "FigureEight.lean (noeud 8_1) -- invariants du twist."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert len(findings) == 1
        assert "STALE_IDENTITY" in findings[0]
        assert "8_1" in findings[0]
        assert "4_1" in findings[0]

    def test_stale_8_2_yields_finding(self, tmp_path: Path):
        """Forme NUE du nom de module (sans ``.lean``) : conservee parce que
        la mesure sur le corpus reel ne lui trouve aucun cout."""
        _write_ground_truth_files(tmp_path)
        src = "see FigureEight (8_2) for the alternative parameterization."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert len(findings) == 1
        assert "8_2" in findings[0]

    def test_no_figure_eight_mention_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "we discuss knot 4_1 and 3_1 (trefoil) in this cell."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert findings == []

    def test_missing_ground_truth_no_finding(self, tmp_path: Path):
        # Pas de _write_ground_truth_files -- FigureEight.lean absent
        src = "FigureEight.lean (noeud 8_1) -- stale."
        findings = scan_classe2(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        # Defensif : on ne sait pas conclure, donc pas de finding.
        assert findings == []


# ---------------------------------------------------------------------------
# Classe 3 -- cas de la premiere generation (conserve, adapte a LeanTruth)
# ---------------------------------------------------------------------------

class TestScanClasse3Heritage:
    def test_fresh_no_stale_marker_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = (
            "knot_11n102_diagram est defini dans Lidman.lean (numEdges := 22). "
            "C'est l'etat actuel du head."
        )
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert findings == []

    def test_stale_todo_yields_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "11n102_diagram n'est pas entre, c'est un TODO PD-code."
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert len(findings) == 1
        assert "STALE_TODO" in findings[0]
        assert "11n102" in findings[0]

    def test_stale_avec_caveat_annule(self, tmp_path: Path):
        # Caveat "au head" doit annuler le finding meme si le marker
        # "manquant" est present.
        _write_ground_truth_files(tmp_path)
        src = (
            "11n102_diagram etait marque manquant mais au head le PD-code "
            "est desormais entre. Voir Lidman.lean l. 67."
        )
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert findings == []

    def test_no_lidman_mention_no_finding(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        src = "we discuss knot 11n_42 (different knot entirely)."
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert findings == []

    def test_missing_ground_truth_no_finding(self, tmp_path: Path):
        # Lidman.lean absent -- on ne peut pas conclure.
        src = "11n102_diagram n'est pas defini."
        findings = scan_classe3(tmp_path / "nb.ipynb", 0, src, _truth(tmp_path))
        assert findings == []


# ---------------------------------------------------------------------------
# scan_notebook -- orchestration (premiere generation, conserve)
# ---------------------------------------------------------------------------

class TestScanNotebookHeritage:
    def test_clean_notebook_no_findings(self, tmp_path: Path):
        _write_ground_truth_files(tmp_path)
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [
            _md("FigureEight.lean = 4_1 (quatre-un)."),
            _md("11n102_diagram est dans Lidman.lean."),
        ])
        findings = scan_notebook(nb, _truth(tmp_path))
        assert findings == []

    def test_mixed_stale_yields_both_findings(self, tmp_path: Path):
        """Fixture PURIFIEE (c.478), l'intention est conservee.

        La v1 affirmait cet attendu sur la cellule
        ``"FigureEight.lean (noeud 8_1) -- c'est faux, c'est 4_1."`` : cette
        ligne nomme le bon numero (4_1) en corrigeant le mauvais, donc la
        signaler etait un FAUX POSITIF que le test encodait. Le cas est
        desormais couvert comme controle NEGATIF
        (``test_negative_self_correcting_line``) ; l'intention de ce test --
        un carnet qui porte un defaut de chaque classe rend deux findings --
        est preservee sur une fixture reellement perimee.
        """
        _write_ground_truth_files(tmp_path)
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [
            _md("FigureEight.lean (noeud 8_1) -- invariants du twist."),
            _md("11n102_diagram n'est pas entre, c'est un TODO PD-code."),
        ])
        findings = scan_notebook(nb, _truth(tmp_path))
        assert len(findings) == 2
        assert any("STALE_IDENTITY" in f for f in findings)
        assert any("STALE_TODO" in f for f in findings)

    def test_negative_self_correcting_line(self, tmp_path: Path):
        """Une ligne qui nomme le bon numero en corrigeant le mauvais n'est
        pas un defaut -- c'est le faux positif que la v1 encodait."""
        _write_ground_truth_files(tmp_path)
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [_md("FigureEight.lean (noeud 8_1) -- c'est faux, c'est 4_1.")])
        assert scan_notebook(nb, _truth(tmp_path)) == []

    def test_load_error_returns_one_finding(self, tmp_path: Path):
        nb = tmp_path / "KNOTS" / "broken.ipynb"
        nb.parent.mkdir(parents=True, exist_ok=True)
        nb.write_text("not a notebook {", encoding="utf-8")
        findings = scan_notebook(nb, LeanTruth())
        assert len(findings) == 1
        assert "load_error" in findings[0] or "lecture" in findings[0]


# ---------------------------------------------------------------------------
# Classe 2 -- controles ajoutes : positifs fondateurs et faux positifs mesures
# ---------------------------------------------------------------------------

class TestClasse2:
    def test_positive_control_founder_instance(self, tmp_path: Path):
        """Fondateur : "FigureEight.lean (noeud 8_1)" alors que le module
        modelise 4_1."""
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = "Le module FigureEight.lean modelise le noeud 8_1 (figure-eight)."
        findings = scan_classe2(Path("nb.ipynb"), 16, src, truth)
        assert len(findings) == 1
        assert "STALE_IDENTITY (classe 2)" in findings[0]
        assert "8_1" in findings[0]

    def test_negative_control_corrected_claim(self, tmp_path: Path):
        """Le texte post-fix ("noeud 4_1") doit rester vert."""
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = "Le module FigureEight.lean modelise le noeud 4_1 (figure-eight)."
        assert scan_classe2(Path("nb.ipynb"), 16, src, truth) == []

    def test_negative_module_reference_without_node_number(self, tmp_path: Path):
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = "On importe FigureEight.lean pour l'exemple."
        assert scan_classe2(Path("nb.ipynb"), 3, src, truth) == []

    def test_negative_module_citing_no_node_cannot_conclude(self):
        """Un module muet sur les noeuds n'autorise aucune conclusion."""
        truth = _bare_truth({"Basic": set()})
        src = "Le module Basic.lean definit le noeud 8_1 comme exemple."
        assert scan_classe2(Path("nb.ipynb"), 3, src, truth) == []

    def test_negative_comparison_with_another_knot(self, tmp_path: Path):
        """Comparer 4_1 a 8_1 n'est pas revendiquer que le module EST 8_1."""
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = "FigureEight.lean (4_1) se compare a 8_1 sur son spectre."
        assert scan_classe2(Path("nb.ipynb"), 16, src, truth) == []

    def test_line_scope_not_cell_scope(self, tmp_path: Path):
        """Cadrage LIGNE mesure : un arbre d'architecture qui liste des
        modules et un noeud sur des lignes differentes ne doit pas rougir
        (faux positif mesure sur la cellule 16 de KNOTS-01)."""
        truth = _truth_from_disk(tmp_path, {
            "FigureEight": FIGURE_EIGHT_LEAN,
            "Invariant": "/-- 3-colorabilite, exemple sur 3_1. -/\ndef invariant := 1\n",
        })
        src = (
            "```text\n"
            "knot_lean/\n"
            "  |-- Invariant.lean      (3-colorabilite)\n"
            "  |-- FigureEight.lean    (noeud 4_1)\n"
            "```\n"
        )
        assert scan_classe2(Path("nb.ipynb"), 16, src, truth) == []

    def test_wrapped_sentence_still_fires(self, tmp_path: Path):
        """Prose repliee a 80 colonnes : « ... FigureEight.lean » puis
        « le noeud 8_1 ... ». Un cadrage mono-ligne perdait ce cas (c.478)."""
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = (
            "Le module FigureEight.lean modelise le\n"
            "noeud 8_1 (figure-eight) sous forme de diagramme.\n"
        )
        findings = scan_classe2(Path("nb.ipynb"), 16, src, truth)
        assert len(findings) == 1
        assert "8_1" in findings[0]
        assert ":L1:" in findings[0]

    def test_wrap_window_does_not_join_two_finished_sentences(self, tmp_path: Path):
        """Une phrase terminee puis une autre ne forme pas une continuation."""
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = (
            "On importe FigureEight.lean pour l'exemple.\n"
            "Le noeud 8_1 sert de temoin ailleurs.\n"
        )
        assert scan_classe2(Path("nb.ipynb"), 16, src, truth) == []

    def test_bare_unknown_capitalised_word_is_not_a_module(self, tmp_path: Path):
        """Sans filtre sur les modules connus, tout mot capitalise deviendrait
        une reference de module."""
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = "Une Remarque generale sur le noeud 8_1, sans module cite."
        assert scan_classe2(Path("nb.ipynb"), 1, src, truth) == []

    def test_finding_reports_line_number(self, tmp_path: Path):
        truth = _truth_from_disk(tmp_path, {"FigureEight": FIGURE_EIGHT_LEAN})
        src = "ligne 1\nligne 2\nFigureEight.lean = noeud 8_1\n"
        findings = scan_classe2(Path("nb.ipynb"), 5, src, truth)
        assert len(findings) == 1
        assert ":L3:" in findings[0]


# ---------------------------------------------------------------------------
# Classe 3 -- controles ajoutes
# ---------------------------------------------------------------------------

class TestClasse3:
    def test_positive_control_founder_instance(self, tmp_path: Path):
        """Fondateur : "le PD-code de 11n102 n'est pas encore entre" alors
        que ``knot_11n102_diagram`` est declare au head."""
        truth = _truth_from_disk(tmp_path, {"Lidman": LIDMAN_LEAN})
        assert "knot_11n102_diagram" in truth.all_defs
        src = "Le PD-code de 11n102 n'est pas encore entre : knot_11n102_diagram manque."
        findings = scan_classe3(Path("nb.ipynb"), 23, src, truth)
        assert findings
        assert "STALE_TODO (classe 3)" in findings[0]
        assert "knot_11n102_diagram" in findings[0]

    def test_negative_caveat_suppresses_finding(self, tmp_path: Path):
        truth = _truth_from_disk(tmp_path, {"Lidman": LIDMAN_LEAN})
        src = (
            "Le PD-code de 11n102 n'est pas encore entre (extrait perime, "
            "refutation du TODO ci-dessous).\n"
            "knot_11n102_diagram est en fait defini."
        )
        assert scan_classe3(Path("nb.ipynb"), 23, src, truth) == []

    @pytest.mark.parametrize(
        "src",
        [
            "Le diagramme `knot_11n102_diagram` manque encore.",
            "`knot_11n102_diagram` : TODO",
            "`knot_11n102_diagram` reste a implementer.",
            "`knot_11n102_diagram` n'existe pas encore.",
            "`knot_11n102_diagram` n'est pas encore entre.",
        ],
    )
    def test_absence_class_fires_on_every_measured_formulation(
        self, tmp_path: Path, src: str
    ):
        """Mesure c.478 : quatre de ces cinq formulations rendaient rc 0.

        La regle vise la CLASSE « absence affirmee », pas la formulation de
        son instance fondatrice ; chaque ligne du tableau de review devient
        un controle qui doit tirer.
        """
        truth = _truth_from_disk(tmp_path, {"Lidman": LIDMAN_LEAN})
        findings = scan_classe3(Path("nb.ipynb"), 23, src, truth)
        assert findings, f"aucun finding pour : {src}"
        assert "STALE_TODO (classe 3)" in findings[0]

    def test_caveat_elsewhere_in_cell_does_not_swallow_a_real_finding(
        self, tmp_path: Path
    ):
        """Portee du caveat : la phrase, pas la cellule (mesure c.478).

        Un « un autre passage est perime » ecrit deux lignes plus haut ne
        doit plus neutraliser un TODO perime reel.
        """
        truth = _truth_from_disk(tmp_path, {"Lidman": LIDMAN_LEAN})
        src = (
            "Un autre passage est perime.\n"
            "\n"
            "`knot_11n102_diagram` n'est pas encore entre.\n"
        )
        findings = scan_classe3(Path("nb.ipynb"), 23, src, truth)
        assert findings, "le caveat a portee cellule a encore avale le finding"

    def test_caveat_attached_to_the_identifier_still_suppresses(
        self, tmp_path: Path
    ):
        """Le caveat qui cite le MEME identifiant reste valide : il porte sur
        la phrase concernee, pas sur la cellule."""
        truth = _truth_from_disk(tmp_path, {"Lidman": LIDMAN_LEAN})
        src = (
            "Etat perime de `knot_11n102_diagram` :\n"
            "`knot_11n102_diagram` n'est pas encore entre.\n"
        )
        assert scan_classe3(Path("nb.ipynb"), 23, src, truth) == []

    def test_negative_plain_word_colliding_with_a_def(self, tmp_path: Path):
        """Faux positif mesure : ``trefoil`` est un nom de ``def`` ET un mot
        ordinaire. Le discriminant underscore le neutralise."""
        truth = _truth_from_disk(
            tmp_path,
            {"Basic": "def trefoil : Knot := 3_1\ndef existe : Bool := true\n"},
        )
        assert "trefoil" in truth.all_defs
        src = "# TODO etudiant: utiliser SnapPy pour creer le trefoil et verifier son volume"
        assert scan_classe3(Path("nb.ipynb"), 33, src, truth) == []

    def test_negative_identifier_not_declared(self, tmp_path: Path):
        truth = _truth_from_disk(tmp_path, {"Lidman": LIDMAN_LEAN})
        src = "Le PD-code de 12n999 n'est pas encore entre : knot_12n999_diagram manque."
        assert scan_classe3(Path("nb.ipynb"), 23, src, truth) == []

    def test_no_absence_marker_no_finding(self, tmp_path: Path):
        truth = _truth_from_disk(tmp_path, {"Lidman": LIDMAN_LEAN})
        src = "`knot_11n102_diagram` porte numEdges := 22."
        assert scan_classe3(Path("nb.ipynb"), 23, src, truth) == []


# ---------------------------------------------------------------------------
# Verite du depot : le modele lui-meme
# ---------------------------------------------------------------------------

class TestLeanTruth:
    def test_build_reads_declarations_and_nodes(self, tmp_path: Path):
        truth = _truth_from_disk(tmp_path, {
            "FigureEight": FIGURE_EIGHT_LEAN,
            "Lidman": LIDMAN_LEAN,
        })
        assert truth.modules_read == 2
        assert "knot_11n102_diagram" in truth.defs["Lidman"]
        assert "4_1" in truth.nodes["FigureEight"]

    def test_build_excludes_vendored_dirs(self, tmp_path: Path):
        root = tmp_path / "knot_lean"
        (root / ".lake/packages/mathlib").mkdir(parents=True)
        (root / ".lake/packages/mathlib/Big.lean").write_text(
            "def nat_gcd_helper : Nat := 1\n", encoding="utf-8")
        (root / "Knots").mkdir(parents=True)
        (root / "Knots/Basic.lean").write_text("def knot_basic : Nat := 1\n", encoding="utf-8")
        truth = LeanTruth.build(root)
        assert truth.modules_read == 1
        assert "nat_gcd_helper" not in truth.all_defs

    def test_build_on_missing_root_is_empty(self, tmp_path: Path):
        truth = LeanTruth.build(tmp_path / "nope")
        assert truth.modules_read == 0
        assert truth.all_defs == set()


# ---------------------------------------------------------------------------
# Orchestration : rc, silence du hook, verdict "non conclu"
# ---------------------------------------------------------------------------

class TestMain:
    def _repo(self, tmp_path: Path, cells: list[dict]) -> Path:
        repo = tmp_path / "repo"
        knots = repo / KNOTS_REL
        _write_nb(knots / "KNOTS-99-demo.ipynb", cells)
        (knots / "knot_lean").mkdir(parents=True, exist_ok=True)
        (knots / "knot_lean/FigureEight.lean").write_text(
            FIGURE_EIGHT_LEAN, encoding="utf-8")
        return repo

    def test_clean_corpus_exits_zero(self, tmp_path: Path):
        repo = self._repo(tmp_path, [_md("FigureEight.lean modelise le noeud 4_1.")])
        assert main(["--repo-root", str(repo)]) == 0

    def test_stale_corpus_exits_one(self, tmp_path: Path):
        repo = self._repo(tmp_path, [_md("FigureEight.lean modelise le noeud 8_1.")])
        assert main(["--repo-root", str(repo)]) == 1

    def test_missing_lean_tree_is_not_concluded(self, tmp_path: Path):
        """Arbre Lean absent : rc 2, jamais un vert trompeur."""
        repo = self._repo(tmp_path, [_md("FigureEight.lean modelise le noeud 8_1.")])
        (repo / KNOTS_REL / "knot_lean").rename(tmp_path / "moved")
        assert main(["--repo-root", str(repo)]) == 2

    def test_changed_mode_without_knots_notebook_is_silent(self, tmp_path: Path):
        repo = self._repo(tmp_path, [_md("FigureEight.lean modelise le noeud 8_1.")])
        other = tmp_path / "elsewhere/other.ipynb"
        _write_nb(other, [_md("FigureEight.lean modelise le noeud 8_1.")])
        assert main(["--repo-root", str(repo), "--changed", str(other)]) == 0

    def test_changed_mode_scans_knots_notebook(self, tmp_path: Path):
        repo = self._repo(tmp_path, [_md("FigureEight.lean modelise le noeud 8_1.")])
        nb = repo / KNOTS_REL / "KNOTS-99-demo.ipynb"
        assert main(["--repo-root", str(repo), "--changed", str(nb)]) == 1


class TestFilterKnots:
    def test_filters_non_ipynb_and_outside_knots(self, tmp_path: Path):
        knots = tmp_path / "KNOTS"
        knots.mkdir()
        inside = knots / "a.ipynb"
        inside.write_text("{}", encoding="utf-8")
        outside = tmp_path / "b.ipynb"
        outside.write_text("{}", encoding="utf-8")
        not_nb = knots / "c.lean"
        not_nb.write_text("", encoding="utf-8")
        kept = _filter_knots([inside, outside, not_nb], knots)
        assert kept == [inside]


# ---------------------------------------------------------------------------
# Non-regression : le scan reste read-only
# ---------------------------------------------------------------------------

class TestReadOnly:
    def test_scan_does_not_modify_notebook_bytes(self, tmp_path: Path):
        nb = tmp_path / "KNOTS/demo.ipynb"
        _write_nb(nb, [_md("FigureEight.lean modelise le noeud 8_1.")])
        before = nb.read_bytes()
        truth = _bare_truth({"FigureEight": {"4_1"}})
        scan_notebook(nb, truth)
        assert nb.read_bytes() == before
