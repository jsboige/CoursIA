"""Tests pour la portee de diff dans scripts/notebook_tools/check_notebook_navlinks.py.

#21016 : la voie rapide (fast-lane) absorbe la garde `check-navlinks` mais perd
sa portee de diff (cf. PR #20582 symetrique pour `check-nav-chain`). Le checker
doit donc calculer lui-meme le diff a partir d'une base et borner les NEW
trouves au perimetre imputable. Tests par classe de portee, miroir de
`test_check_notebook_nav_chain.py::TestDiffBaseScope`, adapte a la cle 4-tuples
(notebook, cell_idx, line_no, target) de navlinks.

Quatre clusters :
  1. TestPartitionNewByDiff — imputabilite notebook-in-diff, fail-closed
  2. TestChangedSince — lecture du diff via git, fail-closed sur erreur git
  3. TestDiffBaseScope — controle de bout en bout par `main()`
  4. TestDiffBaseArgparse — option exposee, aide texte
"""
import subprocess
import sys
from pathlib import Path

import pytest

# import du module sous test (depuis scripts/notebook_tools/)
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))
import check_notebook_navlinks as cnn  # noqa: E402


# ---------------------------------------------------------------------------
# 1. _partition_new_by_diff — imputabilite (notebook in diff)
# ---------------------------------------------------------------------------
class TestPartitionNewByDiff:
    """Scope bloquant (decision c.5854935546 transposable, #21016) : NEW
    imputable au diff bloque, hors diff avertit seulement. Controle positif
    ET negatif exiges par la decision. La cle 4-tuples est
    (notebook, cell_idx, line_no, target) ; l'imputabilite regarde la
    1re composante (le notebook) -- plus simple que nav-chain (pas de
    logique de serie/README : un lien casse est ancre a SON notebook)."""

    NEW_TOUCHED = [("MyIA.AI.Notebooks/Search/foo.ipynb", 3, 5, "prev.ipynb")]
    NEW_UNTOUCHED = [("MyIA.AI.Notebooks/ML/bar.ipynb", 1, 2, "next.ipynb")]

    def test_positive_control_notebook_in_diff_blocks(self):
        diff = {"MyIA.AI.Notebooks/Search/foo.ipynb"}
        blocking, warning = cnn._partition_new_by_diff(self.NEW_TOUCHED, diff)
        assert blocking == self.NEW_TOUCHED and warning == []

    def test_negative_control_out_of_diff_warns_only(self):
        diff = {"MyIA.AI.Notebooks/Search/foo.ipynb"}
        blocking, warning = cnn._partition_new_by_diff(self.NEW_UNTOUCHED, diff)
        assert blocking == [] and warning == self.NEW_UNTOUCHED

    def test_fail_closed_empty_diff_blocks_everything(self):
        # Pas de diff connu -> tout NEW bloque (decision c.5854935546
        # transposable : ne pas tolerer un NEW silencieux si le diff est
        # indisponible).
        blocking, warning = cnn._partition_new_by_diff(self.NEW_UNTOUCHED, set())
        assert blocking == self.NEW_UNTOUCHED and warning == []

    def test_mixed_keys_partitioned_correctly(self):
        diff = {"MyIA.AI.Notebooks/Search/foo.ipynb"}
        both = [self.NEW_TOUCHED[0], self.NEW_UNTOUCHED[0]]
        blocking, warning = cnn._partition_new_by_diff(both, diff)
        assert blocking == [self.NEW_TOUCHED[0]]
        assert warning == [self.NEW_UNTOUCHED[0]]


# ---------------------------------------------------------------------------
# 2. _changed_since — lecture du diff via git
# ---------------------------------------------------------------------------
class TestChangedSince:
    """#21016 : le checker calcule `git diff --name-only REF...HEAD` lui-meme,
    comme split-reading / prose-counts / md-content-loss. Git en echec = diff
    inconnu = ensemble vide, fail-closed comme un fichier de liste absent."""

    def test_reads_base_head_range(self, monkeypatch):
        calls = []

        def fake_run(cmd, **kwargs):
            calls.append(cmd)
            return subprocess.CompletedProcess(
                cmd, 0,
                stdout="MyIA.AI.Notebooks/A/x.ipynb\n\nscripts/y.py\n",
                stderr="",
            )

        monkeypatch.setattr(cnn.subprocess, "run", fake_run)
        assert cnn._changed_since("origin/main") == {
            "MyIA.AI.Notebooks/A/x.ipynb", "scripts/y.py"}
        assert calls[0][-1] == "origin/main...HEAD"
        assert "core.quotePath=false" in calls[0]

    def test_git_failure_is_fail_closed(self, monkeypatch, capsys):
        monkeypatch.setattr(
            cnn.subprocess, "run",
            lambda cmd, **kwargs: subprocess.CompletedProcess(
                cmd, 128, stdout="", stderr="fatal: bad revision"),
        )
        assert cnn._changed_since("origin/absent") == set()
        assert "fail-closed" in capsys.readouterr().err


# ---------------------------------------------------------------------------
# 3. TestDiffBaseScope — controle de bout en bout par main()
# ---------------------------------------------------------------------------
class TestDiffBaseScope:
    """#21016 : la voie rapide n'a pas de fichier de liste. `--diff-base REF`
    fait calculer au checker `git diff REF...HEAD`, le meme diff que le
    `pr_files.txt` du workflow d'origine. Sans cette portee, un NEW du graphe
    global rougissait toute PR touchant un carnet."""

    def test_diff_base_scope_reaches_the_verdict(self, monkeypatch, capsys):
        """Controle positif et negatif de bout en bout, par `main` sur le
        graphe reel. Baseline vide : chaque finding du depot est NEW. Un diff
        qui ne touche pas le notebook du finding n'avertit pas (verdict 0) ;
        le meme argv avec le notebook du finding dans le diff bloque (rc=1).
        """
        # On patche _iter_notebooks pour ne retourner que le carnet qui nous
        # interesse (evite de scanner tout le depot, qui prendrait des
        # minutes et crollerait selon l'etat local).
        nb_path = Path("MyIA.AI.Notebooks/Search/01-Foundations/nb.ipynb")
        monkeypatch.setattr(cnn, "_iter_notebooks",
                            lambda family=None, tracked_only=True: [nb_path])

        # On patche scan_notebook pour rendre un finding controle sur ce
        # notebook (sans toucher le scan reel).
        def fake_scan(nb):
            return [{
                "notebook": str(nb).replace("\\", "/"),
                "cell_idx": 0, "line_no": 1,
                "text": "prev", "target": "missing.ipynb",
                "kind": "nav",
            }]
        monkeypatch.setattr(cnn, "scan_notebook", fake_scan)

        # Baseline vide => finding = NEW.
        monkeypatch.setattr(cnn, "_load_baseline", lambda: set())
        monkeypatch.setattr(cnn, "_load_submodule_paths", lambda: [])

        argv = ["--check", "--diff-base", "origin/main"]

        # 1er cas : diff NE TUE PAS le notebook du finding -> avertissement,
        # verdict 0 (un warning, pas un fail).
        monkeypatch.setattr(cnn, "_changed_since",
                            lambda base: {"scripts/ci/fast_lane_registry.py"})
        assert cnn.main(argv) == 0
        out = capsys.readouterr().out
        assert "WARN" in out and "hors diff" in out and "FAIL" not in out

        # 2e cas : diff TUE le notebook du finding -> bloquant, verdict 1.
        monkeypatch.setattr(cnn, "_changed_since",
                            lambda base: {str(nb_path).replace("\\", "/")})
        assert cnn.main(argv) == 1
        out = capsys.readouterr().out
        assert "FAIL" in out and "imputables au diff" in out

    def test_diff_base_git_failure_falls_back_to_block_all(self, monkeypatch, capsys):
        """Git en echec (diff inconnu) = fail-closed : tout NEW bloque."""
        nb_path = Path("MyIA.AI.Notebooks/Search/01-Foundations/nb.ipynb")
        monkeypatch.setattr(cnn, "_iter_notebooks",
                            lambda family=None, tracked_only=True: [nb_path])
        monkeypatch.setattr(cnn, "scan_notebook", lambda nb: [{
            "notebook": str(nb).replace("\\", "/"),
            "cell_idx": 0, "line_no": 1,
            "text": "prev", "target": "missing.ipynb",
            "kind": "nav",
        }])
        monkeypatch.setattr(cnn, "_load_baseline", lambda: set())
        monkeypatch.setattr(cnn, "_load_submodule_paths", lambda: [])
        # _changed_since -> set() (echec git)
        monkeypatch.setattr(cnn, "_changed_since", lambda base: set())

        argv = ["--check", "--diff-base", "origin/main"]
        # set() vide = fail-closed : tout NEW bloque (cf TestPartitionNewByDiff
        # test_fail_closed_empty_diff_blocks_everything).
        assert cnn.main(argv) == 1
        out = capsys.readouterr().out
        assert "FAIL" in out and "WARN" not in out


# ---------------------------------------------------------------------------
# 4. TestDiffBaseArgparse — option exposee et documentee
# ---------------------------------------------------------------------------
class TestDiffBaseArgparse:
    """#21016 : l'option `--diff-base` doit etre visible dans `--help` pour
    qu'un consommateur (fast-lane) puisse l'utiliser directement."""

    def test_diff_base_in_help(self, capsys):
        with pytest.raises(SystemExit) as exc:
            cnn.main(["--help"])
        assert exc.value.code == 0
        assert "--diff-base" in capsys.readouterr().out

    def test_diff_base_in_modes_docstring(self):
        # Modes (convention check_docs_links.py) -- premiere ligne de la
        # docstring, mise a jour par le fix #21016 pour coherence avec
        # check_notebook_nav_chain.py.
        doc = cnn.__doc__ or ""
        assert "--check --diff-base origin/main" in doc
