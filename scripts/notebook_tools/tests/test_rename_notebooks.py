#!/usr/bin/env python3
"""Tests de l'outil de renommage canonique (#17784).

Chaque test du tableau d'ouverture de l'issue est reproduit ici comme un
controle positif : le defaut historique est FABRIQUE dans un depot temporaire,
puis l'outil doit le traiter sans le reproduire. Un test qui ne construirait
pas le defaut passerait au vert sur un outil casse.

  1. cellule ancienne restauree (#17363)  -> TestI1ByteIdentity
  2. abrege rate                          -> TestAbbreviatedKernelForm
  3. fixture corrompue                    -> TestDeclaredFixtureUntouched
  4. entree Quarto oubliee                -> TestQuartoEntryRewritten
  5. reference nue                        -> TestBareStemReference
  6. reference en cellule de code         -> TestCodeCellNeverRewritten
  7. sortie intacte                       -> TestCommittedOutputUntouched

Plus les invariants structurants : fail-closed sur surfaces melangees,
reference fragmentee listee, discipline des 2 commits, registre, rebase-helper.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

_TOOLS = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_TOOLS))

import rename_notebooks as rn  # noqa: E402


def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git"] + list(args), cwd=str(repo), capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise AssertionError("git %s -> %s" % (" ".join(args), r.stderr[:200]))
    return r.stdout


def _nb(cells: list[dict], kernelspec: str = "python3") -> dict:
    return {"cells": cells, "nbformat": 4, "nbformat_minor": 5,
            "metadata": {"kernelspec": {"name": kernelspec,
                                         "display_name": kernelspec}}}


def _md(text: str) -> dict:
    return {"cell_type": "markdown", "metadata": {}, "source": text.splitlines(keepends=True)}


def _code(src: str, outputs: list[dict] | None = None, exec_count: int = 1) -> dict:
    return {"cell_type": "code", "execution_count": exec_count, "metadata": {},
            "outputs": outputs or [], "source": src.splitlines(keepends=True)}


def _write(repo: Path, rel: str, body: str) -> Path:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8", newline="")
    return p


def _write_nb(repo: Path, rel: str, nb: dict) -> Path:
    return _write(repo, rel, json.dumps(nb, indent=1, ensure_ascii=False) + "\n")


def _init_repo(repo: Path) -> str:
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    _write_nb(repo, "MyIA.AI.Notebooks/S/S-01-Alpha.ipynb", _nb([_md("Base.")]))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    return _git(repo, "rev-parse", "HEAD").strip()


OLD = "MyIA.AI.Notebooks/S/S-01-Alpha.ipynb"
NEW = "MyIA.AI.Notebooks/S/S-01-Alpha-Python.ipynb"


def _forms() -> list[rn.RefForms]:
    return [rn.ref_forms(OLD, NEW)]


class TestI1ByteIdentity(unittest.TestCase):
    """Defaut 1 (#17363) : une cellule ancienne est revenue parce que le
    renommage avait serialise le notebook via json.load/json.dump -- format,
    ordre de cles et cellules restaures d'une version anterieure. L'editeur AU
    TEXTE garantit l'identite octet par octet hors sous-chaines remplacees."""

    def test_markdown_ref_edit_is_bytewise_outside_replacements(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            nb = _nb([_md(f"Voir [S-01]({OLD}) pour la suite."),
                      _code("print('hello')", exec_count=3)])
            p = _write_nb(repo, OLD, nb)
            before = p.read_bytes()

            n = rn.rewrite_file(p, _forms())
            after = p.read_bytes()

            self.assertGreaterEqual(n, 1)
            # Equivalence avec un remplacement de sous-chaine pure : c'est la
            # definition meme de l'edition au texte (I1).
            self.assertEqual(after.decode("utf-8"),
                             before.decode("utf-8").replace(OLD, NEW))
            # La cellule de code et son execution_count traversent intacts.
            got = json.loads(after)
            self.assertEqual(got["cells"][1]["source"], ["print('hello')"])
            self.assertEqual(got["cells"][1]["execution_count"], 3)

    def test_relative_subdir_link_and_papermill_path_are_matched(self):
        """Le lookbehind n'exclut pas `/` : un referent embarque dans un chemin
        relatif ou un metadata.papermill est un referent comme un autre
        (angle mort du premier jet de l'outil, couvert ici)."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            nb = _nb([_md("Voir [voisin](sub/S-01-Alpha.ipynb).")])
            p = _write_nb(repo, "MyIA.AI.Notebooks/S/S-02-Beta.ipynb", nb)
            rn.rewrite_file(p, _forms())
            got = json.loads(p.read_text(encoding="utf-8"))
            self.assertIn("sub/S-01-Alpha-Python.ipynb",
                          "".join(got["cells"][0]["source"]))

    def test_structure_guard_refuses_rather_than_writes(self):
        """Si la garde structurelle echoue, rien n'est ecrit (fail-closed I1)."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            p = _write_nb(repo, OLD, _nb([_md(f"Voir {OLD}")]))
            before = p.read_bytes()
            with mock.patch.object(rn.json, "loads",
                                   side_effect=ValueError("corrompu")):
                with self.assertRaises(SystemExit):
                    rn.rewrite_file(p, _forms())
            self.assertEqual(p.read_bytes(), before)


class TestAbbreviatedKernelForm(unittest.TestCase):
    """Defaut 2 : les abregees portant le suffixe (`Prefixe-NN-Csharp`) dans un
    README n'etaient pas reecrites."""

    def test_abbreviated_kernel_form_in_readme_is_rewritten(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            # Cas reel de tranche : la serie porte deja le suffixe en casse
            # heritee, le README cite l'abregee portante.
            old_rel = "MyIA.AI.Notebooks/S/S-01-Alpha-Csharp.ipynb"
            new_rel = "MyIA.AI.Notebooks/S/S-01-Alpha-CSharp.ipynb"
            p = _write(repo, "MyIA.AI.Notebooks/S/README.md",
                       "Le cours [S-01-Csharp](S-01-Alpha-Csharp.ipynb) ouvre.")
            forms = [rn.ref_forms(old_rel, new_rel)]
            n = rn.rewrite_file(p, forms)
            body = p.read_text(encoding="utf-8")
            self.assertIn("[S-01-CSharp](S-01-Alpha-CSharp.ipynb)", body)
            self.assertNotIn("Csharp", body)
            self.assertGreaterEqual(n, 2)


class TestDeclaredFixtureUntouched(unittest.TestCase):
    """Defaut 3 : une fixture declaree avait ete reecrite et le test qui la
    fixait a echoue. Les fixtures s'excluent par liste DECLAREE, jamais par
    heuristique -- et la liste se monkeypathe par test."""

    def test_declared_fixture_is_scanned_out(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            _write(repo, "scripts/tests/fixtures/old_names.json",
                   json.dumps({"cite": OLD}))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "fixture")

            with mock.patch.object(rn, "FIXTURES_DECLARED",
                                   ("scripts/tests/fixtures/old_names.json",)):
                plan = rn.scan_referents(_forms(), repo)
            self.assertNotIn("scripts/tests/fixtures/old_names.json",
                             plan.rewrites)


class TestQuartoEntryRewritten(unittest.TestCase):
    """Defaut 4 : l'entree _quarto.yml avait ete oubliee."""

    def test_quarto_chapter_is_rewritten(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            _write(repo, "_quarto.yml",
                   "chapters:\n  - " + OLD + "\n")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "quarto")

            plan = rn.scan_referents(_forms(), repo)
            self.assertIn("_quarto.yml", plan.rewrites)
            rn.rewrite_file(repo / "_quarto.yml", _forms())
            self.assertIn(NEW, (repo / "_quarto.yml").read_text(encoding="utf-8"))


class TestBareStemReference(unittest.TestCase):
    """Defaut 5 : la reference nue (stem, sans chemin ni extension) dans une
    cellule markdown."""

    def test_bare_stem_in_markdown_is_rewritten(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            nb = _nb([_md("Le precedent carnet S-01-Alpha restait reference."),
                      _md("Voisin non vise : S-01-AlphaBis doit survivre.")])
            p = _write_nb(repo, "MyIA.AI.Notebooks/S/S-02-Beta.ipynb", nb)
            before = p.read_text(encoding="utf-8")
            rn.rewrite_file(p, _forms())
            after = p.read_text(encoding="utf-8")
            self.assertIn("S-01-Alpha-Python restait", after)
            # Word-bounded : le voisin allonge n'est pas mange.
            self.assertIn("S-01-AlphaBis doit survivre", after)
            self.assertNotIn("S-01-AlphaBis-Python", after)
            del before


class TestCodeCellNeverRewritten(unittest.TestCase):
    """Defaut 6 : une reference dans une CELLULE DE CODE avait ete reecrite,
    forgeant une source que plus personne n'a executee (C.2). Invariant I2 :
    listee, jamais reecrite ; le fichier entier est refuse (fail-closed) quand
    code et markdown coportent des referents."""

    def test_code_cell_reference_is_listed_and_file_refused(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            nb = _nb([_md(f"Voir {OLD}."),
                      _code(f"path = '{OLD}'")])
            _write_nb(repo, "MyIA.AI.Notebooks/S/S-02-Beta.ipynb", nb)
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "referent code")

            plan = rn.scan_referents(_forms(), repo)
            rel = "MyIA.AI.Notebooks/S/S-02-Beta.ipynb"
            self.assertIn((rel, 1, OLD), plan.code_cells)
            self.assertIn(rel, plan.mixed_refused)
            self.assertNotIn(rel, plan.rewrites)
            # Rien n'est ecrit sur un fichier refuse.
            body = (repo / rel).read_text(encoding="utf-8")
            self.assertIn(OLD, body)


class TestCommittedOutputUntouched(unittest.TestCase):
    """Defaut 7 : une SORTIE commise citant l'ancien nom. Invariant I3 : la
    sortie est un compte-rendu d'execution, jamais un champ d'edition
    (secrets-hygiene regle 6)."""

    def test_output_reference_is_listed_and_never_touched(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            out = {"output_type": "stream", "name": "stdout",
                   "text": [f"lit {OLD}\n"]}
            nb = _nb([_code("print('x')", outputs=[out], exec_count=7)])
            _write_nb(repo, "MyIA.AI.Notebooks/S/S-02-Beta.ipynb", nb)
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "sortie citante")

            plan = rn.scan_referents(_forms(), repo)
            rel = "MyIA.AI.Notebooks/S/S-02-Beta.ipynb"
            self.assertTrue(any(r == rel and i == 0 for r, i, _o in plan.outputs))
            self.assertIn(rel, plan.mixed_refused)
            got = json.loads((repo / rel).read_text(encoding="utf-8"))
            self.assertEqual(got["cells"][0]["outputs"][0]["text"], [f"lit {OLD}\n"])


class TestFragmentedReference(unittest.TestCase):
    """Une reference scindee en elements de liste source JSON
    (["...S-01", "-Alpha..."]) est INVISIBLE au remplacement texte : elle doit
    etre LISTEE (manuel), pas ratee en silence ni cassee."""

    def test_fragmented_reference_is_listed(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            nb = _nb([_md("intro"),
                      {"cell_type": "markdown", "metadata": {},
                       "source": ["Voir S-01", "-Alpha ci-dessus."]}])
            _write_nb(repo, "MyIA.AI.Notebooks/S/S-02-Beta.ipynb", nb)
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "fragmentee")

            plan = rn.scan_referents(_forms(), repo)
            self.assertIn(("MyIA.AI.Notebooks/S/S-02-Beta.ipynb", 1),
                          plan.fragmented)


class TestPapermillMetadataRewritten(unittest.TestCase):
    """metadata.papermill.input_path porte le basename : surface autorisee
    (normalisation tolerate #1), reecrite avec le reste."""

    def test_papermill_path_is_rewritten(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            nb = _nb([_md("x")])
            nb["metadata"]["papermill"] = {"input_path": "/abs/old/S-01-Alpha.ipynb",
                                           "output_path": "/abs/old/S-01-Alpha.ipynb"}
            p = _write_nb(repo, "MyIA.AI.Notebooks/S/S-03-Gamma.ipynb", nb)
            rn.rewrite_file(p, _forms())
            got = json.loads(p.read_text(encoding="utf-8"))
            self.assertEqual(got["metadata"]["papermill"]["input_path"],
                             "/abs/old/S-01-Alpha-Python.ipynb")


class TestTwoCommitDiscipline(unittest.TestCase):
    """Invariant I6 : commit 1 = git mv purs (R100), commit 2 = referents.
    Le registre est ecrit ; les organes tournent en fin de passe (stubbes ici :
    leur perimetre est le vrai depot, pas le temporaire)."""

    def test_apply_produces_two_commits_ledger_and_clean_renames(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            _write(repo, "MyIA.AI.Notebooks/S/README.md",
                   f"La serie ouvre par [{OLD}]({OLD}).")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "referents")
            # La table vit HORS du depot (scratchpad) : le `git add -A` du
            # commit 2 ne doit jamais la capturer.
            tsv = Path(str(repo) + ".table.tsv")
            tsv.write_text(f"{OLD}\t{NEW}\n", encoding="utf-8")

            cwd = os.getcwd()
            os.chdir(repo)
            try:
                with mock.patch.object(rn, "run_organs", return_value=0):
                    rc = rn.main(["--mapping", str(tsv), "--apply",
                                 "--lane", "test-lane"])
            finally:
                os.chdir(cwd)
            self.assertEqual(rc, 0)

            # commit 1 : purs renames R100
            c1 = _git(repo, "diff", "--name-status", base, "HEAD~1")
            self.assertIn(f"R100\t{OLD}\t{NEW}", c1)
            # commit 2 : referents + registre, AUCUN .ipynb re-serialise
            c2 = _git(repo, "diff", "--name-status", "HEAD~1", "HEAD")
            self.assertNotIn(f"R100\t{OLD}\t{NEW}", c2)
            self.assertIn("M\tMyIA.AI.Notebooks/S/README.md", c2)
            self.assertIn("A\tdocs/reference/rename-ledger.tsv", c2)
            # le notebook renomme n'est PAS re-serialise au commit 2
            self.assertNotIn(f"M\t{NEW}", c2)
            # le registre porte la paire et la lane
            ledger = (repo / rn.LEDGER_RELPATH).read_text(encoding="utf-8")
            self.assertIn(f"{OLD}\t{NEW}", ledger)
            self.assertIn("test-lane", ledger)


class TestMappingRefusals(unittest.TestCase):
    """Gardes d'entree : table perimee, collision interne, cible deja la."""

    def test_missing_source_file_refuses(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            tsv = Path(str(repo) + ".table.tsv")
            tsv.write_text("MyIA.AI.Notebooks/S/S-09-Absent.ipynb\t"
                           "MyIA.AI.Notebooks/S/S-09-Absent-Python.ipynb\n",
                           encoding="utf-8")
            cwd = os.getcwd()
            os.chdir(repo)
            try:
                rc = rn.main(["--mapping", str(tsv)])
            finally:
                os.chdir(cwd)
            self.assertEqual(rc, 1)

    def test_duplicate_targets_refuse(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            _write_nb(repo, "MyIA.AI.Notebooks/S/S-01-Bis.ipynb", _nb([_md("y")]))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "bis")
            tsv = Path(str(repo) + ".table.tsv")
            tsv.write_text(f"{OLD}\t{NEW}\n"
                           "MyIA.AI.Notebooks/S/S-01-Bis.ipynb\t" + NEW + "\n",
                           encoding="utf-8")
            cwd = os.getcwd()
            os.chdir(repo)
            try:
                rc = rn.main(["--mapping", str(tsv)])
            finally:
                os.chdir(cwd)
            self.assertEqual(rc, 1)


class TestRebaseHelper(unittest.TestCase):
    """--rebase-helper : reecrire les lignes AJOUTEES d'une branche qui citent
    un ancien nom du registre ; dry-run par defaut ; les notebooks restent
    manuels (C.2 : la lane qui edite une cellule la re-execute)."""

    def _setup(self, repo: Path) -> None:
        base = _init_repo(repo)
        (repo / rn.LEDGER_RELPATH).parent.mkdir(parents=True, exist_ok=True)
        (repo / rn.LEDGER_RELPATH).write_text(
            "ancien\tnouveau\tdate\tlane\n"
            f"{OLD}\t{NEW}\t2026-09-25\ttest\n", encoding="utf-8", newline="")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-qm", "registre")
        _write(repo, "docs/notes.md", f"Nouvelle note citant {OLD}.\n")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-qm", "branche qui cite l'ancien nom")
        # Le helper diff contre origin/main : fabrique la ref sans remote reel.
        _git(repo, "update-ref", "refs/remotes/origin/main", base)

    def test_dry_run_then_apply(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            self._setup(repo)
            cwd = os.getcwd()
            os.chdir(repo)
            try:
                rc = rn.main(["--rebase-helper"])
                self.assertEqual(rc, 0)
                self.assertIn(OLD, (repo / "docs/notes.md").read_text(encoding="utf-8"))
                rc = rn.main(["--rebase-helper", "--apply"])
                self.assertEqual(rc, 0)
            finally:
                os.chdir(cwd)
            body = (repo / "docs/notes.md").read_text(encoding="utf-8")
            self.assertIn(NEW, body)
            self.assertNotIn(OLD, body)


class TestPropose(unittest.TestCase):
    """--propose : table canonique, noyaux lus, preuve -Lean-Python citee,
    verdicts CONFORME/EXCLU, collision detectee."""

    def test_propose_table(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            _write_nb(repo, "MyIA.AI.Notebooks/S/S-02-Beta-Lean-Native.ipynb",
                      _nb([_md("x")], kernelspec="lean4-wsl"))
            _write_nb(repo, "MyIA.AI.Notebooks/S/S-03-Gamma.ipynb",
                      _nb([_md("x"),
                           _code("import subprocess\nsubprocess.run(['lake','build'])")]))
            _write_nb(repo, "MyIA.AI.Notebooks/S/research.ipynb",
                      _nb([_md("x")]))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "serie")

            table = rn.propose("MyIA.AI.Notebooks/S", repo)
            self.assertIn("`MyIA.AI.Notebooks/S/S-02-Beta-Lean-Native.ipynb` | "
                          "`MyIA.AI.Notebooks/S/S-02-Beta-Lean.ipynb`", table)
            self.assertIn("RENOMMAGE", table)
            self.assertIn("cell 1", table)          # preuve lean-python citee
            self.assertIn("EXCLU", table)           # research.ipynb
            self.assertIn("S-03-Gamma-Lean-Python", table)


class TestReview17801Guards(unittest.TestCase):
    """Controles positifs des trois points de la review ai-01 (#17801,
    review 5316644366) : chacun FABRIQUE le defaut constate, puis verifie que
    l'outil le ferme au lieu de le reproduire."""

    def _serie_repo(self, repo: Path, files: list[tuple[str, dict]]) -> None:
        _init_repo(repo)
        for rel, nb in files:
            _write_nb(repo, rel, nb)
        _git(repo, "add", "-A")
        _git(repo, "commit", "-qm", "serie")

    def test_1_apply_refuses_dirty_tree(self):
        """>--apply` sur un arbre non propre : refus rc=1, RIEN committe.
        Un scratch/un body de PR en cours ne doit jamais partir dans le commit
        de referents d'un renommage."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            (repo / "scratch.txt").write_text("wip d'une autre session",
                                              encoding="utf-8")
            tsv = Path(str(repo) + ".table.tsv")
            tsv.write_text(f"{OLD}\t{NEW}\n", encoding="utf-8")
            cwd = os.getcwd()
            os.chdir(repo)
            try:
                rc = rn.main(["--mapping", str(tsv), "--apply"])
            finally:
                os.chdir(cwd)
            self.assertEqual(rc, 1)
            # aucun commit cree, la tete n'a pas bouge
            self.assertEqual(_git(repo, "rev-parse", "HEAD").strip(), base)
            self.assertTrue((repo / OLD).is_file())
            self.assertFalse((repo / NEW).exists())

    def test_2_lean_tail_python_kernel_without_proof_goes_to_arbitrate(self):
        """`-Lean` sous python3 SANS preuve : A TRANCHER, jamais un -Python
        silencieux qui effacerait l'information de pilotage (l'inverse exact
        du garde check_kernel_suffix_canon de cette meme PR)."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            self._serie_repo(repo, [
                ("MyIA.AI.Notebooks/S/S-01-FOL-Lab-Lean.ipynb",
                 _nb([_md("lab"), _code("print('aucun appel lake')")])),
            ])
            table = rn.propose("MyIA.AI.Notebooks/S", repo)
            self.assertIn("`MyIA.AI.Notebooks/S/S-01-FOL-Lab-Lean.ipynb` | "
                          "`MyIA.AI.Notebooks/S/S-01-FOL-Lab-Lean.ipynb`", table)
            self.assertIn("A TRANCHER", table)
            self.assertIn("sans preuve", table)
            self.assertNotIn("S-01-FOL-Lab-Python", table)

    def test_2b_run_wsl_lake_build_string_counts_as_proof(self):
        """`run_wsl(f"cd ... && lake build X")` : le pilotage indirect via
        chaine de commande compte comme preuve citee (defaut mesure par ai-01
        sur Tweety-02d/3b/5d/5e, invisibles aux quatre motifs d'origine)."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            self._serie_repo(repo, [
                ("MyIA.AI.Notebooks/S/S-01-FOL-Lab-Lean.ipynb",
                 _nb([_md("lab"),
                      _code('run_wsl(f"cd {to_wsl(LAKE_DIR)} && '
                            'lake build FormalLogic.FolBridge")')])),
            ])
            table = rn.propose("MyIA.AI.Notebooks/S", repo)
            self.assertIn("`MyIA.AI.Notebooks/S/S-01-FOL-Lab-Lean-Python.ipynb`",
                          table)
            self.assertIn("cell 1", table)
            self.assertIn("lake build", table)

    def test_3_non_canonical_target_falls_to_arbitrate(self):
        """Une cible qui ne satisfait pas elle-meme la grammaire (mot de noyau
        en infixe, ou pas de prefixe de serie) tombe en A TRANCHER : la livrer
        promettrait un SECOND renommage."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            self._serie_repo(repo, [
                # prefixe Z3 suivi de Python puis du numero : STEM_RE ne matche
                # pas, l'ancien code se bornait a apposer le suffixe.
                ("MyIA.AI.Notebooks/Z3/Z3-Python-13-UnsatCores.ipynb",
                 _nb([_md("x")])),
                # pas de prefixe, separateur _ : hors grammaire.
                ("MyIA.AI.Notebooks/Z3-Linq2Z3/01_Linq2Z3_Intro.ipynb",
                 _nb([_md("x")], kernelspec=".net-csharp")),
            ])
            table = rn.propose("MyIA.AI.Notebooks/Z3", repo)
            table += rn.propose("MyIA.AI.Notebooks/Z3-Linq2Z3", repo)
            self.assertNotIn("Z3-Python-13-UnsatCores-Python", table)
            self.assertNotIn("01_Linq2Z3_Intro-CSharp", table)
            self.assertEqual(table.count("A TRANCHER"), 2)
            self.assertIn("non canonique", table)

    def test_4_commit_messages_cite_source_no_hardcoded_attribution(self):
        """Les commits citent la SOURCE de la table (--mapping), sans co-auteur
        ni reference d'issue codes en dur : la lane qui execute n'est pas
        toujours ce modele, la table ne vient pas toujours de la meme issue."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            _write(repo, "MyIA.AI.Notebooks/S/README.md",
                   f"La serie ouvre par [{OLD}]({OLD}).")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "referents")
            tsv = Path(str(repo) + ".table.tsv")
            tsv.write_text(f"{OLD}\t{NEW}\n", encoding="utf-8")
            cwd = os.getcwd()
            os.chdir(repo)
            try:
                with mock.patch.object(rn, "run_organs", return_value=0):
                    rc = rn.main(["--mapping", str(tsv), "--apply",
                                 "--lane", "test-lane"])
            finally:
                os.chdir(cwd)
            self.assertEqual(rc, 0)
            log = _git(repo, "log", "--format=%B", "-2")
            self.assertIn(str(tsv), log)          # source citee
            self.assertNotIn("Claude", log)       # pas de co-auteur code en dur
            self.assertNotIn("#17784", log)       # pas d'issue codee en dur

    def test_5_rebase_helper_absent_ledger_is_friendly(self):
        """Registre absent : message clair, rc 0, aucune trace d'erreur."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            self.assertFalse((repo / rn.LEDGER_RELPATH).exists())
            rc = rn.rebase_helper(apply=False, repo=repo)
            self.assertEqual(rc, 0)


if __name__ == "__main__":
    unittest.main()
