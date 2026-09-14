#!/usr/bin/env python3
"""Tests du garde de casse canonique des suffixes de noyau (#15489, defaut 3).

Deux pieges sont tendus a ce garde, et chaque test en couvre un :

1. **Crier a tort.** La mesure de l'arbre donne 114 `-Csharp` contre 16 `-CSharp` :
   si le garde rougissait sur tout `-Csharp` il condamnerait la majorite du
   corpus et serait desactive dans la semaine. Les negatifs -- casse heritee hors
   serie adoptee, convention minuscule assumee (`-python` + noyau python),
   suffixe absent, `-Lean` -- sont donc aussi importants que les positifs.

2. **Se taire a tort.** Un garde qui ne denombre pas ce qu'il a regarde rend le
   meme verdict sur "tout est conforme" et sur "je n'ai rien lu". Chaque test
   assert donc un ETAT nomme dans la sortie, pas seulement un code retour.

Les scenarios tournent contre un **vrai depot git temporaire** : le defaut
d'origine (#5081) etait un angle mort de la vue `git diff` -- un `git mv` vers
une casse non canonique sort en `R100`, invisible sous `--diff-filter=A`. Le
dernier test exige donc d'abord que Git classe bien le commit en rename, faute de
quoi il ne reproduirait plus la condition du defaut et passerait au vert a vide.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

_SCRIPT = (Path(__file__).resolve().parent.parent / "notebook_tools"
           / "check_kernel_suffix_canon.py")

ADOPTED = "MyIA.AI.Notebooks/Search/Applications"


def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(["git"] + list(args), cwd=str(repo), capture_output=True,
                       text=True, encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise AssertionError("git %s -> %s"
                             % (" ".join(args), r.stderr.strip()[:200]))
    return r.stdout


def _notebook(kernelspec: str | None = "python3", with_kernelspec: bool = True) -> str:
    """Notebook minimal valide, kernelspec absent ou nomme."""
    meta: dict = {}
    if with_kernelspec:
        meta["kernelspec"] = {"name": kernelspec, "display_name": kernelspec or "",
                              "language": "python"}
    return json.dumps({"cells": [], "metadata": meta,
                       "nbformat": 4, "nbformat_minor": 5}, indent=1) + "\n"


def _write(repo: Path, rel: str, body: str) -> None:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(body, encoding="utf-8")


def _write_config(repo: Path, adopted_globs: list[str],
                  exceptions: list[dict] | None = None) -> Path:
    cfg = repo / "kernel_suffix_canon.test.json"
    cfg.write_text(json.dumps({
        "adopted": [{"path_glob": g, "note": "test"} for g in adopted_globs],
        "exceptions": exceptions or [],
    }, indent=1), encoding="utf-8")
    return cfg


def _init_repo(repo: Path) -> str:
    _git(repo, "init", "-q")
    _git(repo, "config", "user.email", "test@example.invalid")
    _git(repo, "config", "user.name", "test")
    _git(repo, "config", "diff.renames", "true")
    _write(repo, ADOPTED + "/CSP/App-5-Timetabling-CSharp.ipynb",
           _notebook(".net-csharp"))
    _write(repo, "MyIA.AI.Notebooks/GameTheory/GameTheory-04-Nash.ipynb",
           _notebook(".net-csharp"))
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "base")
    return _git(repo, "rev-parse", "HEAD").strip()


def _run_guard(repo: Path, cfg: Path, base: str | None = None) -> subprocess.CompletedProcess:
    args = [sys.executable, str(_SCRIPT), "--config", str(cfg)]
    if base is None:
        args += ["--scan-all"]
    else:
        args += ["--base", base, "--head", "HEAD"]
    return subprocess.run(args, cwd=str(repo), capture_output=True, text=True,
                          encoding="utf-8", errors="replace")


class TestCaseCanonInAdoptedSeries(unittest.TestCase):
    """Acceptance #15489 defaut 3 : la casse canonique est imposee la ou la serie
    a adopte, et seulement la."""

    def test_positive_new_lowercase_csharp_in_adopted_series_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            _write(repo, ADOPTED + "/CSP/App-21-Foo-Csharp.ipynb",
                   _notebook(".net-csharp"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "new notebook, casse hors canon")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 1,
                             "un nouveau -Csharp dans une serie adoptee doit rougir\n"
                             + r.stdout + r.stderr)
            self.assertIn("case_deviation", r.stdout)
            self.assertIn("App-21-Foo-Csharp.ipynb", r.stdout)
            self.assertIn("attendue CSharp", r.stdout)

    def test_negative_canonical_case_in_adopted_series_stays_green(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            _write(repo, ADOPTED + "/CSP/App-22-Bar-CSharp.ipynb",
                   _notebook(".net-csharp"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "new notebook, casse canonique")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("canonical=1", r.stdout)

    def test_negative_legacy_case_outside_adopted_series_stays_green(self):
        """Le corpus herite ne doit pas etre condamne : c'est la raison d'etre du
        perimetre delta, et la lecon du garde de zero-pad (#12586)."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            _write(repo, "MyIA.AI.Notebooks/GameTheory/GameTheory-28-Foo-Csharp.ipynb",
                   _notebook(".net-csharp"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "nouveau -Csharp dans une serie non adoptee")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("case_deviation_unadopted=1", r.stdout)

    def test_negative_assumed_lowercase_python_series_stays_green(self):
        """Forme Fort-Boyard : `-python` minuscule comme convention assumee d'une
        serie entiere (paire `fort-boyard-python` / `fort-boyard-csharp`)."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            _write(repo, "MyIA.AI.Notebooks/GenAI/Fort-Boyard/fort-boyard-python.ipynb",
                   _notebook("python3"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "convention minuscule assumee")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("case_deviation_unadopted=1", r.stdout)


class TestKernelCoherence(unittest.TestCase):
    """Le suffixe dit quel moteur execute le notebook. S'il ment, c'est un defaut
    factuel -- independant de toute adoption de casse."""

    def test_positive_python_suffix_on_csharp_kernel_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            # Hors serie adoptee : la violation vient de la coherence, pas de la
            # casse. Le controle n'a de valeur que si le perimetre est neutre ici.
            _write(repo, "MyIA.AI.Notebooks/GenAI/Workbook-Template-Python.ipynb",
                   _notebook(".net-csharp"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "suffixe en desaccord avec le noyau")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
            self.assertIn("kernel_mismatch", r.stdout)
            self.assertIn(".net-csharp", r.stdout)

    def test_negative_csharp_suffix_on_csharp_kernel_stays_green(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [])
            _write(repo, "MyIA.AI.Notebooks/GenAI/Notebook-CSharp.ipynb",
                   _notebook(".net-csharp"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "coherent")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("canonical=1", r.stdout)

    def test_lean_suffix_is_not_treated_as_a_kernel_suffix(self):
        """Contre-epreuve d'une exclusion MESUREE : `-Lean` marque le contenu, pas
        le moteur (le pendant Lean porte `-Native` ; 2 des 4 `-Lean` tournent sous
        `python3`). Si quelqu'un remet `-lean` dans KERNEL_LANG_SUFFIXES, ce test
        rougit et le renvoie a la mesure."""
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [])
            _write(repo, "MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16b-Foo-Lean.ipynb",
                   _notebook("python3"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "suffixe de contenu, pas de noyau")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("no_kernel_suffix=1", r.stdout)
            self.assertNotIn("kernel_mismatch", r.stdout)


class TestDistinctStates(unittest.TestCase):
    """'rien trouve' et 'rien regarde' ne doivent jamais partager la meme sortie."""

    def test_no_suffix_is_reported_not_silent(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [])
            _write(repo, "MyIA.AI.Notebooks/GameTheory/GameTheory-29-Plain.ipynb",
                   _notebook("python3"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "rendu unique, sans suffixe de noyau")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("no_kernel_suffix=1", r.stdout)
            self.assertIn("notebooks examines : 1", r.stdout)

    def test_missing_kernelspec_is_a_distinct_state(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [])
            _write(repo, "MyIA.AI.Notebooks/GameTheory/GameTheory-30-NoKs-CSharp.ipynb",
                   _notebook(with_kernelspec=False))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "metadata sans kernelspec")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0,
                             "un kernelspec absent est INVERIFIABLE, pas fautif\n"
                             + r.stdout + r.stderr)
            self.assertIn("kernelspec_missing=1", r.stdout)

    def test_exception_suppresses_a_violation(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            rel = ADOPTED + "/CSP/App-23-Excused-Csharp.ipynb"
            cfg = _write_config(repo, [ADOPTED + "/**"],
                                [{"path": rel, "reason": "derive documentee"}])
            _write(repo, rel, _notebook(".net-csharp"))
            _git(repo, "add", "-A")
            _git(repo, "commit", "-qm", "derive declaree")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("exception=1", r.stdout)

    def test_denominator_is_printed_when_nothing_was_added(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("notebooks examines : 0", r.stdout)

    def test_scan_all_reports_the_whole_tree(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            r = _run_guard(repo, cfg, None)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("notebooks examines : 2", r.stdout)


class TestRenameAwareness(unittest.TestCase):
    """Le defaut d'origine est un angle mort de la vue `git diff` : un rename sort
    en `R100` et `--diff-filter=A` l'ecarte. Le garde lit en `--no-renames`."""

    def test_rename_to_noncanonical_case_in_adopted_series_reddens(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            base = _init_repo(repo)
            cfg = _write_config(repo, [ADOPTED + "/**"])
            _git(repo, "mv",
                 ADOPTED + "/CSP/App-5-Timetabling-CSharp.ipynb",
                 ADOPTED + "/CSP/App-5-Timetabling-Csharp.ipynb")
            _git(repo, "commit", "-qm", "rename vers une casse hors canon")

            # Sans rename classe par Git, le test ne reproduirait plus le defaut
            # et passerait au vert sur un garde aveugle.
            status = _git(repo, "diff", "--name-status", base, "HEAD")
            self.assertIn("R", status,
                          "Git ne classe pas ce commit en rename : le controle "
                          "positif ne reproduit plus la condition du defaut.")

            r = _run_guard(repo, cfg, base)
            self.assertEqual(r.returncode, 1,
                             "un rename vers une casse non canonique dans une "
                             "serie adoptee doit rougir\n" + r.stdout + r.stderr)
            self.assertIn("case_deviation", r.stdout)
            self.assertIn("App-5-Timetabling-Csharp.ipynb", r.stdout)


if __name__ == "__main__":
    unittest.main()
