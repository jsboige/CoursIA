#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Tests pour le detecteur de jobs `python` nu (#17444).

Le contrat de l'organe est tenu par 3 controles :
- un **rouge fondateur** : un cas fabrique qui doit etre attrape ;
- des **contreles faux-positif** : des cas qui ne doivent PAS etre
  attrapes (parce qu'ils sont couverts par `setup-python`, par
  `python3`, ou par l'exemption Windows) ;
- un **verdict stable** : sur le repo, le nombre de defauts est mesure
  comme une metrique (et non un boolean) -- la regression est signalee
  par delta.

L'organe est appele en sous-process pour isoler le test de l'etat du
working tree (les fixtures vivent dans un repertoire temporaire).
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
ORG_SCRIPT = REPO_ROOT / "scripts" / "ci" / "detect_python_nu_jobs.py"


def _run_detector(
    workflows_dir: Path,
    *,
    as_json: bool = False,
    repo_root: Path | None = None,
) -> subprocess.CompletedProcess:
    """Execute l'organe sur un repertoire de workflows isole."""
    # Si repo_root n'est pas fourni, on prend le parent de .github/
    # (le layout standard). Pour les tests, on le passera explicitement
    # a chaque fois.
    if repo_root is None:
        repo_root = workflows_dir.parent.parent
    args = [
        sys.executable,
        str(ORG_SCRIPT),
        "--workflows-dir",
        str(workflows_dir.relative_to(repo_root)),
        "--repo-root",
        str(repo_root),
    ]
    if as_json:
        args.append("--json")
    return subprocess.run(
        args,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(repo_root),
        check=False,
    )


def _write_workflow(workflows_dir: Path, name: str, content: str) -> Path:
    workflows_dir.mkdir(parents=True, exist_ok=True)
    p = workflows_dir / name
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


class DetectPythonNuJobsTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.mkdtemp(prefix="detect_python_nu_")
        self.tmp_dir = Path(self._tmp)
        self.wf_dir = self.tmp_dir / ".github" / "workflows"
        # repo_root = parent de .github/, ce que l'organe attend
        self.repo_root = self.tmp_dir

    def tearDown(self) -> None:
        shutil.rmtree(self._tmp, ignore_errors=True)

    # -------- Rouge fondateur : le cas fabrique DOIT etre attrape --------

    def test_fabrique_self_hosted_python_nu_is_caught(self) -> None:
        """Un job self-hosted avec `python` nu sans setup-python est un
        defaut -- c'est le cas fondateur de la classe #17444."""
        _write_workflow(
            self.wf_dir,
            "fabrique.yml",
            """\
            name: Fabrique
            on: [push]
            jobs:
              sweep:
                runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
                steps:
                  - run: python scripts/fabrique.py
            """,
        )
        result = _run_detector(self.wf_dir, repo_root=self.repo_root)
        self.assertEqual(
            result.returncode,
            1,
            msg=f"defaut attendu, stdout={result.stdout!r} stderr={result.stderr!r}",
        )
        self.assertIn("fabrique.yml sweep", result.stdout)
        self.assertIn("python", result.stdout)

    def test_fabrique_github_hosted_python_nu_is_caught(self) -> None:
        """Un job sur runner GitHub-hosted avec `python` nu sans setup-python
        est aussi un defaut : le cluster peut router vers self-hosted, le
        job est vulnerable."""
        _write_workflow(
            self.wf_dir,
            "fabrique-gh.yml",
            """\
            name: Fabrique GH
            on: [push]
            jobs:
              sweep:
                runs-on: ubuntu-latest
                steps:
                  - run: python scripts/fabrique.py
            """,
        )
        result = _run_detector(self.wf_dir, repo_root=self.repo_root)
        self.assertEqual(
            result.returncode,
            1,
            msg=f"defaut attendu, stdout={result.stdout!r} stderr={result.stderr!r}",
        )
        self.assertIn("fabrique-gh.yml sweep", result.stdout)

    # -------- Controles faux-positif --------

    def test_python3_nu_is_not_caught(self) -> None:
        """`python3` n'est pas `python` nu : un job qui utilise `python3`
        sans setup-python n'est PAS un defaut (la substitution est deja
        faite)."""
        _write_workflow(
            self.wf_dir,
            "py3.yml",
            """\
            name: Py3
            on: [push]
            jobs:
              sweep:
                runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
                steps:
                  - run: python3 scripts/fabrique.py
            """,
        )
        result = _run_detector(self.wf_dir, repo_root=self.repo_root)
        self.assertEqual(
            result.returncode,
            0,
            msg=f"defaut non attendu, stdout={result.stdout!r} stderr={result.stderr!r}",
        )

    def test_setup_python_covers_python_nu(self) -> None:
        """Un job qui utilise `python` nu ET `actions/setup-python` n'est
        PAS un defaut : setup-python rend `python` disponible."""
        _write_workflow(
            self.wf_dir,
            "setup.yml",
            """\
            name: Setup
            on: [push]
            jobs:
              sweep:
                runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
                steps:
                  - uses: actions/setup-python@v5
                    with:
                      python-version: '3.11'
                  - run: python scripts/fabrique.py
            """,
        )
        result = _run_detector(self.wf_dir, repo_root=self.repo_root)
        self.assertEqual(
            result.returncode,
            0,
            msg=f"defaut non attendu, stdout={result.stdout!r} stderr={result.stderr!r}",
        )

    def test_windows_dnx_tests_exempted_named(self) -> None:
        """Le job `windows-dotnet-tests` du workflow
        `windows-self-hosted-tests.yml` est exempté nommement. Un
        refactor qui elargirait l'exemption par regle generale (par
        exemple, "tout job Windows") echouerait ce test."""
        _write_workflow(
            self.wf_dir,
            "windows-self-hosted-tests.yml",
            """\
            name: Windows Self-Hosted Tests
            on: [workflow_dispatch]
            jobs:
              windows-dotnet-tests:
                runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
                steps:
                  - run: python scripts/fabrique.py
              other-windows-job:
                runs-on: [self-hosted, coursia-ephemeral, coursia-fast-guards]
                steps:
                  - run: python scripts/fabrique.py
            """,
        )
        result = _run_detector(self.wf_dir, repo_root=self.repo_root)
        # Le job exempté n'est PAS attrapé, mais `other-windows-job` (qui
        # n'est pas dans l'exemption nommée) EST attrapé.
        self.assertEqual(
            result.returncode,
            1,
            msg=f"defaut attendu sur other-windows-job, stdout={result.stdout!r}",
        )
        self.assertNotIn("windows-dotnet-tests", result.stdout)
        self.assertIn("other-windows-job", result.stdout)

    def test_comment_lines_ignored(self) -> None:
        """Un commentaire qui mentionne `python` n'est pas un appel : la
        detection regarde `run:`, pas la prose. La fixture evite les
        chaines contenant `python` (le detecteur ne distingue pas un
        appel d'une mention textuelle dans un echo)."""
        _write_workflow(
            self.wf_dir,
            "comments.yml",
            """\
            name: Comments
            on: [push]
            jobs:
              sweep:
                runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
                steps:
                  - run: |
                      # ce job utilise python et python3
                      echo "nothing here"
            """,
        )
        result = _run_detector(self.wf_dir, repo_root=self.repo_root)
        self.assertEqual(
            result.returncode,
            0,
            msg=f"defaut non attendu, stdout={result.stdout!r} stderr={result.stderr!r}",
        )

    def test_shebang_alone_is_not_an_invocation(self) -> None:
        """Un shebang `#!/usr/bin/env python` seul n'est pas un appel
        (la longueur apres `python` doit etre >= 2). Cas du shebang
        d'un script inline."""
        _write_workflow(
            self.wf_dir,
            "shebang.yml",
            """\
            name: Shebang
            on: [push]
            jobs:
              sweep:
                runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
                steps:
                  - run: |
                      #!/usr/bin/env python
                      print("hi")
            """,
        )
        result = _run_detector(self.wf_dir, repo_root=self.repo_root)
        # La deuxieme ligne (`print`) n'est pas un appel python -- c'est
        # un appel de fonction. La detection regarde `python` nu, pas
        # `print`. Donc le job n'est PAS attrapé.
        self.assertEqual(
            result.returncode,
            0,
            msg=f"defaut non attendu, stdout={result.stdout!r} stderr={result.stderr!r}",
        )

    # -------- Verdict stable : la sortie JSON est exploitable --------

    def test_json_output_is_well_formed(self) -> None:
        """L'option --json produit un objet avec `ok`, `defects`, `broken`."""
        _write_workflow(
            self.wf_dir,
            "fabrique.yml",
            """\
            name: Fabrique
            on: [push]
            jobs:
              sweep:
                runs-on: [self-hosted, coursia-ephemeral, coursia-linux]
                steps:
                  - run: python scripts/fabrique.py
            """,
        )
        result = _run_detector(self.wf_dir, as_json=True, repo_root=self.repo_root)
        self.assertEqual(result.returncode, 1)
        data = json.loads(result.stdout)
        self.assertIn("ok", data)
        self.assertIn("defects", data)
        self.assertIn("broken", data)
        self.assertFalse(data["ok"])
        self.assertEqual(len(data["defects"]), 1)
        d = data["defects"][0]
        self.assertEqual(d["workflow"], ".github/workflows/fabrique.yml")
        self.assertEqual(d["job"], "sweep")
        self.assertIn("steps_with_python", d)
        self.assertGreaterEqual(len(d["steps_with_python"]), 1)

    def test_clean_repo_yields_no_defects_json(self) -> None:
        """Un repertoire de workflows vide (ou avec que des workflows
        propres) rend `ok: true`."""
        _write_workflow(
            self.wf_dir,
            "clean.yml",
            """\
            name: Clean
            on: [push]
            jobs:
              ok:
                runs-on: ubuntu-latest
                steps:
                  - run: echo "no python"
                  - run: python3 -c "print('hi')"
            """,
        )
        result = _run_detector(self.wf_dir, as_json=True, repo_root=self.repo_root)
        self.assertEqual(result.returncode, 0)
        data = json.loads(result.stdout)
        self.assertTrue(data["ok"])
        self.assertEqual(data["defects"], [])


if __name__ == "__main__":
    unittest.main()
