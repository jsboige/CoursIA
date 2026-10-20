#!/usr/bin/env python3
"""Tests de la capacite ``run --stdin-file`` et de la migration lean_server.

Fichier dedie (issue #15666 case 1, mode stdin) : ``test_lean_exec.py`` est
tenu par la PR #21302 (po-2023), ``test_lean_exec_run_cwd.py`` par #21317 --
les tests de la capacite stdin vivent ici, sans collision.

Deux bouts de la migration, un seul contrat :

1. **Organe** — ``run --stdin-file <f>`` : le fichier est branche sur
   l'entree standard de l'enfant confine (handle fichier, pas pipe : meme
   famille que la capture par fichiers de la mesure case 1), le result JSON
   porte ``stdin_file``, un fichier illisible = refus nomme (125), et le
   chemin sans drapeau ne change pas (pas de cle ``stdin_file``).
2. **Module** — ``lean_server`` ne construit PLUS d'invocation lake directe
   (garde : l'entree allowlist est retiree, 6 -> 5 fichiers en dette) : le
   build passe par ``_organ_run(["lake", "build", "-R", ...])``, les deux
   sites ``lake env lean --stdin`` passent par un snippet ecrit en fichier
   puis ``stdin_file=``. Les contrats #18432 (timeout = verdict-less
   UNKNOWN sauf diagnostic pre-kill) et #8681 (rc != 0 ne valide JAMAIS
   l'integrite) sont verifies sur les codes du client : -1/-2/0/non-zero.

Les tests organe tournent en sous-processus reel (pattern ``_run``/``_last``
de ``test_lean_exec_run_cwd.py``, state dir isole, WSL neutralise) avec des
enfants Python — ils ne dependent pas du toolchain Lean. Les tests module
mockent ``lean_server._organ_run`` : ils eprouvent le ROUTAGE, pas lake.

L'import nu ``from lean_server import LeanVerifier`` est lui-meme un test :
c'est tout ce que fait le gate CI lean-axiom sur un runner sans toolchain
(#8722) — la migration ne doit pas y trainer de dependance.

Execution :
    pytest scripts/lean/tests/test_lean_exec_stdin.py -v
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from unittest import mock

import pytest

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))
import lean_exec as le  # noqa: E402

_AGENT_TESTS = _HERE.parents[2] / (
    "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests")
sys.path.insert(0, str(_AGENT_TESTS))
import lean_server  # noqa: E402
from lean_server import LeanVerifier  # noqa: E402  (import nu = contrat gate CI)

LEAN_EXEC = str(_HERE.parent / "lean_exec.py")
PY = sys.executable

NEUTRAL_RESOURCE_GATE = {
    "LEAN_EXEC_MEM_PER_JOB_MB": "1",
    "LEAN_EXEC_COMMIT_PER_JOB_MB": "1",
    "LEAN_EXEC_MIN_FREE_GB": "0",
}

# L'enfant echo : renvoie sur stdout ce qu'il lit sur stdin, majuscule.
_ECHO_CHILD = (
    "import sys; sys.stdout.write(sys.stdin.read().upper())"
)


def _env(state: Path, **extra) -> dict:
    env = os.environ.copy()
    env["LEAN_EXEC_STATE_DIR"] = str(state)
    env["LEAN_EXEC_WSL"] = "off"
    env.update(NEUTRAL_RESOURCE_GATE)
    env.update({k: str(v) for k, v in extra.items()})
    return env


def _run(state: Path, args: list[str], cwd: Path | None = None,
         timeout: float = 90) -> subprocess.CompletedProcess:
    return subprocess.run(
        [PY, LEAN_EXEC, *args], env=_env(state),
        cwd=str(cwd) if cwd else None,
        capture_output=True, text=True, timeout=timeout,
        encoding="utf-8", errors="replace",
    )


def _last(state: Path) -> dict:
    return json.loads((state / "last_run.json").read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# 1. Organe : --stdin-file
# ---------------------------------------------------------------------------

def test_stdin_file_feeds_child_and_is_recorded(tmp_path):
    """L'enfant confine lit le fichier branche sur son entree standard."""
    state = tmp_path / "state"; state.mkdir()
    stdin_f = tmp_path / "snippet.txt"
    stdin_f.write_text("hello confined stdin\n", encoding="utf-8")
    out_f = tmp_path / "child.out"
    r = _run(state, [
        "run", "--json", "--timeout", "30",
        "--cwd", str(tmp_path),
        "--stdin-file", str(stdin_f),
        "--stdout-file", str(out_f),
        "--", PY, "-c", _ECHO_CHILD,
    ])
    assert r.returncode == 0, r.stderr
    verdict = json.loads(r.stdout[r.stdout.index("{"):])
    assert verdict["status"] == "ok"
    assert out_f.read_text(encoding="utf-8") == "HELLO CONFINED STDIN\n"
    assert _last(state)["stdin_file"] == str(stdin_f)


def test_stdin_file_missing_is_a_named_refusal(tmp_path):
    """Un --stdin-file illisible = refus 125 nomme, pas un spawn bancal."""
    state = tmp_path / "state"; state.mkdir()
    r = _run(state, [
        "run", "--json", "--timeout", "30",
        "--cwd", str(tmp_path),
        "--stdin-file", str(tmp_path / "absent.lean"),
        "--", PY, "-c", "print('never')",
    ])
    assert r.returncode == le.EXIT_REFUSED
    verdict = json.loads(r.stdout[r.stdout.index("{"):])
    assert verdict["status"] == "refused"
    assert "stdin_file illisible" in verdict["reason"]
    # Le run n'a jamais tourne : pas de code enfant.
    assert verdict["child_exit_code"] is None


def test_run_without_stdin_file_unchanged(tmp_path):
    """Sans le drapeau, pas de cle ``stdin_file`` — la voie #21317 ne bouge."""
    state = tmp_path / "state"; state.mkdir()
    r = _run(state, [
        "run", "--json", "--timeout", "30",
        "--cwd", str(tmp_path),
        "--", PY, "-c", "print('ok')",
    ])
    assert r.returncode == 0, r.stderr
    assert "stdin_file" not in _last(state)


# ---------------------------------------------------------------------------
# 2. Module : routage lean_server (mock de _organ_run — le routage, pas lake)
# ---------------------------------------------------------------------------

def _make_project(tmp_path: Path, module_rel: str = "T/A.lean") -> Path:
    """Projet factice avec un module d'une declaration."""
    project = tmp_path / "proj"
    (project / "T").mkdir(parents=True)
    (project / module_rel).write_text(
        "theorem ta : True := trivial\n", encoding="utf-8")
    return project


class _Capture:
    """Mock de lean_server._organ_run qui capture l'appel et rend un rc fixe."""

    def __init__(self, rc=0, out="", err=""):
        self.calls = []
        self.rc, self.out, self.err = rc, out, err

    def __call__(self, project, cmd_args, timeout, stdin_file=None):
        snippet = None
        if stdin_file is not None:
            snippet = Path(stdin_file).read_text(encoding="utf-8")
        self.calls.append({
            "project": project, "cmd": list(cmd_args), "timeout": timeout,
            "stdin_file": stdin_file, "snippet": snippet,
        })
        return self.rc, self.out, self.err


def test_build_site_routes_payload_to_organ(tmp_path):
    cap = _Capture(rc=0, out="info: le build est propre", err="")
    v = LeanVerifier(project_dir=str(tmp_path))
    with mock.patch.object(lean_server, "_organ_run", cap):
        res = v._run_lake_build(Path(tmp_path), "T/A.lean")
    assert len(cap.calls) == 1
    call = cap.calls[0]
    assert call["cmd"] == ["lake", "build", "-R", "T.A"]
    assert call["stdin_file"] is None
    # Le budget #18432 traverse : LEAN_LAKE_BUILD_TIMEOUT_S -> --timeout.
    assert call["timeout"] == int(lean_server._lake_build_timeout_s())
    assert res["success"] is True
    assert res["lake_cmd"] == "lean_exec"


def test_build_site_timeout_semantics_18432(tmp_path):
    """-1 : diagnostic pre-kill = CONFIRMED (wall_clock_exhausted) ; sinon
    verdict-less UNKNOWN (wall_clock_timeout). Contrat #18432 preserve."""
    v = LeanVerifier(project_dir=str(tmp_path))
    with mock.patch.object(
            lean_server, "_organ_run",
            _Capture(rc=-1, out="", err="")):
        res = v._run_lake_build(Path(tmp_path), "T/A.lean")
    assert res["success"] is False
    assert res.get("wall_clock_timeout") is True
    assert res.get("wall_clock_exhausted") is not True
    with mock.patch.object(
            lean_server, "_organ_run",
            _Capture(rc=-1, out="", err="error: T/A.lean:1:0: unknown")):
        res = v._run_lake_build(Path(tmp_path), "T/A.lean")
    assert res["success"] is False
    assert res.get("wall_clock_exhausted") is True
    assert res.get("wall_clock_timeout") is not True


def test_build_site_refused_is_visible_failure(tmp_path):
    cap = _Capture(rc=-2, out="", err="cap sature (2/2)")
    v = LeanVerifier(project_dir=str(tmp_path))
    with mock.patch.object(lean_server, "_organ_run", cap):
        res = v._run_lake_build(Path(tmp_path), "T/A.lean")
    assert res["success"] is False
    assert "lean_exec refused" in res["errors"]
    assert "cap sature" in res["errors"]


def test_check_axioms_routes_snippet_stdin(tmp_path):
    project = _make_project(tmp_path)
    cap = _Capture(rc=0, out="'T.ta' depends on axioms: [propext]", err="")
    v = LeanVerifier(project_dir=str(project))
    with mock.patch.object(lean_server, "_organ_run", cap):
        res = v.check_axioms("T.A")
    assert len(cap.calls) == 1
    call = cap.calls[0]
    assert call["cmd"] == ["lake", "env", "lean", "--stdin"]
    assert call["stdin_file"] is not None
    assert call["snippet"].startswith("import T.A")
    assert "#print axioms" in call["snippet"]
    assert res["success"] is True
    assert res["axioms"] == ["propext"]


def test_check_axioms_dead_build_never_validates(tmp_path):
    """#8681 : rc != 0 ne peut JAMAIS valider l'integrite."""
    project = _make_project(tmp_path)
    cap = _Capture(rc=1, out="whatever", err="crash")
    v = LeanVerifier(project_dir=str(project))
    with mock.patch.object(lean_server, "_organ_run", cap):
        res = v.check_axioms("T.A")
    assert res["success"] is False
    assert res["error"] == "build_failed_returncode_1"


def test_search_lean_routes_snippet_stdin(tmp_path):
    project = _make_project(tmp_path)
    cap = _Capture(rc=0, out="", err="")
    v = LeanVerifier(project_dir=str(project))
    with mock.patch.object(lean_server, "_organ_run", cap):
        res = v.search_lean("T.A", "True", tactic="exact?")
    assert len(cap.calls) == 1
    call = cap.calls[0]
    assert call["cmd"] == ["lake", "env", "lean", "--stdin"]
    assert call["timeout"] == 120
    assert call["snippet"] == (
        "import T.A\nexample : True := by\n  exact?\n")
    assert res["success"] is False  # aucune suggestion dans la sortie vide


def test_lean_server_is_organ_driver(tmp_path):
    """La garde confined-sink exige une reference REELLE a l'organe dans le
    fichier : le finder local doit resoudre l'organe depuis le depot."""
    organ = lean_server._find_lean_exec()
    assert organ.name == "lean_exec.py"
    assert organ.exists()
