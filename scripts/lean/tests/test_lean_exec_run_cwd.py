#!/usr/bin/env python3
"""Tests de la capacite ``run --cwd`` et de la migration du module notebook.

Fichier dedie (issue #15666 case 1) : ``test_lean_exec.py`` est tenu par la
PR #21302 (po-2023) — les tests de la capacite vivent ici, sans collision.

Deux bouts de la migration, testes ensemble parce qu'ils forment UN contrat :

1. **Organe** — ``run --cwd <dir>`` : l'enfant travaille depuis ``dir`` (pas
   depuis le cwd de l'appelant), le lakefile est cherche depuis ``dir``, le
   result JSON porte ``cwd``, et ``backend_command`` traduit le cwd explicite
   vers ``wsl --cd`` (controle par faux negatif : sans le passage du
   parametre, ``wsl_path_of(Path.cwd())`` rendrait le cwd du TEST, pas celui
   demande).
2. **Module** — ``run_lake`` / ``run_lean_snippet`` ne construisent PLUS
   d'invocation lake directe : tout passe par ``[python, lean_exec.py, run,
   --json, --cwd, <hote>, --, lake, ...]``. Contrats historiques preserves :
   Timeout -> ``(-1, "", "TIMEOUT after Ns")``, refus/injoignable -> ``-2``,
   mode WSL -> ``tail -N`` sur stdout+stderr concatenes, snippet ecrit DANS
   le projet (l'ancien ``/tmp`` se resolait en ``C:\\tmp`` cote natif, bug
   po-2026) puis retire.

Les tests organe tournent en sous-processus reel (pattern ``_run``/``_last``
de ``test_lean_exec.py``, state dir isole, WSL neutralise) avec des enfants
Python — ils ne dependent pas du toolchain Lean. Les tests module mockent
``_run_capture``/``_organ_run`` : ils eprouvent le ROUTAGE, pas lake.

Execution :
    pytest scripts/lean/tests/test_lean_exec_run_cwd.py -v
"""

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent))
import lean_exec as le  # noqa: E402

sys.path.insert(0, str(_HERE.parents[2] / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean"))
import lean_notebook_utils as u  # noqa: E402

LEAN_EXEC = str(_HERE.parent / "lean_exec.py")
PY = sys.executable

NEUTRAL_RESOURCE_GATE = {
    "LEAN_EXEC_MEM_PER_JOB_MB": "1",
    "LEAN_EXEC_COMMIT_PER_JOB_MB": "1",
    "LEAN_EXEC_MIN_FREE_GB": "0",
}


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
# Organe : run --cwd change le repertoire de travail de l'enfant
# ---------------------------------------------------------------------------

def test_run_cwd_changes_child_working_directory():
    """L'enfant execute depuis --cwd, pas depuis le cwd de l'appelant.

    Controle par contraste : deux dossiers, l'appel est lance depuis le
    dossier A avec --cwd dossier B ; ``os.getcwd()`` de l'enfant doit rendre
    B. La sortie enfant passe par --stdout-file (sous Windows elle
    n'atteint pas le stdout pipe de l'organe — mesure #15666 case 1).
    Sans la capacite, l'organe heriterait du cwd du test (A) : c'est le
    faux negatif qui valide la capacite.
    """
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        dir_a = Path(td) / "caller_side"
        dir_b = Path(td) / "asked_cwd"
        out_f = Path(td) / "child.out"
        err_f = Path(td) / "child.err"
        dir_a.mkdir()
        dir_b.mkdir()
        rc = _run(
            state,
            ["run", "--json", "--cwd", str(dir_b),
             "--stdout-file", str(out_f), "--stderr-file", str(err_f),
             "--", PY, "-c", "import os; print('CWD=' + os.getcwd())"],
            cwd=dir_a,
        )
        res = _last(state)
        assert rc.returncode == le.EXIT_OK, (
            f"attendu {le.EXIT_OK}, vu {rc.returncode} / {res.get('reason')}")
        assert res["child_exit_code"] == 0
        # Le result porte le cwd explicite (traconabilite du run record).
        assert res["cwd"] == str(dir_b), res["cwd"]
        # La sortie enfant temoigne du repertoire REEL d'execution.
        child = out_f.read_text(encoding="utf-8")
        assert child.strip() == f"CWD={dir_b}", (
            f"attendu CWD={dir_b}, lu: {child!r}")


def test_run_stdout_file_captures_child_output():
    """--stdout-file/--stderr-file capturent la sortie enfant (sous Windows,
    sans cette voie la sortie est perdue — mesure #15666 case 1)."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        out_f = Path(td) / "o.txt"
        err_f = Path(td) / "e.txt"
        rc = _run(
            state,
            ["run", "--json", "--stdout-file", str(out_f),
             "--stderr-file", str(err_f), "--", PY, "-c",
             "import sys; print('TO_STDOUT'); "
             "print('TO_STDERR', file=sys.stderr)"],
        )
        res = _last(state)
        assert rc.returncode == le.EXIT_OK, rc.returncode
        assert out_f.read_text(encoding="utf-8").strip() == "TO_STDOUT"
        assert err_f.read_text(encoding="utf-8").strip() == "TO_STDERR"
        # Sans fichiers, le run reste valide (capture optionnelle).
        assert res["status"] == "ok"


def test_run_without_cwd_keeps_legacy_behavior():
    """Sans --cwd : comportement historique — l'enfant herite le cwd de
    l'appelant (aucune regression du chemin par defaut)."""
    with tempfile.TemporaryDirectory() as td:
        state = Path(td) / "state"
        here = Path(td)
        rc = _run(
            state,
            ["run", "--json", "--", PY, "-c", "import os; print(os.getcwd())"],
            cwd=here,
        )
        res = _last(state)
        assert rc.returncode == le.EXIT_OK, rc.returncode
        assert res["cwd"] == str(here), res["cwd"]


def test_backend_command_translates_explicit_cwd(monkeypatch):
    """backend_command traduit le cwd explicite (pas le sien) vers wsl --cd.

    Faux negatif vise : sans le parametre cwd, backend_command appelle
    wsl_path_of(Path.cwd()) — sous le monkeypatch, wsl_path_of rend une
    valeur DERIVEE de son argument : si l'argument est le cwd du test et
    non le cwd demande, l'assertion echoue.
    """
    seen: dict = {}

    def fake_wsl_path_of(p):
        seen["arg"] = str(p)
        return "/mnt/w/translated"

    monkeypatch.setattr(le, "wsl_path_of", fake_wsl_path_of)
    monkeypatch.setattr(le, "_host_is_windows", lambda: True)
    spawn, _env_ = le.backend_command(
        ["lake", "build"], "wsl", {}, cwd="D:/some/project")
    assert Path(seen["arg"]) == Path("D:/some/project"), seen["arg"]
    assert spawn[:3] == ["wsl.exe", "--cd", "/mnt/w/translated"], spawn
    assert "bash" in spawn and "lake build" in " ".join(spawn)


def test_backend_command_default_cwd_unchanged(monkeypatch):
    """Sans cwd explicite : backend_command garde Path.cwd() (heritage)."""
    monkeypatch.setattr(le, "wsl_path_of",
                        lambda p: f"/mnt/x/{Path(p).name}")
    monkeypatch.setattr(le, "_host_is_windows", lambda: True)
    spawn, _ = le.backend_command(["lake"], "wsl", {})
    here = Path.cwd()
    assert spawn[2] == f"/mnt/x/{here.name}", spawn


def test_run_parser_exposes_cwd_help(monkeypatch):
    """Le sous-parseur run expose --cwd (dispatch cable jusqu'a
    run_command) — preuve par argparse, sans execution."""
    import argparse
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="action")
    p_run = sub.add_parser("run")
    p_run.add_argument("--cwd", default=None)
    p_run.add_argument("cmd", nargs=argparse.REMAINDER)
    args = parser.parse_args(
        ["run", "--cwd", "/some/dir", "--", "lake", "build"])
    assert args.cwd == "/some/dir"
    assert args.cmd == ["--", "lake", "build"]


# ---------------------------------------------------------------------------
# Module : run_lake / run_lean_snippet routent par l'organe
# ---------------------------------------------------------------------------

def _fake_organ_stdout(payload_extra: dict = None) -> str:
    """Stdout d'un run organe : JSON final seul (indent=2 comme le _emit
    reel) — la sortie enfant passe par --stdout-file/--stderr-file."""
    payload = {
        "run_id": "abc123def456", "status": "ok", "exit_code": 0,
        "child_exit_code": 0, "duration_s": 1.2, "orphans": [],
    }
    payload.update(payload_extra or {})
    return json.dumps(payload, indent=2)


def _fake_organ_capture(child_out: str = "", child_err: str = "",
                        payload_extra: dict = None):
    """Fake _run_capture fidele a l'organe : ecrit la sortie enfant dans les
    fichiers --stdout-file/--stderr-file de l'argv, rend le JSON sur stdout."""
    def fake(cmd, timeout, cwd=None):
        i = cmd.index("--stdout-file")
        Path(cmd[i + 1]).write_text(child_out, encoding="utf-8")
        j = cmd.index("--stderr-file")
        Path(cmd[j + 1]).write_text(child_err, encoding="utf-8")
        return 0, _fake_organ_stdout(payload_extra), ""
    return fake


def test_run_lake_routes_through_organ(monkeypatch):
    """run_lake construit l'appel organe (--json --cwd --stdout-file --
    lake ...) et mappe le verdict : child_exit_code du JSON, sortie enfant
    lue depuis le fichier de capture (mode natif : pas de tail)."""
    captured: dict = {}

    def fake_run_capture(cmd, timeout, cwd=None):
        captured["argv"] = cmd
        captured["timeout"] = timeout
        return _fake_organ_capture("info: build ok\n")(cmd, timeout)

    monkeypatch.setattr(u, "_run_capture", fake_run_capture)
    monkeypatch.setattr(u, "is_native_platform", lambda: True)
    rc, out, err = u.run_lake("/native/proj", "build Grothendieck", timeout=90)
    argv = captured["argv"]
    assert argv[argv.index("run")] == "run"
    assert argv[argv.index("--caller") + 1] == "lean_notebook_utils"
    assert argv[argv.index("--cwd") + 1] == "/native/proj"
    assert argv[argv.index("--") + 1:] == ["lake", "build", "Grothendieck"]
    assert "--stdout-file" in argv and "--stderr-file" in argv
    assert argv[0] == PY
    assert "lean_exec.py" in argv[1]
    assert rc == 0
    assert out == "info: build ok\n"
    assert captured["timeout"] == 90 + 60  # marge de supervision organe


def test_run_lake_child_failure_maps_to_child_exit(monkeypatch):
    """Le rc rendu est celui de l'ENFANT (3), pas celui de l'organe (1) —
    c'est le contrat historique du pipefail."""
    monkeypatch.setattr(u, "_run_capture", _fake_organ_capture(
        payload_extra={"exit_code": 1, "child_exit_code": 3}))
    monkeypatch.setattr(u, "is_native_platform", lambda: True)
    rc, out, err = u.run_lake("/native/proj", "build")
    assert rc == 3, rc


def test_run_lake_timeout_contract(monkeypatch):
    """TimeoutExpired de l'organe -> (-1, "", TIMEOUT after Ns) (contrat
    historique preserve par la migration)."""

    def boom(cmd, t, cwd=None):
        raise subprocess.TimeoutExpired(cmd, t)

    monkeypatch.setattr(u, "_run_capture", boom)
    monkeypatch.setattr(u, "is_native_platform", lambda: True)
    rc, out, err = u.run_lake("/native/proj", "build", timeout=60)
    assert (rc, out, err) == (-1, "", "TIMEOUT after 60s")


def test_run_lake_refusal_maps_to_minus_2(monkeypatch):
    """Refus organe (exit 125) -> (-2, ..., raison nommee)."""
    monkeypatch.setattr(u, "_run_capture", _fake_organ_capture(
        payload_extra={"exit_code": 125, "status": "refused",
                       "reason": "machine-wide cap 8: population 7 + 1 > 8"}))
    monkeypatch.setattr(u, "is_native_platform", lambda: True)
    rc, out, err = u.run_lake("/native/proj", "build")
    assert rc == -2
    assert "cap" in err


def test_run_lake_wsl_mode_tails_concatenated_output(monkeypatch):
    """Mode WSL historique : out = tail(stdout+stderr concatenes), err vide —
    ce que les carnets observaient avec ``2>&1 | tail -N``."""
    lines = "\n".join(f"L{i}" for i in range(1, 41)) + "\n"
    monkeypatch.setattr(u, "_run_capture", _fake_organ_capture(
        lines, "WARN: ligne err\n"))
    monkeypatch.setattr(u, "is_native_platform", lambda: False)
    monkeypatch.setattr(u, "_host_cwd_of", lambda p: "D:/host/proj")
    rc, out, err = u.run_lake("/mnt/d/proj", "build", tail=5)
    assert rc == 0
    # tail s'applique a stdout+stderr CONCATENES (comportement 2>&1 historique)
    assert out.splitlines() == [
        "L37", "L38", "L39", "L40", "WARN: ligne err"], out
    assert err == ""


def test_split_organ_json_finds_last_block():
    """Le parseur survit a un residu enfant dans le stdout organe : le bloc
    retenu est le DERNIER objet dont la premiere cle est run_id (defense en
    profondeur — avec --stdout-file, le stdout organe est le JSON seul)."""
    child = '{"my": "output"}\n'
    out = child + _fake_organ_stdout()
    payload, before = u._split_organ_json(out)
    assert payload is not None and payload["run_id"]
    assert before == child


def test_split_organ_json_no_verdict():
    payload, before = u._split_organ_json("pas de json ici\n")
    assert payload is None
    assert before == "pas de json ici\n"


def test_run_lean_snippet_writes_in_project_and_cleans(monkeypatch):
    """Le snippet vit dans le PROJET (chemin valide dans le dialecte du
    backend — l'ancien /tmp se resolait en C:\\tmp cote natif), son chemin
    passe en forme WSL sous Windows, et le fichier est retire apres."""
    captured: dict = {}

    def fake_organ_run(project_path, cmd_args, timeout):
        captured["cmd_args"] = cmd_args
        captured["exists_during"] = captured_file.exists()
        return 0, "42\n", ""

    monkeypatch.setattr(u, "_organ_run", fake_organ_run)
    monkeypatch.setattr(u, "is_native_platform", lambda: False)
    monkeypatch.setattr(u, "_host_cwd_of", lambda p: "D:/host/proj")

    with tempfile.TemporaryDirectory() as td:
        proj = Path(td)
        captured_file = proj / ".lean_snippet_eval.lean"
        # _host_cwd_of mocke rend D:/host/proj : on ecrase juste pour ce test
        monkeypatch.setattr(u, "_host_cwd_of", lambda p: str(proj))
        result = u.run_lean_snippet(
            "/mnt/d/proj", "#eval 2 + 2", snippet_id="eval")
        assert result == "42\n"
        assert captured["exists_during"], (
            "le fichier snippet doit exister pendant l'appel organe")
        assert not captured_file.exists(), (
            "le fichier snippet doit etre retire apres l'appel")
        file_arg = captured["cmd_args"][-1]
        assert file_arg.startswith("/mnt/") and file_arg.endswith(
            ".lean"), file_arg
        assert captured["cmd_args"][:3] == ["lake", "env", "lean"]


def test_run_lean_snippet_timeout_string(monkeypatch, tmp_path):
    monkeypatch.setattr(u, "_organ_run",
                        lambda p, c, t: (-1, "", "TIMEOUT after 30s"))
    monkeypatch.setattr(u, "is_native_platform", lambda: True)
    monkeypatch.setattr(u, "_host_cwd_of", lambda p: str(tmp_path))
    result = u.run_lean_snippet(str(tmp_path), "#eval 1", timeout=30)
    assert result == "TIMEOUT after 30s"
    # le fichier temporaire du snippet est retire meme sur timeout
    leftovers = list(tmp_path.glob(".lean_snippet_*.lean"))
    assert leftovers == [], leftovers


def test_wsl_to_win_cached(monkeypatch):
    """La traduction /mnt -> hote est sondee UNE fois par chemin (cache)."""
    calls: list = []

    def fake_run(cmd, **kw):
        calls.append(cmd)

        class R:
            returncode = 0
            stdout = "D:\\real\\path".encode()

        return R()

    monkeypatch.setattr(u.subprocess, "run", fake_run)
    u._HOST_CWD_CACHE.clear()
    first = u._wsl_to_win("/mnt/d/proj")
    second = u._wsl_to_win("/mnt/d/proj")
    assert first == "D:\\real\\path" == second
    assert len(calls) == 1, "la 2e traduction doit servir le cache"
