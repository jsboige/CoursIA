#!/usr/bin/env python3
"""Le transport `gh` du lecteur est BORNE — #21436.

Sur Windows, `subprocess.run(capture_output=True, timeout=T)` ne rend pas
forcement la main a l'echeance : a l'expiration il tue l'enfant, puis appelle
`communicate()` une seconde fois sans `timeout` (Lib/subprocess.py, `run()`,
branche `_mswindows`), ce qui joint les threads lecteurs avec `join(None)`.
Un descendant qui a herite du handle du pipe suffit a rendre cette jointure
infinie.

Mesure fondatrice (2026-11-15, ce siege) : le tapis `--belt` a
`--belt-time-budget 240` sous `timeout 400` a ete tue `rc=124` sans servir un
seul grain, pile `faulthandler` montrant le thread principal bloque dans
`_gh_graphql` -> `communicate` -> `join`. Trois occurrences le meme jour.

Ce fichier epingle les deux moities du correctif :

1. `_run_bounded` (transport par FICHIERS, sans thread lecteur) rend vraiment
   la main dans sa borne, meme quand un descendant tient le handle ;
2. les fonctions de transport du lecteur l'emploient — une reintroduction de
   `subprocess.run(..., timeout=...)` dans l'une d'elles rougit ici, parce que
   le defaut est invisible a l'execution (il ne se manifeste qu'au moment ou
   `gh` traine, c'est-a-dire jamais dans un test qui va vite).

Run: python -m pytest scripts/tests/test_check_lane_claim_bounded_gh.py
"""
import ast
import subprocess
import sys
import time
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402

READER = Path(__file__).resolve().parents[1] / "check_lane_claim.py"

# Le descendant herite du stdout du parent : c'est lui qui garde le handle du
# pipe ouvert, et donc lui qui rend `join(None)` infini sur l'ancien transport.
# Sa duree ne doit PAS etre plus courte que la tolerance de l'assertion, sinon
# le test ne mord plus : avec `time.sleep(10)`, l'ancien transport rendait la
# main en ~10,1 s, ce que `elapsed < 20` acceptait -- le cas passait donc
# aussi sur le transport fautif (review ai-01 du 2026-11-16).
_GRANDCHILD_SCRIPT = (
    "import subprocess, sys, time\n"
    "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])\n"
    "print('parent-output', flush=True)\n"
    "time.sleep(30)\n"
)


def test_run_bounded_captures_stdout_and_stderr():
    """Le transport rend la sortie comme `subprocess.run(capture_output=True)`."""
    proc = clc._run_bounded(
        [sys.executable, "-c",
         "import sys; print('out-line'); print('err-line', file=sys.stderr)"],
        timeout=30,
    )
    assert proc.returncode == 0
    assert "out-line" in proc.stdout
    assert "err-line" in proc.stderr


def test_run_bounded_enforces_timeout_despite_inheriting_descendant():
    """La borne tient meme quand un descendant garde le handle du pipe.

    C'est la reproduction de la classe : sur l'ancien transport
    (`subprocess.run(capture_output=True, timeout=...)`), ce cas ne rendait
    jamais la main — le test aurait ete tue par le harnais au lieu d'echouer.
    """
    started = time.monotonic()
    with pytest.raises(subprocess.TimeoutExpired):
        clc._run_bounded(
            [sys.executable, "-c", _GRANDCHILD_SCRIPT],
            timeout=2,
        )
    elapsed = time.monotonic() - started
    # Marge large : on epingle l'ordre de grandeur (la borne), pas la
    # precision d'un ordonnanceur charge.
    assert elapsed < 20, (
        f"le transport a rendu la main apres {elapsed:.1f}s pour un timeout "
        f"de 2s -- la borne n'est plus reelle"
    )
    assert elapsed >= 1.5, f"timeout rendu trop tot ({elapsed:.2f}s)"


def test_run_bounded_keeps_simulated_output(monkeypatch):
    """Le seam de simulation survit : un `run` simule rend son texte."""
    def fake_run(cmd, **kwargs):  # noqa: ANN001 - signature de subprocess.run
        return subprocess.CompletedProcess(cmd, 0, "simule-out", "simule-err")

    monkeypatch.setattr(clc.subprocess, "run", fake_run)
    proc = clc._run_bounded(["gh", "api", "graphql"], timeout=5)
    assert proc.stdout == "simule-out"
    assert proc.stderr == "simule-err"


def _calls_subprocess_run(func: ast.FunctionDef) -> list[int]:
    lines = []
    for node in ast.walk(func):
        if not isinstance(node, ast.Call):
            continue
        target = node.func
        if (isinstance(target, ast.Attribute) and target.attr == "run"
                and isinstance(target.value, ast.Name)
                and target.value.id == "subprocess"):
            lines.append(node.lineno)
    return lines


def test_gh_transports_use_the_bounded_runner():
    """Les trois transports du lecteur passent par `_run_bounded`.

    Lecture statique volontaire : le defaut est invisible a l'execution
    ordinaire (il ne se declenche qu'au moment ou `gh` traine). Une
    reintroduction de `subprocess.run(timeout=...)` dans l'un des trois rougit
    ici au lieu d'attendre le prochain tapis tue.
    """
    tree = ast.parse(READER.read_text(encoding="utf-8"))
    wanted = {"_gh_repo_name_with_owner", "_gh_graphql", "_gh_pr_files_rest"}
    found = {}
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name in wanted:
            found[node.name] = _calls_subprocess_run(node)
    assert set(found) == wanted, f"fonctions introuvables: {wanted - set(found)}"
    assert found == {name: [] for name in wanted}, (
        f"transport non borne reintroduit: "
        f"{ {k: v for k, v in found.items() if v} }"
    )


def test_bounded_runner_is_the_same_shape_as_the_picker_one():
    """Les deux transports du depot rendent la meme forme.

    Le picker avait recu ce correctif le 2026-10-24 ; le lecteur non, d'ou
    #21436. On epingle la parite de FORME (CompletedProcess + TimeoutExpired),
    pas l'identite des implementations.
    """
    proc = clc._run_bounded(
        [sys.executable, "-c", "print('x')"], timeout=30)
    assert isinstance(proc, subprocess.CompletedProcess)
    assert proc.args == [sys.executable, "-c", "print('x')"]