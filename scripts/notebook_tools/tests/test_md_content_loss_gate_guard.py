#!/usr/bin/env python3
"""Garde anti-auto-disarmement du gate CI `md-content-loss-gate.yml` (#8656).

Reserve ai-01 c.28 sur #8656 : le gate bouclait `detect_md_content_loss.py`
sur chaque notebook change, traitait `rc=2` (notebook illisible) en simple
`::warning`, et incrementait `checked` AVANT l'appel. Si le detecteur etait
cassee OU la ref git `BASE` manquante, CHAQUE notebook rendait rc=2, le gate
n'analysait rien, et sortait en `::notice ... no content loss` vert — la classe
de defaut meme que ce gate est cense attraper (silencieusement neutralise).

Le garde ajoute : compter `rc=2` a part (`unreadable`), et **fail loud** si
`unreadable == checked > 0` (rien n'a ete analyse -> pas de quitus).

Ces tests extraient le VRAI bloc de boucle du workflow YAML (pas une replique
qui deriverait), l'executent en bash avec un detecteur mock qui rend des rc
controles, et assertent les 4 scenarios :

    1. TOUS illisibles (rc=2 x2)       -> exit 1 (garde declenche, anti-disarmement)
    2. tous propres (rc=0 x2)          -> exit 0 (clean bill, legit)
    3. une vraie perte (rc=1 + rc=0)   -> exit 1 (le cas nominal du gate reste attrape)
    4. partiellement illisible (2 + 0) -> exit 0 (un notebook illisible parmi des
                                           bons NE fait PAS false-tripper le garde :
                                           les lisibles ont ete verifies)

Run:
    pytest scripts/notebook_tools/tests/test_md_content_loss_gate_guard.py
"""
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]  # tests/ -> notebook_tools/ -> scripts/ -> repo
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "md-content-loss-gate.yml"


def _bash_python() -> str:
    """Le nom python invocable DEPUIS le bash du systeme (`python3` sur WSL2,
    `python` sur CI Ubuntu). Le mock etant stdlib-only, l'un ou l'autre le tourne.
    On probe au runtime plutot que d'hardcoder : ce test tourne sur CI Linux
    (`python`) ET en dev Windows (`python3` via WSL -- `python` n'y existe pas).
    """
    r = subprocess.run(
        ["bash", "-c", "command -v python3 || command -v python"],
        capture_output=True, text=True,
    )
    return r.stdout.strip() or "python3"

# Mock detecteur : exit code pilote par `rc_map.json` (JSON {basename: rc}) lu
# depuis le cwd. On passe le rc-map par FICHIER (pas par env) : sous WSL2, bash
# n'herite PAS des vars d'env arbitraires du parent Windows (frontiere WSLENV),
# donc un MOCK_RC_MAP en env n'atteindrait jamais le mock -> il rendrait 0 et le
# garde ne se declencherait jamais (faux-negatif silencieux). Le filesystem, lui,
# est partage.
MOCK_DETECTOR = '''\
import json, sys
from pathlib import Path
try:
    m = json.loads(Path("rc_map.json").read_text(encoding="utf-8"))
except Exception:
    m = {}
nb = Path(sys.argv[-1]).name
sys.exit(int(m.get(nb, m.get("*", 0))))
'''


def _extract_loop_block() -> str:
    """Extrait le bloc bash du workflow entre `fail=0` et le notice final.

    On execute le VRAI code du workflow (zero derive) : si un futur edit retire
    le garde ou change la boucle, ce test execute la nouvelle logique. Le replace
    branche un detecteur mock pour controler les rc.
    """
    wf = WORKFLOW.read_text(encoding="utf-8")
    start = wf.index("          fail=0")
    end = wf.index('          echo "::notice title=Markdown content-loss gate::Checked')
    block = wf[start:end]
    return block.replace(
        "python scripts/notebook_tools/detect_md_content_loss.py",
        'python "{mock}"',  # branche le mock a l'execution
    )


def _run_gate(nb_basenames: list[str], rc_map: dict, tmp_path: Path) -> tuple[int, str]:
    """Execute le bloc du workflow sur des notebooks factices avec un rc_map.

    Retourne (exit_code, combined_output).

    Implemente comme un FICHIER bash execute en chemin RELATIF depuis `tmp_path`
    (cwd). Double raison sur ce Windows + Git-bash :
      (1) `bash -s` (stdin) y parse mal `elif` (quirk confirme firsthand : un
          if/elif/fi minimal echoue via stdin, passe en fichier) ;
      (2) un path absolu Windows (C:\\...) est mange par la traduction MSYS ->
          "No such file". Un nom relatif + cwd evite les deux pieges.
    Tous les chemins internes (notebooks, mock, summary) sont relatifs a tmp_path.
    """
    # Notebooks factices (existence seule -- le mock ne les lit pas).
    for name in nb_basenames:
        (tmp_path / name).write_text("{}", encoding="utf-8")
    (tmp_path / "mock_detector.py").write_text(MOCK_DETECTOR, encoding="utf-8")
    # rc-map en FICHIER (passe la frontiere WSL qu'un env var ne franchit pas).
    (tmp_path / "rc_map.json").write_text(
        __import__("json").dumps(rc_map), encoding="utf-8"
    )

    block = _extract_loop_block().replace('python "{mock}"', f"{_bash_python()} mock_detector.py")
    changed = "\n".join(nb_basenames)
    script = (
        "#!/usr/bin/env bash\n"
        f'BASE="mock-base"\n'
        f"CHANGED=$'{changed}'\n"
        f'GITHUB_STEP_SUMMARY="summary.md"\n'
        f"{block}\n"
        # Apres le bloc : ni le garde ni le fail-check n'ont exit -> succes (mirroir
        # du notice + exit 0 implicite du workflow).
        'echo "GATE_RESULT: pass"\n'
    )
    (tmp_path / "gate.sh").write_text(script, encoding="utf-8", newline="\n")

    proc = subprocess.run(
        ["bash", "gate.sh"],
        capture_output=True, text=True, cwd=str(tmp_path),
    )
    return proc.returncode, proc.stdout + proc.stderr


# ---------------------------------------------------------------------------
# Scenario 1 : tous illisibles -> le garde fail loud (anti-disarmement)
# ---------------------------------------------------------------------------

def test_guard_fires_when_all_notebooks_unreadable(tmp_path):
    """Si CHAQUE notebook rend rc=2, le gate n'a rien analyse -> exit 1.

    C'est le coeur du garde : un detecteur casse ou une ref manquante ne peut
    pas obtenir un quitus vert a l'aveugle. Avant le fix, ce scenario rendait
    exit 0 avec un notice "no content loss" trompeur.
    """
    rc, out = _run_gate(["a.ipynb", "b.ipynb"], {"a.ipynb": 2, "b.ipynb": 2}, tmp_path)
    assert rc == 1, f"Tous illisibles aurait du fail loud. out={out!r}"
    assert "analyzed NOTHING" in out or "unreadable" in out.lower(), (
        f"Le message d'erreur du garde manque. out={out!r}"
    )


def test_guard_fires_on_single_unreadable_notebook(tmp_path):
    """Une PR qui change 1 seul notebook illisible (rc=2) -> exit 1.

    Le gate devait certifier CE notebook et n'a pas pu : pas de quitus. Edge
    case important (checked=1, unreadable=1 == checked).
    """
    rc, _out = _run_gate(["solo.ipynb"], {"solo.ipynb": 2}, tmp_path)
    assert rc == 1, "1 notebook illisible -> le gate n'a rien certifie -> fail."


# ---------------------------------------------------------------------------
# Scenario 2 : tous propres -> pass
# ---------------------------------------------------------------------------

def test_gate_passes_when_all_clean(tmp_path):
    rc, out = _run_gate(["a.ipynb", "b.ipynb"], {"a.ipynb": 0, "b.ipynb": 0}, tmp_path)
    assert rc == 0, f"Tous propres -> pass. out={out!r}"
    assert "GATE_RESULT: pass" in out


# ---------------------------------------------------------------------------
# Scenario 3 : vraie perte de contenu -> le cas nominal reste attrape
# ---------------------------------------------------------------------------

def test_gate_fails_on_real_content_loss(tmp_path):
    """Un notebook en rc=1 (perte reelle) declenche toujours exit 1.

    Le garde anti-disarmement ne doit PAS masquer le cas nominal du gate.
    """
    rc, out = _run_gate(["good.ipynb", "lost.ipynb"], {"good.ipynb": 0, "lost.ipynb": 1}, tmp_path)
    assert rc == 1, f"Perte de contenu reelle -> fail. out={out!r}"


# ---------------------------------------------------------------------------
# Scenario 4 : partiellement illisible -> PAS de false-trip
# ---------------------------------------------------------------------------

def test_guard_does_not_false_trip_on_partial_unreadable(tmp_path):
    """1 notebook illisible parmi des bons -> exit 0 (les lisibles ont ete verifies).

    Le garde ne fail QUE quand RIEN n'a ete analyse (unreadable == checked).
    Un seul notebook illisible par ailleurs ne doit pas bloquer la PR.
    """
    rc, out = _run_gate(
        ["ok.ipynb", "bad.ipynb", "ok2.ipynb"],
        {"ok.ipynb": 0, "bad.ipynb": 2, "ok2.ipynb": 0},
        tmp_path,
    )
    assert rc == 0, f"Partiellement illisible -> pass (les lisibles verifies). out={out!r}"


# ---------------------------------------------------------------------------
# Anti-regression structurelle : le garde est bien present dans le workflow
# ---------------------------------------------------------------------------

def test_workflow_contains_guard_markers():
    """Sanity : si un futur edit retire le garde du YAML, ce test casse (signal).

    On ne depend pas du test d'extraction ci-dessus seul : un grep des marqueurs
    cles rend le retrait du garde visible meme si la boucle est refactorisee.
    """
    wf = WORKFLOW.read_text(encoding="utf-8")
    assert "unreadable=$((unreadable + 1))" in wf, "increment du compteur unreadable absent"
    assert 'unreadable" -eq "$checked"' in wf, "condition du garde (unreadable == checked) absente"
    assert "analyzed NOTHING" in wf, "message d'erreur du garde absent"
