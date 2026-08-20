"""Recette du selecteur du stale-sweep (#11862) : le bloc python HEREDOC livré
dans ``pr-gate-stale-sweep.yml`` est exec-é VERBATIM (aucune copie), via le
seam ``SWEEP_RUNS_FILE`` que le workflow lui-meme porte.

Pourquoi exec-er le bloc livré plutot qu'extraire le selecteur dans un module :
le sweep tourne toutes les 20 minutes sur un depot dont le probleme mesure EST
la penurie de runners, et son en-tete documente l'absence DELIBEREE de checkout
(~40 s economises par passage). Extraire le selecteur en script imposerait un
checkout a chaque passage pour la seule testabilite. La contrepartie d'un
selecteur inline est le drift copie/test -- ce fichier le ferme en testant
l'original, pas une transcription.

Incident fondateur du genre (#11656) : un organe accepte au merge sans avoir
jamais cree un seul job. Le heredoc n'est pas exec-able par CI seul ; ce test
est la seule execution hors-run du selecteur livré.

Acceptance #11862 (3 cas) + regressions du comportement historique :
  1. gate ``cancelled`` seul -> relance (comportement NOUVEAU ; ce test echoue
     sur le RED sans ``cancelled``, c'est le test de falsification) ;
  2. gate ``cancelled`` + autre check rouge -> abstention ;
  3. autre check ``cancelled`` supersede par un vert -> relance (le pliage
     tient, ``cancelled`` n'est PAS passe dans GREEN) ;
  + gate failure/autres verts -> relance (comportement d'origine preserve) ;
  + gate rouge + autre check inacheve -> abstention ;
  + deux legs de gate (failure ancien + success recent) -> relance
    (AND-not-latest-wins, la regression du 2026-08-17) ;
  + autre check dont le PLUS RECENT est ``cancelled`` -> abstention ( jamais
    maquiller en vert).
"""

import json
import os
import re
import subprocess

import pytest
import yaml

REPO_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(__file__), os.pardir, os.pardir)
)
WORKFLOW = os.path.join(
    REPO_ROOT, ".github", "workflows", "pr-gate-stale-sweep.yml"
)


def _extract_selector() -> str:
    """Sortir le bloc python du heredoc, depuis l'arbre YAML (pas le texte brut :
    ce qui est teste est ce que GitHub rend, convention test_workflow_expression_escapes)."""
    with open(WORKFLOW, encoding="utf-8") as f:
        doc = yaml.safe_load(f)
    run = doc["jobs"]["sweep"]["steps"][0]["run"]
    m = re.search(r"python - <<'PY'[^\n]*\n(.*?)\nPY\n", run, re.S)
    assert m, "heredoc python introuvable dans pr-gate-stale-sweep.yml"
    return m.group(1)


SELECTOR = _extract_selector()


def _run_selector(tmp_path, rows):
    """Exec le selecteur livré sur des lignes de fixtures, capture stdout."""
    fixture = tmp_path / "runs.jsonl"
    fixture.write_text(
        "".join(json.dumps(r) + "\n" for r in rows), encoding="utf-8"
    )
    env = dict(os.environ, SWEEP_RUNS_FILE=str(fixture))
    out = subprocess.run(
        ["python", "-c", SELECTOR],
        capture_output=True, text=True, encoding="utf-8", env=env, cwd=tmp_path,
    )
    assert out.returncode == 0, out.stderr
    return out.stdout


def _pr(number, checks, sha="deadbeef", fork=False):
    return {
        "number": number,
        "sha": sha,
        "fork": fork,
        "checks": [
            {"name": n, "status": s, "conclusion": c, "started_at": t}
            for (n, s, c, t) in checks
        ],
    }


GATE_OK = ("PR gate", "completed", "success", "2026-01-01T10:00:00Z")
GATE_CANCELLED = ("PR gate", "completed", "cancelled", "2026-01-01T10:00:00Z")
GATE_FAIL = ("PR gate", "completed", "failure", "2026-01-01T10:00:00Z")
OTHER_GREEN = ("Hermes review", "completed", "success", "2026-01-01T10:05:00Z")
OTHER_RED = ("Hermes review", "completed", "failure", "2026-01-01T10:05:00Z")
OTHER_QUEUED = ("Hermes review", "queued", None, "2026-01-01T10:05:00Z")


def test_gate_cancelled_alone_is_candidate(tmp_path):
    """Acceptance 1 : un gate cancelled, tous les autres verts -> relance.

    Falsification : echoue sur le RED d'avant (sans 'cancelled'), la PR reste
    alors bloquee sans rien de rouge -- le defaut #11862 mot pour mot.
    """
    out = _run_selector(tmp_path, [_pr(101, [GATE_CANCELLED, OTHER_GREEN])])
    assert out.strip() == "101 deadbeef false"


def test_gate_cancelled_with_other_red_abstains(tmp_path):
    """Acceptance 2 : autre check rouge -> le gate n'est pas (seul) fautif."""
    out = _run_selector(tmp_path, [_pr(102, [GATE_CANCELLED, OTHER_RED])])
    assert out.strip() == ""


def test_other_cancelled_superseded_by_green_still_candidate(tmp_path):
    """Acceptance 3 : cancelled supersede par un vert sur un AUTRE check ->
    le pliage tient, la relance a lieu (cancelled n'a pas fui dans GREEN)."""
    cancelled_old = ("Hermes review", "completed", "cancelled", "2026-01-01T09:00:00Z")
    green_new = ("Hermes review", "completed", "success", "2026-01-01T11:00:00Z")
    out = _run_selector(tmp_path, [_pr(103, [GATE_FAIL, cancelled_old, green_new])])
    assert out.strip() == "103 deadbeef false"


def test_gate_failure_others_green_candidate(tmp_path):
    """Regression : le comportement d'origine (failure/timeout/action_required)
    reste candidat."""
    out = _run_selector(tmp_path, [_pr(104, [GATE_FAIL, OTHER_GREEN])])
    assert out.strip() == "104 deadbeef false"


def test_no_gate_leg_skipped(tmp_path):
    out = _run_selector(tmp_path, [_pr(105, [OTHER_GREEN])])
    assert out.strip() == ""


def test_gate_red_with_incomplete_other_skipped(tmp_path):
    """Un autre check inacheve : le gate attend peut-etre legitiment."""
    out = _run_selector(tmp_path, [_pr(106, [GATE_FAIL, OTHER_QUEUED])])
    assert out.strip() == ""


def test_two_gate_legs_and_not_latest_wins(tmp_path):
    """Regression 2026-08-17 (#11532) : deux legs de gate, failure ancienne +
    success recente -> candidat quand meme (AND sur les required, pas
    latest-wins)."""
    gate_success_new = ("PR gate", "completed", "success", "2026-01-01T12:00:00Z")
    out = _run_selector(tmp_path, [_pr(107, [GATE_FAIL, gate_success_new, OTHER_GREEN])])
    assert out.strip() == "107 deadbeef false"


def test_other_latest_cancelled_never_greenwashed(tmp_path):
    """Asymetrie : un cancelled TOUT RECENT sur un autre check n'est pas vert ->
    abstention (une interruption reelle ne se maquille pas)."""
    cancelled_new = ("Hermes review", "completed", "cancelled", "2026-01-01T11:00:00Z")
    out = _run_selector(tmp_path, [_pr(108, [GATE_FAIL, cancelled_new])])
    assert out.strip() == ""


def test_selector_has_cancelled_in_red_not_green(tmp_path):
    """Garde structurl : le correctif est bien asymetrique -- 'cancelled' dans
    RED, absent de GREEN. Ce test echoue si quelqu'un symetrise par inadvertance."""
    assert "cancelled" in SELECTOR
    m = re.search(r'RED = \{[^}]*\}', SELECTOR)
    assert m and "cancelled" in m.group(0)
    m = re.search(r'GREEN = \{[^}]*\}', SELECTOR)
    assert m and "cancelled" not in m.group(0)
