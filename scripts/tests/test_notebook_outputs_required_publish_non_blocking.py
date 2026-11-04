#!/usr/bin/env python3
"""#24441 -- la publication de la section advisory ne doit pas rougir la gate.

Le defaut mesure (constate firsthand par l'adjoint sur la tete de la PR,
puis confirme a la source) : dans ``notebook-outputs-required.yml``, l'etape
qui publie (ou retire) la section collante est dans le **job bloquant**
``validate`` ; elle porte ``set -e`` et appelle ``advisory_sticky.py`` sans
garde. Une erreur d'API (quota, 5xx, PR fermee entre-temps) sortait donc en
rc != 0 et **rougissait le check** -- alors que le contrat ecrit dans le meme
fichier (:206-208) dit l'inverse : « L'echec de cette ecriture ne doit JAMAIS
rougir la gate (lecon notebook-execution-required : un step cosmique ne
rougit jamais une execution-verdict step) ».

Ce fichier epingle l'invariant :

1. l'etape de publication porte ``continue-on-error: true`` ;
2. l'etape de VERDIT (« Run outputs-required check ») reste **bloquante** --
   le correctif ne neutralise pas le verdict outputs reel ;
3. **echec simule** : le bloc ``run:`` de publication est reellement execute
   avec un ``advisory_sticky`` factice qui echoue, et l'echec est mesure
   (rc != 0) puis projete sur le job selon la regle GitHub -- le job reste
   VERT avec le drapeau, il serait ROUGE sans lui (contrefactuel mesure).

Le point 3 est le coeur du correctif : sans lui, un drapeau pose a l'aveugle
serait un correctif non prouve.

Executable deux facons :
    py scripts/tests/test_notebook_outputs_required_publish_non_blocking.py
    npx pytest scripts/tests/test_notebook_outputs_required_publish_non_blocking.py
"""

from __future__ import annotations

import copy
import os
import subprocess
import sys
from pathlib import Path

import pytest
import yaml

from ._bash_resolution import resolve_bash

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "notebook-outputs-required.yml"

JOB = "validate"
VERDICT_STEP = "Run outputs-required check"
PUBLISH_STEP = "Publish (or retract) the outputs-required advisory section"

BASH = resolve_bash()

pytestmark = pytest.mark.skipif(
    BASH is None,
    reason="l'echec simule a besoin d'un bash sain (#17201)",
)


# --------------------------------------------------------------------------
# Lecture du workflow
# --------------------------------------------------------------------------


def _doc() -> dict:
    with open(WORKFLOW, encoding="utf-8") as f:
        return yaml.safe_load(f)


def _steps() -> list:
    return _doc()["jobs"][JOB]["steps"]


def _step(name: str) -> dict:
    for step in _steps():
        if step.get("name") == name:
            return step
    raise AssertionError(f"etape absente du job {JOB} : {name!r}")


# --------------------------------------------------------------------------
# Modele de la regle GitHub Actions
# --------------------------------------------------------------------------


def _job_verdict(steps: list, failed_step_names: set[str]) -> str:
    """Verdict du job selon la regle GitHub Actions.

    Un step en echec fait echouer le job SAUF s'il porte
    ``continue-on-error: true`` (le step reste rouge dans l'UI, le job
    reste vert). C'est le modele de la plateforme, applique tel quel au
    workflow reel.
    """
    for step in steps:
        if step.get("name") in failed_step_names:
            if step.get("continue-on-error") is not True:
                return "failure"
    return "success"


# --------------------------------------------------------------------------
# 1. L'etape de publication est non bloquante
# --------------------------------------------------------------------------


def test_publish_step_is_non_blocking():
    """L'etape cosmetique porte `continue-on-error: true`."""
    assert _step(PUBLISH_STEP).get("continue-on-error") is True


def test_job_carries_no_job_level_continue_on_error():
    """Le job lui-meme ne doit pas etre neutralise : le garde des
    `#24441` porte sur l'etape, pas sur le job entier (sinon le verdict
    outputs reel ne bloquerait plus rien)."""
    assert _doc()["jobs"][JOB].get("continue-on-error") is not True


# --------------------------------------------------------------------------
# 2. Le verdict outputs reste bloquant
# --------------------------------------------------------------------------


def test_verdict_step_stays_blocking():
    """Le pas de la correction : le verdict sortie/sorties reste porte par
    le check-run ROUGE de l'etape de validation."""
    verdict = _step(VERDICT_STEP)
    assert verdict.get("continue-on-error") is not True
    # L'etape doit toujours echouer sur un verdict negatif.
    assert "exit 1" in verdict["run"]


def test_publish_step_still_runs_after_a_verdict_failure():
    """`if: always()` : un verdict ROUGE doit toujours pouvoir publier son
    recapitulatif. Rendre l'etape non bloquante ne doit pas la rendre
    muette."""
    assert "always()" in str(_step(PUBLISH_STEP).get("if", ""))


# --------------------------------------------------------------------------
# 3. Echec simule de la publication
# --------------------------------------------------------------------------


def _fake_sticky(tmp_path: Path) -> Path:
    """Un `advisory_sticky.py` factice qui echoue comme le ferait une
    erreur d'API (quota, 5xx) : rc != 0, message sur stderr."""
    fake = tmp_path / "advisory_sticky_fake.py"
    fake.write_text(
        "import sys\n"
        "sys.stderr.write('API rate limit exceeded for installation.\\n')\n"
        "sys.exit(1)\n",
        encoding="utf-8",
    )
    return fake


def _run_publish_block(tmp_path: Path, state: str) -> subprocess.CompletedProcess:
    """Execute le bloc `run:` reellement livre, avec un `advisory_sticky`
    factice en echec.

    Deux substitutions, minimes et cibles : les deux chemins ABSOLUS
    `/tmp/...` sont replaces par des chemins du `tmp_path` (le `/tmp` de la
    machine n'est pas le meme sous Git Bash et sous le runner Linux), et
    l'appel `python3 scripts/ci/advisory_sticky.py` est remplace par
    l'interpreteur du test + le faux. Le reste du bloc -- dont `set -e` et
    l'absence de `|| true` autour de l'appel -- est execute tel quel.
    """
    run = _step(PUBLISH_STEP)["run"]
    state_file = tmp_path / "outputs_required_state"
    state_file.write_text(state, encoding="utf-8")
    summary_file = tmp_path / "outputs_required_summary.md"
    summary_file.write_text("recapitulatif\n", encoding="utf-8")
    fake = _fake_sticky(tmp_path)

    script = (
        run.replace("/tmp/outputs_required_state", state_file.as_posix())
        .replace("/tmp/outputs_required_summary.md", summary_file.as_posix())
        .replace(
            "python3 scripts/ci/advisory_sticky.py",
            f'"{Path(sys.executable).as_posix()}" "{fake.as_posix()}"',
        )
    )
    script_path = tmp_path / "publish.sh"
    script_path.write_text(script, encoding="utf-8")

    env = os.environ.copy()
    env["PR"] = "24441"
    return subprocess.run(
        [BASH, script_path.as_posix()],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        env=env,
        cwd=str(tmp_path),
    )


@pytest.mark.parametrize("state", ["advisory", "success"])
def test_simulated_publish_failure_is_real(tmp_path: Path, state: str):
    """Le defaut est REEL, pas theorique : execute, le bloc sort en rc != 0
    des que l'API echoue. C'est ce rc qui rougissait la gate.

    Les deux branches sont couvertes : `advisory` (la publication elle-
    meme) et `success` (le retrait de la section sur un run vert).
    """
    proc = _run_publish_block(tmp_path, state)
    assert proc.returncode != 0, (
        "le bloc de publication devrait propager l'echec de l'API ; "
        f"rc={proc.returncode} stdout={proc.stdout!r} stderr={proc.stderr!r}"
    )


@pytest.mark.parametrize("state", ["advisory", "success"])
def test_simulated_publish_failure_does_not_red_the_job(tmp_path: Path, state: str):
    """LE test decisif : l'echec simule ne rougit pas la gate.

    Contrefactuel mesure : le meme bloc, le meme echec simule, mais sans
    le drapeau -- le job serait ROUGE. Avec le drapeau (l'etat livre), il
    reste VERT. La correction est donc porteuse, pas cosmetique.
    """
    proc = _run_publish_block(tmp_path, state)
    assert proc.returncode != 0  # l'echec est bien survenu

    steps = _steps()
    assert _job_verdict(steps, {PUBLISH_STEP}) == "success"

    without_flag = copy.deepcopy(steps)
    for step in without_flag:
        if step.get("name") == PUBLISH_STEP:
            step.pop("continue-on-error", None)
    assert _job_verdict(without_flag, {PUBLISH_STEP}) == "failure"


def test_publish_block_does_not_swallow_the_failure():
    """Le bloc ne doit pas avaler l'echec (`|| true`) : s'il le faisait,
    le drapeau serait inutile et l'echec deviendrait invisible au lieu
    d'etre non bloquant. `set -e` + aucun `|| true` = l'echec remonte au
    step, qui decide -- c'est exactement le contrat voulu."""
    run = _step(PUBLISH_STEP)["run"]
    assert "set -e" in run
    assert "|| true" not in run


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
