#!/usr/bin/env python3
"""Tests for classify_job_deaths.py — issue #15055.

Classification is unit-tested on synthetic job + annotation payloads
matching the API shapes measured on the four red cases of 2026-09-06/07.
No network access: the classifier is a pure function.
"""
from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

from classify_job_deaths import classify_job  # noqa: E402


def _job(conclusion: str, steps: list[dict] | None = None) -> dict:
    return {
        "id": 1,
        "name": "test-job",
        "conclusion": conclusion,
        "runner_name": "some-runner",
        "steps": steps or [],
    }


ANN_NOT_ACQUIRED = [{"message": (
    "The job was not acquired by Runner of type self-hosted even after "
    "multiple attempts"
)}]
ANN_LOST_COMM = [{"message": (
    "The self-hosted runner lost communication with the server. Verify the "
    "machine is running and has a healthy network connection"
)}]
ANN_TIMEOUT = [{"message": (
    "The job running on runner X has exceeded the maximum execution time "
    "of 60 minutes"
)}]


def test_no_runner_acquired():
    """#14945/#14931 : cancelled, 0/0 steps, annotation d'echec d'acquisition."""
    job = _job("cancelled", steps=[])
    assert classify_job(job, ANN_NOT_ACQUIRED) == "NO_RUNNER_ACQUIRED"


def test_no_runner_acquired_runner_empty_is_not_required():
    """La classe tient sur l'annotation, pas sur runner_name vide (le champ
    peut etre absent selon la version d'API) — la regression du discriminant
    serait silencieuse autrement."""
    job = _job("cancelled", steps=[])
    job.pop("runner_name")
    assert classify_job(job, ANN_NOT_ACQUIRED) == "NO_RUNNER_ACQUIRED"


def test_runner_lost_comm():
    """#14958/#14854 : failure, N/M steps resolues, aucune en failure."""
    steps = [
        {"number": 1, "name": "Set up job", "conclusion": "success"},
        {"number": 2, "name": "Checkout", "conclusion": "success"},
        {"number": 3, "name": "Build", "conclusion": None},
        {"number": 4, "name": "Test", "conclusion": None},
    ]
    assert classify_job(_job("failure", steps), ANN_LOST_COMM) == "RUNNER_LOST_COMM"


def test_real_step_failure_wins_over_infra_annotation():
    """Une etape reellement echouee est un rouge de contenu, meme si le
    runner est mort ensuite (steps de post-processing)."""
    steps = [
        {"number": 1, "name": "Checkout", "conclusion": "success"},
        {"number": 2, "name": "Run tests", "conclusion": "failure"},
    ]
    assert classify_job(_job("failure", steps), ANN_LOST_COMM) == "REAL_STEP_FAILURE"


def test_timeout():
    steps = [{"number": 1, "name": "Build", "conclusion": "success"}]
    assert classify_job(_job("failure", steps), ANN_TIMEOUT) == "TIMEOUT"


def test_oom_annotation_is_classified():
    """Mesure 2026-09-21 (job 106270875399, runner myia-ai-01-wsl-8) : le job
    meurt d'un manque de memoire du parc, GitHub pose "Out of memory." sur le
    check-run, et l'etape courante reste en `null` (jamais resolue). Avant
    l'ajout de la classe, ce cas tombait en UNCATEGORIZED_FAILURE."""
    steps = [
        {"number": 1, "name": "Set up job", "conclusion": "success"},
        {"number": 2, "name": "Install dependencies", "conclusion": "success"},
        {"number": 3, "name": "Run tests", "conclusion": None},
        {"number": 4, "name": "Post Run actions/checkout@v4", "conclusion": None},
    ]
    ann = [
        {"message": "Node.js 20 is deprecated. The following actions target "
                    "Node.js 20 but are being forced to run on Node.js 24"},
        {"message": "Out of memory."},
    ]
    assert classify_job(_job("failure", steps), ann) == "OOM"


def test_real_step_failure_wins_over_oom_annotation():
    """Contrat de priorite preserve : une famine memoire peut se manifester en
    exit 1 sur un teardown qui echoue, mais une etape REELLEMENT en echec reste
    un rouge de contenu. Ajouter OOM ne doit pas offrir de blanchiment."""
    steps = [
        {"number": 1, "name": "Checkout", "conclusion": "success"},
        {"number": 2, "name": "Run tests", "conclusion": "failure"},
    ]
    ann = [{"message": "Out of memory."}]
    assert classify_job(_job("failure", steps), ann) == "REAL_STEP_FAILURE"


def test_oom_is_counted_as_infrastructural():
    """Le demi-correctif a mesurer : classer OOM sans le compter laisse le
    rapport annoncer "morts infrastructurelles : 0" sur une mort du parc --
    l'instrument resterait menteur. La somme `infra` ET son detail derivent de
    INFRA_DEATH_CLASSES, donc les deux sites ne peuvent plus diverger."""
    import classify_job_deaths as mod

    payload = {
        "counts": {"OOM": 2, "REAL_STEP_FAILURE": 1},
        "rows": [],
    }
    text = mod.render_markdown(payload)
    assert "morts infrastructurelles : **2**" in text
    assert "AUTRES=0" in text, "3 morts, 2 infra, 1 contenu -> 0 autre"
    for klass in mod.INFRA_DEATH_CLASSES:
        assert f"{klass}=" in text, f"{klass} absent du detail infra"
    assert "OOM=2" in text


# --------------------------------------------------------------------------
# Mort de WORKER : l'etape conclud `failure` avec une annotation generique
# --------------------------------------------------------------------------
# Extraits reels des logs mesures le 2026-09-21 sur le workflow
# "Scripts Tests (CPU)", trois runners du meme hote. Le job 106268236606
# (wsl-7) meurt dans le TEARDOWN xdist -- pytest avait fini sa session
# (`pytest_sessionfinish` -> `dsession.teardown_nodes`) quand le pool explose.
LOG_TEARDOWN_DEATH = (
    '  File ".../_pytest/terminal.py", line 961, in pytest_sessionfinish\n'
    '  File ".../xdist/dsession.py", line 99, in pytest_sessionfinish\n'
    '    nm.teardown_nodes()\n'
    '  File ".../execnet/multi.py", line 337, in termkill\n'
    '    termreply = workerpool.spawn(termfunc)\n'
    '  File ".../execnet/gateway_base.py", line 155, in start\n'
    '    _thread.start_new_thread(func, args)\n'
    "RuntimeError: can't start new thread\n"
)
# Variante du 106253882998 (wsl-8) : le worker meurt EN PLEINE session et le
# planificateur loadscope tombe sur un worker deja disparu.
LOG_XDIST_INTERNALERROR = (
    'INTERNALERROR>   File ".../xdist/scheduler/loadscope.py", line 98, '
    'in _assign_work_unit\n'
    'INTERNALERROR> KeyError: <WorkerController gw5>\n'
)
# Controle positif du 106261152819 (wsl-5) : pytest NOMME son echec.
LOG_CONTENT_RED = (
    '======================= short test summary info '
    '========================\n'
    'FAILED scripts/audit/tests/test_scan_duplicate_test_pairs.py::'
    'test_retroactive_control_sees_third_pair_pre_consolidation\n'
    '= 1 failed, 14430 passed, 97 skipped, 8 xfailed, 3 warnings '
    'in 244.69s (0:04:04) =\n'
)

ANN_EXIT_1 = [
    {"message": "Node.js 20 is deprecated. The following actions target "
                "Node.js 20 but are being forced to run on Node.js 24"},
    {"message": "Process completed with exit code 1."},
]


def _step_failure_job() -> dict:
    """Forme mesuree : `Run tests` conclut `failure`, annotation generique."""
    steps = [
        {"number": 1, "name": "Set up job", "conclusion": "success"},
        {"number": 2, "name": "Checkout", "conclusion": "success"},
        {"number": 3, "name": "Run tests", "conclusion": "failure"},
        {"number": 4, "name": "Post Run actions/checkout@v4",
         "conclusion": "success"},
    ]
    return {
        "id": 106268236606,
        "name": "Scripts Tests (CPU)",
        "conclusion": "failure",
        "runner_name": "myia-ai-01-wsl-7",
        "steps": steps,
    }


def test_worker_death_predicate_on_measured_logs():
    """Le predicat, sur les logs reels : signature + aucun test nomme."""
    import classify_job_deaths as mod

    assert mod.worker_death_from_log(LOG_TEARDOWN_DEATH) is True
    assert mod.worker_death_from_log(LOG_XDIST_INTERNALERROR) is True
    assert mod.worker_death_from_log(LOG_CONTENT_RED) is False


def test_named_failures_are_never_reclassified():
    """Garde-fou : un rouge de contenu peut mourir ensuite (teardown qui
    echoue). Des que pytest a NOMME un test, la classe de contenu est
    conservee -- le predicat est conservateur par construction, sinon
    l'organe offrirait un blanchiment a tout rouge suivi d'une mort."""
    import classify_job_deaths as mod

    mixed = LOG_TEARDOWN_DEATH + LOG_CONTENT_RED
    assert mod.worker_death_from_log(mixed) is False


def test_worker_death_signature_beats_a_step_failure():
    """Le defaut mesure : `Run tests` = failure + annotation "Process
    completed with exit code 1." classait le job en REAL_STEP_FAILURE, donc
    l'organe designait le DIFF alors que le log ne nomme aucun test et porte
    la signature de mort du pool. Deux des quatre rouges de la suite ce
    jour-la (jobs 106268236606 wsl-7 et 106253882998 wsl-8) basculent."""
    import classify_job_deaths as mod

    run = {
        "id": 7,
        "name": "Scripts Tests (CPU)",
        "conclusion": "failure",
        "created_at": "2026-09-21T08:40:00Z",
        "updated_at": "2026-09-21T08:47:00Z",
        "head_sha": "f" * 40,
    }
    orig = (mod.fetch_run_jobs, mod.fetch_annotations, mod.fetch_job_log)
    mod.fetch_run_jobs = lambda run_id: [_step_failure_job()]
    mod.fetch_annotations = lambda job_id: ANN_EXIT_1
    mod.fetch_job_log = lambda job_id: LOG_TEARDOWN_DEATH
    try:
        payload = mod.analyse_runs([run])
    finally:
        mod.fetch_run_jobs, mod.fetch_annotations, mod.fetch_job_log = orig
    assert payload["rows"][0]["class"] == "WORKER_DEATH"


def test_log_absent_keeps_the_step_verdict():
    """Un log absent (blob jamais uploade, cf job OOM 106270875399) ne
    reclasse RIEN : la classe de l'etape est conservee. Fail-closed, sinon
    la moindre expiration de log blanchirait un vrai rouge de contenu."""
    import classify_job_deaths as mod

    assert mod.worker_death_from_log("") is False

    run = {
        "id": 8,
        "name": "Scripts Tests (CPU)",
        "conclusion": "failure",
        "created_at": "2026-09-21T08:40:00Z",
        "updated_at": "2026-09-21T08:47:00Z",
        "head_sha": "f" * 40,
    }
    orig = (mod.fetch_run_jobs, mod.fetch_annotations, mod.fetch_job_log)
    mod.fetch_run_jobs = lambda run_id: [_step_failure_job()]
    mod.fetch_annotations = lambda job_id: ANN_EXIT_1
    mod.fetch_job_log = lambda job_id: ""
    try:
        payload = mod.analyse_runs([run])
    finally:
        mod.fetch_run_jobs, mod.fetch_annotations, mod.fetch_job_log = orig
    assert payload["rows"][0]["class"] == "REAL_STEP_FAILURE"


def test_the_log_is_fetched_only_for_the_ambiguous_class():
    """Cout borne : le fetch du log ne doit se declencher QUE sur
    REAL_STEP_FAILURE. Une classe tranchee par l'annotation (OOM) ne doit pas
    payer un appel reseau supplementaire -- sinon un scan de N jobs rouges
    couterait N fetchs de plusieurs centaines de Ko."""
    import classify_job_deaths as mod

    run = {
        "id": 9,
        "name": "Scripts Tests (CPU)",
        "conclusion": "failure",
        "created_at": "2026-09-21T08:40:00Z",
        "updated_at": "2026-09-21T08:47:00Z",
        "head_sha": "f" * 40,
    }
    oom_job = _step_failure_job()
    for step in oom_job["steps"]:
        step["conclusion"] = None
    calls: list[int] = []
    orig = (mod.fetch_run_jobs, mod.fetch_annotations, mod.fetch_job_log)
    mod.fetch_run_jobs = lambda run_id: [oom_job]
    mod.fetch_annotations = lambda job_id: [{"message": "Out of memory."}]
    mod.fetch_job_log = lambda job_id: calls.append(job_id) or ""
    try:
        payload = mod.analyse_runs([run])
    finally:
        mod.fetch_run_jobs, mod.fetch_annotations, mod.fetch_job_log = orig
    assert payload["rows"][0]["class"] == "OOM"
    assert calls == [], "le log a ete fetch pour une classe deja tranchee"


def test_worker_death_is_counted_as_infrastructural():
    """Meme exigence que pour OOM : la classe doit entrer dans la SOMME infra
    et dans son detail, sinon le rapport annonce une mort du parc comme un
    rouge de contenu."""
    import classify_job_deaths as mod

    assert "WORKER_DEATH" in mod.INFRA_DEATH_CLASSES
    payload = {"counts": {"WORKER_DEATH": 2, "REAL_STEP_FAILURE": 1}, "rows": []}
    text = mod.render_markdown(payload)
    assert "morts infrastructurelles : **2**" in text
    assert "WORKER_DEATH=2" in text
    assert "AUTRES=0" in text


def test_fetch_job_log_tolerates_blob_not_found_only():
    """Un blob absent (job tue avant l'upload) rend "" ; toute autre panne
    (auth, reseau) doit remonter bruyamment -- sinon l'instrument perdrait
    silencieusement la seule surface qui separe une mort du parc d'un rouge
    de contenu."""
    import subprocess

    import classify_job_deaths as mod

    class _R:
        def __init__(self, rc, out, err):
            self.returncode, self.stdout, self.stderr = rc, out, err

    orig = mod.subprocess.run
    try:
        mod.subprocess.run = lambda *a, **k: _R(
            1, "<Error><Code>BlobNotFound</Code></Error>", ""
        )
        assert mod.fetch_job_log(1) == ""
        mod.subprocess.run = lambda *a, **k: _R(1, "", "gh: HTTP 401: Bad credentials")
        try:
            mod.fetch_job_log(1)
            raise AssertionError("401 doit propager, pas rendre \"\"")
        except RuntimeError:
            pass
        mod.subprocess.run = lambda *a, **k: _R(0, "some log text", "")
        assert mod.fetch_job_log(1) == "some log text"
    finally:
        mod.subprocess.run = orig
    assert orig is subprocess.run


def test_cancelled_without_annotation_is_other():
    """Quarto (cancel-in-progress inconditionnel) : cancelled sans annotation
    d'acquisition -> classe distincte de NO_RUNNER_ACQUIRED."""
    assert classify_job(_job("cancelled", steps=[]), []) == "CANCELLED_OTHER"


def test_uncategorized_failure():
    steps = [{"number": 1, "name": "Build", "conclusion": "success"}]
    assert classify_job(_job("failure", steps), []) == "UNCATEGORIZED_FAILURE"


def test_shutdown_signal_is_lost_comm():
    """Variante d'agent : shutdown signal recu pendant le job."""
    ann = [{"message": "The runner has received a shutdown signal"}]
    assert classify_job(_job("failure", []), ann) == "RUNNER_LOST_COMM"


def test_fetch_annotations_tolerates_only_true_404():
    """Review ai-01 : seuls les 404 (job sans annotations) sont une classe
    valide ; un 401 (auth perimee) ou une panne reseau doit remonter
    bruyamment, jamais se fondre dans CANCELLED_OTHER."""
    import classify_job_deaths as mod

    mod.gh_api = lambda *a, **k: (_ for _ in ()).throw(
        RuntimeError("gh api repos/jsboige/CoursIA/check-runs/1/annotations "
                     "failed: gh: HTTP 404: Not Found (HTTP 404)")
    )
    assert mod.fetch_annotations(1) == []
    mod.gh_api = lambda *a, **k: (_ for _ in ()).throw(
        RuntimeError("gh api repos/jsboige/CoursIA/check-runs/1/annotations "
                     "failed: gh: HTTP 401: Bad credentials (HTTP 401)")
    )
    try:
        mod.fetch_annotations(1)
        raise AssertionError("401 doit propager, pas rendre []")
    except RuntimeError:
        pass
    mod.gh_api = lambda *a, **k: (_ for _ in ()).throw(
        RuntimeError("gh api repos/jsboige/CoursIA/check-runs/1/annotations "
                     "failed: connection refused")
    )
    try:
        mod.fetch_annotations(1)
        raise AssertionError("panne reseau doit propager, pas rendre []")
    except RuntimeError:
        pass


def test_sha_validation_is_hex_40_and_rejects_non_hex():
    """Review ai-01 : --sha exige exactement [0-9a-fA-F]{40}, pas seulement
    une longueur de 40 — sinon un sha non-hex rend un zero propre."""
    from classify_job_deaths import is_valid_sha

    assert is_valid_sha("f" * 40)
    assert is_valid_sha("0" * 40)
    assert not is_valid_sha("g" * 40)
    assert not is_valid_sha("z" * 40)
    assert not is_valid_sha("f" * 39)
    assert not is_valid_sha("f" * 41)
    assert not is_valid_sha("f" * 40 + "g")
    assert not is_valid_sha("")


def test_run_cancelled_no_jobs_is_a_distinct_signature():
    """Batch de supersession mesure le 2026-09-07T23:02:33Z : run cancelled
    avec ZERO jobs (annulation avant creation). analyse_runs doit l'emettre
    en RUN_CANCELLED_NO_JOBS — sinon il est compté scanné mais invisible."""
    import classify_job_deaths as mod

    run = {
        "id": 42,
        "name": "Secret Scan",
        "conclusion": "cancelled",
        "created_at": "2026-09-07T23:02:33Z",
        "updated_at": "2026-09-07T23:02:40Z",
        "head_sha": "f5b46030",
    }
    orig_jobs, orig_ann = mod.fetch_run_jobs, mod.fetch_annotations
    mod.fetch_run_jobs = lambda run_id: []
    mod.fetch_annotations = lambda job_id: []
    try:
        payload = mod.analyse_runs([run])
    finally:
        mod.fetch_run_jobs = orig_jobs
        mod.fetch_annotations = orig_ann
    assert len(payload["rows"]) == 1
    assert payload["rows"][0]["class"] == "RUN_CANCELLED_NO_JOBS"


if __name__ == "__main__":
    for name, fn in sorted(globals().items()):
        if name.startswith("test_") and callable(fn):
            fn()
            print(f"{name} OK")
    print("All tests passed.")
