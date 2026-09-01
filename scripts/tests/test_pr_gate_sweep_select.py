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

Acceptance #11862 (3 cas) + #11808 (repli par (run_id, name), pas par nom --
trois workflows emettent un job homonyme "Ratchet (base vs PR)") + regressions
du comportement historique :
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
    return _run_selector_both(tmp_path, rows).stdout


def _run_selector_both(tmp_path, rows):
    """Comme _run_selector mais rend le process complet (stdout + stderr) --
    les diagnostics d'exclusion (#11808) vont sur stderr."""
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
    return out


def _pr(number, checks, sha="deadbeef", fork=False):
    """checks = tuples (name, status, conclusion, started_at[, run_id]).

    Sans 5e element, la fixture ne porte pas de details_url : le selecteur
    replie alors sous la cle sentinel ``unattributed`` (comportement des
    donnees collectees avant #11808). Avec un run_id, la fixture porte le
    details_url REST (.../actions/runs/{run_id}/job/...).
    """
    rows = []
    for ch in checks:
        n, s, c, t = ch[:4]
        row = {"name": n, "status": s, "conclusion": c, "started_at": t}
        if len(ch) > 4 and ch[4]:
            row["details_url"] = (
                "https://github.com/jsboige/CoursIA/actions/runs/"
                f"{ch[4]}/job/96158568958"
            )
        rows.append(row)
    return {"number": number, "sha": sha, "fork": fork, "checks": rows}


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


def test_other_latest_cancelled_is_candidate(tmp_path):
    """#13978 -- INVERSION d'acceptance, datee 2026-09-01.

    L'acceptance 5 d'origine (#11862) abstenait sur un `cancelled` frais porte
    par un AUTRE check, au motif qu'une "interruption reelle ne se maquille
    pas". Sa premisse -- un cancelled frais est une interruption RARE -- est
    tombee : sous `cancel-in-progress: true` sur les workflows advisory, c'est
    l'etat STATIONNAIRE de toute PR ayant recu deux pushes.

    Mesure du sweep 33459621864 (2026-09-01T01:40, 71 PRs ouvertes) : sur 42
    exclusions nommees, 16 -- 38 % -- tenaient a des `cancelled` SEULS, dont 13
    au seul advisory `List open-PR path collisions`. Ce meme advisory annule
    coexiste avec un `PR gate: SUCCESS` sur des PRs MERGEES (#13916, #13860) :
    le filtre etait strictement plus strict que le gate dont il existe pour
    re-rendre le verdict.

    L'intention d'origine tient toujours, et c'est pourquoi l'inversion est
    sure : le sweep ne merge rien -- il RELANCE le gate, qui re-lit l'etat live
    et conclura FAIL si un constituant est reellement rouge. Le verdict reste
    rendu par le gate.
    """
    cancelled_new = ("Hermes review", "completed", "cancelled", "2026-01-01T11:00:00Z")
    out = _run_selector(tmp_path, [_pr(108, [GATE_FAIL, cancelled_new])])
    assert out.strip() == "108 deadbeef false"


def test_other_cancelled_plus_failure_still_abstains(tmp_path):
    """CONTROLE POSITIF de l'inversion ci-dessus (#13978).

    Sans lui, le correctif serait indiscernable d'un filtre debranche : il faut
    montrer qu'un `failure` frais exclut TOUJOURS, y compris quand un
    `cancelled` l'accompagne. Si ce test passe au vert en meme temps que
    l'inversion, c'est que `red_others` ne filtre plus rien du tout.
    """
    cancelled_new = ("Hermes review", "completed", "cancelled", "2026-01-01T11:00:00Z")
    failure_new = ("Papermill ratchet", "completed", "failure", "2026-01-01T11:00:00Z")
    out = _run_selector(tmp_path, [_pr(109, [GATE_FAIL, cancelled_new, failure_new])])
    assert out.strip() == ""


def test_other_startup_failure_still_abstains(tmp_path):
    """#13978 -- l'exemption porte sur UNE conclusion, pas sur le principe.

    `startup_failure` (et toute conclusion future inconnue) doit continuer
    d'exclure : le correctif ajoute `cancelled` a un ensemble non-bloquant, il
    ne remplace pas le filtre par une liste blanche de bloquants.
    """
    startup = ("Hermes review", "completed", "startup_failure", "2026-01-01T11:00:00Z")
    out = _run_selector(tmp_path, [_pr(110, [GATE_FAIL, startup])])
    assert out.strip() == ""


def test_selector_has_cancelled_in_red_not_green(tmp_path):
    """Garde structurl : le correctif est bien asymetrique -- 'cancelled' dans
    RED, absent de GREEN. Ce test echoue si quelqu'un symetrise par inadvertance."""
    assert "cancelled" in SELECTOR
    m = re.search(r'RED = \{[^}]*\}', SELECTOR)
    assert m and "cancelled" in m.group(0)
    m = re.search(r'GREEN = \{[^}]*\}', SELECTOR)
    assert m and "cancelled" not in m.group(0)
    # #13978 : le cote "autres checks" doit exempter `cancelled` EXPLICITEMENT.
    # Un retour au complement nu de GREEN (`not in GREEN`) re-excluerait 38 %
    # du pool bloque sans qu'aucun test d'acceptance ne rougisse.
    assert 'OTHERS_NOT_BLOCKING = GREEN | {"cancelled"}' in SELECTOR
    assert "not in OTHERS_NOT_BLOCKING" in SELECTOR


# --- #11808 : le repli des check-runs par NOM fusionne des workflows homonymes ---

# L'incident mesure sur #11804 (2026-08-19) : trois workflows emettent un job
# affichant "Ratchet (base vs PR)". Replie par nom, le SUCCESS 16:21 (Exec
# Sequence) efface le FAILURE 16:19 (Papermill) -- la sweep a relance le gate
# d'une PR qui portait un rouge vivant.
RATCHET_OK_1616 = ("Ratchet (base vs PR)", "completed", "success",
                   "2026-08-19T16:16:01Z", 32274924047)
RATCHET_FAIL_1619 = ("Ratchet (base vs PR)", "completed", "failure",
                     "2026-08-19T16:19:45Z", 32274924272)
RATCHET_OK_1621 = ("Ratchet (base vs PR)", "completed", "success",
                   "2026-08-19T16:21:06Z", 32274924088)


def test_same_name_three_workflows_red_not_erased(tmp_path):
    """Acceptance 1 (#11808) -- le test de falsification : trois check-runs
    homonymes de run_ids DIFFERENTS, [SUCCESS, FAILURE, SUCCESS]. Le repli par
    nom garde le plus recent (vert) et declare la PR saine ; la PR doit au
    contraire rester HORS candidats tant qu'un des trois est rouge. Ce test
    echoue sur le RED d'avant le fix (la PR y etait candidate)."""
    out = _run_selector(
        tmp_path,
        [_pr(109, [GATE_FAIL, RATCHET_OK_1616, RATCHET_FAIL_1619, RATCHET_OK_1621])],
    )
    assert out.strip() == ""


def test_same_run_rerun_latest_wins(tmp_path):
    """Acceptance 2 : non-regression du latest-wins INTRA-workflow -- memes
    run_id et nom, FAILURE 16:19 puis SUCCESS 16:21 : la relance efface son
    propre verdict perime, la PR reste candidate."""
    fail_then_green = [
        ("Hermes review", "completed", "failure", "2026-01-01T16:19:00Z", 111),
        ("Hermes review", "completed", "success", "2026-01-01T16:21:00Z", 111),
    ]
    out = _run_selector(tmp_path, [_pr(110, [GATE_FAIL] + fail_then_green)])
    assert out.strip() == "110 deadbeef false"


def test_cross_workflow_green_and_red_keeps_pr_out(tmp_path):
    """Meme nom, deux run_ids, un vert + un rouge (sans troisieme leg) : le
    rouge d'un AUTRE workflow suffit a ecarter -- variante minimale du cas
    #11804."""
    out = _run_selector(
        tmp_path, [_pr(111, [GATE_FAIL, RATCHET_FAIL_1619, RATCHET_OK_1621])]
    )
    assert out.strip() == ""


def test_excluded_pr_names_its_blocking_check(tmp_path):
    """Acceptance 5 : la sortie NOMME, pour chaque PR ecartee, quel check
    l'ecarte (et son run) -- sur stderr, pour ne pas polluer candidates.txt.
    Un compte seul serait indiscernable d'un filtre debranche (#11804)."""
    proc = _run_selector_both(
        tmp_path,
        [_pr(109, [GATE_FAIL, RATCHET_FAIL_1619, RATCHET_OK_1621])],
    )
    assert proc.stdout.strip() == ""
    assert "#109" in proc.stderr
    assert "Ratchet (base vs PR)" in proc.stderr
    assert "failure" in proc.stderr
    assert "32274924272" in proc.stderr


def test_excluded_incomplete_pr_names_its_blocking_check(tmp_path):
    """Meme acceptance 5, cas d'un check inacheve (le gate attend peut-etre
    legitiment) -- nomme aussi, verdict 'unfinished'."""
    queued = ("Ratchet (base vs PR)", "queued", None,
              "2026-08-19T16:21:06Z", 32274924088)
    proc = _run_selector_both(tmp_path, [_pr(112, [GATE_FAIL, queued])])
    assert proc.stdout.strip() == ""
    assert "#112" in proc.stderr
    assert "unfinished" in proc.stderr
