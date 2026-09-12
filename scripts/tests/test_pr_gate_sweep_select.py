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
from datetime import datetime, timedelta, timezone

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
    # Le heredoc est localise par contenu, pas par index : une etape
    # d'amorcage (bootstrap gh, #14267) precede desormais le selecteur sans
    # que ce contrat doive bouger.
    for step in doc["jobs"]["sweep"]["steps"]:
        m = re.search(
            r"python - <<'PY'[^\n]*\n(.*?)\nPY\n",
            str(step.get("run", "")),
            re.S,
        )
        if m:
            return m.group(1)
    raise AssertionError(
        "heredoc python introuvable dans pr-gate-stale-sweep.yml"
    )


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
    env = dict(os.environ, SWEEP_RUNS_FILE=str(fixture),
               SWEEP_MUTE_FILE=str(tmp_path / "mute.txt"))
    out = subprocess.run(
        ["python", "-c", SELECTOR],
        capture_output=True, text=True, encoding="utf-8", env=env, cwd=tmp_path,
    )
    assert out.returncode == 0, out.stderr
    return out


def _pr(number, checks, sha="deadbeef", fork=False, workflows=None):
    """checks = tuples (name, status, conclusion, started_at[, run_id]).

    Sans 5e element, la fixture ne porte pas de details_url : le selecteur
    replie alors sous la cle sentinel ``unattributed`` (comportement des
    donnees collectees avant #11808). Avec un run_id, la fixture porte le
    details_url REST (.../actions/runs/{run_id}/job/...).

    Le 6e element est le ``output.title`` collecte (#15825) : absent, la
    fixture decrit la forme PRE-collection du champ et la leg n'est jamais
    classee muette ; les fixtures muettes le portent a "" explicitement --
    la forme exacte que le collecteur emet pour un check-run conclu sans
    output.
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
        if len(ch) > 5:
            row["title"] = ch[5]
        rows.append(row)
    row_out = {"number": number, "sha": sha, "fork": fork, "checks": rows}
    if workflows:
        row_out["workflows"] = {str(k): v for k, v in workflows.items()}
    return row_out


GATE_OK = ("PR gate", "completed", "success", "2026-01-01T10:00:00Z")
GATE_CANCELLED = ("PR gate", "completed", "cancelled", "2026-01-01T10:00:00Z")
GATE_FAIL = ("PR gate", "completed", "failure", "2026-01-01T10:00:00Z")
OTHER_GREEN = ("Hermes review", "completed", "success", "2026-01-01T10:05:00Z")
OTHER_RED = ("Hermes review", "completed", "failure", "2026-01-01T10:05:00Z")
OTHER_QUEUED = ("Hermes review", "queued", None, "2026-01-01T10:05:00Z")
# (#15825) legs portant le titre collecte : muet (rouge, titre vide) vs
# eloquent (rouge, titre porte) -- la mesure 2026-09-12 : 9 muets sur 43.
GATE_MUTE = ("PR gate", "completed", "failure", "2026-01-01T10:00:00Z", 111, "")
GATE_FAIL_TITLED = ("PR gate", "completed", "failure", "2026-01-01T10:00:00Z",
                    111, "FAIL -- failing checks: Proof integrity (knot_lean)")


def test_gate_cancelled_alone_is_candidate(tmp_path):
    """Acceptance 1 : un gate cancelled, tous les autres verts -> relance.

    Falsification : echoue sur le RED d'avant (sans 'cancelled'), la PR reste
    alors bloquee sans rien de rouge -- le defaut #11862 mot pour mot.
    """
    out = _run_selector(tmp_path, [_pr(101, [GATE_CANCELLED, OTHER_GREEN])])
    assert out.strip() == "101 deadbeef false 0"


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
    assert out.strip() == "103 deadbeef false 0"


def test_gate_failure_others_green_candidate(tmp_path):
    """Regression : le comportement d'origine (failure/timeout/action_required)
    reste candidat."""
    out = _run_selector(tmp_path, [_pr(104, [GATE_FAIL, OTHER_GREEN])])
    assert out.strip() == "104 deadbeef false 0"


# --- #15825 : legs muettes (rouge, output.title vide) -> reparation, pas re-run
#
# Mesure 2026-09-12 : 9 echecs `PR gate` sur 43 rendent output.title = null.
# Classe stale-snapshot : le rerun rejoue l'event payload fige, dont le
# checkout PREDATE la machinerie de publication (#15725) -- le script
# re-execute est l'ancien, sans publication. Preuve : run 34608518559 sur
# #15440, 8 tentatives x ~23 s, identiques, pendant que le log portait le
# verdict depuis la premiere. Ces tests epinglent le routage : jamais un
# candidat re-run (inert et brule un slot waiter), toujours le flux de
# reparation (job_id + run_id pour le PATCH du titre depuis le log).


def _run_selector_with_mute(tmp_path, rows):
    """Exec le selecteur livree et rend (stdout, lignes du flux muet)."""
    out = _run_selector_both(tmp_path, rows)
    mute_file = tmp_path / "mute.txt"
    lines = (mute_file.read_text(encoding="utf-8").splitlines()
             if mute_file.exists() else [])
    return out.stdout, lines


def test_mute_gate_leg_routed_to_repair_not_rerun(tmp_path):
    """#15825 critere 2 : un gate rouge SANS output.title va au flux de
    reparation -- stdout VIDE (aucun candidat re-run)."""
    stdout, mute_lines = _run_selector_with_mute(
        tmp_path, [_pr(101, [GATE_MUTE, OTHER_GREEN])])
    assert stdout.strip() == ""
    assert mute_lines == ["101 deadbeef 96158568958 111"]


def test_titled_red_gate_still_rerun_candidate(tmp_path):
    """Contre-falsification : le meme rouge AVEC titre reste un candidat
    re-run -- le predicat muet ne doit pas absorber les gates eloquents."""
    out = _run_selector(tmp_path, [_pr(105, [GATE_FAIL_TITLED, OTHER_GREEN])])
    assert out.strip() == "105 deadbeef false 0"


def test_mute_gate_leg_with_other_red_still_routed_to_repair(tmp_path):
    """La reparation muette est inconditionnelle : nommer la cause vaut meme
    si un autre check est rouge (c'est un diagnostic, pas un deblocage)."""
    stdout, mute_lines = _run_selector_with_mute(
        tmp_path, [_pr(106, [GATE_MUTE, OTHER_RED])])
    assert stdout.strip() == ""
    assert mute_lines == ["106 deadbeef 96158568958 111"]


def test_mute_leg_without_details_url_diagnosed_not_crashed(tmp_path):
    """Leg muette sans details_url (verdict POSTe, aucun run derriere) :
    diag nomme, ni candidat ni reparation -- le selecteur ne crashe pas."""
    leg = ("PR gate", "completed", "failure", "2026-01-01T10:00:00Z", None, "")
    stdout, mute_lines = _run_selector_with_mute(
        tmp_path, [_pr(107, [leg, OTHER_GREEN])])
    assert stdout.strip() == ""
    assert mute_lines == []


def test_titleless_success_leg_is_never_mute(tmp_path):
    """Un SUCCESS sans titre n'est jamais muet (rien a diagnostiquer) ni
    candidat (pas rouge) : PR saine, le sweep la traverse."""
    leg = ("PR gate", "completed", "success", "2026-01-01T10:00:00Z", 111, "")
    stdout, mute_lines = _run_selector_with_mute(
        tmp_path, [_pr(108, [leg, OTHER_GREEN])])
    assert stdout.strip() == ""
    assert mute_lines == []


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
    assert out.strip() == "107 deadbeef false 0"


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
    assert out.strip() == "108 deadbeef false 0"


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
    assert out.strip() == "110 deadbeef false 0"


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


def test_same_workflow_twin_runs_green_supersedes_red(tmp_path):
    """Defaut mesure le 2026-09-01 : un MEME workflow produit DEUX runs sur un
    MEME SHA parce qu'il tire sur deux evenements (`pull_request` et
    `pull_request_review`) -- deux run_id, pas un rerun. Le repli par
    (run_id, name) les garde separes, la failure superseded survit, et le
    sweep exclut la PR a chaque passage (`red gate, kept out`).

    Cas reel : #13869, SHA d207b5e15 -- run 33432764140 (`pull_request`)
    failure 20:05:20Z, run 33435266510 (`pull_request_review`) success
    20:20:51Z. `pr_gate.py` replie par NOM (latest-wins) et voit du vert ;
    le sweep voyait du rouge. 23 des 77 PRs ouvertes (30 %) etaient gelees.

    Falsification : ce test echoue sur le repli par (run_id, name).
    """
    guard_old = ("Always-on guards", "completed", "failure",
                 "2026-01-01T09:00:00Z", 33432764140)
    guard_new = ("Always-on guards", "completed", "success",
                 "2026-01-01T09:15:00Z", 33435266510)
    out = _run_selector(tmp_path, [_pr(
        113, [GATE_FAIL, guard_old, guard_new],
        workflows={33432764140: 555, 33435266510: 555},
    )])
    assert out.strip() == "113 deadbeef false 0"


def test_distinct_workflows_same_name_still_separate(tmp_path):
    """Controle positif de non-regression #11808 : deux workflows DIFFERENTS
    (workflow_id 555 et 777) portant le meme nom de job ne fusionnent pas --
    le vert du second n'efface pas le rouge du premier, la PR reste dehors.

    C'est ce que la clef (workflow_id, name) preserve et qu'un repli par nom
    seul perdrait.
    """
    ratchet_red = ("Ratchet (base vs PR)", "completed", "failure",
                   "2026-01-01T09:00:00Z", 900)
    ratchet_green = ("Ratchet (base vs PR)", "completed", "success",
                     "2026-01-01T09:15:00Z", 901)
    out = _run_selector(tmp_path, [_pr(
        114, [GATE_FAIL, ratchet_red, ratchet_green],
        workflows={900: 555, 901: 777},
    )])
    assert out.strip() == ""


# --- #15375 : le tier de maturite (4e champ), mature-first a la purge --------


def _ts(minutes_ago):
    """Horodatage ISO Z dynamique -- le tier se mesure contre le `now` du
    selecteur, donc les fixtures de ce bloc doivent etre RELATIVES (les dates
    fixes 2026-01-01 du bloc historique sont toutes matures par construction,
    ce qui est aussi pourquoi leurs assertions portent un rang 0)."""
    return (datetime.now(timezone.utc) - timedelta(minutes=minutes_ago)
            ).strftime("%Y-%m-%dT%H:%M:%SZ")


def test_verdict_older_than_floor_is_mature(tmp_path):
    """Le coeur de #15375 forme 3 : un verdict de 180 min sur un plancher de
    120 min est MATURE -- sa relance est immediatement conclusive (le gate
    re-mesurera un head commit forcement plus vieux encore, voir la preuve
    d'etancheite dans le selecteur). Rang 0, servi en priorite."""
    gate_old = ("PR gate", "completed", "failure", _ts(180))
    out = _run_selector(tmp_path, [_pr(120, [gate_old, OTHER_GREEN])])
    assert out.strip() == "120 deadbeef false 0"


def test_young_verdict_is_immature(tmp_path):
    """Falsification : un verdict de 5 min n'a PAS franchise le plancher -- la
    relance ne pourrait que re-rendre le meme FAIL de dwell. Rang 1, servi en
    second, sous un cap retreint."""
    gate_young = ("PR gate", "completed", "failure", _ts(5))
    out = _run_selector(tmp_path, [_pr(121, [gate_young, OTHER_GREEN])])
    assert out.strip() == "121 deadbeef false 1"


def test_newest_red_leg_decides_the_tier(tmp_path):
    """Deux legs de gate rouges : c'est la PLUS RECENTE qui gouverne le tier.
    Une leg ancienne (3 h) ne peut pas faire passer la PR pour mature si une
    leg rouge plus jeune (10 min) existe -- le bornage du dernier evenement
    est la leg la plus recente, pas la plus ancienne."""
    red_old = ("PR gate", "completed", "failure", _ts(200))
    red_new = ("PR gate", "completed", "failure", _ts(10))
    out = _run_selector(tmp_path, [_pr(122, [red_old, red_new, OTHER_GREEN])])
    assert out.strip() == "122 deadbeef false 1"


def test_unreadable_verdict_timestamp_is_immature_never_mature(tmp_path):
    """Un `started_at` vide ou non ISO ne peut pas être lu comme age : tier 1
    (conservateur). Jamais 0 -- mais la file immature le sert quand meme (cap
    de repli), donc pas de famine, seulement une depriorisation."""
    gate_nots = ("PR gate", "completed", "failure", "")
    out = _run_selector(tmp_path, [_pr(123, [gate_nots, OTHER_GREEN])])
    assert out.strip() == "123 deadbeef false 1"
    gate_garbage = ("PR gate", "completed", "failure", "hier-matin")
    out = _run_selector(tmp_path, [_pr(124, [gate_garbage, OTHER_GREEN])])
    assert out.strip() == "124 deadbeef false 1"


def test_workflow_pins_tier_sort_and_per_tier_caps():
    """Garde structurelle : le workflow trie par le 4e champ (tier) avant le
    numero de PR, et porte les deux caps par tier. Sans ce pin, un revert du
    sort binaire ou des caps ramenerait le cap plat de 8 sans qu'aucun test
    d'acceptance du selecteur ne rougisse (le selecteur emet le rang, mais
    rien ne l'oblige a le CONSOMMER)."""
    with open(WORKFLOW, encoding="utf-8") as f:
        doc = yaml.safe_load(f)
    run = str(next(
        step.get("run", "") for step in doc["jobs"]["sweep"]["steps"]
        if "MAX_MATURE" in str(step.get("run", ""))
    ))
    assert "MAX_MATURE=12" in run
    assert "MAX_IMMATURE=4" in run
    assert "MAX_POSTS=8" not in run
    assert "sort -s -k4,4n -k1,1n" in run
    # Le cap d'un tier ne doit pas arreter la boucle : les immatures ranges
    # derriere doivent rester servis (continue, pas break).
    assert "break" not in re.sub(r"#.*", "", run.split("MAX_MATURE=12")[1].split("done <")[0])
