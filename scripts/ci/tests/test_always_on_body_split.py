"""Cas d'essai #22331 : un rouge de contenu survit a une edition de body.

Pourquoi ce fichier existe
--------------------------
`always-on-guards.yml` se declenchait sur `edited`. Avec un `concurrency`
`cancel-in-progress: true`, chaque edition de body annulait le run en file et le
renvoyait en fin d'une file de ~2 100 runs : mesure du 2026-10-24, 113
re-declenchements sur 268 arrivent a tete egale, et aucun run cree apres
05:00:16Z n'avait rendu de succes (formulation par date de CREATION, cf.
review Hermes du 2026-10-24 : dernier succes cree bba8683b a 05:00:16Z,
conclu 10:22:19Z -- conclure par date de conclusion masquait des verts
rendus tard dans la fenetre).

Retirer `edited` du workflow de contenu repond au symptome, mais la raison pour
laquelle les organes de body doivent repasser apres une edition reste vraie :
`Require Grain tag`, `prev: non-closing`, `close-keyword`, `genre diversity` et
`closing-ref vs claim` lisent le CORPS, qui ne produit aucun commit.

La forme retenue -- un workflow separe, jamais un job `if:` saute dans le meme
workflow -- vient d'une contrainte mesuree, pas d'une preference :

    `scripts/pr_gate.py::dedupe_latest` garde, par NOM de check, l'entree au
    `started_at` le plus grand ; et `CONCLUSION_OK` contient `skipped`.

Un job de contenu saute sur `edited` rendrait donc un check-run `skipped` plus
recent que le rouge de contenu de la meme tete, et l'effacerait : c'est le
blanchiment que l'issue interdit. Un job saute ne peut pas s'abstenir de
produire un check-run ; seul un AUTRE workflow, qui ne se declenche pas sur
l'evenement, laisse le verdict de contenu intact.

Deuxieme decision (review coordinateur #22333, 12:14Z) : le job de contenu ne
juge PLUS les organes de body du tout. Tant qu'il les jugeait, un rouge de
body ne pouvait etre leve que par un push (ce job ignore `edited`) -- le
symetrique exact du defaut initial. Les organes vivent donc ENTIEREMENT dans
le workflow de body, qui couvre tous les evenements du workflow de contenu
PLUS `edited` : le verdict de body existe a chaque tete, et une edition seule
suffit a le lever.

Ce que l'epingle couvre
-----------------------
Les invariants structurels qui portent cette propriete, sur les fichiers reels :
declencheurs, noms de job distincts, source unique de la logique, agregat.

Ce qu'elle ne couvre PAS : le comportement runtime de GitHub Actions. Elle
empeche la regression de forme, pas une erreur de logique dans les organes
eux-memes.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[3]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"
CONTENT_WF = WORKFLOWS / "always-on-guards.yml"
BODY_WF = WORKFLOWS / "always-on-guards-body.yml"
COMMENTERS_WF = WORKFLOWS / "always-on-commenters.yml"
ORGANS = REPO_ROOT / "scripts" / "ci" / "always_on_body_organs.sh"
PR_GATE = REPO_ROOT / "scripts" / "pr_gate.py"

CONTENT_JOB = "always-on-guards"
BODY_JOB = "always-on-guards-body"
COMMENTERS_JOB = "always-on-commenters"
BODY_ORGANS = ["tag_required", "prev_guard", "close_keyword", "adjacency", "lane_claim"]


def _load(path: Path) -> dict:
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def _trigger_types(doc: dict) -> list[str]:
    on = doc.get("on", doc.get(True))
    pr = on["pull_request"]
    return pr["types"]


# ------------------------------------------------- 1. les deux declencheurs

def test_content_workflow_never_fires_on_body_edits():
    """Le coeur de la correction : le contenu ne se declenche plus sur `edited`."""
    assert "edited" not in _trigger_types(_load(CONTENT_WF))


def test_body_workflow_fires_on_body_edits():
    """Les organes de body doivent repasser apres une edition, sinon on a
    simplement cesse de garder le corps (le defaut inverse)."""
    types = _trigger_types(_load(BODY_WF))
    assert "edited" in types
    # `opened` garantit que le check-run de body EXISTE sur toute PR, meme
    # jamais editee : un nom exige par le gate doit toujours etre produit.
    assert "opened" in types
    # `synchronize` garantit un verdict de body a CHAQUE tete : le fold du
    # gate garde, par nom, le `started_at` le plus recent -- sans lui, le
    # verdict d'une tete ancienne resterait le plus recent pour ce nom
    # (review coordinateur #22333).
    assert "synchronize" in types


def test_concurrency_groups_never_cross():
    """Une edition ne doit jamais annuler un run de contenu : groupes distincts."""
    content = _load(CONTENT_WF)["concurrency"]["group"]
    body = _load(BODY_WF)["concurrency"]["group"]
    assert content != body
    assert "always-on-guards-body" in body


# ------------------------------------------------- 2. deux noms, deux verdicts

def test_job_names_are_distinct():
    """Le fold du gate est par NOM : deux verdicts distincts exigent deux noms."""
    content = _load(CONTENT_WF)["jobs"]
    body = _load(BODY_WF)["jobs"]
    assert list(content) == [CONTENT_JOB]
    assert list(body) == [BODY_JOB]
    names = {content[CONTENT_JOB]["name"], body[BODY_JOB]["name"]}
    assert len(names) == 2, names


def test_body_job_name_is_not_filtered_as_advisory():
    """`is_advisory()` tairait un nom qui contient « advisory » (pr_gate)."""
    name = _load(BODY_WF)["jobs"][BODY_JOB]["name"].lower()
    assert "advisory" not in name and "optional" not in name


# ------------------------------------- 3. une seule source de verite, UN usage

def test_only_the_body_workflow_calls_the_organs_script():
    """La logique des organes ne doit exister qu'a UN endroit, et n'etre
    EXECUTEE que depuis le workflow de body : tant que le job de contenu
    l'appelait aussi, chaque `opened`/`reopened` doublait les cinq postes
    bloquants (review Hermes #22333, point 3)."""
    content_script = [
        s.get("run", "")
        for s in _load(CONTENT_WF)["jobs"][CONTENT_JOB]["steps"]
        if "always_on_body_organs.sh" in s.get("run", "")
    ]
    body_script = [
        s.get("run", "")
        for s in _load(BODY_WF)["jobs"][BODY_JOB]["steps"]
        if "always_on_body_organs.sh" in s.get("run", "")
    ]
    assert content_script == [], "le job de contenu ne doit plus appeler le script"
    assert len(body_script) == 1, "le job de body doit appeler le script une fois"


def test_no_raw_pr_comment_in_the_organs_script():
    """#15372 / review Hermes #22333 point 3 : chaque poste bloquant passe par
    guard_comment_upsert -- un re-run du workflow (recuperation #9858) ne doit
    pas doubler les commentaires, et un vert doit lever le bloquant perime."""
    text = ORGANS.read_text(encoding="utf-8")
    assert "gh pr comment" not in text


def test_content_workflow_no_longer_inlines_the_body_organs():
    """Un organe Reste inline = deux implementations qui derivent."""
    ids = [s.get("id") for s in _load(CONTENT_WF)["jobs"][CONTENT_JOB]["steps"]]
    for organ in BODY_ORGANS:
        assert organ not in ids, "l'organe %s est encore inline" % organ


def test_script_defines_every_body_organ():
    text = ORGANS.read_text(encoding="utf-8")
    for organ in BODY_ORGANS:
        assert re.search(r"^organ_%s\(\)" % organ, text, re.MULTILINE), (
            "fonction organ_%s absente du script" % organ
        )


def test_script_is_syntactically_valid():
    """`bash -n` : un script casse rendrait le job rouge a chaque edition."""
    # Chemin RELATIF + cwd racine : Git Bash ne resout pas un chemin MSYS
    # absolu passe en argument a `bash -n` (mesure : rc=127 sur D:/...).
    rel = ORGANS.relative_to(REPO_ROOT).as_posix()
    out = subprocess.run(
        ["bash", "-n", rel],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    assert out.returncode == 0, out.stderr


def test_script_has_no_github_expression_left():
    """Un `${{ }}` non substitue n'est PAS evalue dans un script shell : il
    resterait litteral et les organes perdraient leur jeton."""
    text = ORGANS.read_text(encoding="utf-8")
    assert "${{" not in text


# ----------------------------------------------------------- 4. l'agregat

def test_content_aggregate_no_longer_judges_body_organs():
    """Un rouge de body juge par le job de contenu ne pouvait etre leve que
    par un push (il ignore `edited`) -- le symetrique du defaut initial
    (review coordinateur #22333, point 2). L'agregat ne doit plus le citer."""
    aggregate = [
        s for s in _load(CONTENT_WF)["jobs"][CONTENT_JOB]["steps"]
        if s.get("name") == "Agregat des verdicts bloquants"
    ]
    assert len(aggregate) == 1
    assert "body_organs" not in aggregate[0]["run"]


def test_script_aggregate_runs_every_organ():
    """Le script est un step unique SANS continue-on-error par organe : c'est
    `main()` qui execute les cinq puis agrege -- il doit TOUS les invoquer,
    sinon un rouge tairait les verdicts des organes d'apres."""
    text = ORGANS.read_text(encoding="utf-8")
    assert "for id in tag_required prev_guard close_keyword adjacency lane_claim" in text


# ---------------------------------------- 5. la premisse de non-blanchiment

def test_body_red_is_liftable_by_an_edition_alone():
    """Cas d'essai exige par la review coordinateur (#22333) : « un rouge de
    body leve par une edition seule, sans push, laisse le gate vert ». Pour
    que ce soit vrai par construction, une edition ne doit pouvoir toucher
    QUE le workflow de body : le job de contenu ne se declenche pas sur
    `edited` ET ne reference plus le script d'organes nulle part."""
    doc = _load(CONTENT_WF)
    assert "edited" not in _trigger_types(doc)
    for step in doc["jobs"][CONTENT_JOB]["steps"]:
        assert "always_on_body_organs" not in str(step.get("run", "")), (
            "le job de contenu reference encore le script d'organes de body"
        )


def test_pr_gate_fold_still_makes_a_skipped_run_shadow_a_red():
    """La premisse de conception, epinglee a sa source.

    Si `skipped` sortait de CONCLUSION_OK, un job saute cesserait d'ecraser un
    rouge et la separation des workflows deviendrait inutile -- le test doit
    alors etre revu sciemment, pas contourne.
    """
    text = PR_GATE.read_text(encoding="utf-8")
    assert 'CONCLUSION_OK = frozenset({"success", "neutral", "skipped"})' in text


# --------------------------- 6. la famille always-on : UN JOB PAR FICHIER
# (correctif PR #22244, 2026-10-26) : le job `always-on-commenters` a d'abord
# vecu en DEUXIEME job d'always-on-guards.yml. Deux defauts propres a cette
# colocalisation, tous deux mesures :
#
# 1. GitHub rejette en ENTIER un workflow dont un `env:` de niveau JOB
#    reference le contexte `runner` (il n'existe qu'au niveau step) : le
#    fichier portait donc le umbrella des 16 organes ET l'emetteur de
#    commentaires, et l'expression illegale a tue les DEUX -- 6 runs push a
#    zero job, le check-run « Always-on guards -- 16 organes » n'a jamais
#    existe sur la tete. Un fichier par responsabilite limite la panne au
#    coupable ; l'invariant « un seul job par fichier » (test 2 ci-dessus,
#    `list(content) == [CONTENT_JOB]`) etait deja l'epingle, la PR l'avait
#    cassee en ajoutant le deuxieme job.
# 2. Un groupe de concurrence partage entre les deux fichiers laisserait un
#    run de l'un annuler un run de l'autre en pleine execution (les deux se
#    declenchent sur le meme push, `cancel-in-progress: true`) : le fichier
#    demenage porte son PROPRE groupe.


def test_commenters_workflow_has_exactly_one_job():
    """L'invariant « un job par fichier » vaut pour TOUTE la famille
    always-on, pas seulement pour les deux premiers fichiers."""
    assert list(_load(COMMENTERS_WF)["jobs"]) == [COMMENTERS_JOB]


def test_content_workflow_is_back_to_a_single_job():
    """Le demenagement doit etre un DEPLACEMENT : si ce test echoue, le job
    commenters est revenu vivre (ou un troisieme job est ne) dans le fichier
    du umbrella -- retour du rayon d'explosion mesure en #22244."""
    assert list(_load(CONTENT_WF)["jobs"]) == [CONTENT_JOB]


def test_commenters_job_name_is_distinct_from_the_family():
    """Meme premisse que test_job_names_are_distinct : le fold du gate est
    par NOM, trois verdicts exigent trois noms."""
    names = {
        _load(CONTENT_WF)["jobs"][CONTENT_JOB]["name"],
        _load(BODY_WF)["jobs"][BODY_JOB]["name"],
        _load(COMMENTERS_WF)["jobs"][COMMENTERS_JOB]["name"],
    }
    assert len(names) == 3, names


def test_commenters_fires_on_pushes_not_on_edits():
    """Meme declenchement que le job umbrella (`synchronize` : un verdict a
    chaque tete), et PAS `edited` (#22331 : une edition de body ne doit pas
    re-payer un run de file CI -- les stickies sont upsertes au push)."""
    types = _trigger_types(_load(COMMENTERS_WF))
    assert "opened" in types and "synchronize" in types
    assert "edited" not in types


def test_commenters_concurrency_group_is_isolated():
    """Trois groupes distincts : un groupe partage + `cancel-in-progress`
    laisserait le run d'un fichier annuler celui d'un autre fichier en
    pleine execution, les deux etant declenches par le meme push."""
    groups = {
        _load(CONTENT_WF)["concurrency"]["group"],
        _load(BODY_WF)["concurrency"]["group"],
        _load(COMMENTERS_WF)["concurrency"]["group"],
    }
    assert len(groups) == 3, groups
    assert any("always-on-commenters" in g for g in groups), groups


def test_commenters_writes_live_at_job_level_only():
    """Le contrat « l'ecriture est ICI et nulle part ailleurs » (moindre
    privilege) : les droits d'ecriture sont portes par le JOB, pas elargis au
    niveau workflow."""
    doc = _load(COMMENTERS_WF)
    assert doc.get("permissions") == {"contents": "read"}
    job = doc["jobs"][COMMENTERS_JOB]
    assert job["permissions"] == {
        "contents": "read",
        "pull-requests": "write",
        "checks": "write",
    }


def test_no_job_level_env_uses_the_runner_context():
    """LE defaut fondateur (PR #22244) : le contexte `runner` est illégal dans
    un `env:` de niveau workflow comme de niveau job -- GitHub rejette alors
    le fichier ENTIER (mesure : « Unrecognized named-value: 'runner' »,
    6 runs push a zero job). Un `${{ runner.* }}` n'est legal qu'au niveau
    step (env de step, with:, if:). Le scanner parse le YAML : un `runner.`
    dans un COMMENTAIRE n'est pas vu, seul l'etait un vrai defaut."""
    for wf in sorted(WORKFLOWS.glob("*.yml")):
        doc = _load(wf)
        scopes = {"workflow": doc.get("env") or {}}
        for jk, job in (doc.get("jobs") or {}).items():
            if isinstance(job, dict):
                scopes[f"job {jk}"] = job.get("env") or {}
        for scope, env in scopes.items():
            assert isinstance(env, dict)
            for key, val in env.items():
                if isinstance(val, str):
                    assert "runner." not in val, (
                        "%s :: %s :: env %s utilise le contexte runner "
                        "(illegal hors niveau step, fichier rejete en entier)"
                        % (wf.name, scope, key)
                    )


def test_commenters_artifact_uploads_target_the_python_fallback_root():
    """Coherence emetteur/lecteur d'artefacts SANS la variable d'env fautive :
    `fast_lane.py::artifact_root()` retombe sur $RUNNER_TEMP/fast-lane-
    artifacts quand FAST_LANE_ARTIFACT_DIR est absente ; les `path:` des
    uploads doivent cibler la MEME racine (au niveau step, ou l'expression
    `${{ runner.temp }}` est legale)."""
    job = _load(COMMENTERS_WF)["jobs"][COMMENTERS_JOB]
    uploads = [
        s for s in job["steps"]
        if str(s.get("uses", "")).startswith("actions/upload-artifact")
    ]
    assert len(uploads) == 3, "trois artefacts attendus (un par detecteur)"
    for step in uploads:
        path = step["with"]["path"]
        assert path.startswith("${{ runner.temp }}/fast-lane-artifacts/"), path
