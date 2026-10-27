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
ORGANS = REPO_ROOT / "scripts" / "ci" / "always_on_body_organs.sh"
PR_GATE = REPO_ROOT / "scripts" / "pr_gate.py"

CONTENT_JOB = "always-on-guards"
BODY_JOB = "always-on-guards-body"
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
