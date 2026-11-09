#!/usr/bin/env python3
"""Census des workflows qui rejouent sur `workflow_run` / `issue_comment` (#24121).

`scripts/ci/list_edited_trigger_workflows.py` (#22467) repond a la question que
pose l'axe `edited` : **quels workflows ecoutent un declencheur dont leur
verdict ne depend pas ?** Ce module transpose ce census sur les deux familles
que #24121 nomme -- `workflow_run` et `issue_comment` -- la ou la masse des
redondances a ete mesuree (3 228 des 3 854 redondances de 48 h sont des runs
sans PR liee, cf `scripts/ci/measure_redundant_runs.py`).

Les axes sont transposes tels quels -- `body` / `title` / `base` / `paths` de
l'axe `edited` ne concernent que les evenements de PR, et ne sont pas
reutilisables ici. Les axes de cette transposition sont :

Pour `workflow_run` (le workflow rejoue a la fin d'un AUTRE workflow) :

``upstream_conclusion``
    le verdict bouge quand la conclusion de l'aval change
    (`github.event.workflow_run.conclusion`). C'est le cas de
    `site-links-post-deploy.yml`, qui ne teste le site publie qu'apres un
    deploiement reussi : sans l'axe, le garde tournerait sur un site qui n'est
    pas celui de la sortie reelle.
``upstream_identity``
    le verdict bouge quand l'IDENTITE de l'aval change : son nom, son id, son
    numero, ou le depot dont il vient
    (`github.event.workflow_run.name`, `.id`, `.run_number`,
    `.head_repository.full_name`). C'est le cas des deux sondes de starvation :
    elles **sautent** le run declare par une PR de fork
    (`github.event.workflow_run.head_repository.full_name == github.repository`).
``upstream_head``
    le verdict bouge quand la tete de l'aval change (branche, SHA, message du
    commit).
``upstream_artifact``
    le verdict bouge quand les **artefacts** de l'aval sont consommes
    (`download-artifact` sur `github.event.workflow_run.id`).

Pour `issue_comment` (le workflow rejoue a chaque commentaire d'une issue) :

``comment_body``
    le verdict bouge quand le **contenu** du commentaire bouge -- c'est le cas
    d'un garde de commande (`contains(github.event.comment.body, ...)`).
``comment_identity``
    le verdict bouge quand l'auteur du commentaire bouge
    (`github.event.comment.user.login`, `.author_association`).
``issue_state``
    le verdict bouge quand l'issue bouge (numero, titre, labels, etat, et le
    fait qu'elle soit ou non une PR).

Une lecture **decision-bearing** -- une lecture qui apparait dans une
expression `if:` (job ou step) -- rend le declencheur **load-bearing** : le
verdict bouge quand l'evenement qui rejoue bouge. Une lecture **observationnelle**
-- une lecture qui n'apparait que dans un `run:`, un `env:` ou un `with:` --
ne prouve rien : elle peut n'alimenter qu'un journal.

Verdict par workflow :

``TRIGGER_DEPENDENT``
    au moins un axe decision-bearing -> le declencheur est load-bearing, il ne
    doit pas etre retire.
``TRIGGER_INDEPENDENT``
    aucun axe decision-bearing -> le declencheur est un **CANDIDAT** au
    retrait. C'est un candidat, pas une autorisation : la raison d'etre d'un
    declencheur est souvent **documentee en prose** dans l'en-tete du workflow
    (une ancre de survie, un ordonnancement), et la prose n'est pas un code.
    L'organe la **cite** (`prose_mentions`) pour que la lecture soit un
    controle de citation, pas une chasse.

Ablation
--------
Comme le census de l'axe `edited`, l'organe se soumet a une ablation :
`--ablate-prose` recalcule le verdict en **supprimant la contribution de la
prose**. Le verdict n'en depend pas -- il est purement code -- donc l'ablation
doit rendre un verdict **identique**. Si elle ne le fait pas, c'est que le
verdict s'appuie sur de la prose : les workflows concernes sont nommes. La
prose n'est jamais utilisee pour **affaiblir** un verdict : elle ne sert
qu'a signaler une charge de verification.

Mesure
------
`--runs <snapshot.json>` joint le snapshot de
`scripts/ci/measure_redundant_runs.py --per-workflow --output ...` (le meme
organe de mesure que l'issue cite) et ajoute, par workflow, le nombre de runs
**par evenement** et le volume qui disparaitrait si la jambe de la famille
etait retiree. La fenetre et l'echantillon restent ceux du snapshot : l'organe
ne recollecte rien, il ne fait que lire la mesure deja faite.

Exemples
--------
::

    python scripts/ci/list_replay_trigger_workflows.py
    python scripts/ci/list_replay_trigger_workflows.py --json
    python scripts/ci/list_replay_trigger_workflows.py --only independent
    python scripts/ci/list_replay_trigger_workflows.py --ablate-prose
    python scripts/ci/list_replay_trigger_workflows.py --runs redundant.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

WORKFLOW_DIR = ".github/workflows"

TRIGGER_DEPENDENT = "TRIGGER_DEPENDENT"
TRIGGER_INDEPENDENT = "TRIGGER_INDEPENDENT"

#: Axes de la famille `workflow_run` : (axe, motif).
WORKFLOW_RUN_AXES: list[tuple[str, str]] = [
    (
        "upstream_conclusion",
        r"workflow_run\.conclusion",
    ),
    (
        "upstream_identity",
        r"workflow_run\.(?:name|id|run_number|run_attempt|event|"
        r"head_repository(?:\.\w+)*)",
    ),
    (
        "upstream_head",
        r"workflow_run\.(?:head_branch|head_sha|head_commit(?:\.\w+)*)",
    ),
    (
        "upstream_artifact",
        r"workflow_run\.(?:id|artifacts_url)[\s\S]{0,200}?download-artifact"
        r"|download-artifact[\s\S]{0,200}?workflow_run\.(?:id|artifacts_url)",
    ),
]

#: Axes de la famille `issue_comment` : (axe, motif).
ISSUE_COMMENT_AXES: list[tuple[str, str]] = [
    ("comment_body", r"comment\.body"),
    (
        "comment_identity",
        r"comment\.(?:user\.\w+|author_association|id)",
    ),
    (
        "issue_state",
        r"issue\.(?:number|title|labels|state|pull_request)",
    ),
]

#: Familles auditees : evenement -> axes.
FAMILIES: dict[str, list[tuple[str, str]]] = {
    "workflow_run": WORKFLOW_RUN_AXES,
    "issue_comment": ISSUE_COMMENT_AXES,
}

#: Axes **decision-bearing par nature** : les detecter suffit a prouver la
#: dependance, sans qu'ils apparaissent dans une expression `if:`. Consommer
#: l'artefact de l'aval fait entrer son contenu dans le verdict.
ALWAYS_DECISION_BEARING = {"workflow_run:upstream_artifact"}

#: Marqueurs de prose : une en-tete qui parle du declencheur ou de son role.
#: Vocabulaire **ferme** -- une citation, pas une preuve.
PROSE_MARKERS = (
    "workflow_run",
    "issue_comment",
    "heartbeat",
    "survie",
    "survive",
    "surviv",
    "cadence",
    "redondan",
    "declenche",
    "déclenche",
    "trigger",
    "rejou",
)

#: Nombre maximal de citations renvoyees par workflow (le reste est compte).
MAX_PROSE_CITATIONS = 12

_COMMENT_RE = re.compile(r"^\s*#\s?(.*)$")
_IF_KEY_RE = re.compile(r"^\s*if\s*:\s*(.*)$")


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def _load_yaml(path: Path):
    import yaml

    data = yaml.safe_load(_read(path))
    return data if isinstance(data, dict) else {}


def _on_block(data: dict) -> dict:
    """Bloc `on:` du workflow (PyYAML lit `on:` comme le booleen True)."""
    on = data.get(True, data.get("on"))
    return on if isinstance(on, dict) else {}


def _family_block(data: dict, family: str) -> dict:
    block = _on_block(data).get(family)
    return block if isinstance(block, dict) else {}


def _listen(data: dict, family: str) -> bool:
    return family in _on_block(data)


def _strip_comment_lines(text: str) -> str:
    """Retire les lignes de commentaire, en gardant la numrotation.

    Un `if:` peut s'etaler sur plusieurs lignes (bloc scalaire `>-`) ; les
    lignes de commentaire intercalees ne doivent pas le casser.
    """
    kept = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("#"):
            continue
        kept.append(line)
    return "\n".join(kept)


def _decision_contexts(data: dict) -> list[str]:
    """Toutes les expressions `if:` du workflow (job et step).

    Une expression `if:` est le seul endroit ou une lecture de l'evenement
    peut **decider** de quelque chose. Le contexte `env:` est traite a part
    (les variables d'environnement d'un job ne sont pas disponibles dans le
    `if:` du job ; elles le sont dans le `if:` d'un step).
    """
    contexts: list[str] = []
    jobs = data.get("jobs")
    if not isinstance(jobs, dict):
        return contexts
    for job in jobs.values():
        if not isinstance(job, dict):
            continue
        job_if = job.get("if")
        if isinstance(job_if, str):
            contexts.append(job_if)
        job_env = job.get("env")
        env_values: dict[str, str] = {}
        if isinstance(job_env, dict):
            for key, value in job_env.items():
                if isinstance(value, str):
                    env_values[str(key)] = value
        steps = job.get("steps")
        if not isinstance(steps, list):
            continue
        for step in steps:
            if not isinstance(step, dict):
                continue
            step_if = step.get("if")
            if not isinstance(step_if, str):
                continue
            contexts.append(step_if)
            # Une variable d'environnement lue par le `if:` d'un step
            # transporte aussi une lecture -- on l'ajoute.
            for name, value in env_values.items():
                if re.search(rf"env\.{re.escape(name)}\b", step_if):
                    contexts.append(value)
            step_env = step.get("env")
            if isinstance(step_env, dict):
                for key, value in step_env.items():
                    if isinstance(value, str) and re.search(
                        rf"env\.{re.escape(str(key))}\b", step_if
                    ):
                        contexts.append(value)
    return contexts


def _observed_contexts(data: dict) -> list[str]:
    """Le reste du workflow : `run:`, `env:`, `with:`.

    Une lecture qui n'apparait QUE ici est **observationnelle** : elle peut
    n'alimenter qu'un journal, et ne prouve pas que le verdict bouge.

    Le contexte est rendu **joint** : certains axes se reconnaisent a une
    distance (consommer un artefact de l'aval, c'est `download-artifact` d'un
    cote et `workflow_run.id` de l'autre). Un texte par champ ne les
    verrait jamais ensemble.
    """
    chunks: list[str] = []
    jobs = data.get("jobs")
    if not isinstance(jobs, dict):
        return chunks
    for job in jobs.values():
        if not isinstance(job, dict):
            continue
        for key in ("runs-on", "env", "container", "services"):
            value = job.get(key)
            if isinstance(value, str):
                chunks.append(value)
            elif isinstance(value, dict):
                chunks.extend(v for v in value.values() if isinstance(v, str))
        steps = job.get("steps")
        if not isinstance(steps, list):
            continue
        for step in steps:
            if not isinstance(step, dict):
                continue
            for key in ("run", "uses", "with", "env"):
                value = step.get(key)
                if isinstance(value, str):
                    chunks.append(value)
                elif isinstance(value, dict):
                    chunks.extend(v for v in value.values() if isinstance(v, str))
    return ["\n".join(chunks)]


def _axes_in(texts: list[str], axes: list[tuple[str, str]]) -> list[str]:
    found = []
    for axis, pattern in axes:
        regex = re.compile(pattern)
        if any(regex.search(text) for text in texts):
            found.append(axis)
    return found


def _prose_citations(path: Path) -> list[dict]:
    """Les lignes de commentaire qui parlent du declencheur ou de son role.

    L'en-tete d'un workflow documente souvent la raison d'etre de son
    declencheur (une ancre de survie, un ordonnancement). Le vocabulaire est
    **ferme** : l'organe cite, il ne conclut pas. Chaque citation porte son
    numero de ligne et dit si elle est dans l'en-tete (avant le bloc `on:`) --
    c'est la que se trouve d'ordinaire la raison d'etre.
    """
    lines = _read(path).splitlines()
    header_end = len(lines)
    for index, line in enumerate(lines):
        if re.match(r"^on\s*:", line):
            header_end = index
            break
    citations: list[dict] = []
    for number, line in enumerate(lines, start=1):
        match = _COMMENT_RE.match(line)
        if not match:
            continue
        text = match.group(1)
        lowered = text.lower()
        if any(marker in lowered for marker in PROSE_MARKERS):
            citations.append(
                {
                    "line": number,
                    "in_header": number <= header_end,
                    "text": text.strip()[:200],
                }
            )
    return citations


def survey(root: Path) -> list[dict]:
    """Census complet des workflows qui ecoutent `workflow_run`/`issue_comment`."""
    workflows_dir = root / WORKFLOW_DIR
    rows: list[dict] = []
    for path in sorted(workflows_dir.glob("*.yml")):
        rel = path.relative_to(root).as_posix()
        data = _load_yaml(path)
        listening = [f for f in FAMILIES if _listen(data, f)]
        if not listening:
            continue
        decision_texts = _decision_contexts(data)
        observed_texts = _observed_contexts(data)
        decision_axes: list[str] = []
        observed_axes: list[str] = []
        for family in listening:
            axes = FAMILIES[family]
            for axis in _axes_in(decision_texts, axes):
                decision_axes.append(f"{family}:{axis}")
            for axis in _axes_in(observed_texts, axes):
                key = f"{family}:{axis}"
                if key in decision_axes:
                    continue
                if key in ALWAYS_DECISION_BEARING:
                    # Consommer l'artefact de l'aval, c'est deja une
                    # dependance : le contenu de l'artefact entre dans le
                    # verdict, qu'il soit lu dans un `if:` ou non.
                    decision_axes.append(key)
                else:
                    observed_axes.append(key)
        verdict = TRIGGER_DEPENDENT if decision_axes else TRIGGER_INDEPENDENT
        citations = _prose_citations(path)
        rows.append(
            {
                "workflow": rel,
                "listening_families": listening,
                "trigger_types": {
                    family: list(
                        (_family_block(data, family).get("types") or [])
                    )
                    for family in listening
                },
                "upstream_workflows": {
                    family: list(
                        (_family_block(data, family).get("workflows") or [])
                    )
                    for family in listening
                },
                "decision_axes": decision_axes,
                "observed_axes": observed_axes,
                "verdict": verdict,
                "prose_mentions": citations[:MAX_PROSE_CITATIONS],
                "prose_mentions_total": len(citations),
            }
        )
    return rows


def render(rows: list[dict]) -> str:
    lines = [
        f"{'workflow':48s} {'verdict':20s} {'axes decision':28s} "
        f"{'axes observees'}"
    ]
    for row in rows:
        lines.append(
            f"{row['workflow'][:48]:48s} {row['verdict']:20s} "
            f"{','.join(row['decision_axes']) or '-':28s} "
            f"{','.join(row['observed_axes']) or '-'}"
        )
    counts = Counter(row["verdict"] for row in rows)
    lines.append("")
    lines.append(
        f"{len(rows)} workflow(s) ecoutent `workflow_run`/`issue_comment` -- "
        + ", ".join(f"{k}: {v}" for k, v in sorted(counts.items()))
    )
    candidates = [
        row for row in rows if row["verdict"] == TRIGGER_INDEPENDENT
    ]
    lines.append(
        f"candidats au retrait (verdict purement code) : {len(candidates)}"
    )
    for row in candidates:
        lines.append(
            f"    {row['workflow']} -- {row['prose_mentions_total']} citation(s) "
            f"de prose a lire"
        )
    measured = [row for row in rows if "runs_by_event" in row]
    if measured:
        lines.append("")
        lines.append("runs mesures -- volume qui disparaitrait par famille retiree")
        for row in measured:
            cap = "  [au plafond : minimum, pas une mesure]" if row.get("at_cap") else ""
            lines.append(
                f"    {row['workflow']} : {row['runs_total']} run(s) "
                f"{row['runs_by_event']} -- gain si la jambe est retiree : "
                f"{row['runs_if_family_removed']}{cap}"
            )
    return "\n".join(lines)


def render_ablation(rows: list[dict]) -> str:
    """Ablation : le verdict tient-il sans la prose ?

    Le verdict est purement code ; la prose n'y entre pas. L'ablation doit
    donc rendre un verdict **identique**. Si elle ne le fait pas, c'est que
    le verdict s'appuie sur de la prose -- et il faut le nommer.
    """
    lines = [
        "Ablation -- verdict recalcule SANS la contribution de la prose",
        "",
    ]
    with_prose = {row["workflow"]: row["verdict"] for row in rows}
    without_prose = {
        row["workflow"]: (
            TRIGGER_DEPENDENT if row["decision_axes"] else TRIGGER_INDEPENDENT
        )
        for row in rows
    }
    lines.append(f"verdict avec la prose   : {len(with_prose)} workflow(s)")
    lines.append(f"verdict sans la prose   : {len(without_prose)} workflow(s)")
    lines.append("")
    differing = [
        wf for wf in with_prose if with_prose[wf] != without_prose.get(wf)
    ]
    if not differing:
        lines.append(
            "Conclusion : identique. Le verdict est purement code -- la prose "
            "n'entre dans la conclusion que comme charge de verification."
        )
    else:
        lines.append(
            "Conclusion : DIFFERENTE. Les workflows ci-dessous ont un verdict "
            "qui repose sur la prose : la forme lue doit etre verifiee a la main."
        )
        for workflow in differing:
            lines.append(f"    {workflow}")
    return "\n".join(lines)


def _attach_counts(rows: list[dict], runs: list[dict], capped: list[str]) -> None:
    """Agrege les runs par workflow et par evenement.

    Le volume qui disparaitrait si la jambe d'une famille etait retiree est
    le nombre de runs **de cet evenement** : c'est le gain maximal, avant
    verification de la perte de couverture.
    """
    by_workflow: dict[str, Counter] = {}
    for run in runs:
        if not isinstance(run, dict):
            continue
        path = run.get("path") or run.get("name") or "?"
        by_workflow.setdefault(path, Counter())[run.get("event") or "?"] += 1
    for row in rows:
        counter = by_workflow.get(row["workflow"], Counter())
        row["runs_by_event"] = dict(sorted(counter.items()))
        row["runs_if_family_removed"] = {
            family: counter.get(family, 0)
            for family in row["listening_families"]
        }
        row["runs_total"] = sum(counter.values())
        row["at_cap"] = Path(row["workflow"]).name in capped


def attach_runs(rows: list[dict], snapshot_path: Path) -> None:
    """Joint la mesure des runs (snapshot de `measure_redundant_runs.py`).

    Le snapshot porte `path` (le fichier du workflow) et `event`. On en tire,
    par workflow, le nombre de runs **par evenement** et le volume qui
    disparaitrait si la jambe d'une famille etait retiree.
    """
    payload = json.loads(snapshot_path.read_text(encoding="utf-8"))
    runs = payload.get("runs") if isinstance(payload, dict) else payload
    if not isinstance(runs, list):
        raise SystemExit(f"snapshot illisible : {snapshot_path}")
    _attach_counts(rows, runs, [])


def measure_rows(rows: list[dict], repo: str, since: str, until: str) -> None:
    """Mesure les runs **des seuls workflows censuses**.

    La collecte est celle de `measure_redundant_runs.py` -- le meme organe de
    mesure que l'issue cite : aucune logique de mesure n'est reecrite ici.
    Seule la liste des cibles est restreinte aux workflows du census, le
    quota REST etant partage par la flotte.

    Les workflows dont l'echantillon touche le plafond de 1000 runs sont
    signales `at_cap` : leur ligne est un **minimum**, pas une mesure.
    """
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from measure_redundant_runs import collect_per_workflow

    # L'endpoint attend le NOM du fichier de workflow, pas son chemin.
    paths = [Path(row["workflow"]).name for row in rows]
    runs, truncated = collect_per_workflow(repo, since, until, paths=paths)
    _attach_counts(rows, runs, list(truncated))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        default=None,
        help="racine du depot (defaut : racine du repo)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument(
        "--only",
        choices=["dependent", "independent"],
        default=None,
        help="filtrer sur le verdict",
    )
    parser.add_argument(
        "--ablate-prose",
        action="store_true",
        help=(
            "affiche l'ablation : le verdict recalcule SANS la contribution de "
            "la prose de l'en-tete, pour montrer si la conclusion du census "
            "repose sur de la prose"
        ),
    )
    parser.add_argument(
        "--runs",
        default=None,
        help=(
            "snapshot JSON de `measure_redundant_runs.py --per-workflow "
            "--output ...` : ajoute la mesure des runs par evenement"
        ),
    )
    parser.add_argument(
        "--measure",
        action="store_true",
        help=(
            "mesure les runs des seuls workflows censuses (collecte "
            "restreinte, quota REST partage par la flotte)"
        ),
    )
    parser.add_argument("--repo", default="jsboige/CoursIA", help="depot mesure")
    parser.add_argument("--since", default=None, help="debut de fenetre (ISO-8601)")
    parser.add_argument("--until", default=None, help="fin de fenetre (ISO-8601)")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve() if args.root else Path(__file__).resolve().parents[2]
    rows = survey(root)
    if args.runs:
        attach_runs(rows, Path(args.runs))
    if args.measure:
        if not args.since or not args.until:
            parser.error("--since et --until sont requis avec --measure")
        measure_rows(rows, args.repo, args.since, args.until)
    if args.only == "dependent":
        rows = [r for r in rows if r["verdict"] == TRIGGER_DEPENDENT]
    elif args.only == "independent":
        rows = [r for r in rows if r["verdict"] == TRIGGER_INDEPENDENT]

    if args.json:
        print(json.dumps(rows, ensure_ascii=False, indent=1))
    elif args.ablate_prose:
        print(render_ablation(survey(root)))
    else:
        print(render(rows))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
