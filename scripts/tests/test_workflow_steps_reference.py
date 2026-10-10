#!/usr/bin/env python3
"""Chaque `steps.<id>` cite dans un job y est defini, et sa sortie declaree (#19668).

Classe de defaut
----------------
Une expression `${{ steps.<id>... }}` ne se resout que si le job courant porte
une etape `id: <id>`. GitHub n'echoue **pas** quand l'id est absent : l'expression
vaut la chaine vide. Un job peut donc rester vert en ecrivant une valeur vide --
c'est exactement le defaut releve par la revue ai-01 sur #19668 : dans
`.github/workflows/lean-build.yml`, le job matriciel `ci-matrix` nommait
`steps.lake-cache.outputs.cache-primary-key` alors que l'etape `id: lake-cache`
ne vit que dans le job `ci` et dans la composite `./.github/actions/lean-build`
(appelee sous `id: build`). Sur `main` et sur cache manque, le SAVE du fan-out
matriciel (#13751) recevait une cle vide.

Ce que le garde verifie
-----------------------
1. **Resolution de l'id** -- tout `steps.<id>` cite dans un job y est defini.
2. **Declaration de la sortie** -- quand l'etape portant cet id appelle une
   composite locale (`uses: ./.github/actions/...`), le nom de sortie cite est
   declare dans le bloc `outputs:` de cette composite. Sans (2), le correctif
   naif de (1) deplacerait la chaine vide d'un cran au lieu de la fermer.

Le scanner se valide par ses faux negatifs
------------------------------------------
Un motif de detection ne se valide pas par ses hits : il se valide par les formes
qu'il DOIT attraper. Les controles positifs ci-dessous font donc tourner le
verificateur sur des workflows **synthetiques** fautifs -- id absent, sortie non
declaree, forme collee sans espaces -- et exigent qu'il les denonce. Les
controles suivants l'exigent muet sur les formes legitimes (id defini, job
appelant un reusable sans `steps`), parce qu'un garde qui rougit a tort sera
desactive, et un garde desactive ne garde rien.
"""

import os
import re
import sys

import yaml

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORKFLOWS = os.path.join(REPO, ".github", "workflows")
ACTIONS = os.path.join(REPO, ".github", "actions")

STEPS_REF = re.compile(r"steps\.([A-Za-z0-9_-]+)")
STEPS_OUTPUT_REF = re.compile(r"steps\.([A-Za-z0-9_-]+)\.outputs\.([A-Za-z0-9_-]+)")


def _walk_strings(node):
    """Toutes les chaines d'un sous-arbre YAML, quelle que soit la profondeur.

    La marche est exhaustive a dessein : une reference `steps.*` peut vivre dans
    un `run:`, un `with:`, un `if:` ou un `env:` -- restreindre la lecture a
    `run:` laisserait passer le `key:` qui a fonde ce garde.
    """
    if isinstance(node, str):
        yield node
    elif isinstance(node, dict):
        for value in node.values():
            yield from _walk_strings(value)
    elif isinstance(node, list):
        for value in node:
            yield from _walk_strings(value)


def _steps_of(container):
    return [s for s in (container.get("steps") or []) if isinstance(s, dict)]


def _local_composite_paths(steps):
    """id -> chemin repo-relatif de la composite locale appelee par cette etape."""
    out = {}
    for step in steps:
        uses = step.get("uses")
        if step.get("id") and isinstance(uses, str) and uses.startswith("./"):
            out[step["id"]] = uses
    return out


def composite_outputs(uses_path, repo=REPO):
    """Noms de sortie declares par une composite locale, ou None si illisible."""
    path = os.path.join(repo, uses_path[2:] if uses_path.startswith("./") else uses_path, "action.yml")
    if not os.path.isfile(path):
        return None
    with open(path, encoding="utf-8") as handle:
        doc = yaml.safe_load(handle) or {}
    outputs = doc.get("outputs")
    return set(outputs) if isinstance(outputs, dict) else set()


def check_steps_refs(jobs, composites=None):
    """Rend la liste des references non resolues, une phrase par finding.

    `composites` : chemin de composite -> ensemble des sorties declarees (ou None
    quand inconnu -- un `None` desarme le controle (2) pour ce chemin, jamais le
    controle (1) : un id absent reste denonce meme si la composite est illisible).
    """
    composites = composites or {}
    findings = []
    for job_name, job in (jobs or {}).items():
        if not isinstance(job, dict):
            continue
        steps = _steps_of(job)
        defined = {s["id"] for s in steps if s.get("id")}
        local = _local_composite_paths(steps)
        for text in _walk_strings(job):
            for step_id in STEPS_REF.findall(text):
                if step_id not in defined:
                    findings.append(
                        f"job '{job_name}': 'steps.{step_id}' est cite mais aucune etape "
                        f"du job ne porte 'id: {step_id}'")
            for step_id, out_name in STEPS_OUTPUT_REF.findall(text):
                uses_path = local.get(step_id)
                if uses_path is None:
                    continue
                declared = composites.get(uses_path)
                if declared is not None and out_name not in declared:
                    findings.append(
                        f"job '{job_name}': 'steps.{step_id}.outputs.{out_name}' -- la composite "
                        f"'{uses_path}' ne declare pas cette sortie")
    return findings


def _iter_repo_units(repo=REPO):
    """(etiquette, jobs, composites) pour chaque workflow et action du depot."""
    composites = {}
    names = []
    wf_dir = os.path.join(repo, ".github", "workflows")
    if os.path.isdir(wf_dir):
        for name in sorted(os.listdir(wf_dir)):
            if name.endswith((".yml", ".yaml")):
                names.append((f"workflow:{name}", os.path.join(wf_dir, name)))
    act_dir = os.path.join(repo, ".github", "actions")
    if os.path.isdir(act_dir):
        for name in sorted(os.listdir(act_dir)):
            path = os.path.join(act_dir, name, "action.yml")
            if os.path.isfile(path):
                names.append((f"action:{name}", path))
                composites[f"./.github/actions/{name}"] = (
                    set((yaml.safe_load(open(path, encoding="utf-8")) or {}).get("outputs") or {}))
    for label, path in names:
        with open(path, encoding="utf-8") as handle:
            doc = yaml.safe_load(handle) or {}
        jobs = doc.get("jobs")
        if jobs is None and isinstance(doc.get("runs"), dict):
            jobs = {f"{label}:runs": doc["runs"]}
        yield label, jobs, composites


def test_no_unresolved_steps_reference_in_repo():
    findings = []
    for label, jobs, composites in _iter_repo_units():
        findings += [f"{label}: {f}" for f in check_steps_refs(jobs, composites)]
    assert findings == [], "references steps.* non resolues :\n  " + "\n  ".join(findings)


def test_lean_matrix_save_names_the_composite_key_not_a_foreign_id():
    """Controle de non-regression sur le defaut fondateur (#19668).

    Le job matriciel doit nommer la cle via l'id qu'il definit vraiment (`build`),
    jamais via `lake-cache`, qui appartient au job `ci`.
    """
    with open(os.path.join(WORKFLOWS, "lean-build.yml"), encoding="utf-8") as handle:
        doc = yaml.safe_load(handle)
    jobs = doc["jobs"]
    assert "lake-cache" not in {s["id"] for s in _steps_of(jobs["ci-matrix"]) if s.get("id")}
    key_lines = [s for s in _steps_of(jobs["ci-matrix"])
                 if "cache/save" in str(s.get("uses", ""))
                 and "Save Lake build artifacts" in str(s.get("name", ""))]
    assert len(key_lines) == 1, f"attendu 1 etape de SAVE, trouve {len(key_lines)}"
    assert key_lines[0]["with"]["key"] == "${{ steps.build.outputs.lake-cache-key }}"


# --- Controles positifs : le detecteur DOIT denoncer ces formes fautives ------

_SYNTH_DANGLING_ID = """
on: push
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - id: compile
        run: echo hi
      - run: echo "${{ steps.ghost.outputs.key }}"
"""

_SYNTH_DANGLING_ID_GLUED = """
on: push
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - id: compile
        run: echo hi
      - run: echo "${{steps.ghost.outcome}}"
"""

_SYNTH_UNDECLARED_OUTPUT = """
on: push
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - id: build
        uses: ./.github/actions/lean-build
      - run: echo "${{ steps.build.outputs.inexistante }}"
"""

_SYNTH_OK = """
on: push
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - id: compile
        run: echo hi
      - run: echo "${{ steps.compile.outputs.key }}"
"""


def test_detector_catches_undefined_id():
    findings = check_steps_refs(yaml.safe_load(_SYNTH_DANGLING_ID)["jobs"])
    assert any("steps.ghost" in f for f in findings), findings


def test_detector_catches_glued_form_without_spaces():
    findings = check_steps_refs(yaml.safe_load(_SYNTH_DANGLING_ID_GLUED)["jobs"])
    assert any("steps.ghost" in f for f in findings), findings


def test_detector_catches_undeclared_composite_output():
    findings = check_steps_refs(
        yaml.safe_load(_SYNTH_UNDECLARED_OUTPUT)["jobs"],
        {"./.github/actions/lean-build": {"lake-cache-hit", "lake-cache-key"}},
    )
    assert any("inexistante" in f for f in findings), findings


def test_detector_is_silent_on_a_defined_id():
    assert check_steps_refs(yaml.safe_load(_SYNTH_OK)["jobs"]) == []


def test_detector_ignores_a_reusable_call_job_without_steps():
    jobs = {"ci": {"uses": "./.github/workflows/lean-build.yml"}}
    assert check_steps_refs(jobs) == []


def test_detector_still_flags_a_missing_id_when_composite_is_unreadable():
    """Le controle (1) ne depend pas de la lisibilite de la composite."""
    findings = check_steps_refs(yaml.safe_load(_SYNTH_DANGLING_ID)["jobs"], {})
    assert any("steps.ghost" in f for f in findings), findings


if __name__ == "__main__":
    _findings = [f"{label}: {f}"
                 for label, jobs, comps in _iter_repo_units()
                 for f in check_steps_refs(jobs, comps)]
    for _line in _findings:
        print(_line)
    sys.exit(1 if _findings else 0)
