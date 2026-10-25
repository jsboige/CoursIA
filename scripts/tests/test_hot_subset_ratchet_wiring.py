#!/usr/bin/env python3
"""Tests for the hot-subset ratchet wiring in always-on-guards.yml (#15196).

Issue #15196 (5e occurrence du motif #10416 -- un garde aveugle a son
SUJET) : le cliquet hot-subset de traduction (#13551) vit dans
scripts/translation/tests/test_hot_subset_ratchet.py et se declenchait via
scripts-tests.yml, dont le `pull_request` est filtre par
`paths: [scripts/**, tests/**, ...]`. Or la SOURCE qui fait deriver une
ligne CSV (`SRC_DRIFT`) est un edit de notebook sous
`MyIA.AI.Notebooks/**` -- EXACTEMENT hors de ce filtre. Le cliquet ne
tournait donc jamais sur la PR qui pouvait le casser : son sujet etait
hors de son declencheur.

La correction (Option B) absorbe le cliquet comme organe de
always-on-guards.yml, un workflow WITHOUT filtre `paths:` sur son
declencheur (invariant de canary bloquante, cf en-tete du fichier +
regle 2 d'#10045 + #13232). Sa surface nominale est TOUTES les PR : il ne
peut pas etre aveugle au sujet du cliquet.

Ce test epingle la correspondance sujet <-> declencheur. Il ne execute pas
le workflow -- il parse le YAML et verifie :

  (1) le trigger `pull_request` n'a PAS de filtre `paths:` (couverture
      structurelle de `MyIA.AI.Notebooks/**`) et couvre `synchronize`
      (l'edit de notebook pousse sur une PR ouverte) ;
  (2) le workflow invoque bien le cliquet (`id: hot_subset` + le chemin du
      fichier de test) ;
  (3) l'etape AGREGAT collecte `check hot_subset ...` (sans cela, un rouge
      du ratchet ne rougirait jamais le job = la cecite de #15196 sous un
      autre costume).
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
ALWAYS_ON = REPO_ROOT / ".github" / "workflows" / "always-on-guards.yml"

RATCHET_TEST_REL = "scripts/translation/tests/test_hot_subset_ratchet.py"


def _yaml_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _extract_pull_request_block(yaml_text: str) -> str:
    """Lines of the `on: pull_request:` block, down to the next sibling key.

    Stops at the first line indented to exactly the key level (2 spaces) or a
    top-level comment at that level -- those are the `on:` siblings. Comments
    THAT ARE DIRECT CHILDREN of `pull_request:` (4-space indented) are part of
    the block and are kept, but they only mention ``paths:`` in prose and are
    correctly ignored by the real-key regex below.
    """
    lines = yaml_text.splitlines()
    out: list[str] = []
    in_block = False
    for line in lines:
        if not in_block:
            if re.match(r"^\s*pull_request:\s*$", line):
                in_block = True
                out.append(line)
            continue
        # Sibling key or top-level comment at key indentation (2 spaces).
        if re.match(r"^  \S", line):
            break
        out.append(line)
    return "\n".join(out)


def _has_real_paths_key(block: str) -> bool:
    """A yaml `paths: <value>` key (not ``paths`` mentioned in a comment)."""
    return re.search(r"^[ \t]+paths:[ \t]*(%.*)?$", block, re.MULTILINE) is not None


# ---------------------------------------------------------------------------
# (1) The `pull_request` trigger covers the ratchet's subject structurally.
# ---------------------------------------------------------------------------


def test_always_on_workflow_exists() -> None:
    """The fused always-on workflow must exist -- the organ rides it."""
    assert ALWAYS_ON.is_file(), (
        f"{ALWAYS_ON} introuvable -- le workflow fusionne (#13384) a-t-il "
        f"ete retire ? L'organe hot-subset (#15196) vivrait sur rien."
    )


def test_pull_request_trigger_has_no_paths_filter() -> None:
    """The `pull_request` trigger must NOT carry a `paths:` filter.

    always-on-guards.yml est la canary bloquante (en-tete du fichier +
    pr-gate.yml) : elle doit rendre un verdict sur TOUTE PR, y compris celles
    qui ne declenchent aucun autre CI. Un filtre `paths:` la desarmerait sur
    les PR hors-scope (#13232) -- et pour le cliquet hot-subset, un edit de
    notebook (`MyIA.AI.Notebooks/**`, le SUJET du cliquet) sortirait du filtre,
    rendant le cliquet aveugle comme sous scripts-tests.yml (#15196).
    """
    text = _yaml_text(ALWAYS_ON)
    trigger = _extract_pull_request_block(text)
    assert not _has_real_paths_key(trigger), (
        "always-on-guards.yml `pull_request:` porte un filtre `paths:` :\n"
        f"{trigger}\nRegle 2 d'#10045 + #13232 : un garde filtre par chemins "
        f"reste `pending` / est desarme sur les PR hors-scope. Retire-le -- "
        f"c'est precisement la cecite que #15196 corrige."
    )


def test_pull_request_trigger_covers_synchronize() -> None:
    """The trigger must include `synchronize` (the notebook-edit push).

    L'espece de PR qui fait deriver une ligne CSV est un edit de notebook
    pousse sur une PR deja ouverte -> `synchronize`. Sans ce type, le cliquet
    ne tournerait pas au moment ou il sert.
    """
    text = _yaml_text(ALWAYS_ON)
    trigger = _extract_pull_request_block(text)
    assert "synchronize" in trigger, (
        f"Le trigger `pull_request:` doit couvrir `synchronize` (edit de "
        f"notebook pousse sur PR ouverte) :\n{trigger}"
    )


# ---------------------------------------------------------------------------
# (2) The workflow invokes the hot-subset ratchet as an organ.
# ---------------------------------------------------------------------------


def test_workflow_invokes_hot_subset_ratchet() -> None:
    """always-on-guards.yml doit executer le cliquet hot-subset."""
    text = _yaml_text(ALWAYS_ON)
    assert "id: hot_subset" in text, (
        "Organe hot_subset manquant : always-on-guards.yml doit porter une "
        "etape avec `id: hot_subset` (l'agregat la collecte)."
    )
    assert RATCHET_TEST_REL in text, (
        f"L'organe hot_subset doit invoquer le cliquet "
        f"`python -m pytest {RATCHET_TEST_REL}`."
    )


def test_hot_subset_is_blocking_organ() -> None:
    """L'organe doit etre bloquant : `continue-on-error: true` + `exit 1`."""
    text = _yaml_text(ALWAYS_ON)
    id_match = re.search(
        r'(?ms)^\s*- name:.*\n\s*id: hot_subset\n((?:\s+.*\n?)+)', text
    )
    assert id_match is not None, "id: hot_subset introuvable."
    step = id_match.group(1)
    assert "continue-on-error: true" in step, (
        "L'organe hot_subset doit porter `continue-on-error: true` (l'etape "
        "veut rougir AU TRAVERS de l'agregat, pas arreter les organes "
        "suivants)."
    )
    assert "exit 1" in step, (
        "L'organe hot_subset doit `exit 1` quand le ratchet echoue (sinon "
        "l'echec est avale)."
    )


# ---------------------------------------------------------------------------
# (3) The aggregate collects the ratchet's outcome.
# ---------------------------------------------------------------------------


def test_aggregate_collects_hot_subset() -> None:
    """L'etape AGREGAT doit collecter `check hot_subset ...`.

    Sans cette ligne, un rouge du ratchet ne rougirait jamais le job -- le
    cliquet passerait en silence = la cecite de #15196, mais en plus silencieux.
    """
    text = _yaml_text(ALWAYS_ON)
    assert "check hot_subset" in text and "steps.hot_subset.outcome" in text, (
        "L'etape AGREGAT doit collecter `check hot_subset \"${{ "
        "steps.hot_subset.outcome }}\"`. (Les outcomes sont injectes au "
        "templating du workflow, chaque organe est enumere explicitement.)"
    )


# ---------------------------------------------------------------------------
# (4) #22435 -- un code retour de pytest n'est pas un verdict de contenu.
#
# Le corps de l'etape traduisait tout rc non nul en « SRC_DRIFT » : un rc 2
# (collecte interrompue, `ImportError` du toolcache) imprimait un verdict de
# derive de traduction alors que la mesure n'avait pas eu lieu. Mesure du
# 25/10 : #22130 et #22264, ratchet pourtant vert sur leur tete exacte.
#
# Ces tests EXECUTENT le corps de l'etape (stubbe : pas de pytest, pas de
# reseau) au lieu de lire sa prose -- le defaut etait precisement que le
# shell disait autre chose que ce qu'il mesurait. Un test de texte n'aurait
# pas vu la difference entre « ecrit NON MESURE » et « sort en 0 ».
# ---------------------------------------------------------------------------

PYTEST_LINE = (
    "python -m pytest scripts/translation/tests/test_hot_subset_ratchet.py "
    "-q && RC=0 || RC=$?"
)
DIFF_LINE = (
    'git diff --name-only "origin/${BASE}...HEAD" '
    "> /tmp/hot_subset_diff.txt 2>/dev/null"
)

BASH = shutil.which("bash")


def _hot_subset_run_body() -> str:
    """Corps `run: |` de l'etape hot_subset, dedente (indentation retiree)."""
    lines = _yaml_text(ALWAYS_ON).splitlines()
    start = None
    for i, line in enumerate(lines):
        if re.match(r"^\s*id: hot_subset\s*$", line):
            start = i
            break
    assert start is not None, "id: hot_subset introuvable."
    run_at = None
    for i in range(start, min(start + 40, len(lines))):
        m = re.match(r"^(\s*)run: \|\s*$", lines[i])
        if m:
            run_at, indent = i, len(m.group(1))
            break
    assert run_at is not None, "corps `run: |` de hot_subset introuvable."
    body: list[str] = []
    for line in lines[run_at + 1:]:
        if not line.strip():
            body.append("")
            continue
        cur = len(line) - len(line.lstrip())
        if cur <= indent:
            break
        body.append(line[indent + 2:])
    return "\n".join(body) + "\n"


def _run_step(rc: int, changed: list[str] | None):
    """Execute le corps de l'etape avec un rc de pytest impose.

    ``changed`` = chemins du diff simule ; ``None`` = diff illisible.
    """
    body = _hot_subset_run_body()
    for needle in ("pip install --quiet pytest", PYTEST_LINE, DIFF_LINE):
        assert needle in body, (
            f"Le corps de l'etape ne contient plus `{needle}` : adapter ce "
            f"test, sinon il stube a cote et n'execute plus rien."
        )
    body = body.replace("pip install --quiet pytest", ":")
    body = body.replace(PYTEST_LINE, f"RC={rc}")
    if changed is None:
        body = body.replace(DIFF_LINE, "false > /tmp/hot_subset_diff.txt 2>/dev/null")
    elif changed:
        body = body.replace(
            DIFF_LINE,
            "printf '%s\\n' " + " ".join(changed)
            + " > /tmp/hot_subset_diff.txt 2>/dev/null",
        )
    else:
        body = body.replace(DIFF_LINE, ": > /tmp/hot_subset_diff.txt")
    env = dict(os.environ, GITHUB_BASE_REF="main")
    return subprocess.run(
        [BASH, "-s"], input=body.encode("utf-8"), capture_output=True, env=env
    )


def _out(proc) -> str:
    return (proc.stdout + proc.stderr).decode("utf-8", "replace")


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc0_is_green() -> None:
    """rc 0 : la mesure a eu lieu, aucun verdict de derive."""
    proc = _run_step(0, ["MyIA.AI.Notebooks/x.ipynb"])
    assert proc.returncode == 0, _out(proc)
    assert "::error::" not in _out(proc), _out(proc)


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc1_is_the_content_verdict_and_still_blocks() -> None:
    """rc 1 = des tests ont echoue : le seul rc qui parle du contenu."""
    proc = _run_step(1, ["MyIA.AI.Notebooks/x.ipynb"])
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "::error::" in out and "SRC_DRIFT" in out, out


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_on_a_notebook_pr_does_not_block() -> None:
    """rc 2 sur une PR hors organe : NON MESURE, pas SRC_DRIFT, non bloquant.

    C'est le cas fondateur (#22130, #22264) : un `ImportError` du toolcache
    partage rougissait une PR dont le contenu etait vert.
    """
    proc = _run_step(2, ["MyIA.AI.Notebooks/x.ipynb"])
    assert proc.returncode == 0, _out(proc)
    out = _out(proc)
    assert "::warning::" in out and "NON MESURE" in out, out


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_on_an_organ_pr_blocks_and_names_attribution() -> None:
    """rc 2 sur une PR qui touche l'organe : la cause est attribuable, rouge."""
    proc = _run_step(2, ["scripts/translation/x.py"])
    assert proc.returncode == 1, _out(proc)
    out = _out(proc)
    assert "::error::" in out and "ATTRIBUABLE" in out, out


@pytest.mark.skipif(BASH is None, reason="bash absent : corps d'etape non executable")
def test_rc2_with_unreadable_diff_stays_non_blocking() -> None:
    """Diff illisible : la cause reste a etablir -- jamais un rouge invente."""
    proc = _run_step(2, None)
    assert proc.returncode == 0, _out(proc)
    out = _out(proc)
    assert "INDECISE" in out and "NON MESURE" in out, out
