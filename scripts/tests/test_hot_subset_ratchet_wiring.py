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

import re
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
