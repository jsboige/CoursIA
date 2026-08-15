#!/usr/bin/env python3
"""Garde-fou #10329 critere 6+7 : le scan out-of-scope de T2 est INCONDITIONNEL.

Contexte (issue #10329) : le pipeline T1 est incremental sur un etat qui n'a
jamais ete initialise — la derive anterieure au cablage du pipeline n'entre
dans aucun perimetre, et aucun run futur ne la rattrape. La parade exigee par
le critere 6 : « T2 journalise la derive hors-perimetre a chaque run » —
pas seulement en mode --full. C'est exactement le scenario qui a cree la
dette (78/163 lignes sur finetuning.csv) : des notebooks enrichis sans
passer par le pipeline, invisibles de tous les runs verts.

La premiere livraison (#10371) ne branchait `--report-out-of-scope` qu'en
mode T1_MODE=full — un run incremental restait aveugle. La presente PR le
rend inconditionnel. Ce test verrouille le pattern pour empecher la
regression (re-scoper le flag au mode full) :

  (1) le step « T2 detect drift » de translation-sync.yml invoque
      check_translation_sync.py AVEC --report-out-of-scope ;
  (2) l'invocation n'est PAS conditionnee au mode (pas de garde
      `if [ "$T1_MODE" = "full" ]` autour du flag ou du notice) ;
  (3) le notice T2 out-of-scope est emis inconditionnellement.

Comme scripts/tests/test_workflow_branch_pattern.py, ce test n'execute PAS
le workflow — il parse le YAML et grep les blocs bash.
"""
from __future__ import annotations

import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
TRANSLATION_SYNC = (
    REPO_ROOT / ".github" / "workflows" / "translation-sync.yml"
)


def _t2_run_block() -> str:
    """Extrait le bloc run: du step « T2 detect drift »."""
    text = TRANSLATION_SYNC.read_text(encoding="utf-8")
    m = re.search(
        r"- name: T2 detect drift.*?run: \|\n(.*?)(?=\n +-\s+name:|\Z)",
        text,
        flags=re.S,
    )
    assert m is not None, (
        "step « T2 detect drift » introuvable dans translation-sync.yml — "
        "le workflow a ete restructure ; mettre a jour ce garde-fou"
    )
    return m.group(1)


def test_t2_invokes_report_out_of_scope():
    block = _t2_run_block()
    assert "--report-out-of-scope" in block, (
        "T2 doit invoquer check_translation_sync.py avec --report-out-of-scope "
        "(critere 6 de #10329 : journalisation hors-perimetre a CHAQUE run)"
    )


def test_t2_out_of_scope_not_gated_on_mode():
    block = _t2_run_block()
    # Le flag ne doit pas vivre derriere un garde de mode : la dette creee
    # par un enrichissement hors pipeline est invisible d'un run incremental.
    # On verifie qu'aucun if T1_MODE ne precede (dans le bloc) l'invocation
    # qui porte le flag.
    flagged = [
        line for line in block.splitlines() if "--report-out-of-scope" in line
    ]
    assert flagged, "flag --report-out-of-scope absent du bloc T2"
    for line in flagged:
        assert "T1_MODE" not in line, (
            "l'invocation de --report-out-of-scope ne doit pas etre "
            "conditionnee au mode (regression critere 6 de #10329)"
        )
    # Et aucun if T1_MODE ne doit subsister dans le bloc T2 (toute
    # re-conditionalisation du scan est suspecte).
    assert 'T1_MODE' not in block, (
        "le bloc T2 ne doit plus contenir de garde T1_MODE : le scan "
        "out-of-scope est inconditionnel depuis #10329 (critere 6)"
    )


def test_t2_out_of_scope_notice_unconditional():
    block = _t2_run_block()
    assert "title=T2 out-of-scope" in block, (
        "le notice T2 out-of-scope doit etre emis (garde-fou critere 7 de "
        "#10329 : la derive reste visible au run suivant)"
    )
    # Le notice et l'archivage du rapport ne doivent pas etre gates :
    # la ligne du notice ne doit pas etre imbriquee sous un if de mode.
    notice_lines = [
        (i, ln) for i, ln in enumerate(block.splitlines())
        if "title=T2 out-of-scope" in ln
    ]
    assert notice_lines, "notice T2 out-of-scope absent"
    for _i, ln in notice_lines:
        assert "if [" not in ln
