#!/usr/bin/env python3
"""Temoins du correctif #27162 -- une portee MORTE d'une autre lane rend
BLOCKED (epic-wide), y compris en requete PATH_SCOPED.

Le defaut, mesure le 17/11 sur #27139 : le claim d'une autre lane portait

    [CLAIMED] lane myia-po-2028:CoursIA-2 -- paths:
        MyIA.AI.Notebooks/Sudoku/** ; claim pose au dispatch par le coordinateur

La prose collee au glob rend la portee MORTE. La requete de la lane
appelante portait sur un chemin (`--paths`), donc la porte etait classee
PATH_SCOPED, et la portee morte n'etait pas elevee en epic-wide : le verdict
rendu etait `CLEAR` (rc=0) alors que la lane concurrente verrouillait le
grain. Effet mesure : la lane claudish a livre #27152 sur un grain deja
reclame, et la collision a demande un arbitrage.

Le mecanisme, isole : la relaxation de creation (#21431) lisait ce glob
pollue comme « un fichier a creer dans un repertoire qui existe » (le
parent `MyIA.AI.Notebooks/Sudoku` existe) -- donc PAS de lever epic-wide,
puis comparaison PAR MOTIF, qui ne voit pas le chemin de l'appelant : la
lane concurrente sortait des bloqueurs.

Le correctif : une portee qui porte de la PROSE n'est pas une portee de
creation (condition (d) de `_scope_is_creation`) -- c'est un claim casse,
qui garde le lever epic-wide du #10958 (fail-CLOSED).

Ces tests pignent AUSSI ce qui ne doit PAS changer :
- une portee de creation LEGITIME (fichier a creer, repertoire qui existe,
  glob propre) reste comparee par motif et ne leve pas l'issue entiere
  (#21431) ;
- une portee VIVANTE reste bloquee par intersection, pas par lever
  (#26657 : PR ouverte citee, chemin renomme -- temoins dans
  `test_check_lane_claim_scope_resolution.py`) ;
- deux lanes d'une MEME machine ne se confondent jamais.

Run: python -m pytest scripts/tests/test_check_lane_claim_dead_scope_path_scoped.py
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402


# --- helpers -----------------------------------------------------------------

# L'arbre suivi est monkeypatche : le verdict ne doit dependre ni de l'etat
# du clone ni du contenu reel du depot.
TRACKED = [
    "MyIA.AI.Notebooks/Sudoku/Sudoku-14-BDD-Python.ipynb",
    "scripts/check_lane_claim.py",
    "scripts/notebook_tools/check_output_collapse.py",
]
SUDOKU_NB = "MyIA.AI.Notebooks/Sudoku/Sudoku-14-BDD-Python.ipynb"

# Le glob pollue du cas #27139, verbatim.
POLLUE = ("MyIA.AI.Notebooks/Sudoku/** ; claim pose au dispatch par le "
          "coordinateur")


def comment(body, created_at, author="jsboige", url=None):
    return {
        "body": body,
        "createdAt": created_at,
        "author": {"login": author},
        "url": url,
    }


def payload(*comments, number=27139, title="t", labels=None):
    d = {"number": number, "title": title, "comments": list(comments)}
    if labels is not None:
        d["labels"] = labels
    return d


def _summary(capsys):
    """(JSON de synthese, stderr) emis par `_run_check`."""
    captured = capsys.readouterr()
    return json.loads(captured.out.split("\n\n", 1)[0]), captured.err


def _claim_mort(lane, paths=POLLUE, created="2026-11-17T16:34:00Z"):
    """Le claim de #27139 : une lane concurrente, une portee MORTE."""
    return comment(f"[CLAIMED] lane {lane} -- paths: {paths}", created)


def _delivered(lane, pr_ref, paths, created="2026-11-17T18:27:55Z"):
    body = clc._DELIVERED_BODY_TMPL.format(
        lane=lane, pr_ref=pr_ref, paths_clause=clc._paths_clause(paths),
    )
    return comment(body, created)


# --- le cas mesure (#27139) --------------------------------------------------


def test_portee_morte_dune_autre_lane_bloque_en_requete_path_scoped(
        capsys, monkeypatch):
    """Le cas #27139 EXACT : une portee morte d'une autre lane rend BLOCKED
    dans une requete qui porte un chemin (`--paths`).

    Avant le correctif : rc=0, `query_scope: PATH_SCOPED`,
    `blocking_lanes: []`, verdict `CLEAR`. La lane concurrente etait
    silencieusement retiree des bloqueurs.
    """
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: list(TRACKED))
    p = payload(_claim_mort("myia-po-2028:CoursIA-2"))

    rc = clc._run_check(p, "myia-po-2028:claudish", my_paths=[SUDOKU_NB])
    summary, err = _summary(capsys)

    assert rc == 1, (
        f"Expected BLOCKED (portee morte d'une autre lane) but got rc={rc}. "
        f"stderr:\n{err}\naudit:\n{summary}"
    )
    assert "BLOCKED" in err
    assert summary["blocking_lanes"] == ["myia-po-2028:CoursIA-2"], (
        f"la lane concurrente doit rester bloqueuse : {summary}"
    )
    # Le temoin reste visible : la lane voit la portee morte et la corrige.
    assert summary["dead_scope_globs"] == {
        "myia-po-2028:CoursIA-2": [POLLUE]
    }


def test_portee_morte_dune_autre_lane_bloque_meme_sur_un_chemin_disjoint(
        capsys, monkeypatch):
    """La portee morte est lue EPIC-WIDE : elle bloque meme quand le chemin de
    l'appelant ne touche pas le repertoire du glob.

    C'est la consequence attendue du fail-CLOSED (l'issue le demande :
    « une portee morte d'une autre lane rend BLOCKED (epic-wide) dans toute
    requete, PATH_SCOPED compris »). Une portee morte ne prouve rien sur le
    chevauchement : l'hypothese sure est que la lane concurrente voulait
    dire autre chose.
    """
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: list(TRACKED))
    p = payload(_claim_mort("myia-po-2028:CoursIA-2"))

    rc = clc._run_check(p, "myia-po-2028:claudish",
                        my_paths=["scripts/check_lane_claim.py"])
    summary, err = _summary(capsys)

    assert rc == 1, (
        f"Expected BLOCKED (portee morte levee en epic-wide) but got "
        f"rc={rc}. stderr:\n{err}\naudit:\n{summary}"
    )
    assert summary["blocking_lanes"] == ["myia-po-2028:CoursIA-2"]


# --- deux lanes d'une meme machine -------------------------------------------


def test_deux_lanes_dune_meme_machine_ne_se_confondent_jamais(
        capsys, monkeypatch):
    """`myia-po-2028:claudish` (l'appelante) et `myia-po-2028:CoursIA-2` (la
    concurrente) sont deux lanes distinctes de la meme machine.

    La portee morte de la concurrente bloque l'appelante, et l'appelante n'a
    aucun claim propre : `my_active_claim` reste faux (aucune confusion
    « resuming your own active claim »).
    """
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: list(TRACKED))
    p = payload(_claim_mort("myia-po-2028:CoursIA-2"))

    rc = clc._run_check(p, "myia-po-2028:claudish", my_paths=[SUDOKU_NB])
    summary, err = _summary(capsys)

    assert rc == 1
    assert summary["my_active_claim"] is False, (
        f"l'appelante n'a aucun claim propre : {summary}"
    )
    assert summary["blocking_lanes"] == ["myia-po-2028:CoursIA-2"]
    assert "resuming your own active claim" not in err


def test_le_claim_propre_de_l_appellante_ne_masque_pas_la_lane_concurrente(
        capsys, monkeypatch):
    """Le cas REEL de #27139 : l'appelante `myia-po-2028:claudish` avait
    elle-meme un claim vivant (sa livraison #27152, PR encore ouverte).

    La note « resuming your own active claim » decrivait donc son PROPRE
    claim (mesure : le marqueur `[DELIVERED] lane myia-po-2028:claudish --
    PR #27152` existe sur #27139) -- elle ne confondait pas les deux lanes.
    Ce test le fixe : le claim propre est reconnu comme tel, ET la lane
    concurrente reste un bloqueur a part entiere.
    """
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: list(TRACKED))
    p = payload(
        _claim_mort("myia-po-2028:CoursIA-2"),
        _delivered("myia-po-2028:claudish", 27152, [SUDOKU_NB]),
    )

    rc = clc._run_check(p, "myia-po-2028:claudish", my_paths=[SUDOKU_NB],
                        pr_states={27152: "OPEN"})
    summary, _err = _summary(capsys)

    assert summary["my_active_claim"] is True, (
        f"le claim propre de l'appelante doit etre visible : {summary}"
    )
    assert summary["blocking_lanes"] == ["myia-po-2028:CoursIA-2"], (
        f"la lane concurrente reste un bloqueur distinct : {summary}"
    )
    assert rc == 1


# --- ce qui ne doit PAS changer ----------------------------------------------


def test_une_portee_de_creation_legitime_ne_leve_pas_l_issue(
        capsys, monkeypatch):
    """#21431 reste vivant : une portee de creation PROPRE (fichier a creer
    dans un repertoire qui existe) est comparee par motif, pas levee en
    epic-wide. Deux lanes qui creent deux organes distincts ne se bloquent
    pas.
    """
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: list(TRACKED))
    p = payload(
        comment("[CLAIMED] lane myia-ai-01:CoursIA-2 -- paths: "
                "scripts/notebook_tools/check_concession_prose.py",
                "2026-10-19T15:00:00Z"),
        number=21424,
    )
    rc = clc._run_check(
        p, "myia-po-2023:CoursIA-2",
        my_paths=["scripts/notebook_tools/check_output_flood.py"],
    )
    summary, err = _summary(capsys)

    assert rc == 0, (
        f"Expected CLEAR (portee de creation legitime) but got rc={rc}. "
        f"stderr:\n{err}\naudit:\n{summary}"
    )
    assert summary["blocking_lanes"] == []


def test_une_portee_vivante_bloque_par_intersection(capsys, monkeypatch):
    """Le claim CORRIGE du cas #27139 (`paths: .../Sudoku/** -- <prose>`) :
    la portee est VIVANTE, elle bloque par intersection -- pas par lever
    epic-wide. La voie normale reste la voie normale.
    """
    monkeypatch.setattr(clc, "_git_tracked_files", lambda: list(TRACKED))
    p = payload(
        comment("[CLAIMED] lane myia-po-2028:CoursIA-2 -- paths: "
                "MyIA.AI.Notebooks/Sudoku/** -- fournee de la classe verdict "
                "fige dans Sudoku",
                "2026-11-17T21:26:32Z"),
    )
    rc = clc._run_check(p, "myia-po-2028:claudish", my_paths=[SUDOKU_NB])
    summary, _err = _summary(capsys)

    assert rc == 1
    assert summary["blocking_lanes"] == ["myia-po-2028:CoursIA-2"]
    # Portee vivante : aucun glob mort, donc pas de lever epic-wide.
    claim = summary["active_claims"]["myia-po-2028:CoursIA-2"]
    assert claim["empty_scope"] == []


def test_scope_is_creation_refuse_une_portee_qui_porte_de_la_prose():
    """Le discriminateur, au niveau unite : un glob PROPRE dans un repertoire
    qui existe est une creation ; le meme glob avec une rationale collee
    n'en est pas une (c'est un claim casse : il garde le lever epic-wide)."""
    tracked = list(TRACKED)
    # Creation legitime : repertoire existant, fichier absent.
    assert clc._scope_is_creation(
        ["scripts/notebook_tools/check_concession_prose.py"], tracked) is True
    # Meme repertoire, mais la prose est collee au glob (#27139).
    assert clc._scope_is_creation(
        ["scripts/notebook_tools/check_concession_prose.py ; tranche A"],
        tracked) is False
    assert clc._scope_is_creation([POLLUE], tracked) is False
    # Un glob propre, mais dont le repertoire n'existe pas : typo (#21431 (c)).
    assert clc._scope_is_creation(["scripts/nowhere/typo.py"], tracked) is False


def test_glob_carries_prose_detecte_les_fragments():
    """Le detecteur de prose : un fragment de clause mal decoupee. Un glob
    propre (avec ou sans meta-caracteres) n'est pas de la prose."""
    assert clc._glob_carries_prose(POLLUE) is True
    assert clc._glob_carries_prose("a/** ; tranche") is True
    assert clc._glob_carries_prose("a/** pour la tranche B") is True
    assert clc._glob_carries_prose("MyIA.AI.Notebooks/Sudoku/**") is False
    assert clc._glob_carries_prose("scripts/check_lane_claim.py") is False
