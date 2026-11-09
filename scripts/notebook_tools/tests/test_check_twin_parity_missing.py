#!/usr/bin/env python3
"""Un carnet SUPPRIME n'est pas une derive de contenu (gate twin-parity).

Defaut corrige
--------------
Le gate par-PR (`twin-parity.yml`, mode `--per-pair`) selectionnait les paires
a reparer sur le seul `verdict == "DRIFT_INTRODUCED"`, sans regarder le statut
de la paire au HEAD. Or `DRIFT_INTRODUCED` couvre DEUX situations distinctes
(`_classify_per_pair`) :

  - derive de contenu : les deux carnets existent, leur blob SHA a bouge
    (head_status = DRIFT / NUMBERING-DRIFT) -> le rebaseline `--update --pair`
    atteste la nouvelle empreinte, comportement correct ;
  - carnet SUPPRIME par la PR : base_status = OK, head_status = MISSING ->
    AUCUN rebaseline ne peut restaurer un fichier supprime. `--update --pair`
    echoue ou fait un no-op, et le message envoyait l'agent sur une piste morte.

Le discriminant etait deja dans la donnee : `head_status`, produit par
`check_pair` (vocabulaire de statut des PAIRES : OK / DRIFT / NUMBERING-DRIFT /
MISSING -- a ne pas confondre avec le vocabulaire des VERDICTS de PR :
OK / DRIFT_INTRODUCED / DRIFT_RESOLVED / DRIFT_PRE_EXISTING).

Le correctif branche le message ET la commande sur `head_status`
(`split_introduced_pairs` / `render_introduced_remediation`), et le workflow
appelle ces fonctions au lieu de re-inliner un filtre sur `verdict`.

Ce que ces tests pincent
------------------------
  1. DRIFT (contenu divergent) -> commande de rebaseline, comme avant ;
  2. MISSING (carnet supprime) -> message de suppression, AUCUN rebaseline ;
  3. un cas non liste (DRIFT_PRE_EXISTING) n'est jamais traite comme MISSING ;
  4. un rapport mixte separe les deux lots sans contaminer l'un par l'autre ;
  5. une entree AJOUTEE dont le carnet n'existe pas tombe dans le lot MISSING
     (rebaseline impossible aussi) avec son propre remede ;
  6. le SNIPPET REEL du workflow (extrait de twin-parity.yml et execute) ne
     propose aucun rebaseline pour une paire MISSING -- c'est le controle qui
     mord : reinverser le filtre sur `verdict` seul le fait echouer.

Run:
    pytest scripts/notebook_tools/tests/test_check_twin_parity_missing.py -q
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

NOTEBOOK_TOOLS = Path(__file__).resolve().parents[1]
REPO_ROOT = NOTEBOOK_TOOLS.parents[1]
WORKFLOW = REPO_ROOT / ".github" / "workflows" / "twin-parity.yml"

sys.path.insert(0, str(NOTEBOOK_TOOLS))

import check_twin_parity as ctp  # noqa: E402
from check_twin_parity import (  # noqa: E402
    render_introduced_remediation,
    split_introduced_pairs,
)


# --- fixtures ----------------------------------------------------------------

def _pair(name: str, base_status: str, head_status: str, verdict: str,
          details: list[str] | None = None) -> dict:
    """Une entree de `report["pairs"]` telle que produite par le mode --per-pair."""
    return {
        "name": name,
        "family": "Search",
        "parity_level": "surface",
        "base_ref": "deadbeef",
        "base_status": base_status,
        "head_status": head_status,
        "verdict": verdict,
        "base_details": [],
        "head_details": details if details is not None else [],
    }


CONTENT_DRIFT = _pair("Search-01-CSP", "OK", "DRIFT", "DRIFT_INTRODUCED",
                      ["Python a drift : aaaaaaaa -> bbbbbbbb"])
DELETED = _pair(
    "Search-02-Queens", "OK", "MISSING", "DRIFT_INTRODUCED",
    ["Python MANQUANT dans git : MyIA.AI.Notebooks/Search/Search-02.ipynb"],
)
ADDED_WITHOUT_NOTEBOOK = _pair(
    "Search-99-New", "MISSING", "MISSING", "DRIFT_INTRODUCED",
    ["C# MANQUANT dans git : MyIA.AI.Notebooks/Search/Search-99.ipynb"],
)
PRE_EXISTING_MISSING = _pair("Search-03-Old", "DRIFT", "MISSING",
                             "DRIFT_PRE_EXISTING")
RESOLVED = _pair("Search-04-Fixed", "DRIFT", "OK", "DRIFT_RESOLVED")


def _report(pairs: list[dict]) -> dict:
    return {
        "mode": "per_pair",
        "base_ref": "deadbeef",
        "total": len(pairs),
        "ok": sum(1 for p in pairs if p["verdict"] == "OK"),
        "drift_introduced": sum(1 for p in pairs if p["verdict"] == "DRIFT_INTRODUCED"),
        "drift_resolved": sum(1 for p in pairs if p["verdict"] == "DRIFT_RESOLVED"),
        "drift_pre_existing": sum(1 for p in pairs if p["verdict"] == "DRIFT_PRE_EXISTING"),
        "pairs": pairs,
    }


def _workflow_remediation_payload() -> str:
    """Extrait le code python de la ligne `CMDS=$(python -c "...")` du workflow.

    Le gate n'est pas testable autrement : le snippet est exactement ce que la CI
    execute. Le test echoue si la ligne disparait ou change de forme -- c'est
    volontaire, un garde muet ne garde rien.
    """
    text = WORKFLOW.read_text(encoding="utf-8")
    matches = re.findall(r'CMDS=\$\(python -c "([^"]*)"\)', text)
    assert matches, (
        "La ligne CMDS=$(python -c \"...\") est introuvable dans twin-parity.yml : "
        "le gate a change de forme, mettre ce test a jour AVANT de merger."
    )
    assert len(matches) == 1, f"Plusieurs lignes CMDS= trouvees ({len(matches)})."
    return matches[0]


def _run_payload(payload: str, tmp_path: Path) -> tuple[str, str, int]:
    """Execute le payload du workflow dans un cwd isole portant le rapport."""
    (tmp_path / "twin_parity_report.json").write_text(
        json.dumps(_report([CONTENT_DRIFT, DELETED])), encoding="utf-8")
    env = dict(os.environ)
    env["PYTHONPATH"] = os.pathsep.join(
        [str(NOTEBOOK_TOOLS), env.get("PYTHONPATH", "")]).strip(os.pathsep)
    proc = subprocess.run(
        [sys.executable, "-c", payload],
        cwd=tmp_path, env=env, capture_output=True, text=True, encoding="utf-8",
    )
    return proc.stdout, proc.stderr, proc.returncode


# --- 1. derive de contenu : comportement historique preserve -----------------

def test_content_drift_pair_gets_the_rebaseline_command():
    drift, missing = split_introduced_pairs([CONTENT_DRIFT])
    assert [p["name"] for p in drift] == ["Search-01-CSP"]
    assert missing == []

    lines = render_introduced_remediation([CONTENT_DRIFT])
    text = "\n".join(lines)
    assert ('--update --pair "Search-01-CSP" --by "<machine:workspace>"') in text
    assert "[MISSING]" not in text


# --- 2. carnet supprime : message de suppression, PAS de rebaseline ----------

def test_deleted_notebook_gets_a_deletion_notice_without_rebaseline():
    drift, missing = split_introduced_pairs([DELETED])
    assert drift == []
    assert [p["name"] for p in missing] == ["Search-02-Queens"]

    text = "\n".join(render_introduced_remediation([DELETED]))
    assert "[MISSING]" in text
    assert "SUPPRIME" in text
    # Les deux corrections reelles sont nommees : restaurer, ou retirer l'entree.
    assert "restaure le carnet" in text
    assert "twin_pairs.d/" in text
    # Le chemin fautif du rapport est repris, pas resume.
    assert "Search-02.ipynb" in text
    # Et surtout : aucune commande de rebaseline ne peut restaurer un fichier
    # supprime -- le gate ne doit pas en proposer une.
    assert "--update" not in text
    assert "--pair" not in text


def test_added_pair_whose_notebook_is_absent_is_missing_too():
    """Une entree ajoutee pointant un carnet inexistant : rebaseline impossible."""
    drift, missing = split_introduced_pairs([ADDED_WITHOUT_NOTEBOOK])
    assert drift == []
    assert [p["name"] for p in missing] == ["Search-99-New"]

    text = "\n".join(render_introduced_remediation([ADDED_WITHOUT_NOTEBOOK]))
    assert "[MISSING]" in text
    assert "entree ajoutee par cette PR" in text
    assert "restaure le carnet" not in text  # ce n'est pas une suppression
    assert "--update" not in text


# --- 3. un cas non liste n'est PAS traite comme MISSING ----------------------

def test_non_listed_pair_is_never_treated_as_missing():
    """`DRIFT_PRE_EXISTING` (carnet absent, mais drift deja present au base-ref)
    ne fait pas rougir le gate : il ne doit entrer dans aucun des deux lots."""
    drift, missing = split_introduced_pairs([PRE_EXISTING_MISSING, RESOLVED])
    assert drift == []
    assert missing == []

    text = "\n".join(render_introduced_remediation([PRE_EXISTING_MISSING, RESOLVED]))
    assert "[MISSING]" not in text
    assert "Search-03-Old" not in text
    assert "Search-04-Fixed" not in text


# --- 4. rapport mixte : les deux lots restent distincts ----------------------

def test_mixed_report_keeps_the_two_lots_apart():
    pairs = [CONTENT_DRIFT, DELETED, ADDED_WITHOUT_NOTEBOOK, PRE_EXISTING_MISSING]
    drift, missing = split_introduced_pairs(pairs)
    assert [p["name"] for p in drift] == ["Search-01-CSP"]
    assert [p["name"] for p in missing] == ["Search-02-Queens", "Search-99-New"]

    lines = render_introduced_remediation(pairs)
    text = "\n".join(lines)
    # Une seule commande de rebaseline, celle de la paire en derive de contenu.
    rebaselines = [ln for ln in lines if "--update --pair" in ln]
    assert len(rebaselines) == 1
    assert "Search-01-CSP" in rebaselines[0]
    assert "Search-02-Queens" not in rebaselines[0]
    assert "Search-99-New" not in rebaselines[0]
    assert text.count("[MISSING]") == 2


def test_empty_report_keeps_the_historical_placeholder():
    """Sans paire DRIFT_INTRODUCED (cas defensif : le gate sort avant), la
    commande generique historique reste disponible, jamais un bloc vide."""
    lines = render_introduced_remediation([])
    assert len(lines) == 1
    assert "--update --pair" in lines[0]
    assert "<nom exact de l entree>" in lines[0]


# --- 5. le snippet REEL du workflow (controle qui mord) ----------------------

def test_workflow_snippet_proposes_no_rebaseline_for_a_deleted_notebook(tmp_path):
    """Execute le python du workflow sur un rapport DRIFT + MISSING.

    C'est le controle du lot : si la selection repasse a un filtre sur `verdict`
    seul (sans `head_status`), la paire supprimee ressort avec une commande
    `--update --pair` et ce test echoue.
    """
    payload = _workflow_remediation_payload()
    # Le snippet est celui du workflow, pas une reimplementation : il doit
    # vraiment appeler le selecteur partage.
    assert "render_introduced_remediation" in payload

    out, err, rc = _run_payload(payload, tmp_path)
    assert rc == 0, f"snippet du workflow en echec (rc={rc}) : {err}"
    assert '--update --pair "Search-01-CSP"' in out
    assert "Search-02-Queens" in out
    assert "[MISSING]" in out
    # Aucune ligne de commande ne vise la paire supprimee.
    assert '--update --pair "Search-02-Queens"' not in out
    assert "--update --pair \"Search-02-Queens" not in out


def test_workflow_selects_on_status_not_on_verdict_alone():
    """Garde statique : le workflow ne re-inline plus de filtre `verdict` seul.

    Le test precedent prouve le comportement en executant le snippet ; celui-ci
    nomme la cause si quelqu'un revient a un filtre en ligne.
    """
    text = WORKFLOW.read_text(encoding="utf-8")
    assert "render_introduced_remediation" in text
    # L'ancienne forme fautive : selection sur verdict seul, sans statut.
    assert "p.get('verdict')=='DRIFT_INTRODUCED'] or ['<nom exact de l entree>']" not in text
