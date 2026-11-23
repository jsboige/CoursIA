#!/usr/bin/env python3
"""Tests de `scripts/ci/body_consuming_guards.py` (#22603).

L'organe inventorie les gardes qui consomment le body d'une PR, canal par
canal, et rougit quand le depot s'ecarte de sa table de reference. Les
controles ici epinglent exactement ce qui distingue un detecteur d'un
casse-goulet :

  - la decouverte est **mecanique** : un garde ecrit dans un arbre vierge, que
    la reference n'a jamais vu, est quand meme releve (anti-liste-en-dur) ;
  - le mode `--check` rend 0 sur un arbre conforme et **1** sur chaque forme
    de deviation : consommateur non declare, consommateur disparu, canal
    disparu, cablage declare mais absent du workflow, canal sans cablage ni
    motif ecrit ;
  - un commentaire qui *mentionne* un canal ne cable rien : sans le filtre,
    un commentaire documentaire suffirait a faire croire le canal cable ;
  - le cablage est attribue **par script** : un workflow qui passe
    `--pr-body-file` a un autre garde n'en credite aucun ;
  - `--pr-body` et `--pr-body-file` sont deux canaux distincts ;
  - l'organe ne se decouvre pas lui-meme malgre les litteraux de sa table.

Tout est hermetique : les arbres synthetiques vivent dans `tmp_path`, et le
seul acces disque hors de ces repertoires vise le depot lui-meme. Aucun
reseau, aucun `gh`.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
_SCRIPT = _REPO_ROOT / "scripts" / "ci" / "body_consuming_guards.py"
_spec = importlib.util.spec_from_file_location("body_consuming_guards", _SCRIPT)
assert _spec and _spec.loader, f"could not load {_SCRIPT}"
bcg = importlib.util.module_from_spec(_spec)
sys.modules["body_consuming_guards"] = bcg
_spec.loader.exec_module(bcg)


# ---------------------------------------------------------------------------
# Arbres synthetiques
# ---------------------------------------------------------------------------

#: Garde complet : canal memoire lu statiquement, et option fichier posee sur
#: plusieurs lignes (la forme qui a echappe aux premieres versions du
#: detecteur -- voir `add_argument` multi-ligne).
GUARD_PY = '''\
import argparse
import os


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--pr-body-file",
        default=None,
    )
    body = os.environ.get("SYNTH_PR_BODY", "")
    return ap, body
'''

#: Garde qui va chercher son body lui-meme, comme les sweeps du depot.
FETCHER_PY = '''\
import subprocess


def pr_body(number):
    subprocess.run(
        ["gh", "pr", "view", str(number), "--json", "body"],
        check=True,
    )
'''

#: Script sans rapport : ne doit jamais etre releve.
BYSTANDER_PY = """\
import os
value = os.environ.get("HOME", "")
"""


def _make_tree(tmp_path, guard=True, fetcher=True, workflow_body=True):
    """Arbre synthetique minimal : scripts + un workflow qui cable le body."""
    scripts = tmp_path / "scripts" / "notebook_tools"
    scripts.mkdir(parents=True)
    workflows = tmp_path / ".github" / "workflows"
    workflows.mkdir(parents=True)

    if guard:
        (scripts / "synth_guard.py").write_text(GUARD_PY, encoding="utf-8")
    if fetcher:
        (scripts / "synth_fetcher.py").write_text(FETCHER_PY, encoding="utf-8")
    (scripts / "bystander.py").write_text(BYSTANDER_PY, encoding="utf-8")

    if workflow_body:
        body_line = "          SYNTH_PR_BODY: ${{ github.event.pull_request.body }}"
    else:
        # La seule mention du canal est un commentaire : rien n'est cable.
        body_line = "          # SYNTH_PR_BODY serait le canal du body, s'il etait cable"
    (workflows / "synth-gate.yml").write_text(
        "name: synth\n"
        "jobs:\n"
        "  gate:\n"
        "    steps:\n"
        "      - run: python scripts/notebook_tools/synth_guard.py\n"
        + body_line
        + "\n",
        encoding="utf-8",
    )
    return tmp_path


#: Reference declaree pour l'arbre synthetique canonique.
SYNTH_REFERENCE = {
    "scripts/notebook_tools/synth_guard.py": {
        "channels": {
            "cli:--pr-body-file": {
                "cabled_in": [],
                "uncabled_reason": "appel local dans l'arbre de test",
            },
            "env:SYNTH_PR_BODY": {
                "cabled_in": ["synth-gate.yml"],
            },
        },
    },
    "scripts/notebook_tools/synth_fetcher.py": {
        "channels": {
            "api-gh": {
                "cabled_in": [],
                "uncabled_reason": "va chercher le body lui-meme",
            },
        },
    },
}


def _check_cli(tmp_path, reference) -> int:
    """Passe par le CLI, avec la reference synthetique passee en JSON."""
    ref_file = tmp_path / "reference.json"
    ref_file.write_text(json.dumps(reference), encoding="utf-8")
    return bcg.main(
        ["--root", str(tmp_path), "--reference-json", str(ref_file), "--check"]
    )


# ---------------------------------------------------------------------------
# Decouverte mecanique
# ---------------------------------------------------------------------------


def test_discovery_sees_a_guard_the_reference_never_knew(tmp_path):
    """Anti-liste-en-dur : l'arbre vierge est inventorie sans aucune declaration."""
    _make_tree(tmp_path)
    found = bcg.discover_consumers(tmp_path)
    guard = found["scripts/notebook_tools/synth_guard.py"]
    assert "env:SYNTH_PR_BODY" in guard.channels
    # L'option posee sur deux lignes est vue : la detection ne depend pas
    # d'une regex mono-ligne.
    assert "cli:--pr-body-file" in guard.channels
    assert "scripts/notebook_tools/synth_fetcher.py" in found
    assert "api-gh" in found["scripts/notebook_tools/synth_fetcher.py"].channels
    assert "scripts/notebook_tools/bystander.py" not in found


def test_dynamic_env_name_without_literal_is_flagged_not_hidden(tmp_path):
    """Un canal dont le nom est choisi a l'execution est nomme, jamais tu."""
    scripts = tmp_path / "scripts"
    scripts.mkdir(parents=True)
    (scripts / "dyn.py").write_text(
        "import os\n"
        "import argparse\n"
        "ap = argparse.ArgumentParser()\n"
        "ap.add_argument('--body-env', default='')\n"
        "args = ap.parse_args()\n"
        "text = os.environ.get(args.body_env)\n",
        encoding="utf-8",
    )
    found = bcg.discover_consumers(tmp_path)
    channels = found["scripts/dyn.py"].channels
    assert list(channels) == ["env:<nom-dynamique>"]
    assert channels["env:<nom-dynamique>"]["dynamic_name"] is True


def test_organ_does_not_discover_itself():
    """Les litteraux de la table REFERENCE ne font pas de l'organe un consommateur."""
    found = bcg.discover_consumers(_REPO_ROOT)
    own = "scripts/ci/body_consuming_guards.py"
    assert own not in found


# ---------------------------------------------------------------------------
# Cas positif : arbre conforme
# ---------------------------------------------------------------------------


def test_check_green_on_conforming_tree(tmp_path):
    _make_tree(tmp_path)
    fatal, notes = bcg.compare(tmp_path, SYNTH_REFERENCE)
    assert fatal == []
    assert notes == []
    assert _check_cli(tmp_path, SYNTH_REFERENCE) == 0


def test_check_green_on_real_repo():
    """L'inventaire est sain sur le depot : la reference est bien derivee."""
    fatal, _ = bcg.compare(_REPO_ROOT, bcg.REFERENCE)
    assert fatal == []


def test_cli_check_returns_zero_on_real_repo():
    assert bcg.main(["--check"]) == 0


# ---------------------------------------------------------------------------
# Cas negatifs : chaque deviation rougit
# ---------------------------------------------------------------------------


def test_check_red_when_workflow_drops_the_cabling(tmp_path):
    """Le defaut fondateur (#21552) : le garde existe, le canal n'est plus passe."""
    _make_tree(tmp_path, workflow_body=False)
    fatal, _ = bcg.compare(tmp_path, SYNTH_REFERENCE)
    codes = {(d.code, d.detail) for d in fatal}
    assert any(
        code == "CABLING_MISSING" and "synth-gate.yml" in detail
        for code, detail in codes
    ), fatal
    assert _check_cli(tmp_path, SYNTH_REFERENCE) == 1


def test_comment_mentioning_the_channel_is_not_cabling(tmp_path):
    _make_tree(tmp_path, workflow_body=False)
    cabled = bcg.find_cabling(
        tmp_path, "scripts/notebook_tools/synth_guard.py", "env:SYNTH_PR_BODY"
    )
    assert cabled == []


def test_check_red_when_consumer_is_undeclared(tmp_path):
    """Un garde apparu sans etre declare : c'est la decouverte qui rougit."""
    _make_tree(tmp_path)
    reference = {
        "scripts/notebook_tools/synth_guard.py": SYNTH_REFERENCE[
            "scripts/notebook_tools/synth_guard.py"
        ],
    }
    fatal, _ = bcg.compare(tmp_path, reference)
    assert any(
        d.code == "UNDECLARED" and "synth_fetcher" in d.path for d in fatal
    ), fatal
    assert _check_cli(tmp_path, reference) == 1


def test_check_red_when_declared_consumer_vanishes(tmp_path):
    _make_tree(tmp_path, guard=False)
    fatal, _ = bcg.compare(tmp_path, SYNTH_REFERENCE)
    assert any(d.code == "VANISHED" for d in fatal), fatal
    assert _check_cli(tmp_path, SYNTH_REFERENCE) == 1


def test_check_red_when_declared_channel_is_dropped(tmp_path):
    """Le script existe toujours mais ne lit plus le canal declare."""
    scripts = tmp_path / "scripts" / "notebook_tools"
    scripts.mkdir(parents=True)
    (tmp_path / ".github" / "workflows").mkdir(parents=True)
    (scripts / "synth_guard.py").write_text(
        "import os\nbody = os.environ.get('SYNTH_PR_BODY', '')\n",
        encoding="utf-8",
    )
    fatal, _ = bcg.compare(tmp_path, SYNTH_REFERENCE)
    dropped = [d for d in fatal if d.code == "CHANNEL_DROPPED"]
    assert dropped and all("--pr-body-file" in d.detail for d in dropped), fatal
    assert _check_cli(tmp_path, SYNTH_REFERENCE) == 1


def test_check_red_when_channel_has_no_cabling_and_no_reason(tmp_path):
    """Une absence de cablage ne passe que motivee par ecrit."""
    reference = {
        "scripts/notebook_tools/synth_guard.py": {
            "channels": {
                "cli:--pr-body-file": {"cabled_in": []},
                "env:SYNTH_PR_BODY": {"cabled_in": ["synth-gate.yml"]},
            },
        },
        "scripts/notebook_tools/synth_fetcher.py": SYNTH_REFERENCE[
            "scripts/notebook_tools/synth_fetcher.py"
        ],
    }
    _make_tree(tmp_path)
    fatal, _ = bcg.compare(tmp_path, reference)
    assert any(
        d.code == "UNCABLED" and "--pr-body-file" in d.detail for d in fatal
    ), fatal
    assert _check_cli(tmp_path, reference) == 1


def test_check_red_when_declared_workflow_disappears(tmp_path):
    _make_tree(tmp_path)
    (tmp_path / ".github" / "workflows" / "synth-gate.yml").unlink()
    fatal, _ = bcg.compare(tmp_path, SYNTH_REFERENCE)
    assert any(d.code == "WORKFLOW_MISSING" for d in fatal), fatal
    assert _check_cli(tmp_path, SYNTH_REFERENCE) == 1


# ---------------------------------------------------------------------------
# Attributions et confusions de canaux
# ---------------------------------------------------------------------------


def test_cabling_is_attributed_per_script(tmp_path):
    """Un workflow qui cable un autre garde n'en credite aucun."""
    scripts = tmp_path / "scripts" / "notebook_tools"
    scripts.mkdir(parents=True)
    workflows = tmp_path / ".github" / "workflows"
    workflows.mkdir(parents=True)
    (scripts / "target.py").write_text(
        "import argparse\nap = argparse.ArgumentParser()\n"
        "ap.add_argument('--pr-body-file', default=None)\n",
        encoding="utf-8",
    )
    (workflows / "other-gate.yml").write_text(
        "name: other\njobs:\n  gate:\n    steps:\n"
        "      - run: python scripts/notebook_tools/somewhere_else.py --pr-body-file b.md\n",
        encoding="utf-8",
    )
    cabled = bcg.find_cabling(
        tmp_path, "scripts/notebook_tools/target.py", "cli:--pr-body-file"
    )
    assert cabled == []


def test_pr_body_and_pr_body_file_are_distinct_channels():
    text = "run: tool --pr-body-file body.md\n"
    assert bcg._channel_present(text, "cli:--pr-body-file")
    assert not bcg._channel_present(text, "cli:--pr-body")


def test_fast_lane_cabling_requires_the_registry_to_name_the_script(tmp_path):
    """Le fast lane ne cable un garde que si le registre le cite."""
    scripts = tmp_path / "scripts"
    (scripts / "ci").mkdir(parents=True)
    (scripts / "notebook_tools").mkdir()
    workflows = tmp_path / ".github" / "workflows"
    workflows.mkdir(parents=True)
    (scripts / "ci" / "fast_lane_registry.py").write_text(
        "KNOWN = ['registered_guard.py']\n", encoding="utf-8"
    )
    (scripts / "notebook_tools" / "registered_guard.py").write_text(
        "import os\nbody = os.environ.get('REG_PR_BODY', '')\n", encoding="utf-8"
    )
    (scripts / "notebook_tools" / "unknown_guard.py").write_text(
        "import os\nbody = os.environ.get('UNK_PR_BODY', '')\n", encoding="utf-8"
    )
    (workflows / "fast.yml").write_text(
        "name: fast\njobs:\n  gate:\n    steps:\n"
        "      - run: python scripts/ci/fast_lane.py\n"
        "        env:\n"
        "          REG_PR_BODY: ${{ github.event.pull_request.body }}\n"
        "          UNK_PR_BODY: ${{ github.event.pull_request.body }}\n",
        encoding="utf-8",
    )
    assert bcg.find_cabling(
        tmp_path, "scripts/notebook_tools/registered_guard.py", "env:REG_PR_BODY"
    ) == ["fast.yml"]
    assert (
        bcg.find_cabling(
            tmp_path, "scripts/notebook_tools/unknown_guard.py", "env:UNK_PR_BODY"
        )
        == []
    )


# ---------------------------------------------------------------------------
# Cablage ajoute : observation, pas un rouge
# ---------------------------------------------------------------------------


def test_added_cabling_is_reported_without_failing(tmp_path):
    """Ajouter un cable ne casse rien ; le retirer, si."""
    _make_tree(tmp_path)
    second = tmp_path / ".github" / "workflows" / "second-gate.yml"
    second.write_text(
        "name: second\njobs:\n  gate:\n    steps:\n"
        "      - run: python scripts/notebook_tools/synth_guard.py\n"
        "        env:\n"
        "          SYNTH_PR_BODY: ${{ github.event.pull_request.body }}\n",
        encoding="utf-8",
    )
    fatal, notes = bcg.compare(tmp_path, SYNTH_REFERENCE)
    assert fatal == []
    assert any(
        n.code == "CABLING_ADDED" and "second-gate.yml" in n.detail for n in notes
    ), notes
    assert _check_cli(tmp_path, SYNTH_REFERENCE) == 0
