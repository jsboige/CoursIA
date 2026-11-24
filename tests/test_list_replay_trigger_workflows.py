#!/usr/bin/env python3
"""Tests du census des workflows qui rejouent sur `workflow_run`/`issue_comment`.

Le census (#24121) transpose `scripts/ci/list_edited_trigger_workflows.py`
sur deux familles. Ce qui est verifie ici, c'est la **discrimination** entre
une lecture *decision-bearing* (une lecture dans un `if:` -- le verdict bouge
quand l'evenement bouge) et une lecture *observationnelle* (une lecture qui
n'alimente qu'un journal), et le fait que la prose n'entre **jamais** dans le
verdict.

Les fixtures sont ecrites a la main dans un temporaire : elles sont plus
lisibles qu'un extrait du depot, et elles fixent le comportement attendu.
"""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))

import list_replay_trigger_workflows as census  # noqa: E402


DEPENDENT = census.TRIGGER_DEPENDENT
INDEPENDENT = census.TRIGGER_INDEPENDENT


def _write(root: Path, name: str, text: str) -> None:
    path = root / ".github" / "workflows" / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


class CensusTests(unittest.TestCase):
    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.root = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)

    # -- cas 1 : une lecture dans un `if:` rend le declencheur load-bearing

    def test_upstream_conclusion_in_if_is_decision_bearing(self) -> None:
        _write(
            self.root,
            "dependent.yml",
            "name: Dep\n"
            "on:\n"
            "  workflow_run:\n"
            "    workflows: [Up]\n"
            "    types: [completed]\n"
            "jobs:\n"
            "  j:\n"
            "    if: github.event.workflow_run.conclusion == 'success'\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - run: echo hello\n",
        )
        rows = census.survey(self.root)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["verdict"], DEPENDENT)
        self.assertIn("workflow_run:upstream_conclusion", rows[0]["decision_axes"])

    # -- cas 2 : une lecture qui n'alimente qu'un journal n'est PAS un axe

    def test_log_only_read_is_observational(self) -> None:
        _write(
            self.root,
            "observational.yml",
            "name: Obs\n"
            "on:\n"
            "  workflow_run:\n"
            "    workflows: [Up]\n"
            "    types: [completed]\n"
            "jobs:\n"
            "  j:\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - run: echo \"conclusion=${{ github.event.workflow_run.conclusion }}\"\n",
        )
        rows = census.survey(self.root)
        self.assertEqual(rows[0]["verdict"], INDEPENDENT)
        self.assertEqual(rows[0]["decision_axes"], [])
        self.assertIn("workflow_run:upstream_conclusion", rows[0]["observed_axes"])

    # -- cas 3 : la famille `issue_comment`

    def test_issue_comment_body_axis(self) -> None:
        _write(
            self.root,
            "comment.yml",
            "name: Cmd\n"
            "on:\n"
            "  issue_comment:\n"
            "    types: [created]\n"
            "jobs:\n"
            "  j:\n"
            "    if: contains(github.event.comment.body, '/run')\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - run: echo hello\n",
        )
        rows = census.survey(self.root)
        self.assertEqual(rows[0]["verdict"], DEPENDENT)
        self.assertIn("issue_comment:comment_body", rows[0]["decision_axes"])

    # -- cas 4 : une variable d'environnement lue par le `if:` d'un step

    def test_env_read_by_step_if_is_decision_bearing(self) -> None:
        _write(
            self.root,
            "envstep.yml",
            "name: EnvStep\n"
            "on:\n"
            "  workflow_run:\n"
            "    workflows: [Up]\n"
            "    types: [completed]\n"
            "jobs:\n"
            "  j:\n"
            "    runs-on: ubuntu-latest\n"
            "    env:\n"
            "      UP: ${{ github.event.workflow_run.head_branch }}\n"
            "    steps:\n"
            "      - if: env.UP == 'main'\n"
            "        run: echo hello\n",
        )
        rows = census.survey(self.root)
        self.assertEqual(rows[0]["verdict"], DEPENDENT)
        self.assertIn("workflow_run:upstream_head", rows[0]["decision_axes"])

    # -- cas 4 bis : la consommation d'artefacts de l'aval est un axe

    def test_upstream_artifact_axis(self) -> None:
        _write(
            self.root,
            "artifact.yml",
            "name: Art\n"
            "on:\n"
            "  workflow_run:\n"
            "    workflows: [Up]\n"
            "    types: [completed]\n"
            "jobs:\n"
            "  j:\n"
            "    if: github.event.workflow_run.conclusion == 'success'\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - uses: actions/download-artifact@v4\n"
            "        with:\n"
            "          run-id: ${{ github.event.workflow_run.id }}\n",
        )
        rows = census.survey(self.root)
        # consommer l'artefact de l'aval est decision-bearing par nature
        self.assertIn("workflow_run:upstream_artifact", rows[0]["decision_axes"])
        self.assertEqual(rows[0]["verdict"], DEPENDENT)

    # -- cas 5 : la prose est citee, jamais utilisee comme verdict

    def test_prose_is_cited_but_never_decides(self) -> None:
        _write(
            self.root,
            "prose.yml",
            "name: Prose\n"
            "# Le declencheur est une ancre de survie : le workflow doit\n"
            "# survivre a la panne du scheduler qu'il observe.\n"
            "on:\n"
            "  workflow_run:\n"
            "    workflows: [Up]\n"
            "    types: [completed]\n"
            "jobs:\n"
            "  j:\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - run: echo hello\n",
        )
        rows = census.survey(self.root)
        # La prose est citee...
        self.assertTrue(rows[0]["prose_mentions"])
        self.assertTrue(rows[0]["prose_mentions"][0]["in_header"])
        # ...mais elle ne change pas le verdict : purely code.
        self.assertEqual(rows[0]["verdict"], INDEPENDENT)
        # L'ablation rend le meme verdict.
        ablation = census.render_ablation(rows)
        self.assertIn("identique", ablation)

    # -- cas 6 : l'ablation signale un verdict qui repose sur de la prose

    def test_ablation_reports_a_prose_backed_verdict(self) -> None:
        row = {
            "workflow": ".github/workflows/x.yml",
            "verdict": DEPENDENT,
            "decision_axes": [],
            "observed_axes": [],
            "prose_mentions": [],
            "prose_mentions_total": 0,
        }
        self.assertIn("DIFFERENTE", census.render_ablation([row]))

    # -- cas 7 : un workflow qui n'ecoute ni l'un ni l'autre est ignore

    def test_unrelated_workflow_is_ignored(self) -> None:
        _write(
            self.root,
            "plain.yml",
            "name: Plain\n"
            "on:\n"
            "  push:\n"
            "    branches: [main]\n"
            "jobs:\n"
            "  j:\n"
            "    runs-on: ubuntu-latest\n"
            "    steps:\n"
            "      - run: echo hello\n",
        )
        self.assertEqual(census.survey(self.root), [])

    # -- cas 8 : la mesure jointe compte le volume par evenement

    def test_attach_counts_reports_the_removable_volume(self) -> None:
        rows = [
            {
                "workflow": ".github/workflows/x.yml",
                "listening_families": ["workflow_run"],
                "verdict": INDEPENDENT,
                "decision_axes": [],
                "observed_axes": [],
                "prose_mentions": [],
                "prose_mentions_total": 0,
            }
        ]
        runs = [
            {"path": ".github/workflows/x.yml", "event": "workflow_run"},
            {"path": ".github/workflows/x.yml", "event": "workflow_run"},
            {"path": ".github/workflows/x.yml", "event": "schedule"},
        ]
        census._attach_counts(rows, runs, [])
        self.assertEqual(rows[0]["runs_total"], 3)
        self.assertEqual(rows[0]["runs_if_family_removed"], {"workflow_run": 2})

    # -- cas 9 : le snapshot de l'organe de mesure est lisible tel quel

    def test_snapshot_is_readable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            snapshot = Path(tmp) / "snap.json"
            snapshot.write_text(
                json.dumps(
                    {
                        "runs": [
                            {
                                "path": ".github/workflows/x.yml",
                                "event": "workflow_run",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            rows = [
                {
                    "workflow": ".github/workflows/x.yml",
                    "listening_families": ["workflow_run"],
                }
            ]
            census.attach_runs(rows, snapshot)
        self.assertEqual(rows[0]["runs_total"], 1)


if __name__ == "__main__":
    unittest.main()
