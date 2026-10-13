"""Tests de l'audit des besoins locaux des jobs auto-heberges (#17397).

Chaque test epingle une **classe de faux positif mesuree** sur le depot, pas une
forme inventee. C'est le point : un motif de detection se valide par ses faux
negatifs et ses faux positifs, jamais par ses hits -- le motif `elan` a classe
« besoin local » deux workflows parce qu'il matchait « relance ».

Les fixtures sont construites ligne a ligne (indentation explicite) plutot que
par `textwrap.dedent` : l'indentation d'une constante interpolee entre dans le
calcul du prefixe commun, et deux fixtures sur trois se retrouvaient avec un
`runs-on` hors de son mapping.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import audit_self_hosted_needs as audit  # noqa: E402

SELF_HOSTED = "[self-hosted, coursia-ephemeral, coursia-linux]"


def workflow(
    *,
    title: str = "Workflow",
    runs_on: str = SELF_HOSTED,
    on_lines: tuple[str, ...] = ("  pull_request:",),
    header_lines: tuple[str, ...] = (),
    step_lines: tuple[str, ...] = ("      - run: python scripts/ci/x.py",),
) -> str:
    lines = [f"name: {title}", *header_lines, "on:", *on_lines, "jobs:", "  job:"]
    lines.append(f"    runs-on: {runs_on}")
    lines.append("    steps:")
    lines.extend(step_lines)
    return "\n".join(lines) + "\n"


def verdict_for(tmp_path: Path, body: str, name: str = "wf.yml") -> audit.WorkflowVerdict:
    path = tmp_path / name
    path.write_text(body, encoding="utf-8")
    return audit.audit_workflow(path)


def write(tmp_path: Path, name: str, body: str) -> Path:
    path = tmp_path / name
    path.write_text(body, encoding="utf-8")
    return path


# --- Classe 1 : le mot vit dans un COMMENTAIRE ------------------------------


def test_comment_mention_does_not_accuse(tmp_path: Path) -> None:
    """Le faux positif fondateur : `elan` matche « relance » et « appelant »."""
    body = workflow(
        title="Re-aggregate",
        header_lines=(
            "# Ce sweep ne se relance que sur un push, et un appelant manuel",
            "# peut le declencher. Aucun besoin reel ici.",
        ),
    )
    verdict = verdict_for(tmp_path, body)
    assert verdict.self_hosted_jobs
    assert verdict.has_local_need is False
    assert verdict.families == []


def test_shell_comment_inside_a_run_block_is_stripped(tmp_path: Path) -> None:
    body = workflow(
        step_lines=(
            "      - run: |",
            "          # commentaire shell : on ne lance PAS lake build ici",
            "          python scripts/ci/guard.py",
        )
    )
    assert verdict_for(tmp_path, body).has_local_need is False


# --- Classe 2 : le mot vit dans un champ de PROSE ou de DECLENCHEMENT ------


def test_workflow_title_is_not_a_need(tmp_path: Path) -> None:
    """`name: Notebook Papermill Ratchet` : le titre nomme, il n'execute pas."""
    body = workflow(title="Notebook Papermill Ratchet")
    assert verdict_for(tmp_path, body).has_local_need is False


def test_trigger_paths_filter_is_not_a_need(tmp_path: Path) -> None:
    """`paths: ['**.ipynb']` est une CONDITION D'ENTREE, pas un besoin."""
    body = workflow(
        title="Solution leak guard",
        on_lines=("  pull_request:", "    paths:", "      - '**.ipynb'"),
        step_lines=("      - run: python scripts/notebook_tools/audit_solution_leaks.py",),
    )
    assert verdict_for(tmp_path, body).has_local_need is False


def test_script_path_named_after_a_capability_is_not_a_need(tmp_path: Path) -> None:
    """`scripts/notebook_tools/...` est un CHEMIN, pas un besoin de notebook."""
    body = workflow(
        title="Catalog",
        on_lines=("  schedule:",),
        step_lines=("      - run: python scripts/notebook_tools/generate_catalog.py",),
    )
    assert verdict_for(tmp_path, body).has_local_need is False


def test_directory_named_after_an_internal_service_is_not_a_need(tmp_path: Path) -> None:
    """`Playwright-OWUI/package-lock.json` a accuse un nom de REPERTOIRE."""
    body = workflow(
        title="OWUI check",
        step_lines=(
            "      - uses: actions/cache@v4",
            "        with:",
            "          path: GenAI/Open-WebUI/Playwright-OWUI/package-lock.json",
        ),
    )
    assert verdict_for(tmp_path, body).has_local_need is False


# --- Classe 3 : un token automatique n'est pas un besoin LOCAL -------------


def test_automatic_github_token_is_not_a_local_need(tmp_path: Path) -> None:
    body = workflow(
        title="Advisory",
        on_lines=("  schedule:",),
        step_lines=(
            "      - env:",
            "          GH_TOKEN: ${{ secrets.GITHUB_TOKEN }}",
            "        run: gh api repos/x/y",
        ),
    )
    verdict = verdict_for(tmp_path, body)
    assert verdict.has_local_need is False
    assert verdict.families == []
    # Mesure informative conservee : le retrait du motif est auditable.
    assert "secret-automatic" in {
        item.family for item in verdict.self_hosted_jobs[0].evidence
    }


def test_custom_repository_secret_is_a_need(tmp_path: Path) -> None:
    body = workflow(
        title="Deploy",
        on_lines=("  push:",),
        step_lines=(
            "      - env:",
            "          PAT: ${{ secrets.RUNNERS_READ_PAT }}",
            "        run: gh api repos/x/y",
        ),
    )
    verdict = verdict_for(tmp_path, body)
    assert verdict.has_local_need is True
    assert "secret" in verdict.families


# --- Besoins reels : l'organe ne doit pas etre aveugle ---------------------


def test_papermill_in_a_run_step_is_a_notebook_need(tmp_path: Path) -> None:
    body = workflow(step_lines=("      - run: papermill in.ipynb out.ipynb",))
    verdict = verdict_for(tmp_path, body)
    assert verdict.has_local_need is True
    assert "notebook" in verdict.families


def test_nvidia_smi_is_a_gpu_need(tmp_path: Path) -> None:
    body = workflow(
        title="Train",
        on_lines=("  schedule:",),
        step_lines=("      - run: nvidia-smi && python train.py",),
    )
    assert "gpu" in verdict_for(tmp_path, body).families


def test_localhost_is_an_internal_network_need(tmp_path: Path) -> None:
    body = workflow(
        title="Stack",
        on_lines=("  workflow_dispatch:",),
        step_lines=("      - run: curl -sf http://localhost:8188/system_stats",),
    )
    assert "internal-network" in verdict_for(tmp_path, body).families


def test_lake_build_is_a_lean_need(tmp_path: Path) -> None:
    body = workflow(
        title="Lean",
        on_lines=("  push:",),
        step_lines=("      - run: lake build",),
    )
    assert "lean" in verdict_for(tmp_path, body).families


# --- Detection du pool ------------------------------------------------------


def test_dynamic_runs_on_resolving_to_the_pool_is_self_hosted(tmp_path: Path) -> None:
    body = workflow(
        title="Gate",
        runs_on=(
            "${{ (github.event.pull_request.head.repo.full_name == github.repository)"
            " && fromJSON('[\"self-hosted\",\"coursia-waiter\"]') || 'ubuntu-latest' }}"
        ),
        step_lines=("      - run: python scripts/ci/pr_gate.py",),
    )
    assert len(verdict_for(tmp_path, body).self_hosted_jobs) == 1


def test_github_hosted_job_is_not_reported(tmp_path: Path) -> None:
    body = workflow(
        title="Hosted",
        runs_on="ubuntu-latest",
        step_lines=("      - run: papermill in.ipynb out.ipynb",),
    )
    assert verdict_for(tmp_path, body).self_hosted_jobs == []


# --- Decomposition de la sur-accusation ------------------------------------


def test_legacy_source_labels_a_comment_accusation(tmp_path: Path) -> None:
    body = workflow(header_lines=("# le sweep ne se relance pas tout seul",))
    path = write(tmp_path, "c.yml", body)
    assert audit.audit_workflow(path).legacy_source == "comment"


def test_legacy_source_labels_an_automatic_secret_accusation(tmp_path: Path) -> None:
    body = workflow(
        title="Advisory",
        on_lines=("  schedule:",),
        step_lines=(
            "      - env:",
            "          GH_TOKEN: ${{ secrets.GITHUB_TOKEN }}",
            "        run: gh api repos/x/y",
        ),
    )
    path = write(tmp_path, "a.yml", body)
    assert audit.audit_workflow(path).legacy_source == "automatic-secret"


def test_legacy_source_labels_a_title_or_trigger_accusation(tmp_path: Path) -> None:
    path = write(tmp_path, "t.yml", workflow(title="Conda notebooks"))
    assert audit.audit_workflow(path).legacy_source == "name-or-trigger"


# --- Rapport et CLI ---------------------------------------------------------


def test_report_separates_the_two_error_directions(tmp_path: Path) -> None:
    write(tmp_path, "over.yml", workflow(title="Papermill Ratchet"))
    write(
        tmp_path,
        "need.yml",
        workflow(title="Exec", step_lines=("      - run: papermill in.ipynb out.ipynb",)),
    )
    verdicts, broken = audit.audit(tmp_path)
    report = audit.build_report(verdicts, broken, tmp_path)
    assert broken == []
    assert report["self_hosted_workflows"] == 2
    assert report["without_local_need"] == 1
    assert report["legacy_over_accused"] == ["over.yml"]
    assert report["legacy_under_accused"] == []
    assert report["legacy_over_accused_sources"] == {"name-or-trigger": 1}


def test_cli_json_and_out_dir(tmp_path: Path) -> None:
    write(
        tmp_path,
        "need.yml",
        workflow(title="Exec", step_lines=("      - run: papermill in.ipynb out.ipynb",)),
    )
    out_dir = tmp_path / "out"
    rc = audit.main(
        ["--workflows-dir", str(tmp_path), "--json", "--out-dir", str(out_dir)]
    )
    assert rc == audit.EXIT_OK
    assert (out_dir / "latest.json").exists()
    assert (out_dir / "latest.md").exists()
    report = json.loads((out_dir / "latest.json").read_text(encoding="utf-8"))
    assert report["with_local_need"] == 1


def test_cli_reports_a_missing_directory(tmp_path: Path) -> None:
    rc = audit.main(["--workflows-dir", str(tmp_path / "absent")])
    assert rc == audit.EXIT_BROKEN


def test_invalid_yaml_is_broken_not_silent(tmp_path: Path) -> None:
    write(tmp_path, "bad.yml", "name: [unclosed\n")
    _, broken = audit.audit(tmp_path)
    assert broken and "bad.yml" in broken[0]


def test_repository_audit_reads_every_workflow() -> None:
    """Le depot reel se lit sans instrument casse.

    L'assertion est la COMPLETUDE, pas un compte : figer un nombre ferait
    rougir l'organe au prochain workflow legitime, ce que le scanner de policy
    self-hosted documente deja comme anti-pattern (#13135).
    """
    workflows_dir = Path(__file__).resolve().parents[2] / ".github" / "workflows"
    verdicts, broken = audit.audit(workflows_dir)
    assert broken == []
    assert verdicts
    names = [verdict.name for verdict in verdicts]
    assert len(names) == len(set(names))
