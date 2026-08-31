"""#13861 cliquet: notebook-validation and validation-matrix expose workflow_dispatch.

Cancel-in-progress cancels each PR's run on the next push, leaving the final
tree of a merge batch un-revalidated (issue #13861). Workflow_dispatch is the
only way to revalidate the final tree without an empty commit. This test
ensures the trigger stays present; removing it would silently re-break the
defect the issue was opened against.
"""
from __future__ import annotations

import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
WORKFLOWS = REPO_ROOT / ".github" / "workflows"

NEEDS_DISPATCH = (
    "notebook-validation.yml",
    "validation-matrix.yml",
)


def _triggers(path: Path) -> set[str]:
    """Return the set of trigger names declared on the workflow.

    YAML parses the bare ``on:`` key as Python True (a YAML 1.1 quirk). Be
    defensive about both spellings so the test does not blink if a future
    contributor writes ``on:`` as a quoted string.
    """
    data = yaml.safe_load(path.read_text(encoding="utf-8"))
    if True in data:
        return set(data[True].keys())
    if "on" in data:
        return set(data["on"].keys())
    return set()


def test_revalidate_workflows_expose_workflow_dispatch() -> None:
    missing = []
    for name in NEEDS_DISPATCH:
        triggers = _triggers(WORKFLOWS / name)
        if "workflow_dispatch" not in triggers:
            missing.append(name)
    assert not missing, (
        f"workflow_dispatch absent on {missing}; revalidation after a merge "
        f"batch (#13861) breaks without it."
    )


def test_revalidate_workflows_no_job_level_pull_request_filter() -> None:
    """A job-level `if: github.event_name != 'pull_request'` would skip
    workflow_dispatch-derived runs (event_name == 'workflow_dispatch').

    Such a guard was never introduced on these two workflows, and this test
    pins that absence so a future copy-paste from another workflow does not
    silently break revalidation.
    """
    import re

    for name in NEEDS_DISPATCH:
        text = (WORKFLOWS / name).read_text(encoding="utf-8")
        # job-level ifs sit under `jobs:`; pull_request_filter would look like
        # `if: github.event_name != 'pull_request'` or similar. We tolerate
        # the workflow-level concurrency guard (cancel-in-progress) which is
        # not at the job level.
        in_jobs = re.search(r"^jobs:.*?(?=^[a-z]|\Z)", text, re.S | re.M)
        assert in_jobs, f"{name}: no `jobs:` block found"
        jobs_block = in_jobs.group(0)
        assert "github.event_name" not in jobs_block or (
            "workflow_dispatch" in jobs_block
        ), (
            f"{name}: job-level `if:` filters on `github.event_name` would "
            f"skip the workflow_dispatch revalidate path; pin it explicitly "
            f"or remove the filter."
        )


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))  # type: ignore[name-defined]
