"""Helper for the markdown-table-guard workflow.

Reads the JSON output of `scan_md_table_syntax.py --json` from
`/tmp/md-table-findings.json` and writes a Markdown summary to
`$GITHUB_STEP_SUMMARY` (or stdout if the env var is unset).

Designed to be called from the CI workflow as a single, self-contained step
rather than embedding Python in YAML heredocs (which makes the workflow
file itself fail `check_workflow_label_paths.py` YAML parsing).
"""

import collections
import json
import os
import sys
from pathlib import Path


JSON_PATH = Path("/tmp/md-table-findings.json")


def main() -> int:
    if not JSON_PATH.exists():
        print("ERROR: no findings JSON at /tmp/md-table-findings.json", file=sys.stderr)
        return 1

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    total = data["total"]
    flagged = data["flagged"]
    findings = data["findings"]

    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    out_lines: list[str] = []

    if flagged == 0:
        out_lines.append(f"## markdown-table-guard (advisory): 0/{total} files flagged.")
        out_lines.append("")
        out_lines.append("No COL_MISMATCH / NO_SEP / NO_BLANK_BEFORE / NO_BLANK_AFTER defects detected.")
    else:
        by_pathology = collections.Counter(f["pathology"] for f in findings)
        by_file = collections.Counter(f["file"] for f in findings)
        out_lines.append(
            f"## markdown-table-guard (advisory): {flagged}/{total} files flagged, "
            f"{len(findings)} findings."
        )
        out_lines.append("")
        out_lines.append("### Distribution by pathology")
        for p, c in by_pathology.most_common():
            out_lines.append(f"- **{p}**: {c}")
        out_lines.append("")
        out_lines.append("### Top files")
        for f, c in by_file.most_common(15):
            out_lines.append(f"- `{f}`: {c}")
        out_lines.append("")
        out_lines.append("See the job log for full findings. This guard is advisory only.")

    payload = "\n".join(out_lines) + "\n"
    if summary_path:
        Path(summary_path).write_text(payload, encoding="utf-8")
    else:
        print(payload)
    return 0


if __name__ == "__main__":
    sys.exit(main())
