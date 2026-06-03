#!/usr/bin/env python3
"""
Scan student forks for commits without PRs.

Identifies students who pushed to their fork but never opened a PR,
so their submissions are invisible to the grading pipeline.

Usage:
    # Dry-run (default): scan and report
    python scan_student_forks.py --school epita --output tmp/scan_2026-04-30/

    # Scan all schools
    python scan_student_forks.py --school all --output tmp/scan_2026-04-30/

    # Apply mode: also create PRs for flagged forks (interactive confirmation)
    python scan_student_forks.py --school epita --apply --output tmp/scan_2026-04-30/
"""

import argparse
import csv
import json
import os
import re
import subprocess
import sys
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# --- Configuration ---

REPOS = {
    "coursia": "jsboige/CoursIA",
    "epita-prcon": "jsboigeEpita/2026-Epita-Programmation-par-Contraintes",
}

ECE_REPOS = [
    f"jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet{i}-Gr{g:02d}"
    for i in [1, 2] for g in [1, 2, 3]
]

EPF_REPO = "jsboigeEPF/2025-MSBNS3IN03-GenAI"

GDRIVE_BASE = Path("G:/Mon Drive/MyIA/Formation")

ROSTER_PATHS = {
    "epita": {
        "inscriptions": GDRIVE_BASE / "Epita/2026/SCIA-2026-Inscription-PrCon.csv",
        "groups": GDRIVE_BASE / "Epita/2026/Groupe Programmation Par Contrainte - Feuille 1.csv",
    },
    "ece": {
        "group1": GDRIVE_BASE / "ECE/2026/Groupe1_participants.csv",
        "group2": GDRIVE_BASE / "ECE/2026/Groupe2_participants.csv",
        "group3": GDRIVE_BASE / "ECE/2026/Groupe3_participants.csv",
    },
}


# --- Data classes ---

@dataclass
class Student:
    first_name: str = ""
    last_name: str = ""
    email: str = ""
    school: str = ""
    group: str = ""
    epita_login: str = ""


@dataclass
class ForkInfo:
    owner: str
    repo: str
    commits_ahead: int = 0
    ahead_shas: list = field(default_factory=list)
    student: Optional[Student] = None
    has_pr: bool = False
    pr_number: int = 0
    pr_state: str = ""
    files_modified: list = field(default_factory=list)
    flagged: bool = False


# --- Helpers ---

def gh_api(endpoint: str, jq: str = ".") -> str:
    """Call gh api with pagination, return raw JSON string."""
    result = subprocess.run(
        ["gh", "api", "--paginate", endpoint],
        capture_output=True, text=True, timeout=120
    )
    if result.returncode != 0:
        print(f"  WARN: gh api {endpoint} failed: {result.stderr.strip()}", file=sys.stderr)
        return "[]"
    return result.stdout


def gh_api_jq(endpoint: str, jq_filter: str) -> list:
    """Call gh api and extract with jq."""
    result = subprocess.run(
        ["gh", "api", "--paginate", endpoint, "--jq", jq_filter],
        capture_output=True, text=True, timeout=120
    )
    if result.returncode != 0:
        return []
    return [line for line in result.stdout.strip().split("\n") if line]


def strip_accents(text: str) -> str:
    """Remove accents for fuzzy matching."""
    nfkd = unicodedata.normalize("NFKD", text)
    return "".join(c for c in nfkd if not unicodedata.combining(c))


def normalize_name(name: str) -> str:
    """Normalize for comparison: lowercase, no accents, no spaces/hyphens."""
    return strip_accents(name).lower().replace(" ", "").replace("-", "").replace("'", "")


# --- Roster loading ---

def load_epita_roster() -> list[Student]:
    """Load EPITA PrCon student roster from CSV."""
    students = []
    path = ROSTER_PATHS["epita"]["inscriptions"]
    if not path.exists():
        print(f"  WARN: EPITA roster not found: {path}", file=sys.stderr)
        return students

    with open(path, encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)
        for row in reader:
            if not row.get("Prenom"):
                continue
            # Extract login from mail (prenom.nom@epita.fr)
            email = row.get("Mail", "")
            epita_login = email.split("@")[0] if "@" in email else ""
            students.append(Student(
                first_name=row.get("Prenom", "").strip(),
                last_name=row.get("Nom", "").strip(),
                email=email.strip(),
                school="EPITA",
                group="SCIA 2027",
                epita_login=epita_login.strip(),
            ))
    print(f"  Loaded {len(students)} EPITA students")
    return students


def load_ece_roster() -> list[Student]:
    """Load ECE student rosters from all 3 group CSVs."""
    students = []
    for group_key in ["group1", "group2", "group3"]:
        path = ROSTER_PATHS["ece"][group_key]
        if not path.exists():
            print(f"  WARN: ECE roster not found: {path}", file=sys.stderr)
            continue
        group_num = group_key.replace("group", "")
        with open(path, encoding="utf-8-sig") as f:
            reader = csv.DictReader(f)
            for row in reader:
                prenom = row.get("Prénom", "").strip()
                nom = row.get("Nom de famille", "").strip()
                if not prenom:
                    continue
                email = row.get("Adresse de courriel", "").strip()
                students.append(Student(
                    first_name=prenom,
                    last_name=nom,
                    email=email,
                    school="ECE",
                    group=f"Ing4 Finance Gr{group_num}",
                ))
    print(f"  Loaded {len(students)} ECE students")
    return students


# --- Fork scanning ---

def list_forks(repo: str) -> list[str]:
    """List all fork owner logins for a repo."""
    owners = gh_api_jq(f"repos/{repo}/forks", ".[].owner.login")
    return owners


def get_ahead_commits(repo: str, fork_owner: str) -> tuple[int, list[str]]:
    """Get number of commits ahead and their SHAs."""
    try:
        result = subprocess.run(
            ["gh", "api", f"repos/{repo}/compare/main...{fork_owner}:main",
             "--jq", ".ahead_by, (.commits // [] | .[].sha)"],
            capture_output=True, text=True, timeout=30
        )
        if result.returncode != 0:
            return 0, []
        lines = result.stdout.strip().split("\n")
        if not lines or not lines[0].strip():
            return 0, []
        ahead_by = int(lines[0].strip())
        shas = [line.strip()[:7] for line in lines[1:] if line.strip()]
        return ahead_by, shas
    except (subprocess.TimeoutExpired, ValueError):
        return 0, []


def get_commit_details(repo: str, fork_owner: str, sha: str) -> dict:
    """Get commit details: author, message, files."""
    try:
        result = subprocess.run(
            ["gh", "api", f"repos/{fork_owner}/{repo.split('/')[-1]}/commits/{sha}",
             "--jq", '{author: .commit.author.name, email: .commit.author.email, message: .commit.message, files: [.files[].filename]}'],
            capture_output=True, text=True, timeout=30
        )
        if result.returncode != 0:
            return {}
        return json.loads(result.stdout)
    except (subprocess.TimeoutExpired, json.JSONDecodeError):
        return {}


def check_existing_pr(repo: str, fork_owner: str) -> tuple[bool, int, str]:
    """Check if a PR already exists from this fork."""
    # Strategy 1: search by fork owner name in PR titles
    # (more reliable than --head for cross-fork PRs)
    result = subprocess.run(
        ["gh", "pr", "list", "--repo", repo,
         "--state", "all", "--search", fork_owner,
         "--json", "number,state,title", "--limit", "10"],
        capture_output=True, text=True, timeout=30
    )
    if result.returncode == 0 and result.stdout.strip():
        prs = json.loads(result.stdout)
        for pr in prs:
            title = pr.get("title", "").lower()
            if fork_owner.lower() in title:
                return True, pr["number"], pr["state"]

    # Strategy 2: try --head filter (works for PRs created by fork owner)
    result2 = subprocess.run(
        ["gh", "pr", "list", "--repo", repo,
         "--state", "all", "--head", f"{fork_owner}:main",
         "--json", "number,state,title", "--limit", "5"],
        capture_output=True, text=True, timeout=30
    )
    if result2.returncode == 0 and result2.stdout.strip():
        prs = json.loads(result2.stdout)
        if prs:
            return True, prs[0]["number"], prs[0].get("state", "unknown")

    return False, 0, ""


# --- Student matching ---

def match_student(fork_owner: str, commit_authors: list[dict],
                  students: list[Student]) -> Optional[Student]:
    """Match a fork owner to a student using heuristics."""
    owner_norm = normalize_name(fork_owner)

    # Strategy 1: Direct login match (EPITA logins like "lilou.mayot" -> "LilouMayot")
    for s in students:
        if s.epita_login:
            login_norm = normalize_name(s.epita_login.replace(".", ""))
            if login_norm == owner_norm:
                return s

    # Strategy 2: Name in fork owner
    for s in students:
        full_norm = normalize_name(s.first_name + s.last_name)
        if full_norm == owner_norm:
            return s

    # Strategy 3: Commit author email matches roster email
    for ca in commit_authors:
        email = ca.get("email", "").lower()
        for s in students:
            if s.email.lower() == email:
                return s

    # Strategy 4: Commit author name matches student name (fuzzy)
    for ca in commit_authors:
        author_name = ca.get("author", "")
        author_norm = normalize_name(author_name)
        for s in students:
            student_norm = normalize_name(s.first_name + s.last_name)
            if author_norm == student_norm:
                return s
            # Also try last name only
            if normalize_name(s.last_name) in author_norm:
                return s

    return None


# --- Main scanning logic ---

def scan_repo(repo: str, students: list[Student], school: str) -> list[ForkInfo]:
    """Scan all forks of a repo for unsubmitted work."""
    print(f"\n{'='*60}")
    print(f"Scanning {repo} ({school})")
    print(f"{'='*60}")

    forks = list_forks(repo)
    print(f"  Found {len(forks)} forks")

    results = []
    for i, owner in enumerate(forks):
        print(f"  [{i+1}/{len(forks)}] {owner}...", end="", flush=True)

        ahead, shas = get_ahead_commits(repo, owner)

        if ahead == 0:
            print(" no commits ahead, skip")
            continue

        print(f" {ahead} commits ahead", flush=True)

        # Get commit details for matching
        commit_details = []
        for sha in shas[:10]:
            detail = get_commit_details(repo, owner, sha)
            if detail:
                commit_details.append(detail)

        # Collect files modified
        all_files = set()
        for cd in commit_details:
            for f in cd.get("files", []):
                all_files.add(f)

        # Check for existing PR
        has_pr, pr_num, pr_state = check_existing_pr(repo, owner)

        # Match student
        student = match_student(owner, commit_details, students)

        info = ForkInfo(
            owner=owner,
            repo=repo,
            commits_ahead=ahead,
            ahead_shas=shas[:10],
            student=student,
            has_pr=has_pr,
            pr_number=pr_num,
            pr_state=pr_state,
            files_modified=sorted(all_files),
            flagged=not has_pr and ahead > 0,
        )
        results.append(info)

    return results


# --- Report generation ---

def generate_markdown_report(all_results: list[ForkInfo], output_dir: Path) -> Path:
    """Generate markdown report."""
    date_str = datetime.now().strftime("%Y-%m-%d")
    report_path = output_dir / f"fork_scan_report_{date_str}.md"

    total_forks = len(all_results)
    flagged = [f for f in all_results if f.flagged]
    with_pr = [f for f in all_results if f.has_pr]

    lines = [
        f"# Fork Scan Report - {date_str}",
        "",
        "## Summary",
        "",
        f"- Forks with commits ahead: **{total_forks}**",
        f"- Forks with existing PR: **{len(with_pr)}**",
        f"- **Forks WITHOUT PR (to investigate): {len(flagged)}**",
        "",
    ]

    if not flagged:
        lines.append("**All forks with commits have corresponding PRs. No action needed.**")
    else:
        lines.append("## Flagged Forks (commits without PR)")
        lines.append("")
        for i, f in enumerate(flagged, 1):
            student_info = ""
            if f.student:
                student_info = f"{f.student.first_name} {f.student.last_name} ({f.student.school} - {f.student.group})"
            else:
                student_info = "*Unknown student*"

            lines.append(f"### {i}. {student_info}")
            lines.append(f"- Fork: `{f.owner}/{f.repo.split('/')[-1]}`")
            lines.append(f"- Commits ahead: {f.commits_ahead} ({', '.join(f.ahead_shas[:5])})")
            if f.files_modified:
                # Group by directory
                dirs = set()
                for fp in f.files_modified:
                    parts = fp.split("/")
                    dirs.add(parts[0] if len(parts) > 1 else fp)
                lines.append(f"- Files modified: {', '.join(sorted(dirs)[:10])}")
            lines.append(f"- PR: None")
            lines.append("")

    # Also list forks with PRs for completeness
    if with_pr:
        lines.append("## Forks with Existing PRs")
        lines.append("")
        lines.append("| Fork | Student | PR | State | Commits |")
        lines.append("|------|---------|-----|-------|---------|")
        for f in with_pr:
            name = f"{f.student.first_name} {f.student.last_name}" if f.student else f.owner
            lines.append(f"| {f.owner} | {name} | #{f.pr_number} | {f.pr_state} | {f.commits_ahead} |")
        lines.append("")

    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text("\n".join(lines), encoding="utf-8")
    return report_path


def generate_actionable_json(flagged: list[ForkInfo], output_dir: Path) -> Path:
    """Generate JSON file for PR creation."""
    date_str = datetime.now().strftime("%Y-%m-%d")
    json_path = output_dir / f"forks_to_pr_{date_str}.json"

    entries = []
    for f in flagged:
        student = f.student or Student()
        entries.append({
            "fork": f"{f.owner}/{f.repo.split('/')[-1]}",
            "fork_owner": f.owner,
            "repo": f.repo,
            "school": student.school or "Unknown",
            "promotion": student.group or "Unknown",
            "student_name": f"{student.first_name} {student.last_name}".strip() or "Unknown",
            "student_email": student.email or "",
            "commits": f.ahead_shas,
            "commits_ahead": f.commits_ahead,
            "files_modified": f.files_modified,
            "branch_target": f"feat/student-tp-{normalize_name(student.first_name + student.last_name) or f.owner}",
            "discord_pinged": False,
        })

    json_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps({"to_pr": entries, "generated": date_str}, indent=2, ensure_ascii=False), encoding="utf-8")
    return json_path


# --- CLI ---

def main():
    parser = argparse.ArgumentParser(description="Scan student forks for unsubmitted work")
    parser.add_argument("--school", choices=["epita", "ece", "all"], default="all",
                        help="School to scan (default: all)")
    parser.add_argument("--output", default="tmp/scan_latest",
                        help="Output directory for reports")
    parser.add_argument("--apply", action="store_true",
                        help="Also create PRs for flagged forks (interactive)")
    parser.add_argument("--repo", choices=["coursia", "epita-prcon", "all-repos"], default="all-repos",
                        help="Which repo to scan (default: all)")
    args = parser.parse_args()

    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)

    print("=" * 60)
    print("Student Fork Scanner")
    print(f"School: {args.school} | Output: {output_dir}")
    print("=" * 60)

    # Load rosters
    students = []
    if args.school in ("epita", "all"):
        students.extend(load_epita_roster())
    if args.school in ("ece", "all"):
        students.extend(load_ece_roster())

    print(f"\nTotal students loaded: {len(students)}")

    # Scan repos
    all_results = []

    if args.repo in ("coursia", "all-repos"):
        results = scan_repo(REPOS["coursia"], students, args.school)
        all_results.extend(results)

    if args.repo in ("epita-prcon", "all-repos"):
        results = scan_repo(REPOS["epita-prcon"], students, "epita")
        all_results.extend(results)

    if args.repo == "all-repos":
        # Scan ECE repos
        for ece_repo in ECE_REPOS:
            try:
                results = scan_repo(ece_repo, students, "ece")
                all_results.extend(results)
            except Exception as e:
                print(f"  WARN: Failed to scan {ece_repo}: {e}")

    # Generate reports
    flagged = [f for f in all_results if f.flagged]
    with_pr = [f for f in all_results if f.has_pr]

    print(f"\n{'='*60}")
    print("SCAN RESULTS")
    print(f"{'='*60}")
    print(f"Forks with commits ahead: {len(all_results)}")
    print(f"Forks with existing PR: {len(with_pr)}")
    print(f"Forks WITHOUT PR (flagged): {len(flagged)}")

    if flagged:
        print("\nFlagged forks:")
        for f in flagged:
            name = f"{f.student.first_name} {f.student.last_name}" if f.student else f.owner
            print(f"  - {name} ({f.owner}): {f.commits_ahead} commits, files: {len(f.files_modified)}")

    # Write reports
    report_path = generate_markdown_report(all_results, output_dir)
    print(f"\nMarkdown report: {report_path}")

    json_path = generate_actionable_json(flagged, output_dir)
    print(f"Actionable JSON: {json_path}")

    # Apply mode: create PRs
    if args.apply and flagged:
        print(f"\n{'='*60}")
        print("APPLY MODE: Creating PRs for flagged forks")
        print(f"{'='*60}")
        for f in flagged:
            name = f"{f.student.first_name} {f.student.last_name}" if f.student else f.owner
            print(f"\nCreate PR for {name} ({f.owner})?")
            print(f"  Repo: {f.repo}")
            print(f"  Commits: {f.commits_ahead}")
            print(f"  Files: {', '.join(f.files_modified[:5])}")
            answer = input("  [y/N] ").strip().lower()
            if answer == "y":
                branch = f"feat/student-tp-{normalize_name(name) if f.student else f.owner}"
                print(f"  Would create PR on branch {branch}")
                print(f"  TODO: implement PR creation via gh pr create")

    print("\nDone.")


if __name__ == "__main__":
    main()
