---
name: review-student-prs
description: Review and merge student exercise PRs during TP sessions. Arguments: <repo-url> [--class <class-id>] [--timeslot <HH:MM-HH:MM>] [--dry-run]
---

# Review Student PRs

Review, validate, and intelligently merge student exercise PRs submitted during TP sessions.

**Target**: `$ARGUMENTS`

## Arguments

- `repo-url`: GitHub repository URL (e.g., `https://github.com/jsboigeECE/2026-ECE-Ing4-Fin-IA-Projet1-Gr01`)
- `--class <class-id>`: Class identifier (e.g., `Gr01`, `Gr02`, `Gr03`)
- `--timeslot <HH:MM-HH:MM>`: Authorized submission window (e.g., `08:00-12:00`). PRs outside this window are flagged
- `--dry-run`: Review only, no merge or commit

## Process

### Phase 1 - Discovery & Identification

1. **Fetch open PRs** from the target repo using `gh pr list`
2. **Filter by timeslot** - Only PRs created within the authorized submission window
3. **Identify students**:
   - Parse PR title/body for student name, group, notebook claimed
   - Cross-reference GitHub username with submission account
   - If available, match against inscription spreadsheet (`G:\Mon Drive\MyIA\Formation\ECE\2026\`)
4. **Flag anomalies**: PRs outside timeslot, duplicate claims on same notebook, unknown accounts

### Phase 2 - Code Review

For each valid PR:

1. **Fetch PR diff** using `gh pr diff <number>`
2. **Identify modified notebooks** and changed cells
3. **Validate exercise completion**:
   - Check that exercise cells have been filled (not empty or placeholder)
   - Verify code is syntactically correct
   - Check markdown cells for explanations if required
4. **Execute locally**:
   - Checkout PR branch locally
   - Execute modified notebook cells using `python scripts/notebook_tools/notebook_helpers.py execute <path> --verbose`
   - For .NET notebooks: use MCP cell-by-cell execution
   - Record execution results (pass/fail, output, errors)
5. **Quality assessment** (per exercise):
   - Code correctness (executes without error)
   - Code quality (reasonable approach, not copy-paste from examples)
   - Explanation quality (if markdown present)
   - Score: VALID / PARTIAL / INVALID

### Phase 3 - Report Generation

Generate a correction report in `reports/corrections/` (gitignored):

```
reports/corrections/YYYY-MM-DD_<class-id>_review.md
```

Report format:
```markdown
# TP Review - <date> - <class-id>

## Summary
- PRs reviewed: N
- Valid exercises: N (+0.5 pts each)
- Partial: N (manual review needed)
- Invalid: N

## Per-Student Results

### <Student Name> (GitHub: @username)
- **PR**: #<number> - <title>
- **Notebook**: <notebook-name>
- **Timeslot**: <created-at> (VALID/LATE)
- **Exercises**:
  | Exercise | Status | Score | Notes |
  |----------|--------|-------|-------|
  | Ex 1     | VALID  | +0.5  | Clean implementation |
  | Ex 2     | PARTIAL| 0     | Missing explanation |
- **Total bonus**: +X.X points
```

### Phase 4 - Intelligent Merge

For each VALID exercise (skip if `--dry-run`):

1. **Transform exercise result into example**:
   - The student's completed exercise cell becomes a new example cell
   - Rewrite the preceding markdown to frame it as "Example - <topic>" instead of "Exercise"
   - Add brief commentary on the approach used
   - Preserve the student's code as-is (it's their contribution)

2. **Create replacement exercise**:
   - Add a NEW exercise cell after the newly created example
   - The new exercise must be:
     - Different from the one just solved (not a trivial variant)
     - Not directly derivable from the example above
     - At a similar difficulty level
     - Related to the same topic/concept
   - Add appropriate markdown instructions for the new exercise

3. **Curate redundancy**:
   - If multiple students solved the same exercise across PRs:
     - Keep the most pedagogically valuable solution as example
     - Remove redundant examples that don't add new insight
     - Ensure the notebook flow remains coherent
   - If a notebook accumulates too many examples (>3 consecutive examples on same concept):
     - Keep the 2 most distinct/illustrative ones
     - Remove the others
     - Adjust markdown transitions

4. **Commit changes**:
   ```
   feat(ece): integrate student exercise <notebook> - <student> (+0.5 bonus)

   - Exercise result converted to example
   - New replacement exercise added
   - Reviewed and validated during TP <date>

   Co-Authored-By: <Student Name> <student-email-if-available>
   Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>
   ```

5. **Push** to main (after all PRs for the session are processed)

### Phase 5 - Cleanup

1. **Close merged PRs** with a comment thanking the student and confirming bonus
2. **Update the correction report** with final merge status
3. **Summary output** to the user with:
   - Number of exercises validated
   - Bonus points attributed per student
   - Any issues requiring manual attention
   - List of notebooks updated with new exercises

## Important Notes

- **Timing**: Run between classes (e.g., noon-2pm) so afternoon class gets fresh exercises
- **Merge order**: Process PRs in submission order (FIFO)
- **Conflict resolution**: If two PRs modify the same notebook, merge the first, rebase the second
- **Security**: Never execute untrusted code outside the notebook sandbox
- **Backup**: Create a local branch backup before merging: `backup/pre-merge-<date>`
- **No force push**: All merges are regular merges or fast-forwards
- **Report confidentiality**: Reports in `reports/corrections/` are gitignored, never committed

## Notebook Types

| Series | Kernel | Execution Method |
|--------|--------|-----------------|
| Probas | .NET C# | MCP cell-by-cell |
| GameTheory | Python (WSL) | papermill or notebook_helpers |
| ML | Mixed (.NET + Python) | Depends on notebook |

## Spreadsheet Reference

Student inscriptions and evaluations:
- `G:\Mon Drive\MyIA\Formation\ECE\2026\` - CSV/XLSX files
- Match GitHub usernames to student names for bonus attribution
