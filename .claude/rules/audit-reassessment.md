# Audit Reassessment Protocol

**Source:** Issue #499 — Mandatory verification before fixing any NanoClaw (#488) finding.
**Rationale:** NanoClaw audit has ~60% false positive rate (verified independently on 17-item sample). Blind fixes propagate fake work.

## When This Applies

This rule applies to **any fix based on automated audit findings** (NanoClaw #488 or similar tools). Do NOT open a PR for an audit finding without completing the reassessment protocol first.

## Protocol (4 steps, mandatory before any fix PR)

### Step 1: Mechanical Verification

```python
import json
with open(notebook_path) as f:
    nb = json.load(f)
code = [c for c in nb['cells'] if c['cell_type']=='code']
exec_count = sum(1 for c in code if c.get('execution_count'))
outputs = sum(1 for c in code if c.get('outputs'))
errors = sum(1 for c in code if any(o.get('output_type')=='error' for o in c.get('outputs',[])))
print(f'{len(code)} cells, {exec_count} executed, {outputs} outputs, {errors} errors')
```

If `exec_count == len(code)` and `errors == 0` while audit reports "code never executed" -> **FALSE POSITIVE**. Stop here.

### Step 2: Pedagogical Verification (only if Step 1 shows issues)

Read the notebook directly. Classify the finding:

| Classification | Meaning | Action |
|---------------|---------|--------|
| **CONFIRMED bug** | Code errors that persist on re-execution | Fix code + re-execute |
| **CONFIRMED outputs stripped** | Code exec OK but outputs cleared before commit | Re-execute only, no code fix PR needed |
| **CONFIRMED pedagogy** | Interpretation describes different results than actual outputs | Reformulate markdown or re-execute |
| **FALSE POSITIVE** | Everything is fine, audit finding is wrong | Report on dashboard, no PR |

### Step 3: Report

Before opening a PR, report on RooSync dashboard:
```
Item M-XX : [CONFIRMED bug | CONFIRMED outputs stripped | CONFIRMED pedagogy | FALSE POSITIVE]
Details : [direct read vs audit claim]
```

### Step 4: Fix (only if CONFIRMED)

- **CONFIRMED bug**: fix code + Papermill re-execution
- **CONFIRMED outputs stripped**: re-execute only (no PR fix code)
- **CONFIRMED pedagogy**: reformulate interpretations or re-execute
- **FALSE POSITIVE**: report on dashboard, close the finding, no PR

## Known False Positive Patterns

NanoClaw systematically misidentifies:
- .NET Interactive notebooks with rich HTML outputs (not detected)
- Notebooks with outputs cleaned before commit (valid but `outputs=0` confused with "never executed")
- Exercise cells with valid `execution_count: N` and empty `outputs: []` (stubs, not missing exec)
- Shortened/old file paths in findings
- Incomplete exercise/TODO detection

## Items Already Verified

### Confirmed Bugs
- M-64 RiskParity: simulation off-by-one, 5/9 cells with errors
- M-66 Temporal-CNN: 2/5 cells with errors

### Confirmed Outputs Stripped
- M-49 Crypto-MultiCanal: 15/24 exec, 0 outputs
- M-56 QC/BTC-MACD-ADX: 5/5 exec, 0 outputs

### Confirmed Pedagogy Gaps
- M-13 Audio/02-5: 0 exercises (no-exercise notebook)
- M-23 Cross-Stitch-Legacy: 2/6 cells exec
- M-70 App-13-TSP: 3 exercises all pre-resolved (no stubs)

### Confirmed False Positives (do NOT re-dispatch)
- M-2 GT-10-ForwardInduction-SPE (14/14 exec 0 err)
- M-3 GT-12-ReputationGames (12/12 exec 0 err)
- M-4 GT-14-DifferentialGames (11/11 exec 0 err)
- M-5 GT-1-Setup (20/20 exec 0 err)
- M-7 GT-7-ExtensiveForm (14/14 exec 10 outputs)
- M-20 SK-01-Intro (9/9 exec 0 err)
- M-34 Video/01-3-Qwen-VL (9/10 exec 7 outputs)
- M-40 IIT-Intro_to_PyPhi (11/11 exec 10 outputs 0 err)
- M-68 App-9b-EdgeDetection-CSharp (11/11 exec 11 outputs 0 err)
- SC-22 Solana-Anchor (6/6 exec 0 err — print-based demos are only viable approach for Solana/Rust in Python kernel)
- SC-11 LLM-Assisted (15/15 exec 0 err — exercise stubs correctly have empty outputs)

## Acceptance Criteria

- Every PR based on audit findings must include: "Reassessed by [agent]: CONFIRMED [type]"
- Dashboard documents identified FP to prevent re-dispatch
- This rule is the reference for any future audit-based mission
