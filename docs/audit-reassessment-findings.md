# Audit Reassessment Findings (NanoClaw #488)

Liste des items déjà reclassés par le protocole [.claude/rules/audit-reassessment.md](../.claude/rules/audit-reassessment.md). Mettre à jour lors de chaque nouvelle reassessment.

## Confirmed Bugs

- M-64 RiskParity: simulation off-by-one, 5/9 cells with errors
- M-66 Temporal-CNN: 2/5 cells with errors

## Confirmed Outputs Stripped

- M-49 Crypto-MultiCanal: 15/24 exec, 0 outputs
- M-56 QC/BTC-MACD-ADX: 5/5 exec, 0 outputs

## Confirmed Pedagogy Gaps

- M-13 Audio/02-5: 0 exercises (no-exercise notebook)
- M-23 Cross-Stitch-Legacy: 2/6 cells exec
- M-70 App-13-TSP: 3 exercises all pre-resolved (no stubs)

## Confirmed False Positives (do NOT re-dispatch)

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

## NanoClaw Known False Positive Patterns

NanoClaw systematically misidentifies :
- .NET Interactive notebooks with rich HTML outputs (not detected)
- Notebooks with outputs cleaned before commit (valid but `outputs=0` confused with "never executed")
- Exercise cells with valid `execution_count: N` and empty `outputs: []` (stubs, not missing exec)
- Shortened/old file paths in findings
- Incomplete exercise/TODO detection
