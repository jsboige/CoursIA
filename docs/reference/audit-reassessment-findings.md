# Audit Reassessment Findings (NanoClaw #488)

Liste des items déjà reclassés par le protocole [.claude/rules/audit-reassessment.md](../../.claude/rules/audit-reassessment.md). Mettre à jour lors de chaque nouvelle reassessment.

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

## FP connus — organe `check_density_anchor`, ancre « stub d'exercice »

Mesuré le 2026-10-04 sur `MyIA.AI.Notebooks/QuantConnect/Python/*.ipynb` : 46 findings de la sous-classe `ancre = stub d'exercice` / `ancre sans aucun output (stub d'exercice)`. **45 sont des faux positifs.**

L'heuristique d'ancrage prend la cellule de code précédente ; quand celle-ci est un stub d'exercice, elle conclut que la cellule de lecture commente le stub. Or la cellule de lecture est presque toujours un **récapitulatif de fin de section** ou un **titre de la section suivante**, placé après le bloc d'exercice par construction :

- `### <section> — ce qu'il faut retenir` : cite des valeurs mesurées dans des cellules **antérieures** (QC-Py-21 c30 cite α = 0.020, mesuré en c24 — ce n'est pas la réponse de l'exercice 2) ;
- `### Limites de ...`, `## Partie N : ...`, `### Feature Importance Preview` : titres de section, sans rapport avec le stub ;
- `> **Interprétation**` d'une autre partie, déplacée par une consolidation (QC-Py-22 c37/c48, renvois transversaux #13756).

Filtre mécanique (prose portant à la fois une référence en avant — « qui suit », « ci-dessous » — et « exercice N ») : une seule cellule sur les 46. **Ne pas re-dispatcher cette sous-classe** : une réparation en masse produirait 45 éditions aveugles.

## Confirmed — ancrage de lecture réellement mal placé

- QC-Py-04-Research-Workflow c33 : seconde interprétation de la volatilité rolling, dont la prose annonce « l'exercice 1 **qui suit** », alors que l'exercice 1 (c31-c32) se trouve **au-dessus** d'elle — la prose désignait une cellule située en arrière. Corrigé par déplacement de la cellule entre c30 et c31 : la prose redevient vraie, et l'ancrage repasse du stub à la cellule de code qui produit les valeurs citées (c29, 3 outputs). Vérifié après coup : `check_density_anchor.py` ne rapporte plus cette cellule.

## Step 1 — vérification mécanique (script)

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

Si `exec_count == len(code)` et `errors == 0` alors que l'audit reporte "code never executed" → **FALSE POSITIVE**. Stop ici.

## NanoClaw Known False Positive Patterns

NanoClaw systematically misidentifies :
- .NET Interactive notebooks with rich HTML outputs (not detected)
- Notebooks with outputs cleaned before commit (valid but `outputs=0` confused with "never executed")
- Exercise cells with valid `execution_count: N` and empty `outputs: []` (stubs, not missing exec)
- Shortened/old file paths in findings
- Incomplete exercise/TODO detection
