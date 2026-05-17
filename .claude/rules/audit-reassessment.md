# Audit Reassessment Protocol

**Source:** Issue #499 — Mandatory verification before fixing any NanoClaw (#488) finding.
**Rationale:** NanoClaw audit has ~60% false positive rate (verified on 17-item sample). Blind fixes propagate fake work.

S'applique à **tout fix basé sur audit automatisé** (NanoClaw ou similaire). Pas de PR sur un audit finding sans avoir complété le protocole.

**Items déjà reclassés + patterns NanoClaw false positive connus** : [docs/audit-reassessment-findings.md](../../docs/audit-reassessment-findings.md).

## Protocole 4 étapes (HARD)

### Step 1 : Vérification mécanique

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

### Step 2 : Vérification pédagogique (seulement si Step 1 montre des problèmes)

Lire le notebook directement. Classifier :

| Classification | Signification | Action |
|---------------|---------------|--------|
| **CONFIRMED bug** | Erreurs code persistantes à la re-exécution | Fix code + re-execute |
| **CONFIRMED outputs stripped** | Code exec OK mais outputs cleared avant commit | Re-execute seulement, pas de PR code |
| **CONFIRMED pedagogy** | Interprétation décrit des résultats différents des outputs réels | Reformuler markdown ou re-execute |
| **FALSE POSITIVE** | Tout va bien, audit faux | Reporter sur dashboard, pas de PR |

### Step 3 : Reporter sur dashboard

```
Item M-XX : [CONFIRMED bug | CONFIRMED outputs stripped | CONFIRMED pedagogy | FALSE POSITIVE]
Details : [direct read vs audit claim]
```

### Step 4 : Fix (seulement si CONFIRMED)

- **CONFIRMED bug** : fix code + Papermill re-exécution
- **CONFIRMED outputs stripped** : re-execute seulement (pas de PR fix code)
- **CONFIRMED pedagogy** : reformuler interpretations ou re-execute
- **FALSE POSITIVE** : reporter sur dashboard, fermer le finding, pas de PR

## Critères d'acceptation

- Chaque PR basée sur audit findings doit inclure : `Reassessed by [agent]: CONFIRMED [type]`
- Dashboard documente les FP identifiés pour prévenir re-dispatch
- Cette règle est la référence pour toute mission audit-based future
