# Audit Reassessment Protocol

**Source:** Issue #499 — vérification obligatoire avant tout fix sur NanoClaw (#488) finding.
**Rationale:** NanoClaw audit a ~60% false positive rate (vérifié sur 17-item sample). Fixes aveugles propagent fake work.

S'applique à **tout fix basé sur audit automatisé** (NanoClaw ou similaire). Pas de PR sur un audit finding sans avoir complété le protocole.

**Items déjà reclassés, script Step 1, patterns FP connus** : [docs/audit-reassessment-findings.md](../../docs/reference/audit-reassessment-findings.md).

## Protocole 4 étapes (HARD)

| Step | Action | Conclusion |
|------|--------|------------|
| **1. Vérif mécanique** | Compter cellules code, `execution_count`, `outputs`, `errors` (script Python : [detail](../../docs/reference/audit-reassessment-findings.md#step-1--vérification-mécanique)) | `exec_count == len(code)` et `errors == 0` alors que audit dit "never executed" → **FALSE POSITIVE**, stop |
| **2. Vérif pédagogique** | Lire le notebook directement, classifier | `CONFIRMED bug` / `CONFIRMED outputs stripped` / `CONFIRMED pedagogy` / `FALSE POSITIVE` |
| **3. Reporter dashboard** | `Item M-XX : [classification] — details : [direct read vs audit claim]` | Documenter pour prévenir re-dispatch |
| **4. Fix si CONFIRMED** | bug→fix+re-exec ; outputs stripped→re-exec seul ; pedagogy→reformuler ; FP→fermer | Pas de PR sur FP |

## Critères d'acceptation

- Chaque PR basée sur audit findings doit inclure : `Reassessed by [agent]: CONFIRMED [type]`
- Dashboard documente les FP identifiés pour prévenir re-dispatch
- Cette règle est la référence pour toute mission audit-based future
