# Cycle c.793 — Pilotage audit sémantique cross-famille (issue #8052)

> **Statut.** Cycle pilote, scope = protocole + grille outillée + 3 notebooks Probas/DecInfer échantillonnés. Documentation pérenne : [`docs/audit/sampling-protocol.md`](../../sampling-protocol.md). Outil : [`scripts/audit/extract_claims_vs_outputs.py`](../../../../scripts/audit/extract_claims_vs_outputs.py).
> **Acceptance.** Valider que la grille **extrait** (claim numérique / fallback silencieux / verdict positif / SOTA tool / cohérence pédagogique) **sans décider** — verdict final = revue humaine/agent compétent dans le domaine, conformément au protocole.

## Échantillon (≥5% de 10 DecInfer)

| Notebook | numeric_claims_total | matched | unmatched | SOTA mentioned | SOTA imported | finding |
|----------|---------------------:|--------:|----------:|----------------|---------------|---------|
| DecInfer-1-Utility-Foundations | 319 | 0 | 319 | Infer.NET, Microsoft.ML.Probabilistic | Infer.NET, Microsoft.ML.Probabilistic | ✅ OK (notebook .NET Interactive, claims nombreux = data brute pour filtrage humain) |
| DecInfer-2-Lean-ExpectedUtility | 44 | 43 | 1 | Infer.NET, Microsoft.ML.Probabilistic, mathlib, **pymc** | (aucun) | ⚠️ **MAJOR : `pymc` mentionné markdown mais 0 import — fallback silencieux possible OU mention pédagogique comparative** |
| DecInfer-4-Multi-Attribute | 242 | 0 | 242 | Infer.NET, Microsoft.ML.Probabilistic | Infer.NET, Microsoft.ML.Probabilistic | ✅ OK |

## Findings notables

### F-c793-1 — DecInfer-2 `pymc` mentioned-not-imported (MAJOR)

- **Pattern** : `sota_mentioned_not_imported` (litmus 4 du protocole)
- **Claim markdown** : présence du token `pymc` dans cellules markdown
- **Réalité code** : 0 `import pymc` ni `#r "nuget:...pymc..."` ni `using ... pymc ...`
- **Hypothèse 1 (vraie)** : notebook mentionne pymc en comparaison pédagogique (« voir aussi pymc pour la même tâche ») sans l'invoquer → finding **faux positif à clarifier** (mais valide comme signal à la revue humaine)
- **Hypothèse 2 (sombre)** : cellule code tente `import pymc` dans un try/except ImportError silencieux qui réassigne à trivial → finding **vrai positif de fallback silencieux** (incident fondateur TenSEAL du protocole)
- **Action revue humaine** : lire la cellule où `pymc` apparaît dans le markdown, vérifier le code adjacent, conclure.

### F-c793-2 — DecInfer-1 et DecInfer-4 : matched=0 (ATTENDU)

- **Pattern** : la regex `CLAIM_NUMERIC_RE` attrape **tous** les nombres (execution_count, listes, indices, identifiants d'assets). Sans match substrat avec les outputs, ce n'est pas un finding de fallback : c'est du **bruit** à filtrer.
- **Action** : raffinement du script = exclure les nombres < 10 (execution_count, indices) ou dans une heuristique de contexte (ex: `f"step {i}"` ≠ claim). **Hors scope c.793** (le protocole assume explicitement ce bruit en raw material).
- **Référence protocole** : §"Sortie attendue par cycle" — « 0 PR de fix automatique **dans le même cycle** (audit = reportage, fix = cycle séparé pour ne pas confondre les genres G-VAR-3) ».

## Validation de la grille

- ✅ Litmus 1 (numeric claims) : extracts
- ✅ Litmus 2 (fallback silencieux) : pattern `try: import ... except ImportError:` détécté (cf `detect_fallback_silent`), **pas testé sur DecInfer car notebooks .NET** — à valider sur notebooks Python (ML.NET tutorials, Search Part1 Python, etc.)
- ⏳ Litmus 3 (verdict positif markdown) : non déclenché sur l'échantillon DecInfer
- ✅ Litmus 4 (SOTA tool) : **finding pilote F-c793-1** trouvé sur DecInfer-2 — preuve que la grille fonctionne
- ⏳ Litmus 5 (cohérence pédagogique) : nécessite lecture cellule-par-cellule, hors scope automatisé

## Périmètre familles (scope c.793)

- **Probas / DecInfer** : 3/10 notebooks échantillonnés (30%, dépasse plancher ≥5%).
- **ML / ML.NET** : 0/40 notebooks (différé cycle suivant — cf protocole §"Application pilote" + §"Familles différées").
- **Search / Sudoku / QC** : **différés** explicitement par le protocole (cf §"Familles différées").

## Ce que ce cycle ne prétend PAS

- **Pas une validation du contenu DecInfer** : l'audit trouve des *candidates* à la revue humaine/agent-compétent ; il ne tranche pas `pymc fallback silencieux vs mention comparative`.
- **Pas une garantie 0 finding CRITICAL** : l'échantillon de 3 notebooks sur 10 laisse 7 non-audités (cycles c.794+).
- **Pas une automatisation du verdict** : la grille est un *filtre brut* + rapport, conformément au litmus anti-LIGHT du protocole.

## Suite logique

| Cycle | Cible | Statut |
|-------|-------|--------|
| c.794 | DécInfer 5-10 (5 restants) + 1 ML.NET tutoriel | à dispatcher |
| c.795+ | Probas / PyMC (parité cross-langage Python↔C# jumeaux, cf #8057) | à dispatcher |
| c.796+ | Search Part1 Python (autre famille CPU) | à dispatcher |

## Repères vérifiables

- Issue-source : [#8052](https://github.com/jsboige/CoursIA/issues/8052)
- Epic parente : [#4208](https://github.com/jsboige/CoursIA/issues/4208)
- Protocole : [`docs/audit/sampling-protocol.md`](../../sampling-protocol.md)
- Outil : [`scripts/audit/extract_claims_vs_outputs.py`](../../../../scripts/audit/extract_claims_vs_outputs.py)
- Findings YAML bruts : `/tmp/audit_<notebook>.yaml` (cf commande documentée §Workflow protocole)
- Branch : `feature/c793-audit-semantic-sampling-8052`
