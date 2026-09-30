# Issue #18493 — Scan des compteurs littéraux dans commentaires code

## Origine

Issue : #18493 (`hygiene(notebooks): compteurs litteraux dans commentaires de cellules code`).

La classe de l'issue est **distincte** de la prose markdown visée par #17636 : un compteur en dur dans un commentaire de cellule code `# ~10 mots`, `# ~1500 fichiers` est de même nature qu'un compteur prose (littéral qui dérive), mais sa correction **casse la byte-identité** de la cellule code et déclenche une ré-exécution C.2 du carnet entier. Les relais md-only (#17636) ne s'y appliquent pas — ces compteurs exigent une PR par carnet.

## Scan exhaustif

Outil : `scripts/notebook_tools/scan_code_comment_counters.py` (ajouté par cette PR).

```bash
python scripts/notebook_tools/scan_code_comment_counters.py
# total hits: 21
# notebooks touched: 17

python scripts/notebook_tools/scan_code_comment_counters.py --json
# sortie structuree : by_kind, by_notebook, records (notebook, cell_index, line, kind, snippet)
```

Le scan distingue 4 kinds :

| Kind | Pattern | Action recommandée |
|---|---|---|
| `NOTE_runtime` | `# NOTE: ~1500 fichiers` | KEEP-with-annotation (note technique, approximation pédagogique) |
| `tilde_count` | `# ~10 mots` ou `var = N  # ~K unite` | A-INVESTIGUER (calibration runtime ou commentaire pédagogique) |
| `gt_runtime_threshold` | `# > 0 si ...` | KEEP (commentaire de logique opérationnelle, **PAS** un compteur) |
| `config_dict_doc` | `# "large" : mathlib4, >100k theoremes` | KEEP (doc utilisateur pour choix de preset) |

## Classification mesurée des 21 hits

### KEEP (5 hits) — pas un compteur runtime

| Carnet | Cellule | Snippet |
|---|---|---|
| `SymbolicAI/Lean/Lean-10-LeanDojo.ipynb` | c.2 l.16 | `# "large"  : mathlib4, >100k théorèmes (2-4h 1ere fois)` |
| `SymbolicAI/Lean/Lean-10-LeanDojo.ipynb` | c.6 l.6 | `# NOTE: Tous les repos Lean 4 incluent ~1500 fichiers de la stdlib.` |
| `SymbolicAI/Lean/Lean-21-MIMO-Detection-Flips.ipynb` | c.3 l.27 | `gain = obj - obj_new  # > 0 si le flip diminue l'objectif` |
| `GameTheory/SocialChoice/05-Gibbard-Satterthwaite.ipynb` | c.9 l.27 | `gain = sincere_rank - new_rank  # > 0 si mieux` |

Ces lignes sont soit de la documentation utilisateur (Lean-10 c.2), soit des notes techniques avec une approximation pédagogique (`~1500 fichiers` mesure d'ordre de grandeur pour la stdlib Lean 4 — la réalité évolue avec chaque release Mathlib), soit des commentaires de logique opérationnelle (`# > 0 si mieux`). Aucune n'est un compteur runtime à dériver.

### A-INVESTIGUER (16 hits) — calibration runtime documentée

Carnets où le commentaire calibre une valeur runtime en unité métier. Le chiffre est **fixe** dans le code (`SEQ_LEN = 96`), le commentaire `~4 mois de trading days` aide le lecteur à comprendre l'ordre de grandeur. **Pas un compteur qui dérive** : la calibration est co-écrite avec la valeur et reste correcte tant que la calibration reste valide.

| Carnet | Cellule | Snippet |
|---|---|---|
| `SymbolicAI/SMT/Z3-API/Z3-16c-Meal-Planner-Patient-Capstone-Python.ipynb` | c.14 l.2 | `energieMin = 3347    # ~800 kcal cumules minimum par menu` |
| `SymbolicAI/SMT/Z3-API/Z3-16c-Meal-Planner-Patient-Capstone-Python.ipynb` | c.14 l.3 | `energieMax = 10878   # ~2600 kcal cumules maximum par menu` |
| `SymbolicAI/SmartContracts/05-Alternative-Chains/SC-20-Bitcoin-Scripting-Python.ipynb` | c.27 l.24 | `csv_blocks = 144  # ~24 heures` |
| `QuantConnect/Python/QC-Py-12-Backtesting-Analysis.ipynb` | c.9 l.3 | `n_days = 504  # ~2 ans de trading` |
| `QuantConnect/Python/QC-Py-15-Parameter-Optimization.ipynb` | c.46 l.3 | `n_days_wf = 1260  # ~5 ans` |
| `QuantConnect/Python/QC-Py-22-Deep-Learning-LSTM.ipynb` | c.19 l.2 | `SEQ_LEN = 96      # ~4 mois de trading days` |
| `QuantConnect/Python/QC-Py-22-Deep-Learning-LSTM.ipynb` | c.19 l.3 | `PRED_LEN = 24     # ~1 mois de prediction` |
| `QuantConnect/research/research_rl_ppo.ipynb` | c.3 l.X | `EPISODE_LEN = 252      # ~1 year of trading per episode` |
| `QuantConnect/research/research_vrp_putwrite.ipynb` | c.7 l.X | `MONTHS = 21             # ~21 jours ouvres par mois` |
| `ML/DataScienceWithAgents/04-Vision/4.3-TransferLearning-ResNet.ipynb` | c.11 | `modele_base = resnet18(...)  # ~45 Mo telecharges au premier run` |
| `IIT/ICT-Series/ICT-15g-EmpiricalHuangExploitation.ipynb` | c.20 | `window_size = max(2, n_total // 30)  # ~30 fenetres, comme ICT-15d` |
| `GenAI/PostTraining/PT_11a_grpo_qwen35_rlvr.ipynb` | c.14 | `STEPS = 100  # ~15 min sur RTX 3070 ; ajuster selon la fenetre` |
| `GenAI/Video/02-Advanced/02-5-LTX2-Audiovisual.ipynb` | c.13 | `# ~492 s sur RTX 3090, seed 42).` |
| `GenAI/Video/02-Advanced/02-7-CogVideoX-Text-to-Video.ipynb` | c.1 | `num_inference_steps = 25           # ~25 etapes = bon compromis qualite/temps` |
| `GenAI/Video/04-Applications/04-5-MiniMax-H3-Cloud-Video.ipynb` | c.4 | `for i in range(54):  # ~9 min max` |
| `GenAI/Audio/02-Advanced/02-1-Chatterbox-TTS.ipynb` | c.17 | `# "Short text here with ten words exactly."  # ~10 mots` |
| `GenAI/Audio/02-Advanced/02-1-Chatterbox-TTS.ipynb` | c.17 | `# "Medium text here with about twenty words total for testing."  # ~20 mots` |

## Recommandation par cas

### Voie 1 — KEEP (recommandée pour les 4 hits `KEEP`)

Aucun changement. Le compteur est soit absent (logique opérationnelle), soit une approximation pédagogique non-runtime, soit une doc utilisateur pour choix de preset.

### Voie 2 — EDIT (à arbitrer au cas par cas pour les 17 hits `A-INVESTIGUER`)

Remplacer la calibration statique par un calcul runtime :
```python
SEQ_LEN = 252  # ~1 year of trading days
# devient
SEQ_LEN = int(252 * (window.end - window.start).days / 365)
```

**Coût** : modification de cellule code → ré-exécution C.2 du carnet entier → 17 PRs Papermill par carnet. **Bénéfice** : la calibration reste vraie si la fenêtre change.

**Voie recommandée uniquement si** la calibration change avec le contexte d'exécution. Pour `SEQ_LEN = 96  # ~4 mois` dans QC-Py-22, la valeur est un hyperparamètre — le commentaire est juste une aide à la lecture ; le runtime ne la calcule pas.

### Voie 3 — REMOVE (proscrite)

Retirer le commentaire sans valeur de remplacement perd l'information pédagogique. **Pas une voie de fix**, c'est une régression.

## Décision de cette PR

Cette PR livre **uniquement** :
1. Le script `scripts/notebook_tools/scan_code_comment_counters.py` (l'organe de mesure).
2. Ce rapport de classification (l'artefact durable).

**Aucun carnet n'est édité** → aucune cellule code touchée → aucune ré-exécution C.2 due → aucune dépendance Papermill.

Les voies EDIT (17 carnets à modifier) restent un travail de fond, à prioriser carnet par carnet par les lanes de chaque famille. Le script de scan permet de re-mesurer la classe après chaque campagne.

## Acceptance

- [x] Scan dédié produit la liste exhaustive (cf. section "Scan exhaustif")
- [x] Classification KEEP/EDIT/REMOVE par hit documentée (cf. section "Classification mesurée")
- [x] Aucun carnet édité → C.2 non applicable (cf. "Décision de cette PR")
- [x] Les compteurs restants sont classés KEEP (4 hits) ou A-INVESTIGUER (17 hits) avec justification

## Liens

- #18493 (issue d'origine)
- #17636 (campagne prose markdown — relay c15) : autre classe, byte-identité préservée
- `proactive-coordination.md` R6 — variété anti-monoculture : ce PR est `LIGHT/tooling`, pas un DEEP de contenu, et le DEEP est porté par PR #18506 (livrée juste avant)
- `scan_md_hierarchy drift` (workflow `md-hierarchy-drift.yml`) : autre ratchet sur la hiérarchie markdown
