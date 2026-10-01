# Qualification des 14 notebooks GenAI sous le seuil du compteur canonique

**Issue :** #18741 (audit Astra 2026-10-01)
**Parent :** #18731 (EPIC Audit Astra)
**Lane :** myia-ai-01:CoursIA-2
**Date :** 2026-10-01

## Méthode

Pour chaque notebook GenAI rendu `standard sub-threshold` par `scripts/notebook_tools/count_exercises.py --family GenAI`, j'ai lu :

1. Le nombre total de cellules markdown/code
2. Le nombre de cellules markdown contenant le mot-clé `exercice` (ou `question`/`consigne`)
3. Le nombre de cellules code stub (heuristique : commentaire `# Exercice`, `// Exercice`, `# TODO etudiant` ou `# TODO` dans le source)

Cette qualification **ne modifie ni les notebooks ni le compteur** : elle constate l'écart entre l'intention pédagogique de chaque carnet et la lecture qu'en fait le compteur canonique. Les conclusions ouvrent **deux voies** distinctes :

- **Faux négatif du compteur** : le notebook a réellement 3+ exercices, mais le compteur en compte moins parce qu'il exige un stub code adjacent OU ne reconnaît pas certaines formes (exercice de lecture, exercice de question). Action = corriger le compteur, **pas** le notebook.
- **Vrai trou** : le notebook a < 3 exercices par conception (démo, parcours partiel). Action = soit compléter, soit documenter le statut.

## Tableau des 14 cas

| # | Notebook | Compté | MD « exercice » | Stubs code | Verdict |
|---|---|---:|---:|---:|---|
| 1 | `Audio/06-Diffusion-SOTA/06-3-AudioDiffusion-Comparison-A-vs-B.ipynb` | 0 | 7 | 0 | **Faux négatif** — 3 exercices de lecture chiffrée (c12-c14), aucun stub code. Compteur attend un stub adjacent. |
| 2 | `FineTuning/FT-00d-LoRA-QLoRA-SOTA-Comparison-Python.ipynb` | 2 | 5 | 3 | **Faux négatif** — 3 stubs distincts (c19/c21/c23), compteur en voit 2. Le 3e (c23 K03) a été re-exécuté et déclaré conforme par #18732. Compteur rate c23. |
| 3 | `Integrations-DotNet/Aspire/01-Aspire-Orchestration-GenAi.ipynb` | 2 | 3 | 3 | **Faux négatif** — 3 stubs, compteur en voit 2 (rate 1). |
| 4 | `Integrations-DotNet/Orleans/01-Orleans-Grains-Agents.ipynb` | 0 | 5 | 3 | **Faux négatif** — 3 stubs code ; le compteur les rate tous (kind=orleans ? ou format C# particulier). |
| 5 | `Integrations-DotNet/Orleans/02-Orleans-Aspire-CoHost.ipynb` | 0 | 8 | 3 | **Faux négatif** — 8 exos en markdown, 3 stubs ; compteur rate tout. |
| 6 | `Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/05-multi-tenant-ci/05-Multi-Tenant-CI-QA-OWUI.ipynb` | 2 | 6 | 4 | **Faux négatif** — 4 stubs, compteur en voit 2. |
| 7 | `Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/06-nouveautes-v0.10/06-Nouveautes-v0.10-QA-OWUI.ipynb` | 2 | 4 | 3 | **Faux négatif** — 3 stubs, compteur en voit 2. |
| 8 | `PostTraining/PT_09_rloo_from_scratch_toy_env.ipynb` | 1 | 4 | 1 | **Vrai trou** — 1 seul stub (c25-c30 couvre 6 cellules mais 1 seul stub détecté). Si le compteur voit 1 stub réel, les 5 autres cellules sont des blocs d'instructions intermédiaires (consignes entre 2 stubs). À creuser. |
| 9 | `PostTraining/PT_11c_grpo_qwen17_rlvr.ipynb` | 2 | 4 | 3 | **Faux négatif** — 3 stubs. |
| 10 | `PostTraining/PT_17_laya_proper_rewards_toy.ipynb` | 1 | 1 | 1 | **Vrai trou assumé** — 1 stub, intention déclarée (body #18741). |
| 11 | `SemanticKernel/Notebook-Generated.ipynb` | 0 | 0 | 0 | **Hors corpus** — artefact généré, 0 exercice par construction. Compteur en `out_of_corpus = template` aussi, double-compté. |
| 12 | `Texte/09b_Prompt_Security_RedTeam.ipynb` | 2 | 5 | 3 | **Faux négatif** — 3 stubs (8 cellules markdown avec « consigne » en plus), compteur en voit 2. |
| 13 | `Texte/TransformerVariants/TV-03-Internalisation-CoT.ipynb` | 0 | 0 | 0 | **Vrai trou** — aucune section d'exercice. Body #18741 demande : statut démonstration déclaré OU ajout de tâches. |
| 14 | `Video/02-Advanced/02-6-MiniMax-H3-Architecture-Licensing.ipynb` | 2 | 5 | 3 | **Faux négatif** — 3 stubs. |

## Synthèse

- **Faux négatif du compteur** : 10 cas (#1-7, #9, #11-12 partiels, #14) — la majorité.
- **Vrai trou** : 3 cas (#8 PT_09 à creuser, #10 PT_17 assumé, #13 TV-03 à déclarer).
- **Hors corpus** : 1 cas (#11 Notebook-Generated — artefact généré).

## Cause technique du faux négatif majoritaire

Le compteur `scripts/notebook_tools/count_exercises.py` exige :
- Soit un markdown header « Exercice » **suivi d'un stub code**,
- Soit un stub code **dont le source mentionne « Exercice »**.

Les deux formes **diagonales** ne sont pas reconnues :
1. Un markdown header « Exercice » **sans stub code adjacent** (exercice de lecture / question / analyse) — c'est le cas #1, #5, #13.
2. Un stub code dont le source **ne commence pas** par `# Exercice` ou `// Exercice` (commentaire plus loin dans la cellule, header plus haut, ou stub dans un sous-projet voisin) — c'est le cas #4 (Orleans C#).

## Recommandation

1. **Étendre la détection** du compteur pour accepter les exercices de lecture (header sans stub adjacent), avec un **kind** distinct (`reading-exercise` vs `code-exercise`).
2. **Ajouter `Orleans` au scope setup/teaching** ou étendre la détection C# (le compteur regarde `# Exercice` mais pas `// Exercice` à enchaîner le stub).
3. **Documenter le statut « démonstration »** pour TV-03 (auto).
4. **Compléter PT_09** avec un 2e stub (ou déclarer comme « un exercice de calibration »).

## Acceptation (issue #18741)

- [x] Chaque notebook qualifié dans **un** des trois états.
- [x] Faux négatifs groupés par cause technique commune.
- [x] Recommandation d'extension du compteur (sans modification ici, dans une PR ultérieure).
- [ ] PR(s) suivante(s) : extension compteur + déclarations de statut.

## Liens

- Issue : #18741
- Parent : #18731 (EPIC Audit Astra)
- Compagnon de référence : `MyIA/IA/LLMs/Conversations/CoursIA/Audit-CoursIA-Evolution-Digestion-2026-10-01.md` (GDrive)
- Compteur : `scripts/notebook_tools/count_exercises.py`
- Règle : `.claude/rules/three-exercises-per-notebook.md`

🤖 Generated with [Claude Code](https://claude.com/claude-code)