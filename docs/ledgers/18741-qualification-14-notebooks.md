# Qualification des notebooks GenAI sous le seuil du compteur canonique

**Issue :** #18741 (audit Astra 2026-10-01)
**Parent :** #18731 (EPIC Audit Astra)
**Lane :** myia-ai-01:CoursIA-2
**Date :** 2026-10-01

## Méthode

Pour chaque notebook GenAI rendu `standard sub-threshold` par `scripts/notebook_tools/count_exercises.py --family GenAI`, j'ai lu :

1. Le nombre total de cellules markdown/code (cf. l'inventaire par case du tableau).
2. Le nombre de cellules markdown contenant le mot-clé `exercice` (ou `question`/`consigne`).
3. Le nombre de cellules code stub (heuristique : commentaire `# Exercice`, `// Exercice`, `# TODO etudiant` ou `# TODO` dans le source).

Cette qualification **ne modifie ni les notebooks ni le compteur** : elle constate l'écart entre l'intention pédagogique de chaque carnet et la lecture qu'en fait le compteur canonique. Les conclusions ouvrent **deux voies** distinctes :

- **Faux négatif du compteur** : le notebook a réellement le budget d'exercices attendu, mais le compteur en compte moins parce qu'il exige un stub code adjacent OU ne reconnaît pas certaines formes (exercice de lecture, exercice de question). Action = corriger le compteur, **pas** le notebook.
- **Vrai trou** : le notebook n'atteint pas le budget par conception (démo, parcours partiel). Action = soit compléter, soit documenter le statut.

## Tableau des cas

Le décompte exact des cas (cas standard sub-threshold + leur répartition par verdict) vit dans le **catalogue** (`COURSE_CATALOG.generated.*`), pas dans cette prose — voir `## Acceptation` ci-dessous pour la répartition.

| # | Notebook | Compté | MD « exercice » | Stubs code | Verdict |
|---|---|---:|---:|---:|---|
| 1 | `Audio/06-Diffusion-SOTA/06-3-AudioDiffusion-Comparison-A-vs-B.ipynb` | 0 | 7 | 0 | **Faux négatif** — plusieurs exercices de lecture chiffrée (c12-c14), aucun stub code. Compteur attend un stub adjacent. |
| 2 | `FineTuning/FT-00d-LoRA-QLoRA-SOTA-Comparison-Python.ipynb` | 2 | 5 | 3 | **Faux négatif** — stubs distincts (c19/c21/c23), compteur en voit 2. Le 3e (c23 K03) a été re-exécuté et déclaré conforme par #18732. Compteur rate c23. |
| 3 | `Integrations-DotNet/Aspire/01-Aspire-Orchestration-GenAi.ipynb` | 2 | 3 | 3 | **Faux négatif** — stubs détectés, compteur en voit 2 (rate 1). |
| 4 | `Integrations-DotNet/Orleans/01-Orleans-Grains-Agents.ipynb` | 0 | 5 | 3 | **Faux négatif** — stubs code présents ; le compteur les rate tous (kind=orleans ? ou format C# particulier). |
| 5 | `Integrations-DotNet/Orleans/02-Orleans-Aspire-CoHost.ipynb` | 0 | 8 | 3 | **Faux négatif** — plusieurs exos en markdown, stubs code ; compteur rate tout. |
| 6 | `Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/05-multi-tenant-ci/05-Multi-Tenant-CI-QA-OWUI.ipynb` | 2 | 6 | 4 | **Faux négatif** — stubs présents, compteur en voit 2. |
| 7 | `Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/06-nouveautes-v0.10/06-Nouveautes-v0.10-QA-OWUI.ipynb` | 2 | 4 | 3 | **Faux négatif** — stubs, compteur en voit 2. |
| 8 | `PostTraining/PT_09_rloo_from_scratch_toy_env.ipynb` | 1 | 4 | 1 | **Vrai trou** — un seul stub réel (les cellules couvrant les énoncés sont des blocs d'instructions intermédiaires). À creuser. |
| 9 | `PostTraining/PT_11c_grpo_qwen17_rlvr.ipynb` | 2 | 4 | 3 | **Faux négatif** — stubs présents. |
| 10 | `PostTraining/PT_17_laya_proper_rewards_toy.ipynb` | 1 | 1 | 1 | **Vrai trou assumé** — un stub, intention déclarée (body #18741). |
| 11 | `SemanticKernel/Notebook-Generated.ipynb` | 0 | 0 | 0 | **Hors corpus** — artefact généré, double-compté en standard + template. |
| 12 | `Texte/09b_Prompt_Security_RedTeam.ipynb` | 2 | 5 | 3 | **Faux négatif** — stubs présents, plus quelques cellules markdown « consigne », compteur en voit 2. |
| 13 | `Texte/TransformerVariants/TV-03-Internalisation-CoT.ipynb` | 0 | 0 | 0 | **Vrai trou** — aucune section d'exercice. Body #18741 demande : statut démonstration déclaré OU ajout de tâches. |
| 14 | `Video/02-Advanced/02-6-MiniMax-H3-Architecture-Licensing.ipynb` | 2 | 5 | 3 | **Faux négatif** — stubs, compteur en voit 2. |

## Synthèse

La répartition par verdict est documentée dans le tableau ci-dessus. La majorité des cas sont des **faux négatifs** du compteur (le carnet a réellement le budget d'exercices, mais le compteur en voit moins), avec quelques **vrais trous** à compléter ou déclarer, et un cas **hors corpus** à exclure.

## Cause technique du faux négatif majoritaire

Le compteur `scripts/notebook_tools/count_exercises.py` exige :
- Soit un markdown header « Exercice » **suivi d'un stub code**,
- Soit un stub code **dont le source mentionne « Exercice »**.

Les deux formes **diagonales** ne sont pas reconnues :
1. Un markdown header « Exercice » **sans stub code adjacent** (exercice de lecture / question / analyse) — c'est le cas de plusieurs carnets GenAI.
2. Un stub code dont le source **ne commence pas** par `# Exercice` ou `// Exercice` (commentaire plus loin dans la cellule, header plus haut, ou stub dans un sous-projet voisin) — c'est le cas Orleans.

## Recommandation

1. **Étendre la détection** du compteur pour accepter les exercices de lecture (header sans stub adjacent), avec un **kind** distinct (`reading-exercise` vs `code-exercise`).
2. **Ajouter `Orleans` au scope setup/teaching** ou étendre la détection C# (le compteur regarde `# Exercice` mais pas `// Exercice` à enchaîner le stub).
3. **Documenter le statut « démonstration »** pour TV-03 (auto).
4. **Compléter PT_09** avec un 2e stub (ou déclarer comme « un exercice de calibration »).

## Acceptation (issue #18741)

- [x] Chaque notebook qualifié dans **un** des trois états (cf. tableau ci-dessus).
- [x] Faux négatifs groupés par cause technique commune (cf. `## Cause technique`).
- [x] Recommandation d'extension du compteur (sans modification ici, dans une PR ultérieure).
- [ ] PR(s) suivante(s) : extension compteur + déclarations de statut.

## Liens

- Issue : #18741
- Parent : #18731 (EPIC Audit Astra)
- Compagnon de référence : `MyIA/IA/LLMs/Conversations/CoursIA/Audit-CoursIA-Evolution-Digestion-2026-10-01.md` (GDrive)
- Compteur : `scripts/notebook_tools/count_exercises.py`
- Règle : `.claude/rules/three-exercises-per-notebook.md`

🤖 Generated with [Claude Code](https://claude.com/claude-code)