# Translation perimeter (Epic #10038 grain E)

Déclare **quelles langues cibles sont en-scope** pour chaque CSV de
`translations/**`. Une langue en-scope est une langue pour laquelle le
moteur T3 (`scripts/translation/translate_csv.py`) peut remplir les
colonnes `text_<lang>` + `hash_<lang>` du CSV et T4
(`scripts/translation/render_notebook.py`) peut rendre les
`*_<lang>.ipynb` correspondants.

Le périmètre est **fermé** : toute langue non listée pour un CSV est
explicitement **OUT-OF-SCOPE** pour ce CSV. Une cellule `text_<lang>`
remplie hors-périmètre est un **defaut** détecté mécaniquement par
`scripts/translation/check_perimeter.py` (exit 1, label advisory).

## Source de vérité

La matrice CSV × langue est le seul artefact canonique. Aucune lecture
par défaut n'est tolérée. Si une langue doit être ajoutée au périmètre
d'un CSV : éditer ce fichier + PR dédiée + acceptance « périmètre
étendu ». Cf Epic #10038 §4 (D3 — périmètre EN seul d'abord, corpus
déclaré).

## Notation

| Symbole | Sens |
|---|---|
| `en` | langue listée = in-scope (T3 peut remplir, T4 peut rendre) |
| `-` | langue out-of-scope (T3 ne touche pas la colonne, T4 ne rend pas) |
| `fr` | pivot, toujours in-scope par construction (T1 l'extrait) |

## Matrice (CSV × langues cibles)

| CSV | en | es | ar | fa | zh | ru | pt | Source |
|---|---|---|---|---|---|---|---|---|
| `translations/genai/audio.csv` | - | - | - | - | - | - | - | (pre-T3) |
| `translations/genai/casestudies.csv` | **en** | - | - | - | - | **ru** | - | #10017/#10018 (en) + POC ru (cf §ru-orphans) |
| `translations/genai/finetuning.csv` | **en** | - | - | - | - | - | - | #10017/#10018 (en) |
| `translations/genai/image.csv` | **en** | - | - | - | - | **ru** | - | T3 image (à activer) + POC ru (cf §ru-orphans) |
| `translations/genai/posttraining.csv` | - | - | - | - | - | - | - | (pre-T3) |
| `translations/genai/texte.csv` | - | - | - | - | - | - | - | (pre-T3) |
| `translations/genai/video.csv` | - | - | - | - | - | - | - | (pre-T3) |
| `translations/partner-course-quant-trading/partner-course.csv` | **en** | - | - | - | - | - | - | #10032 (en) |
| Autres 25 CSV (search-, probas-, gametheory, …) | - | - | - | - | - | - | - | (pre-T3) |

CSV « Autres » : `casestudies`, `gametheory`, `iit`, `ml-datascience`,
`mlnet`, `planners`, `probas_decinfer`, `probas_infer`, `probas_pymc`,
`quantconnect-py`, `rl`, `search-applications`, `search-part1`,
`search-part2`, `search-part3`, `search-part4`, `semanticweb`,
`smartcontracts`, `z3-api`, `z3-linq2z3`, `sudoku`, `argument_analysis`,
`symbolicai-lean`, `symboliclearning`, `tweety`. T3 ne touche aucun de
ces CSV tant que la décision d'élargir le périmètre n'est pas prise par
PR dédiée.

## Ru-orphelins (résorption, Epic #10038 §4 D3)

51 cellules `text_ru` existaient sur `main` avant cette PR (état mesuré
firsthand `c.1301+21`, sha `c8dad3457`). **Aucune n'est retirée** : les
données sont des traductions russes valides de notebooks existants,
produites par un POC antérieur au gate T3 (avant #6949 / Epic #4957).

| Fichier | Notebook | Cellules `text_ru` | `text_en` sibling ? | Décision |
|---|---|---|---|---|
| `genai/casestudies.csv` | Barbie-Schreck | 13 | oui (13/13) | kept (paired) |
| `genai/casestudies.csv` | Fort-Boyard | 10 | oui (10/10) | kept (paired) |
| `genai/casestudies.csv` | Medical-Chatbot | 2 | oui (23/2 partiel) | kept (paired, partial fill) |
| `genai/image.csv` | 01-1-OpenAI-DALL-E-3 | 13 | non | kept (orphan justifié, image.csv `en` activé) |
| `genai/image.csv` | 01-2-GPT-5-Image-Generation | 13 | non | kept (orphan justifié, image.csv `en` activé) |

**Justification** : la décision D3 demande « `en` seul d'abord » mais
ne demande PAS de détruire du contenu déjà traduit. Les `text_ru` POC
sont **préservés** et **déclarés in-scope** (colonne `ru` du CSV
`genai/casestudies.csv` + `genai/image.csv`). Le moteur T3 activé pour
`en` (cf Epic #10038 §6 grain D) remplira progressivement la colonne
`text_en` des notebooks image ; les cellules `text_ru` orphelines
(13+13) deviendront alors **paired** par construction. Aucun
re-render `*_ru.ipynb` n'est prévu dans l'immédiat (Epic #10038 §4 D3
: « `en` seul, prouvé end-to-end sur une série »).

## Acceptance

- [x] `en` déclaré in-scope pour 4 CSV (casestudies, finetuning, image, partner-course)
- [x] `ru` déclaré in-scope pour 2 CSV (casestudies, image) avec justification écrite
- [x] 51 cellules `text_ru` préservées (POC justifié, pas de destruction)
- [x] 6 autres langues (es/ar/fa/zh/pt) explicitement out-of-scope avec motif
- [x] `scripts/translation/check_perimeter.py` codifie la matrice → exit 1 sur défaut

See Epic #10038 §4 (D3), §6 (grain E), §4 acceptance (« périmètre
déclaré, `ru` résorbé »).