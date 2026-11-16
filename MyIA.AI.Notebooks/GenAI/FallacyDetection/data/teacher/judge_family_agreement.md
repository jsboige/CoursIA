# Accord inter-familles de juges — split val FR

Ce que mesure ce rapport : la section 2a de la revue EPITA (c.6344505010) —
un juge **d'une autre famille** que le generateur reclasse-t-il les 200 paires tirees ?

## Parametres

- corpus : `MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl` (280 paires, SHA-256 `d7621fffa05dc857b2110fc44299b04fdbce670efbd76c633ec3917e83aef52c`)
- tirage : graine 42, 200 paires, stratifie par famille ({'Abus de langage': 15, 'Argument pertinent': 15, 'Erreur de raisonnement': 14, 'Erreur mathématique': 14, 'Honnêteté intellectuelle': 14, 'Influence': 14, 'Inférence maîtrisée': 15, 'Insuffisance': 15, 'Justesse lexicale': 13, 'Obstruction': 14, 'Présentation intègre': 14, 'Sens quantitatif': 14, 'Tricherie': 15, 'Échange enrichissant': 14})
- questionnaire : 5 distracteurs de meme polarite, cadre FR du controle aller-retour, temperature 0.0

## Taux d'accord

| Juge | Famille | Modele | Mesurees | Non parses | Taux | IC Wilson 95 % |
|---|---|---|---|---|---|---|
| openai | GPT (OpenAI) | gpt-4o-mini | 200/200 | 0 | 0.8250 | [0.7664 ; 0.8714] |
| openrouter | Mistral (OpenRouter) | mistralai/mistral-small-24b-instruct-2501 | 200/200 | 0 | 0.8000 | [0.7391 ; 0.8495] |
| generateur (auto-accord, sous-ensemble) | Qwen (vLLM maison) | celui du corpus | 200/200 | 0 | 0.8950 | [0.8448 ; 0.9303] |

La ligne « generateur » est le contraste : le taux aller-retour du generateur
**restreint au meme sous-ensemble** (champ `roundtrip` du corpus, aucun appel).
C'est la reference meme-famille-definition-visible face a laquelle lire les
juges externes : un juge externe proche d'elle ne fait que confirmer le
reclassement ; un juge externe bas ne dit pas lequel des deux a tort, il dit
que l'etiquette ne survit pas au changement de famille.

## Par famille

| Famille | openai | openrouter | generateur |
|---|---|---|---|
| Abus de langage | 11/15 | 14/15 | 13/15 |
| Argument pertinent | 13/15 | 12/15 | 15/15 |
| Erreur de raisonnement | 14/14 | 12/14 | 13/14 |
| Erreur mathématique | 13/14 | 13/14 | 13/14 |
| Honnêteté intellectuelle | 12/14 | 12/14 | 13/14 |
| Influence | 13/14 | 11/14 | 13/14 |
| Inférence maîtrisée | 8/15 | 7/15 | 13/15 |
| Insuffisance | 14/15 | 15/15 | 14/15 |
| Justesse lexicale | 8/13 | 10/13 | 11/13 |
| Obstruction | 12/14 | 14/14 | 14/14 |
| Présentation intègre | 10/14 | 12/14 | 9/14 |
| Sens quantitatif | 10/14 | 2/14 | 11/14 |
| Tricherie | 15/15 | 13/15 | 15/15 |
| Échange enrichissant | 12/14 | 13/14 | 12/14 |

## Empreintes

- corpus d'entree : `d7621fffa05dc857b2110fc44299b04fdbce670efbd76c633ec3917e83aef52c`
- rapport JSON : `e0dc48a2d0c2720cfe25300f1fee1159eba81c803a41978b5da7a95b9de0b04b` (`judge_family_agreement.json`)

Rejouabilite : `python -m fallacy_detection.judge_family_agreement --report-only` reconstruit ce rapport sans aucun appel ni cle — depuis le checkpoint local s'il existe, sinon depuis le rapport publie.
