# GameTheory-16h — mémo de gel du protocole de coopération LLM (c.2344)

Issue : [#20884](https://github.com/jsboige/CoursIA/issues/20884) — side-car de la sous-série `GameTheory-16`. Ce mémo est le document annoncé par la section `Livrable` de l'issue et resté absent de `main` après le merge de [#21021](https://github.com/jsboige/CoursIA/pull/21021) (2026-10-20). Il **n'introduit aucune mesure nouvelle** : il fige par écrit ce que le carnet [`GameTheory-16h-Cooperation-LLM-Python.ipynb`](../../MyIA.AI.Notebooks/GameTheory/GameTheory-16h-Cooperation-LLM-Python.ipynb) porte déjà, et il en donne les chiffres tels qu'ils figurent dans ses sorties commitées.

**Le carnet est la source de vérité.** En cas d'écart entre ce mémo et lui, c'est le carnet qui fait foi, et l'écart est un défaut de ce document.

## 0. Gel — ce qui est figé avant le premier appel d'agent

Le §0 du carnet est écrit **avant** toute exécution. Toute déviation constatée à l'exécution se consigne au §8 du carnet comme violation de protocole ; elle ne se corrige pas en silence dans le gel.

| Élément | Valeur figée |
|---|---|
| Jeu | Dilemme du prisonnier itéré (Axelrod 1984), payoffs `(T, R, P, S) = (5, 3, 1, 0)` |
| Rôles | `agent_0` et `agent_1`, **symétrie d'information** |
| Information observée | historique complet des coups de l'adversaire ; aucune information cachée |
| Rounds par rencontre | `N_ROUNDS = 100` |
| Rencontres indépendantes par paire | `N_MATCHES_PER_PAIR = 50` |
| Seeds | `{0, 1, 7, 42, 99}` — 5 seeds, au-delà du minimum de 4 |
| Métrique principale | `cooperation_rate` = proportion de rounds où l'agent joue `C` |
| Métrique secondaire | `total_payoff` sur les 100 rounds |

### Hétérogénéités (4 retenues, dont 1 contrôle négatif)

Une hétérogénéité est un **couple de politiques** `(strat_0, strat_1)`, pas une étiquette de modèle.

| Nom | Couple | Rôle dans le protocole |
|---|---|---|
| `llm_only` | `(llm_proxy_tft, generous_tft)` | deux « agents LLM » (proxy scripté généreux) |
| `mix_llm_scripted` | `(llm_proxy_tft, tit_for_tat)` | hétérogénéité **inter-classes** : LLM face à scripté strict |
| `scripted_only` | `(generous_tft, suspicious_tft)` | baseline purement scriptée, hétérogène en générosité |
| `always_defect` | `(always_defect, always_defect)` | **contrôle négatif** — doit rendre exactement 0 |

Une assertion d'implémentation (`set(HET_PAIRS.keys()) == set(HETEROGENEITIES)`) empêche qu'une hétérogénéité du gel soit oubliée à l'implémentation.

### Hypothèses et seuils de verdict

- **H0** — la coopération moyenne est **constante cross-hétérogénéité** : chaque hétérogénéité tombe dans une bande de **±0,05** autour du modèle nul.
- **H1** — la coopération moyenne **dépend** de l'hétérogénéité : au moins une hétérogénéité sort de cette bande.
- **Modèle nul** : `uniform_random_seed` (chaque agent joue `C` ou `D` avec probabilité 0,5). Mesuré à **0,5038**.
- **Contrôle négatif** : `always_defect` doit rendre **exactement 0** — c'est la validation mécanique du pipeline, pas un résultat scientifique.

Les seuils sont lus **dans le gel**, jamais choisis après avoir vu les chiffres. Une moyenne arithmétique sur les seeds ne remplace pas la conjonction : le verdict se lit par hétérogénéité.

## 1. Résultats mesurés (sorties commitées du carnet)

| Hétérogénéité | Coopération | Lecture |
|---|---|---|
| `llm_only` | **1,0000** (5/5 seeds, écart-type 0) | point fixe trivial : deux TFT généreux se pardonnent et ne dévient jamais |
| `mix_llm_scripted` | **1,0000** (5/5 seeds, écart-type 0) | le TFT strict n'a jamais l'occasion de représailles : le proxy ne dévie pas |
| `scripted_only` | **0,9187 ± 0,0104** | le `suspicious_tft` ouvre par une défection, la traînée persiste (~0,08) |
| `always_defect` | **0,0000** (5/5 seeds) | contrôle négatif : pipeline validé |
| modèle nul | **0,5038** | référence de la bande H0 |

Verdicts : **0 H0, 4 H1**, dont 1 contrôle négatif, donc **3 résultats**. La variabilité qui compte est **inter-hétérogénéité** ; l'écart inter-seed est de 0,0104 sur `scripted_only`, nul ailleurs (grâce aux 50 rencontres par paire) ; la variabilité intra-seed atteint 0,09.

## 2. Ce que ces chiffres ne disent pas

Le proxy « LLM » est **scripté**. Les 1,0000 de `llm_only` et `mix_llm_scripted` sont donc le résultat attendu de deux politiques généreuses face à face — **pas** une observation sur le comportement d'agents LLM réels, et le carnet le dit lui-même dans sa lecture du §4. Ce point est la limite principale du livrable v1 et la raison pour laquelle l'exécution LLM est hors périmètre.

Conséquence pratique : la conclusion « l'hétérogénéité importe » est **portée par `scripted_only`** (0,9187), c'est-à-dire par la seule hétérogénéité où une politique réellement différente entre en jeu. Les deux hétérogénéités étiquetées LLM sont, en l'état, deux variantes de la même politique généreuse.

## 3. Extension prévue — appels LLM réels

Le §8 du carnet documente l'extension : remplacer `llm_proxy_tft` par un appel réel, sur une lane équipée d'un proxy LLM. Rien à réécrire dans le protocole — le gel est déjà posé, seule l'implémentation de la politique change. Contrainte respectée par la v1 : la lane qui a produit le carnet est **CPU-only sans proxy garanti** (règle F), donc aucun appel n'a été tenté et aucun résultat n'est présenté comme s'il en venait.

Critère de réussite de l'extension, formulable dès maintenant : à protocole identique, si `llm_only` cesse d'être un point fixe à 1,0000 et se met à varier cross-seed, c'est que le comportement LLM diffère du proxy — auquel cas le §4 du carnet demande une lecture neuve, pas un ajustement des seuils.

## 4. Sources

Gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA\GameTheory\` (identité vérifiée sur première page le 2026-10-15, `bibliography-hygiene.md`) :

- Vallinder A., Hughes C. (2024) — *Cultural Evolution of Cooperation among LLM Agents*.
- Payne J., Alloui M., Cros A. (2025) — *Strategic Intelligence in Large Language Models*.
- Axelrod R. (1984) — *The Evolution of Cooperation* (IPD, tournoi informatique) — cité pour les payoffs. Recherche par auteur et par titre dans le rayon `GameTheory\` au 2026-10-24 : **aucune copie archivée** ; le gisement porte en revanche `2014 - Barasz et al - Robust Cooperation…` et `2022 - Critch Dennis Russell - Cooperative and Uncooperative Institution Designs`, qui ne sont pas la source des payoffs.

## 5. Renvois

- Carnet : [`GameTheory-16h-Cooperation-LLM-Python.ipynb`](../../MyIA.AI.Notebooks/GameTheory/GameTheory-16h-Cooperation-LLM-Python.ipynb) (§0 gel, §2 hétérogénéités, §4 résultats, §7 verdicts, §8 extension).
- Pilote de la sous-série : `GameTheory-16e` (Othman–Sandholm, SAGT 2009) · populations : `GameTheory-16g`.
- Parents : [#14468](https://github.com/jsboige/CoursIA/issues/14468) (Epic distillations), [#15397](https://github.com/jsboige/CoursIA/issues/15397) (sous-série `GameTheory-16`).
