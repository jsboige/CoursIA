# Pré-enregistrement — réalisation de pertinence : engagement, traitement adverse et re-commitment

**Issue :** #8182 (veille et distillation progressive, candidat Vervaeke)
**Lane :** `myia-ai-01:CoursIA-2`
**Scellé :** 2026-10-23, **avant** toute implémentation et avant toute exécution sur les graines d'étude.

Ce document fixe les grandeurs mesurées, les bras comparés, les prédictions et leurs bandes **avant** de coder le module. Il est révisable une seule fois, par un commit distinct qui dit ce qui a changé et pourquoi (protocole de scellement v1 → v2 de la tranche Schurger, #13459) ; toute révision antérieure à l'évaluation held-out reste visible dans l'historique git.

---

## 1. Source, provenance et ce qui est attribué

**Référence lue :** Jaeger J, Riedl A, Djedovic A, Vervaeke J, Walsh D (2024), « Naturalizing relevance realization: why agency and cognition are fundamentally not computational », *Frontiers in Psychology* 15:1362658, DOI `10.3389/fpsyg.2024.1362658`, CC-BY.

**Copie archivée :** `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\2024 - Jaeger, Riedl, Djedovic, Vervaeke, Walsh - Naturalizing relevance realization (Front Psychol 15-1362658, CC-BY, OA).pdf`

Les passages sur lesquels repose ce carnet, cités verbatim depuis le texte extrait de cette copie :

1. « All of this involves a radically context-dependent generative dialectic called opponent processing—the continual establishment of trade-offs and synergies between competing and complementary organismic behaviors and dynamics (Vervaeke et al., 2012). » (§ introduction)
2. « Opponent processing means that organisms constantly play different approaches and strategies against each other in a process that iteratively evaluates progress toward a problem solution (toward reaching a particular goal). This can include dynamically switching back and forth between opposing strategies, if the necessity arises. » (§ introduction)
3. « […] an economic perspective (Vervaeke et al., 2012; Vervaeke and Ferraro, 2013a,b), which frames the problem of relevance based on **commitment**, i.e., the dynamic allocation of resources by an agent to the pursuit of a range of potentially conflicting or competing goals. Opponent processing is seen as a **meta-heuristic** approach: the agent employs a number of complementary or even antagonistic heuristics that are played against each other in the presence of different kinds of challenges and trade-offs. » (§ 2)
4. « Commitment to a specific action or strategy will immediately change the affordance landscape and will likely also affect the set of goals of the agent. » (§ 6)

**Ce que l'article soutient et que ce carnet ne teste pas.** Thèse de l'article : la réalisation de pertinence **ne peut pas être capturée complètement par un algorithme** (problème du cadre = problème de la pertinence). Aucune prédiction ci-dessous ne prétend réfuter ou confirmer cette thèse : on ne teste **pas** la non-formalisabilité, on teste la **partie opérationnelle** que les auteurs explicitent (points 1–4), sur un terrain fini et déclaré.

**Grade de provenance.** Les citations sont de grade A (copie archivée, lue). L'**opérationnalisation** qui suit est de grade C : c'est une **traduction choisie par cette lane**, pas une mesure que l'article revendique. Aucune phrase du carnet ne présentera l'opérationnalisation comme un résultat de l'article.

---

## 2. Surrogate déclaré

**Tâche.** Un agent doit **s'engager** sur un sous-ensemble de `k` indices parmi `n` (n = 24, k = 6) ; la récompense d'un pas est `|engagement ∩ pertinents(t)| / k`. Les pertinents changent : le terrain alterne deux régimes de pertinence et **bascule** à des instants planifiés (`shifts`), sans que l'agent en soit informé.

**Heuristiques adverses (au sens de la citation 2), deux et antagonistes :**
- `H_exploit` — conserver l'engagement courant, ne remplacer qu'un indice à la fois, choisi sur le signal d'erreur récent ;
- `H_explore` — ré-estimer l'engagement depuis zéro sur la fenêtre d'erreur récente.

**Allocateur adverse.** Chaque heuristique est créditée par le **progrès** qu'elle aurait produit sur la fenêtre récente (moyenne des récompenses contrefactuelles, calculée sans exécuter deux fois le terrain). L'engagement effectif est tiré du crédit relatif (tirage borné, graine fixée). L'agent **re-commite** (bascule d'heuristique) quand le déficit de crédit du perdant dépasse un seuil `theta`.

**Bras comparés (mêmes graines, même terrain, mêmes heuristiques disponibles) :**
| Bras | Règle d'allocation |
|---|---|
| `opponent` | crédit glissant + re-commitment au seuil `theta` |
| `static` | poids fixes 0,8 / 0,2, **aucune** bascule |
| `sham_rate` | même **nombre** de bascules que `opponent`, à des instants **tirés au hasard** (contrôle d'appariement de taux) |
| `stationary` | terrain **sans** bascule de pertinence (les quatre bras y sont rejoués) |

**Métriques.** `grip` = récompense moyenne sur les 40 derniers pas ; `switch_rate` par fenêtre ; `impasse` = plus longue suite de pas sans amélioration avant une bascule ; `concentration` = part des bascules qui tombent dans les 15 pas suivant une bascule de terrain, divisée par la part du temps que représentent ces fenêtres.

**Déterminisme.** Tout est graine-fixe ; `numpy.random.default_rng(seed+offset_bras)`. Aucune dépendance hors stdlib + numpy.

---

## 3. Prédictions pré-enregistrées

Toutes portent sur les graines d'étude `(0, 1, 7, 42, 99)` ; les bandes sont **fixées ici**, avant le pilote de calibration (graine `1000`, disjoint, hors étude).

| # | Prédiction | Bande préfixée | Réfutation |
|---|---|---|---|
| **P1** | Sur terrain à bascules, l'allocateur adverse garde mieux la prise que l'allocateur fixe. | `grip(opponent) − grip(static) ≥ 0,05` sur **chaque** graine d'étude | une seule graine sous la bande ⇒ réfutée |
| **P2** | Le bénéfice vient de l'**évaluation**, pas de la variabilité : un sham apparié en taux ne récupère pas la prise. | `grip(opponent) − grip(sham_rate) ≥ 0,03` sur **chaque** graine | une seule graine sous la bande ⇒ réfutée |
| **P3** | Le re-commitment est **déclenché** par la bascule, pas périodique. | `concentration ≥ 2,0` sur la médiane des graines, et `switch_rate` après bascule au moins 2× le taux hors fenêtre | médiane < 2,0 ⇒ réfutée |
| **P4** | Le re-commitment utile est **précédé d'une impasse mesurable**. | `impasse ≥ 3` pas avant au moins 60 % des bascules qui améliorent la prise (gain ≥ 0,02 sur les 10 pas suivants) | < 60 % ⇒ réfutée |
| **P5** | L'avantage est **conditionnel** à la bascule : pas de supériorité en terrain stationnaire. | `grip(opponent) − grip(static) ≤ 0,02` en terrain stationnaire sur **chaque** graine | une graine > 0,02 ⇒ réfutée |

**Verdict.** `SUPPORTED` si P1–P5 tiennent toutes sur les 5 graines ; `PARTIAL` si P1 et P2 tiennent et au moins deux des trois autres ; `REFUTED` sinon. Un verdict `PARTIAL` se publie tel quel, avec la liste exacte des prédictions tombées.

**Contre-régime explicité d'avance.** Un résultat où `sham_rate` égale `opponent` réfuterait l'attribution à l'évaluation et serait publié comme tel : ce serait la preuve que la simple variabilité suffit sur ce terrain, et la discussion devrait dire pourquoi la traduction de la citation 2 ne discrimine pas ici.

---

## 4. Ce qui ne sera pas fait

- Aucun ajustement de bande après lecture des graines d'étude. Un ajustement post-pilote est possible **avant** l'étude et se commit séparément (v2), en nommant la valeur v1 et la raison.
- Aucune généralisation à la thèse de non-formalisabilité de l'article.
- Aucun terrain choisi pour favoriser l'allocateur adverse : le terrain, les heuristiques et les seuils sont écrits avant le module et ne dépendent pas des résultats.
