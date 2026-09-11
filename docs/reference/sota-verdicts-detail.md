# SOTA — détail : mandat verbatim, incidents d'axes, mesures anti-fabrication

Détail durable de [`.claude/rules/sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) (harness-hygiene tier 2). La règle porte les tables opératoires (5 verdicts, checklist 6 axes, enforcement) ; ce fichier porte les verbatims, les incidents fondateurs et les mesures qui les justifient.

Registre des audits par famille : [`docs/ledgers/3801-sota-axe2.md`](../ledgers/3801-sota-axe2.md).

## 1. Mandat user 2026-06-21 — les trois messages

> **[msg1]** outil SOTA approprie proprement **installe ou invoque** s'il s'agit d'un service ; sinon, **le brancher avec un coup de main user**, ou **le rebrancher** s'il l'a ete dans le passe, typiquement sur une **machine particuliere avec le bon environnement**.
>
> **[msg2]** tenir un **registre** et **resserrer le harnais ET le comportement de review des bots** (le leur signaler) — pour l'heure le **reflexe reste de chercher des workarounds degrades** plutot qu'installer et corriger ce qu'il faut.
>
> **[msg3]** **qualite des problemes souvent trop basiques** (cf BFS vs A*) — complexifier les pbs actuels ou proposer des pbs additionnels plus complexes pour **faire valoir toutes les capacites des moteurs externes**, la ou des exemples triviaux ne les mettent pas en valeur ; **modulo un temps de traitement raisonnable**.

Les trois prongs de la règle en dérivent directement : msg1 → Prong A (5 verdicts), msg2 → registre #3801 + enforcement bots, msg3 → Prong B (problème non-trivial).

## 2. Checklist 6 axes — origine de la 6ᵉ entrée (#10459)

Trois verdicts `INTRINSIC` OpenSpiel **convergents** dans 3 PRs distinctes (#10390 / #10394 / #10454) — aucun n'avait examiné l'axe **PythonNet**. Aucun des trois auteurs n'a menti ni bâclé : l'axe était simplement absent de la taxonomie d'audit, donc sauté par tous.

Le dépôt certifiait pourtant déjà le pont ailleurs : `MyIA.AI.Notebooks/GenAI/SemanticKernel/09-SemanticKernel-Building-CLR.ipynb` (PythonNet 3.0.5 + `Runtime.PythonDLL` loading), verdict `SOTA-OK` au ledger #3801. Le user l'a rappelé verbatim le 2026-08-11 :

> « PythonNet pour bridger est tout a fait acceptable, fonctionne plutot bien … overhead negligeable »

**Preuve d'exécution par l'axe 5** — 5 PRs **MERGED** sur `main` posant le pont `.NET → CPython → pyspiel` :

| PR | Mesure livrée |
|---|---|
| #10464 | CFR exploitability **0.008226** |
| #10470 | MCTS **action = 4** |
| #10496 | rollout Kuhn poker |
| #10585 | `kuhn_poker` **NashConv 0.0230** |
| #10598 | stratégie axelrod |

Plus la précédente SK-09 (documentée au ledger). La porte était fermée à tort ; elle est désormais **prouvée**, avec cinq mesures distinctes.

**Ce que l'incident enseigne.** C'est la **deuxième** omission d'axe (la première était `IKVM`, pont Java). Deux occurrences de la même classe démontrent qu'une règle non explicite ne se corrige pas par plus de vigilance : elle demande un **organe** — ici la checklist nominative, qui rend l'omission visible au reviewer au lieu de dépendre de ce que l'auteur pense à examiner. Cf [[taxonomy-omission-propagates-to-every-auditor]] et [[rule-needs-an-organ-not-more-vigilance]].

## 3. Prong B — mesurer la discrimination AVANT de clamer « l'heuristique échoue »

Un enrichissement Prong-B ne se déclare pas sur un **pitch plausible** : on **mesure** d'abord la discrimination firsthand (installer le solveur — règle F — et comparer résultat-heuristique vs optimum exact sur le graphe candidat). Un pitch non mesuré est une violation G.9 en attente d'être livrée.

### Anti-exemple vérifié firsthand (c.598, ortools 9.15 + networkx 3.4.2)

Le pitch : « les heuristiques gloutonnes ratent le nombre chromatique sur les graphes de Mycielski, donc CP-SAT est essentiel ».

La mesure : sur M_3 (C5), M_4 (Grötzsch), M_5, la coloration gloutonne **et** DSATUR **avec l'ordre networkx par défaut** trouvent **le** χ exact (3 / 4 / 5). Le folklore « greedy rattrape sur Mycielski » **ne reproduit pas** ici — il exige des ordres de sommets adversariaux qu'un notebook pédagogique ne construit pas. S'en servir comme cas Prong-B de coloration = fabriquer un enrichissement faux.

Le vrai cas discriminant pour CP-SAT en coloration est le **graphe aléatoire dense Erdős-Rényi G(n, p ≥ 0.3)**, où greedy utilise strictement plus de couleurs que χ — et `App-2-GraphColoring` le démontre déjà (cellule benchmark : n = 200, greedy = 22 / DSATUR = 19 / CP-SAT = 18).

### Faux signal technique — grep MiniZinc

Un notebook MiniZinc couvre l'optimisation via la syntaxe `solve minimize obj;` (**chaîne dans le modèle**), pas via `.minimize(` Python. Un `grep '.minimize('` renvoie `opt=0` sur des notebooks qui traitent bel et bien l'optimisation. Pour MiniZinc, grepper `solve (min|max)imize` dans les chaînes de modèle.

## 4. Registre axe-2 — critère de fin et pièges de dénombrement

Une entrée de registre est une **section `## Entry #NNN — <Famille> (owner <lane>, c.NNN)`** dans
[`docs/ledgers/3801-sota-axe2.md`](../ledgers/3801-sota-axe2.md), la « Convention d'entrée » se lit en
tête du fichier, et l'entrée arrive **par PR** — jamais en commentaire d'issue : sept entrées ont été
postées sur l'EPIC #3801 après sa fermeture (la dernière le 2026-08-07) ; aucune requête `--state open`
ne les atteint et un `grep` d'auditeur sur le dépôt ne les voit pas.

**Critère de fin de l'axe-2** — trois conditions, toutes vérifiables :

1. **chaque famille de notebooks du dépôt porte une entrée** ;
2. **chaque entrée porte un verdict agrégé** (un des 5) ;
3. **chaque verdict != `SOTA-OK` est soldé** : soit une PR de fix **mergée** citée dans l'entrée, soit un
   `INTRINSIC` établi par la checklist 6 axes (section 2).

La condition 1 se **mesure**, elle ne se recopie pas :

```bash
grep -c '^## Entry #' docs/ledgers/3801-sota-axe2.md          # entrées au registre
grep -oE '^## Entry #[0-9]+ — [^(]+' docs/ledgers/3801-sota-axe2.md   | sed 's/^## Entry #[0-9]* — //;s/ *$//' | sort -u          # familles couvertes
```

**Piège du grain** : le ledger indexe par **famille** (`Search`, `Tweety`), pas par répertoire — comparer
son compte à un `find MyIA.AI.Notebooks -name '*.ipynb'` agrégé par répertoire donne deux nombres qui ne
se soustraient pas.

**Piège des « Cumul entries »** : il y en a **deux**, tous deux périmés (mesure du 2026-09-03) — `## Cumul
entries` (l.485) s'arrête à l'entrée **8** (2026-07-10) et `### Cumul entries (registre axe-2 SOTA)`
(l.854) à l'entrée **22** (2026-07-11), alors que le fichier porte **30** entrées. Le plus récent
sous-compte d'un facteur ~1,4 ; le plus ancien, d'un facteur ~3,8. Rafraîchir et **fusionner les deux
tableaux en un seul** est un grain à part (le fichier dépasse #14519).

## Voir aussi

- [`.claude/rules/sota-not-workaround.md`](../../.claude/rules/sota-not-workaround.md) — la règle (tables opératoires)
- [`docs/ledgers/3801-sota-axe2.md`](../ledgers/3801-sota-axe2.md) — registre des audits par famille
- [`.claude/rules/secrets-hygiene.md`](../../.claude/rules/secrets-hygiene.md) règle 6 — Stop & Repair (triage cause A/B/C + incidents)
- [`.claude/rules/pr-review-discipline.md`](../../.claude/rules/pr-review-discipline.md) §H — enforcement bots
