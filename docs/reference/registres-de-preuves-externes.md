# Registres de preuves externes — lire un registre vivant à côté de nos organes

**Statut** : note de doctrine, pérenne. Issue de rattachement : [#28430](https://github.com/jsboige/CoursIA/issues/28430), jalon 3 (« note de doctrine bornée, aucune modification du harnais »).
**Mesures** : 25/11/2026, relevees sur `origin/main` = `0731e94382e3e4e787ffc50bba686227a4aa4452`.
**Nature de la source** : donnée tierce. Aucun compte créé, aucune adhésion, aucun agent branché sur le service du registre. Le contenu est cité et lié, jamais recopié.

---

## 1. Pourquoi cette note existe

Un registre de preuve externe pratique trois choses que nos organes ne font pas encore : il **réécrit ses énoncés** quand une conjecture est retirée, il **facture une réfutation comme une preuve**, et il **sépare l'orchestrateur du juge** — celui qui écrit n'est pas celui qui valide.

Nous avons des équivalents partiels pour certains de ces points, et des absences réelles pour d'autres. Cette note les met en regard, mesure chaque chemin qu'elle cite, et **ne modifie aucun fichier de `agent_tests/prover`**. Ce qu'elle propose comme suites (#1453) est une liste d'expériences, pas un chantier ouvert.

## 2. Le registre consulté

Registre : `pequalnp.com` (« P vs NP, attacked live by a fleet of AI agents »), édité par Brilliant. Relevé du **25/11/2026 13:57:03Z**, sans authentification.

Copie archivée au gisement partagé (donnée tierce, hors dépôt public) :

```text
G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\Complexity Theory and Hardness\
  2026 - Brilliant - pequalnp.com - P vs NP attacked live by a fleet of AI agents (releve date du 25-11-2026)\
```

| Fichier | URL | Prélevé (UTC) | Octets | sha256 (préfixe) |
|---|---|---|---|---|
| `index.html` | `https://pequalnp.com/` | 2026-11-25T13:57:01Z | 21 654 | `4525eaa4` |
| `feed.atom` | `https://pequalnp.com/feed.atom` | 2026-11-25T13:57:01Z | 11 368 | `4f316027` |
| `how.html` | `https://pequalnp.com/how` | 2026-11-25T13:57:01Z | 16 807 | `8f48dd9b` |
| `about.html` | `https://pequalnp.com/about` | 2026-11-25T13:57:01Z | 13 945 | `1547c895` |
| `graveyard.html` | `https://pequalnp.com/graveyard` | 2026-11-25T13:57:02Z | 9 823 | `8b5b6ce4` |
| `board.html` | `https://pequalnp.com/board` | 2026-11-25T13:57:02Z | 9 052 | `ac4bbbbd` |
| `live.html` | `https://pequalnp.com/live` | 2026-11-25T13:57:02Z | 9 127 | `96ce0abf` |
| `programs.html` | `https://pequalnp.com/programs` | 2026-11-25T13:57:01Z | 8 545 | `bf974d83` |
| `papers.html` | `https://pequalnp.com/papers` | 2026-11-25T13:57:01Z | 8 550 | `31ae3f4c` |
| `robots.txt` | `https://pequalnp.com/robots.txt` | 2026-11-25T13:57:02Z | 1 248 | `8fa3036c` |

Le manifeste complet (URL, horodatage, taille, empreinte) est `MANIFEST.md` dans ce même dossier.

**Ce que le relevé autorise à dire.** Le flux `feed.atom` archivé contient 30 entrées : 13 `lemma_proposed`, 13 `lemma_checked`, 4 `lemma_refuted`. C'est un **comptage**, il ne dit rien de la vérité mathématique des lemmes.

**Ce qu'il n'autorise pas.** `robots.txt` ne porte aucune ligne `Content-Signal` : ni autorisation ni restriction selon sa clause (c). Le site ne publie **ni dépôt ni licence**. Rien de ce qui suit n'est donc réutilisable comme source de code ; c'est une donnée, consultée et citée.

## 3. Le protocole du registre, six règles mesurées

Chaque règle est vérifiée dans la copie archivée, pas dans un souvenir.

| # | Règle | Forme relevée | Fichier source |
|---|---|---|---|
| R1 | Le noyau revérifie, sans axiome hors des trois standards | « The checker builds the file in a pinned environment, has the kernel verify it a second time, and accepts it only if it proves exactly the recorded statement and rests on no gap and no axiom outside the standard three. » | `how.html` |
| R2 | Le juge ne juge pas la **fidélité** de l'énoncé | « What it cannot decide is whether a statement says what its plain sentence says: an orchestrator that did not write it reads that. » | `how.html` |
| R3 | Écrire et valider sont deux rôles | « Orchestrators write; the checker rules. » | `how.html` |
| R4 | Réfuter, c'est vérifier la **négation** | « Refuted: L-meta-10041 is false: its negation, L-meta-10042, is checked. » | `feed.atom` |
| R5 | Un contre-exemple a le **même statut** qu'une preuve | « … a counterexample to one of our own claims is recorded with the same standing as a proof. » | `how.html` |
| R6 | Le papier ne fait pas un résultat | « Only a step that survives that is handed to builder agents, who write it in Lean for the checker. Nothing argued on paper is shown as a result. » | `how.html` |

Deux précisions de mesure, qui change la lecture :

- **R4 : l'identifiant de la négation n'est pas systématiquement `N−1`.** Dans la fenêtre archivée, `L-meta-10041` est réfuté par `L-meta-10042`, `L-meta-10038` par `L-meta-10037`, `L-meta-11110` par `L-meta-11109`. La forme est « sa négation est vérifiée », pas « la négation suit l'énoncé ».
- **Le retrait avec remplacement existe, mais il n'est pas dans cette fenêtre.** Les deux fenêtres du 24/11 (consignées dans `releve-issue-28430-corps-integral.md`, même dossier d'archive) portent 3 retraits, de la forme « `lemma_retired: seat-clb-1 retired L-meta-4540, replaced by L-meta-4747: … plain now says AND/OR, two earlier wires ; same term` ». La fenêtre archivée du 25/11 n'en porte **aucune** (catégories `lemma_checked`, `lemma_proposed`, `lemma_refuted` seules). Le mécanisme est donc **attribué et daté**, pas récurrent.

**La conséquence qui compte pour nous.** « `same term` » signifie que le terme mathématique n'a pas changé quand la formulation, si. Toute borne reprise de ce flux doit être relue dans sa forme exacte au moment de l'emploi — c'est la règle que le carnet `Complexity-03g` applique à ses témoins.

## 4. Correspondance avec nos organes

Chaque chemin de la colonne « notre organe » a été **relevé sur `origin/main`** le 25/11/2026. Un chemin qui n'existe pas est écrit tel qu'il a été trouvé.

| Point du protocole | Notre organe | État | Chemin et ligne vérifiés |
|---|---|---|---|
| Aucun axiome hors des standards, aucune trace de `sorry` | `lean-axiom.yml` : allow-list par défaut `propext, funext, Classical.choice, Quot.lift, Quot.mk, Quot.sound` (`allow-axioms`, l. 55-58) ; `fail-on-sorry` à `true` par défaut (l. 59-69) ; le pas d'exécution est factorisé dans `axiom_check_step.py` (extrait verbatim du heredoc du workflow, #17336), `FAIL_ON_SORRY` y vaut `'true'` par défaut (l. 22, l. 160) | **comblé** | `.github/workflows/lean-axiom.yml` · `scripts/lean/axiom_check_step.py` |
| — idem, pour les ancres toujours interdites | `ALWAYS_FORBIDDEN_ANCHORS = ("native_decide", "Lean.ofReduceBool")` | **comblé** | `scripts/lean/axiom_i18n_siblings.py:96` |
| Fidélité de l'énoncé (R2) | Aucun état ne juge « l'énoncé dit-il ce que sa phrase dit ». `derive_result_kind` classe un **run**, pas une formulation ; `correctly_refused` signifie « objectif abandonné via `mark_sorry_intractable` », pas « négation vérifiée » | **absent** | `…/agent_tests/prover/verdicts.py:31` (fonction), l. 43-47 et l. 108-109 (verdict `correctly_refused`) · `…/agent_tests/prover/tools.py:3104` (`mark_sorry_intractable`) |
| Réfutation = négation vérifiée (R4) | Aucun état `refuted` : recherche de `refuted` sur `agent_tests/prover/*.py` → **0 occurrence**. Le harnais connaît le contre-exemple comme **stratégie de prompt** (« STRATEGY: negative result — construct explicit counterexample »), il sait le **figer comme garde** (`p4_nw_overlap_wall_c92_counterexample`), mais il ne forge pas de négation et n'a pas d'état « réfuté » | **absent** | `…/agent_tests/prover/config.py:851`, l. 888 (stratégie), l. 2036 (`cexBlock*`), l. 2041 (garde figée) |
| Retrait avec remplacement et motif (registre 24/11) | Aucun état de retrait : recherche de `lemma_retired` / `retired_by` / `replaced_by` sur `agent_tests/prover/*.py` → **0 occurrence** | **absent** | `…/agent_tests/prover/*.py` |
| Contre-exemple au même rang qu'une preuve (R5) | Le contre-exemple existe dans la **couche des énoncés** (démos, section de réfutation `cexBlock*`) et comme **garde figée** ; il n'existe pas comme entrée de rang dans le magasin de connaissances : `proof_knowledge.json` (232 476 octets, 10 clés racine : `version`, `last_updated`, `source_files`, `entries`, `tactic_cookbook`, `failed_approaches`, `mathlib_api`, `proved_theorems_inventory`, `proven_successful_tactics`, `wall_clock_burn_patterns`) ne porte **aucune** clé de contre-exemple ni de réfutation (recherche `cex` → 0) | **partiel** | `…/agent_tests/prover/proof_knowledge.json` · `…/agent_tests/prover/config.py` |
| Preuve sans trace (R1) | `LeanVerifier.check_axioms(..., fail_on_sorry=True, timeout=180)` : le `sorryAx` transitif fait échouer la vérification | **comblé** | `…/agent_tests/prover/lean_utils.py:1691` |
| Rôle du rédacteur distinct du rôle du juge (R3) | Séparés : l'agent rédige, le noyau rejoue ; mais **aucun acteur tiers** ne relit la fidélité de l'énoncé — le juge du dépôt est le même noyau qui a construit le fichier | **partiel** | `…/agent_tests/prover/verdicts.py:31` |

**Correction de chemin.** Le tableau de la distillation (#28430, §5) situait `lean_utils.py` et `config.py` sous `scripts/lean/` et `agent_tests/prover/`. Les deux fichiers sont en réalité sous `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/`, et `ALWAYS_FORBIDDEN_ANCHORS` vit dans `scripts/lean/axiom_i18n_siblings.py`, pas dans `axiom_check_step.py`. Les chemins ci-dessus sont les chemins **relevés** ; ceux de la distillation sont rectifiés ici.

## 5. Ce que la comparaison change, et ce qu'elle ne change pas

**Elle ne change rien dans le harnais.** Aucun fichier de `agent_tests/prover` n'est modifié par ce grain, et aucune porte de CI n'est touchée.

**Elle change trois convictions, à bon coût :**

1. `correctly_refused` n'est pas une réfutation. C'est un objectif abandonné. Le dire dans un rapport comme « l'agent a refusé, donc la conjecture est fausse » serait une inférence de travers — et c'est exactement la confusion que le registre rend visible en facturant ses réfutations comme des preuves.
2. Notre contre-exemple existe au niveau des **énoncés** et des **gardes**, pas au niveau des **connaissances**. Un contre-exemple que rien ne range n'a pas le statut que le registre lui donne.
3. Notre porte d'axiomes est **plus exigeante** que le juge du registre sur un point : nous refusons `native_decide` par défaut, le registre ne parle que des « trois standards ». L'écart est dans notre sens.

## 6. Deux expériences à faire naître sous #1453

Proposées, non engagées. Elles ne sont pas des tâches ouvertes par cette note.

1. **Enregistrer l'énoncé exact à côté de chaque tentative** — texte ou empreinte — pour que la question « avons-nous prouvé ce qui était enregistré ? » admette une réponse mécanique. C'est le point que le registre nomme explicitement (R2) et que notre harnais ne couvre pas.
2. **Un état `refuted` réservé à une négation vérifiée au noyau**, distinct de `correctly_refused` : l'un dirait « c'est faux, et voici la preuve », l'autre « j'ai abandonné ». Les deux ne doivent pas se lire l'un pour l'autre.

## 7. Ce que cette note ne prouve pas

- Elle ne prouve rien du registre : ni ses lemmes, ni ses réfutations, ni ses retraits. Elle en **décrit un protocole** à une date donnée.
- Elle ne dit pas que notre harnais est en retard : elle dit, chemin par chemin, où il l'est — et la plupart des lignes sont « comblé ».
- Elle n'ouvre aucun chantier : les deux expériences du §6 appartiennent à l'EPIC #1453.

## 8. Sources

- Registre (donnée tierce, archive datée du 25/11/2026 13:57:03Z) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\Complexity Theory and Hardness\2026 - Brilliant - pequalnp.com - P vs NP attacked live by a fleet of AI agents (releve date du 25-11-2026)\` — `MANIFEST.md`, `feed.atom`, `how.html`, `about.html`, `releve-issue-28430-corps-integral.md`.
- Distillation d'origine (cité pour la fenêtre du 24/11 et pour le tableau de correspondance) : [#28430](https://github.com/jsboige/CoursIA/issues/28430), §2 et §5.
- Nos organes, relevés sur `origin/main` (`0731e94382e3e4e787ffc50bba686227a4aa4452`) le 25/11/2026 : `.github/workflows/lean-axiom.yml`, `scripts/lean/axiom_check_step.py`, `scripts/lean/axiom_i18n_siblings.py`, `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/{verdicts,config,tools,lean_utils}.py`, `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/proof_knowledge.json`.
