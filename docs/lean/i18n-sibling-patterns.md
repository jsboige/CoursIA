# Lean i18n — patterns de paires FR/ER et discipline du checker (#4980)

**Statut** : référence durable (2026-07). EPIC **#4980** (harmonisation FR + traduction EN des `*.lean`).
**Scope** : tout `*.lean` « own » (hors `.lake/packages/`, `_peters/`, `reference_docs/`, `agent_tests/`, libs vendored) portant une paire sibling `Foo.lean` (FR canonique) / `Foo_en.lean` (miroir EN), convention Pattern A ratifiée user 2026-07-04.

Ce fichier **complète** [`i18n-inventory-cycle-38.md`](i18n-inventory-cycle-38.md) (qui porte la *proposition de convention* Options A/B/C) et l'inventaire live [`I18N_INVENTORY.md`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/I18N_INVENTORY.md). Il documente ce que ni l'un ni l'autre ne couvre : les **trois formes structurelles** qu'une paire sibling peut légitimement prendre, et **la discipline opératoire** qui évite de casser un build en « corrigeant » une sortie de checker.

## Convention de base (rappel §Lean i18n de `code-style.md`)

- **FR canonique** (`Foo.lean`), **EN miroir** (`Foo_en.lean`) dans le même lake, **les deux compilent**.
- Suffixe `_en` sur le **namespace** (`namespace FooLean` ↔ `namespace FooLean_en`) et les **imports** (`import Foo.Bar` ↔ `import Foo.Bar_en`).
- **Énoncés de théorèmes/lemmes, tactiques, noms de lemmes, références Mathlib** restent en anglais dans les DEUX fichiers.
- Seules les **docstrings `/-- … -/`** et **commentaires `-- …`** diffèrent (traduction). Le reste est **byte-identique modulo le suffixe `_en`** — vérifiable par `scripts/lean/check_i18n_siblings.py` (#6711).

## Les trois formes légitimes d'une paire sibling

Une paire « conforme » n'est pas nécessairement un miroir texte-à-texte. Trois formes existent, **toutes valides**, chacune reconnue par une classification distincte du checker :

### Forme 1 — Miroir auto-contenu (`OK`)

Le fichier EN **redéclare** toutes les entités du FR avec le suffixe `_en`, et compile de façon autonome. C'est la forme par défaut (rollout `conway_lean`, 23/23 paires). Le checker normalise le suffixe `_en` symétriquement (`\b(\w+)_en\b → \1`) et compare les corps dépouillés des commentaires/lignes structurelles : verdict **`OK`** si byte-identique.

Deux sous-variantes également valides (leçon C565-L1) :
- **reuse-FR-names** : l'EN fait `open <NamespaceFR>` et réutilise les identifiants FR.
- **prefixed-suffix** : l'EN définit des entités suffixées `_en` (ex. `TUGame_en`).

### Forme 2 — Jumeau consommateur (`OK-CONSUMER`)

Le fichier EN **`import`e le FR canonique** et **réutilise ses defs** (via `open`), ne **redéclarant QUE** les lemmes/théorèmes qu'il énonce lui-même. Il **NE DOIT PAS re-mirrorer** les defs partagées : les redéclarer côté EN les **shadow/conflit** avec celles importées → `lake build` **FAIL**.

Le checker (#6718) reconnaît ce motif : quand l'EN `import`e le sibling FR, les blocs FR sans contrepartie EN sont classés « réutilisés via import » (pas un drift), et seuls les blocs EN effectivement énoncés doivent matcher un bloc FR. Verdict **`OK-CONSUMER`** — p.ex. `StableMarriage/Lattice_en.lean` : « 4 FR declaration block(s) reused via import; all EN-stated blocks match FR ».

> **Piège fondateur (#6717)** : un worker voit le checker *ancien* signaler « 4 defs manquants côté EN » et les **réintroduit** → casse le build sur les propres cibles de la PR (root-cause forensique po-2024 c.520 + po-2026 c.468). La bonne action était l'inverse : **ne rien réintroduire**. Un jumeau consommateur qui compile est déjà conforme.

### Forme 3 — Divergence de qualifieur légitime (`OK`, intrinsèque)

Quand une entité existe **au top-level** côté FR mais **dans un namespace** côté EN, la **résolution de nom Lean diffère** et **impose** des qualifieurs différents dans les deux fichiers — ce n'est **pas** un drift de substance, c'est **intrinsèque** :

- FR : `def is_strictly_best` top-level → une référence désambiguïse avec `_root_.is_strictly_best`.
- EN : la def vit dans `namespace SocialChoice_en` → `_root_.` **ne résout pas**, il **faut** écrire `SocialChoice_en.is_strictly_best`.

Les deux qualifieurs **doivent** différer pour que **chacun** compile. Un checker byte-identité naïf voit un « drift » là où la divergence est obligatoire (la résolution de nom scope-dépendante est **invisible textuellement**). Le checker #6718 normalise les self-qualifiers (`_root_.X` ↔ `<Ns_en>.X` du namespace local) : verdict **`OK`** — c'est le faux positif qui avait cassé **#6716** (fermé comme FP après l'errata).

## Roots aggregators sans sibling `_en` — classification des faux positifs

Les trois formes ci-dessus décrivent une **paire sibling existante** (`Foo.lean` + `Foo_en.lean`). Une source de confusion récurrente distincte : le **root aggregator** d'un lake (`<Lib>.lean`) qui **n'a pas** de `<Lib>_en.lean`. Un scan naïf « FR > EN » (ou un checker `ORPHAN`) le signale comme un gap à corriger — **souvent à tort**. Vérifié firsthand c.559–c.560 (origin/main `6c6aeb1b9`) :

| Catégorie | Le root porte… | `_en` attendu ? | Exemples vérifiés firsthand |
|-----------|---------------|-----------------|-----------------------------|
| **Inline Option B** | FR + EN dans sa docstring (« ce fichier root aggregator est bilingue inline ») | **NON** — créer un `_en` contredirait la convention déclarée | `Finiteness.lean`, `Argumentation.lean`, `SocialChoice.lean`, `Grothendieck.lean`, `Minimax.lean` |
| **Exemption documentée** | FR-only ; déclare que les siblings `_en` des leaves sont **exprès non importés** (landmine de collision de namespace) | **NON** — l'exemption est écrite dans le root | `CooperativeGames.lean` (abbrev `Coalition` top-level dupliquée `Basic.lean`/`Basic_en.lean`) |
| **Skeleton comment-only** | 0 import actif (commentaire de plan de regroupement) | **NON** — hors scope i18n | `GameTheory.lean` (c.299, EPIC #4365) |
| **FR-only substantiel (Pattern A)** | FR-only, **importe** ses leaves substantiels | **OUI** si **tous** les leaves importés ont leur `_en` | `Utility.lean`/`Gittins.lean`/`Coherence.lean` (decision_theory), `RepeatedGames.lean`/`StableMarriage.lean` (game_theory), `Knots.lean`, `Sensitivity.lean`, `Astar.lean`, `Sudoku.lean` |

### Test de classification (à exécuter AVANT de créer un `<Root>_en.lean`)

1. **Lire la docstring du root FR.** Si elle déclare « bilingue inline » → **Pattern B inline**, ne pas créer de `_en` (FP).
2. Sinon, si elle déclare une **exemption** (siblings `_en` non importés exprès, collision documentée) → **ne pas créer de `_en`** (FP).
3. Sinon, si le root est un **skeleton comment-only** (0 `import`) → **hors scope**.
4. Sinon (root FR-only substantiel qui importe ses leaves) → vérifier que **chaque leaf importé a son `_en`**. Si oui → Pattern A, créer `<Root>_en.lean` est un grain légitime (convention-pure split, cf #6682/#6685/#6662). Si un leaf importé manque son `_en` → traiter ce leaf d'abord (le root `_en` sans ses leaves `_en` ne compile pas).

> **Incident de méthode (c.559–c.560)** : un steer coordinateur avait classé `SocialChoice.lean` comme « root `_en` légitime dès le 8ᵉ sibling », mais le root est **déjà inline Option B** et le « 8ᵉ module » (`_SmokeTest.lean` = trivial sanity test `0+n=n`) est explicitement exclu de la liste des substantiels. Verdict reposait sur 2 FP non vérifiés par lecture du root. **La lecture du root FR est non-négociable** avant tout grain i18n root — le label « ORPHAN » d'un checker ou un claim hérité ne remplace pas la lecture de la déclaration de convention dans la docstring.

## Discipline opératoire — HARD

> **Une sortie de checker `DRIFT` / `ORPHAN` est un POINT DE DÉPART D'INVESTIGATION, JAMAIS un grain à exécuter verbatim.**

Les incidents **#6716** (Arrow, qualifieur intrinsèque pris pour un drift → PR fermée) et **#6717** (Lattice, jumeau consommateur « re-mirroré » → build cassé) partagent la **même erreur de méthode** : traiter la ligne `DRIFT`/`ORPHAN` d'un outil comme une consigne de correction, sans line-verify ni build. Avant d'**auteur** ou de **dispatcher** un fix i18n :

1. **Line-verify** la paire réelle : lire le FR ET l'EN, identifier laquelle des 3 formes s'applique. Un `DRIFT` peut être une divergence de qualifieur (Forme 3) ou un jumeau consommateur (Forme 2) — ni l'un ni l'autre ne se « corrige » en alignant le texte.
2. **`lake build <cible>_en` en local** (ou CI cold-build à glob correct) **AVANT** de committer/dispatcher. Le seul juge d'un fix i18n est la **compilation**, pas la byte-identité textuelle.
3. Un `ORPHAN` (EN sans frère FR) n'est pas forcément un grain : vérifier s'il s'agit d'un lake **legacy-absorbé** (ex. `repeated_games_lean/RepeatedGames_en` = tracké #4365, sa suppression est la bonne action, **pas** la création d'un frère FR).

## Gate de merge d'une PR i18n

- **Byte-identity PASS** via `check_i18n_siblings.py` sur le lake modifié (verdict `OK` / `OK-CONSUMER` — un `DRIFT` résiduel non justifié bloque).
- **CI Lean verte** = cold-build du lake (les lakes à glob correct — `conway_lean` `Conway.*`, `game_theory_lean` — cold-compilent réellement en CI ; un `Lake build (<lake>)` **RED** est un **bloqueur de merge dur**). Le cold-build local ~8-40 min étant impraticable en cadence worker, **le CI EST le gate** ; un claim « lake build SUCCESS » dans le body, non prouvé par le CI in-PR-glob, ne suffit pas (cf [lean-merge-discipline.md](../../.claude/rules/lean-merge-discipline.md)).
- **Forensique EXEC_PROVED** côté worker (le fichier compile, pas seulement « le texte matche »).

## Outil de vérification

```bash
python scripts/lean/check_i18n_siblings.py MyIA.AI.Notebooks/GameTheory/game_theory_lean   # un lake
python scripts/lean/check_i18n_siblings.py --all                                            # tout le dépôt
```

Sortie : `N/M pairs byte-identical | k consumer-pattern | j drift | i orphan`, avec le diff par paire en `DRIFT` (exit 1 si drift/orphan). Tests : `scripts/lean/tests/test_check_i18n_siblings.py` (13 cas, dont les repros des FP #6716 Forme 3 et #6717 Forme 2, auto-collectés par `scripts-tests.yml`).

## Voir aussi

- [`code-style.md` §Lean (i18n)](../../.claude/rules/code-style.md) — convention Pattern A ratifiée, siblings `Foo.lean`/`Foo_en.lean`
- [`i18n-inventory-cycle-38.md`](i18n-inventory-cycle-38.md) — proposition de convention (Options A/B/C), méthodologie d'inventaire
- [`I18N_INVENTORY.md`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/I18N_INVENTORY.md) — inventaire de couverture live
- [`lean-merge-discipline.md`](../../.claude/rules/lean-merge-discipline.md) — Lake build local/CI avant merge Lean
- [`readme-french-first.md`](../../.claude/rules/readme-french-first.md) — FR d'abord, EN préservé (parallèle prose ↔ docstrings)
