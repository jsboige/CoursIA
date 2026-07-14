# Diagnostic Volet C Argumentum — prérequis PR-1 bump submodule

> **Statut** : PRÉPARATOIRE — c.494 po-2025 — 2026-07-14
> **Cible** : workers cherchant à exécuter le PR-1 = bump submodule Argumentum
> **Issue référente** : [#6409](https://github.com/jsboige/CoursIA/issues/6409) — Argumentum Volet C
> **Lead pressenti** : lane SK/Argument (po-2025) selon spécification ai-01

## TL;DR — findings L468-L1 verify-before-claim

L'issue #6409 annonce un PR-1 = bump submodule `053257c7 → 6fe0a84b` comme « pickup zero-code immédiat » avec promesse de récupérer E1-E4 (translators, arbitre neuro-symbolique, harness, shims). **La vérification croisée montre que le delta FF master ne récupère PAS E1-E4** — il s'agit essentiellement de docs(taxonomy/DNN/release) et feat(taxonomy) AIF serialization. PR-1 reste faisable techniquement (FF propre, 37 commits) mais son contenu réel ≠ celui suggéré par l'énoncé de l'issue.

## Périmètre vérifié firsthand

| Item | Énoncé issue #6409 | Réalité disque (2026-07-14) |
|------|---------------------|------------------------------|
| HEAD submodule (parent pointer) | `053257c7` | `053257c7d4d2fcf4b21e0e04eb335bfb0f50ff21` ✓ |
| HEAD submodule (working tree) | n/a | `ac33f607` **DETACHED** sur worktree parente — pas sur pointer |
| origin/master tip | `6fe0a84b` | `6fe0a84b81df53767d47a108a923b884766bf79d` ✓ |
| Commits between HEAD ptr et tip | « 37 commits behind » | **37 commits** (`git log 053257c7..origin/master --oneline \| wc -l`) ✓ |
| FF propre | « AUCUN force » | ancestry validée : `git merge-base --is-ancestor 053257c7 origin/master` → YES ✓ |
| Delta size | non quantifié | **71 fichiers, +7632/-478 insertions** (modeste) |
| Working tree state (worktree parente) | n/a | **DETACHED sur `ac33f607`** ≠ pointer parent `053257c7` — divergence warning |
| E1 translators (`structured_arg_translator.py`) | commits #1422/#1427/#1428/#1431 | **AUCUN commit** dans le delta FF, **AUCUN fichier** dans le submodule (`find . -name "*translator*"` = 0 hit, `orchestration/` = n'existe pas) |
| E2 arbitre neuro-symbolique Dung + `cq_evaluator` | #1433/#1435 | **AUCUN commit** dans le delta FF |
| E3 harness comparaison multi-backend | #1432/#1438/#1439 | **AUCUN commit** dans le delta FF |
| E4 shims C186h+ | « rend les handlers vendored importables » | **AUCUN commit** dans le delta FF |

## Composition réelle du delta FF (37 commits)

```
docs(taxonomy/ontology/dnn/release)        ~21 commits
feat(taxonomy): #498 AIF serialization     ~15 commits
test(ontology): #133 round-trip            ~1 commit
─────────────────────────────────────────────
Total                                       37 commits ✓
```

### Substance récupérée par PR-1 bump (catégorisation G.1)

| Substance | Valeur pour CoursIA | Risque |
|-----------|--------------------|--------|
| **145 AIF fallacies fully-modeled** (vs 121 au HEAD parent) — `#498` Fallacies AIF serialization phases 1-3 (tranches b/c/d/e/f/g) | **HAUTE** : enrichissement ontologique pour Argumentum OWL (post-`#4960` shutdown handlers) | OK — gated, GO ai-01 confirmé dans messages commits |
| **OWL prep round-trip `#133` cleared** — argumentum.owl regeneré (AIF attack 93→145) | **HAUTE** : ferme une dette connue `#133` | OK — test baseline 595/1 → 596/0 |
| **Multilingual drift audit 2026-07** — real content clean (0 write prod) | **MOYENNE** : audit publication-ready | OK — read-only diagnostic |
| **DNN-Platform GoLive runbooks refresh** post-execution (10.3.2+2sxc21) | **MOYENNE** : ops docs | OK — déploiement réel documenté |
| **i18n link_* scoping gap isolated** — 3822 cells, 0 write | **MOYENNE** : rapport diagnostic, pas d'action immédiate | OK — documented scope |
| **CHANGELOG/RELEASE-NOTES v0.9.0** — AIF layer + 595 tests | **BASSE** : publication bookkeeping | OK — standard release notes |

### Substance NON récupérée par PR-1 (E1-E4 absents)

Les promesses E1-E4 de l'issue #6409 référencent des numéros de commits (`#1422`-`#1439`) **hors du delta FF master actuel**. Trois hypothèses :

1. **Branches upstream non-mergées** : les commits existent sur des branches `feat/*` upstream Argumentum jamais mergées sur master → un PR-1 de simple FF ne les ramène pas, il faudrait cherry-pick ciblé.
2. **Renommage upstream** : les translators existent sous un autre nom/chemin que celui annoncé.
3. **Issue #6409 spéculative** : les commits #1422-#1439 sont un plan projeté qui n'a pas encore été implémenté en upstream.

**Recommandation** : avant tout PR-1, vérifier auprès de l'upstream (Argumentum maintainer) le statut des commits E1-E4. Si ils existent sur une branche `feat/translators` ou similaire, faire un PR-1bis = cherry-pick ciblé de ces commits.

## Garde-fous opérationnels (HARD)

### Submodule partagé entre worktrees (L487-L1 ★★★)

Le submodule `Argumentum` a son `.git` directory dans `.git/modules/...` partagé entre les 45 worktrees actives du dépôt. Toute manipulation du submodule working tree (checkout, reset, etc.) affecte potentiellement toutes les worktrees.

**Anti-pattern observé en worktree parente** :
- HEAD working tree = `ac33f607` (DETACHED)
- HEAD pointer parent = `053257c7`
- → divergence de 143 commits entre working tree et pointer

**Procédure recommandée pour PR-1 (par worker suivant)** :

```bash
# 1. Worktree isole FRAIS depuis origin/main
git worktree add ../CoursIA-c495-arg-bump -b feature/c495-arg-pr1-bump origin/main

# 2. Init submodule (peut timeout si réseau lent, retry)
cd ../CoursIA-c495-arg-bump
git submodule update --init MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum

# 3. Checkout du target dans le submodule
cd MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum
git fetch origin
git checkout 6fe0a84b  # DETACHED OK pour bump, le commit sera figé par le parent

# 4. Vérifier avant commit parent
cd ../..  # retour au worktree parent
git status  # doit montrer: modified: Argumentum (new commit)
git diff --stat MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum
# doit montrer 71 files / +7632/-478 insertions

# 5. Commit + PR
git add MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum
git commit -m "feat(argumentum,#6409): PR-1 bump submodule 053257c7 → 6fe0a84b..."
```

### Risques identifiés

| Risque | Mitigation |
|--------|-----------|
| `git submodule update --init` timeout (réseau) | Retry avec `--depth 1` |
| Worktree collision (submodule partagé) | Worktree isole FRAIS, JAMAIS manipuler le submodule depuis la worktree parente |
| `--depth 1` masque l'historique | OK pour PR-1 (juste besoin du tip), pas pour cherry-pick futur |
| Force push interdit sur shared branches | `git push` simple vers `feature/c495-arg-pr1-bump` |
| PII étudiants (cf issue #6409 garde-fou) | Audit tree pré-bump : exclure `1.4.1-JTMS`, `2.1.6_*`, `2.3.x_*`, `3.1.5_*`, `evaluation/corpus/*.json` |

## Substance récupérable post-PR-1 (recommandation pour c.495+)

Une fois PR-1 mergé, le worker suivant peut attaquer les PR-2+ du plan #6409 :

- **PR-2** = shims runtime C186h+ (E4) — **débloquant technique**, à prioriser
- **PR-3** = 1 notebook pédagogique FR par essence E1/E2/E3 — **port distillé** (PAS bulk-copy des 125k lignes Argumentum)
- **NOTICE-EPITA** obligatoire sur chaque port (cf issue #6409 garde-fou PII/exclude)
- **Prose FR** (readme-french-first.md)

## Conformité règles

| Règle | Application |
|-------|-------------|
| §A single-subject | ✓ Ce PR = diagnostic PR-1, pas bump |
| §E doctrine corrigée | ✓ Pas de modification figures |
| R1 catalog-pr-hygiene | ✓ 0 fichier catalogue touché |
| R2 rebase frais | ✓ Worktree c.494 base = origin/main `f6a42a173` |
| L268 LF-only | ✓ Diagnostic en LF |
| L143 secrets-hygiene | ✓ 0 secret inline (lecture seule) |
| L468-L1 verify-before-claim DURCIE | ✓ **APPLIQUÉ** : findings cross-check documentent l'écart entre énoncé et réalité |
| L487-L1 ★★★ submodule partagé | ✓ 0 touch submodule, worktree isole |

## Liens utiles

- **Issue** : [#6409 Argumentum Volet C](https://github.com/jsboige/CoursIA/issues/6409)
- **EPIC source** : [#4960 Argument_Analysis v3 landing essence multidimensionnelle EPITA-IS](https://github.com/jsboige/CoursIA/issues/4960) (CLOSED — handlers vendored, source de vérité)
- **Submodule upstream** : [`ArgumentumGames/Argumentum`](https://github.com/ArgumentumGames/Argumentum) (master tip = `6fe0a84b`)
- **MEMORY L468-L1** : verify-before-claim DURCIE — leçon issue #5780 figures audit
- **MEMORY L487-L1** : submodule working tree partagé entre worktrees
- **MEMORY L429** : Substance > Sweep — pivot post-sweep §E po-2025

---

_Document generated by po-2025 c.494, lead SK/Argument, 2026-07-14_
