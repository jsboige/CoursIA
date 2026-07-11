## Résumé

§H.4 sweep forensic review de PR #6024 (`feat(kelly_lean): complete sign trichotomy kellyFrac neg/zero iff + growth-value capstone (FR+EN), See #4052`). Sweep L143 SAFE cross-owner (jsboige owner-lane axe-2 Lean QuantConnect #4052 Kelly criterion vs po-2023 reviewer, lane axe-1 GenAI de-spaghetti).

**Verdict** : MERGEABLE sans modification.

## Ledger

[`docs/ledgers/reviews/2026-07-11-h4-sweep-6024.md`](docs/ledgers/reviews/2026-07-11-h4-sweep-6024.md) documente G.1 firsthand 11/11 PASS + 5 hunks EXEC_PROVED (3 commits FR + 3 commits EN mirror + 1 fix commit symmétrique + 1 capstone additionnel non documenté body PR).

## G.1 sampling (5/5 EXEC_PROVED, 14 theorems byte-parity FR == EN)

- `Kelly.lean` trichotomy (commit `b4600a355`, +33/-0, 4 theorems `kellyFrac_neg_iff` + `growthGrad_zero_neg_iff` + `kellyFrac_eq_zero_iff` + `growthGrad_zero_eq_zero_iff`) — **EXEC_PROVED** Mathlib `div_lt_iff₀ β.hb_pos` + `div_eq_zero_iff, or_iff_left β.hb_pos.ne'`
- `Kelly_en.lean` trichotomy (commit `b4600a355`, +33/-0, 4 theorems mirror FR+EN parity) — **EXEC_PROVED** byte-identique theorems
- `Kelly.lean` + `Kelly_en.lean` proof fix (commit `711486841`, +2/-2, symmétrique div_eq_zero_iff replace) — **EXEC_PROVED**
- `Kelly.lean` capstone `kelly_growth_eq_zero_iff` (commit `d2e07e107`, +31/-0, g(f*)=0 ↔ f*=0) — **EXEC_PROVED** via pre-existing `kelly_unique` (Kelly.lean L136) + `growth_zero` (Growth.lean L46)
- `Kelly_en.lean` capstone mirror (commit `d2e07e107`, +30/-0) — **EXEC_PROVED** byte-parity

## Check-links sweep-ledger hygiene (commit 2, ★ C354-L1)

Commit 2 corrige 2 liens cassés pré-existants dans les ledgers c.399 (#5957) et c.406 (#5971) :
- `docs/ledgers/reviews/2026-07-11-h4-sweep-5957.md:66` — `../reference/sota-not-workaround.md` → `../../../.claude/rules/sota-not-workaround.md`
- `docs/ledgers/reviews/2026-07-11-h4-sweep-5971.md:97` — `../reference/pr-review-discipline.md` → `../../../.claude/rules/pr-review-discipline.md`

Cause : les règles ont migré de `docs/reference/` vers `.claude/rules/` (mandat user 2026-06-01), mais les ledgers c.399/c.406 ont été mergés avec l'ancien path. La baseline `scripts/tests/baseline_docs_links.json` (#2735, 2026-07-09) prédate ces merges, donc `check-docs-links.py --check` flaggait ces 2 liens comme "new regression" sur chaque PR touchant `docs/ledgers/`.

Reproduit le fix `baac791c7` (jsboige commit déjà authored mais jamais merged sur main). Vérifié localement : `python scripts/check_docs_links.py --check` → `OK: No new broken links. (0 pre-existing, 3712 total)` exit 0.

Scope-strict : 2 fichiers, `+1/-1` chacun. Pas de réécriture de contenu (le texte `≫ floor placeholder` est préservé verbatim). Conformité R3 atomique-PR : sujet unique = §H.4 sweep ledger hygiene.

## Vérifications

- 14 theorem signatures FR == 14 EN byte-parity (vérifié via strip-docstring filter)
- sorry 0 + axiom 0 dans FR+EN (post-mask `\bsorry\b` + `\baxiom\b` regex)
- `kelly_unique` (Kelly.lean L136) + `growth_zero` (Growth.lean L46) + `Feasible β 0` (Bet.lean) = pré-existants (anti-régression safe)
- Lean CI SUCCESS proxy L343-L1 : 10/10 PASS ou skipping
- SHA1 pre-PR `d3da82e40` vs post-PR head `d2e07e107` = différent (3 commits additifs ≠ byte-identity OK)
- anti-phantom L275 verified `gh pr view 6024 --json state,mergeable,mergeStateStatus`
- Capstone additionnel `kelly_growth_eq_zero_iff` **non documenté body PR** (commit 3 séparé) — body claim limite à trichotomy 4 theorems

## Doctrine appliquée

- **L143 SAFE cross-owner** : sweep purement structurelle (diff + sampling G.1 + Lean CI SUCCESS proxy + Mathlib lemmes standard + FR+EN byte-parity + cross-ref pre-existing theorems).
- **L268 anti-régression** : PR additive pure 2 fichiers +127/-0 = 7 new theorems sign-equivalence + 1 capstone (0 régression sur code pré-existant), fichier par fichier byte-identity préservée.
- **L275 anti-phantom** : `gh pr view 6024 --json state,mergeable,mergeStateStatus` firsthand.
- **L279 / #1502** : worker sweep_only consultatif, JAMAIS `gh pr merge`.
- **L298 anti-§D byte-identity Lean i18n** : siblings `_en.lean` byte-parity theorems préservés.
- **L327 additif strict** : +127/-0 additif pur, 0 hit `^-` sur contenu code existant.
- **L335 pivot R6 8ᵉ cycle** : c.346 §E SymbolicLearning + c.347 §E Image 03-Orchestration + c.348 §H.4 sweep axe-1 + c.349 PR substantive livraison GenAI + c.350 §E Audio 01-Foundation + c.351 §E Video 01-Foundation restructuration + c.352 §H.4 sweep C#-rest L3966-L1 + **c.353 §H.4 sweep axe-2 Lean Kelly QuantConnect #4052** = registre §H.4 sweep ≠ §E rollout (alternance), famille axe-2 Lean QuantConnect ≠ SymbolicLearning/Image/Audio/Video/C#-rest (cross-famille).

## ★ C353-L1 NEW — Capstone non documenté body PR

Body PR #6024 claim "+66 lines" et liste 4 theorems du trichotomy. **Mais** `git diff origin/main...pr-6024 --stat` révèle **+127 total** sur **3 commits** distincts :
1. `b4600a355` trichotomy (+66) — body documente
2. `711486841` fix `div_eq_zero_iff` (+2/-2) — body ne mentionne pas explicitement
3. `d2e07e107` capstone `kelly_growth_eq_zero_iff` (+61) — body ne documente PAS ce commit additionnel

**Pattern transférable** : sweep §H.4 doit lire TOUS les commits upstream via `git log pr-N` + hunk-by-hunk diff, pas seulement le body claim. Le body peut omettre des commits valides qui ajoutent de la substance distincte. Le capstone boucle la formalisation `g(f*) = 0 ↔ f* = 0` (étape réelle dans la roadmap EPIC #4052 Kelly criterion).

## Single-file clean §A archétype (L395 reaffirmed c.353, 4ᵉ cycle axe-2 Lean)

2 fichiers << 15 seuil strict §A = MERGEABLE single-file clean §A canonique FR+EN pair. Pattern c.394 + c.395 + c.396 + c.397 + c.400 + c.402 + c.353 sustained 7ᵉ cycle sur des PRs single-file clean différentes.

## Forward ai-01

- EPIC **#4052** Kelly criterion **progrès cumulatif** : c.402 #5987 (sign-positive, +61) + **c.353 #6024** (sign-trichotomy + capstone, +127) = **14 theorems sign-equivalence cumulés** dans Kelly.lean/Kelly_en.lean. Le cap opérationnel complet `sign(f*) = sign(edge) = sign(g'(0))` ET `g(f*) = 0 ↔ f* = 0` est **maintenant 100% formalisé**.
- PR #6024 = candidate pour batch-merge ai-01 (cf c.336-L2 ai-01 batch merge 8 PRs convergence EPIC).
- Capstone additionnel `kelly_growth_eq_zero_iff` = roadmap #4052 step 3 (après step 2 trichotomy c.353 + step 1 sign-positive c.402).

See #4052 (EPIC Kelly criterion umbrella).