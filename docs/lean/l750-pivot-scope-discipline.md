# L750 ★★ — Pivot Lean specialist, discipline de scope, remédiation OOM

Détail durable de [`.claude/rules/lean-merge-discipline.md`](../../.claude/rules/lean-merge-discipline.md) §L750 (harness-hygiene tier 2).

**Source** : c.750, PR **#7895** MERGED `feat(lean,#2159)`. Pivot verbatim ai-01 (`msg-20260722T050055-i12hh3`) qui avait greenlité `Folk.lean` Tactic-1 — refuté firsthand (STRETCH polytope dur, Fudenberg-Maskin) → pivot vers Grothendieck `pullback_union` DEEP, **même lake**, rebase propre entre grains.

## Règle 1 — Vérifier le scope STRETCH avant tout `sorry` (anti-claim-discharge)

Avant tout cycle sur un `sorry` d'un lake à doctrine STRETCH (exemple : `Folk.lean` / issue #4880 exige `0-sorry` **uniquement** sur `grim_trigger_sustains_iff`, **pas** sur `folk_theorem_discounted` / `folk_theorem_boundary`) :

```bash
grep -nE "theorem.*:=|:=|sorry" MyIA.AI.Notebooks/<lake>/<file>.lean | head -50
# corps = "True := by sorry" sur un théorème marqué STRETCH dans l'issue parent
#   → le grain Tactic-1 n'existe pas : STOP + pivot
```

**Anti-pattern** : commencer un cycle Tactic-1 sur un `sorry` STRETCH en présumant « trivial ». STOP + report + pivot dans la même seconde (greenlight ai-01 verbatim = pré-requis du pivot).

## Règle 2 — Un pivot verbatim ai-01 est un grain canonique pour casser G-VAR-3

**Tell** : un pivot ai-01 pré-emptif verbatim (dashboard ou inbox) constitue un grain canonique **si** les trois conditions sont réunies :

1. **Sous-domaine voisin** — même lake ou famille compatible (rebase propre entre grains, pas de rebase sale cross-lake) ;
2. **Substance genuinement distincte** — preuves / théorèmes différents, pas des variantes scan-générées ;
3. **Dead-end source documenté** — verdict G.1 firsthand (« Folk STRETCH polytope dur, Fudenberg-Maskin »), jamais « je n'ai pas trouvé ».

**Pattern appliqué c.750** : `Folk.lean` → `grothendieck_lean pullback_union`, même écosystème Lean, donc rebase propre et zéro churn cross-lake.

## Règle 3 — WSL Ubuntu, remédiation OOM Mathlib (L743 ★★, HARD infra)

**Symptôme** : `INTERNAL PANIC: out of memory` vers ~95 % du progrès Mathlib sur runner Windows (cap 8 GB RAM, conflit du GC .NET avec le RSS de `lake`, OOM-killer). **Ce n'est pas un verdict Lean, c'est de l'infra récurrente** — 4 occurrences consolidées : c.672 / c.733 / c.743 / c.750.

```bash
# Écrire le script via heredoc WSL (PAS de quoting cmd.exe, qui corrompt $PATH)
wsl -d Ubuntu bash -c "cat > /tmp/wsl_build.sh <<'EOF'
export PATH=~/.elan/bin:\$PATH
cd /mnt/c/dev/<worktree>/MyIA.AI.Notebooks/SymbolicAI/Lean/<lake>
lake build <Module> 2>&1 | tail -30
EOF
chmod +x /tmp/wsl_build.sh && bash /tmp/wsl_build.sh"
```

Sortie attendue : `Build completed successfully (N jobs)` — propre, sans warning.

**Anti-pattern** : retenter le build Windows une 5ᵉ fois en croisant les doigts. Migrer sur WSL dès la **1ʳᵉ** occurrence L743. Un build WSL frais coûte ~30 min mais réussit ; un `.lake` Windows OOM-killé produit 0 olean et n'est pas réutilisable.

## Règle 4 — Scope #2159 Phase 2 : trois cibles, une par PR

| Cible | Statut | Source |
|---|---|---|
| `pullback_pullback` (composée contravariante) | déjà présent (`SieveLattice.lean:67`) | pré-existant |
| **`pullback_union`** | **DONE** (c.750, PR #7895) | cette PR |
| `pullback_imap` (sous transformations naturelles) | DEFER (hors scope Phase 2) | post-Phase-2 |

**Convention** : `See #2159` en partiel (**pas** `Closes #2159`, puisque 1 cible sur 3 est adressée et que `pullback_imap` est un DEFER explicite). `Closes #N` est réservé au cas où la PR résout **entièrement** l'issue.

## Règle 5 — `pullback_union` : le pattern de preuve (dual Mathlib Sites/Sieves)

```lean
theorem pullback_union {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X) (S R : Sieve X) :
    Sieve.pullback f (S ⊔ R) = Sieve.pullback f S ⊔ Sieve.pullback f R := by
  ext Z g
  simp [Sieve.pullback]
```

**Pourquoi** : `Mathlib/CategoryTheory/Sites/Sieves.lean` fournit `pullback_inter` (ligne 835) mais **pas** son dual `pullback_union`. La dualité de treillis des cribles (`⊔` dual de `⊓`) reste incomplète tant que cette identité manque. `simp [Sieve.pullback]` déplie les deux définitions, et le simp-set décharge automatiquement le `∨`.

**Note de calibration** : ajouter `Sieve.union` comme argument de `simp` est **inutile** (warning linter `unusedSimpArgs`) — `simp [Sieve.pullback]` suffit, la définition étant inlinée. Tag CALIBRATION = `ext + simp`, **pas** `ext + simp + Sieve.union`.

## Pourquoi L750 est cotée ★★ et non ★★★

Les cinq règles sont opérationnelles et vérifiables, mais chaque incident fondateur reste **recoverable** isolément : STRETCH polytope dur = pivot immédiat (coût 1 cycle) · OOM Windows = remédiation WSL (coût ~30 min) · scope 1/3 = convention R4 (coût nul). Les leçons `★★★` (L898 collision cross-lane, L721 stale tracker) coûtent des **heures** de travail perdu.

## Voir aussi

- [`.claude/rules/lean-merge-discipline.md`](../../.claude/rules/lean-merge-discipline.md) — la règle
- [`docs/lean/coordinator-workflow.md`](coordinator-workflow.md) — build local, cache get, mapping DEMO_ID, interprétation forensique
- [`docs/lean/l902_tactic_pitfalls.md`](l902_tactic_pitfalls.md) — pièges `rfl` / `rw` / `subst` sur constructeurs polymorphes d'univers
- [`.claude/rules/variation-protocol.md`](../../.claude/rules/variation-protocol.md) — G-VAR-3, adjacence de genre (règle 2 ci-dessus)
