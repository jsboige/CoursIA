---
paths: "{**/*.lean,**/Lean/**/*,**/lean/**/*,**/social_choice_lean/**/*}"
---

# Lean PR discipline — Lake build local + BG iter post-po-2026

S'applique a **toute PR touchant `*.lean`** + au **coordinateur ai-01** pour BG iter prover.

## 1. Lake build SUCCESS local OBLIGATOIRE avant merge (HARD)

Avant CHAQUE merge Lean : `lake build <module>` LOCAL par ai-01. Le claim "lake build SUCCESS Xs" dans le body PR n'est **PAS suffisant** (trust mais verifie). Pas d'env Lean local : dispatcher po-2026 avec build log complet + `grep -c sorry` avant/apres + diff sur defs partagees.

**CI != Lake build local** : `lean-social-choice.yml` ne build PAS Voting.lean. CI SUCCESS != module compile.

**Incident source** : 2026-05-10 merge #866 sur claim non-verifie → revert #885, 1 cycle perdu.

## 2. Prover BG systematique post-PR/msg po-2026 (HARD)

Apres **chaque PR** ou **message dashboard/inbox** de `myia-po-2026:*` mentionnant un sorry Lean CoursIA, **lancer SYSTEMATIQUEMENT** un BG iter prover depuis ai-01 sur le meme sorry/file.

**Anti-pattern interdit** : "Le BG a deja FAILED hier, pas la peine de relancer". Le contexte change a chaque iteration manual po-2026. Meme si re-echec : donnee diagnostic precieuse.

**Verification fin de cycle** : avant `[DONE]` dashboard, repondre "Est-ce qu'il y a eu un PR ou msg po-2026 ce cycle ? Si oui, BG iter a-t-il ete lance ?". Pas de DONE sans cet item adresse.

**Source** : User 2026-05-16 ~13:55Z mandate explicite.

## L750 ★★ Leçons ancrées — Pivot Lean specialist + scope discipline

**Leçons ancrées** — L750 ★★ (c.750, PR #7895 MERGED feat(lean,#2159) ; détail en mémoire locale per-machine) : 5 règles opérationnelles pour pivot/scope Lean specialist. Source : pivot verbatim ai-01 (msg-20260722T050055-i12hh3) qui a greenlit Folk.lean Tactic-1 (refuted firsthand, STRETCH polytope dure Fudenberg-Maskin) → Grothendieck `pullback_union` DEEP, même lake, rebase propre entre grains.

### Règle 1 — Vérifier scope STRETCH avant tout sorry (anti-claim discharge)

**Avant tout cycle sur un sorry d'un lake avec STRETCH doctrine** (Folk.lean/Issue #4880 = `0-sorry` exigé QUE sur `grim_trigger_sustains_iff`, PAS sur `folk_theorem_discounted`/`folk_theorem_boundary`) :

```bash
# Vérif mécanique scope STRETCH — pattern canonique
grep -nE "theorem.*:=|:=|sorry" MyIA.AI.Notebooks/<lake>/<file>.lean | head -50
# Si corps = "True := by sorry" sur théorème marqué STRETCH dans issue parent : grain Tactic-1 inexistant, STOP+pivot
```

**Anti-pattern** : commencer un cycle Tactic-1 sur sorry STRETCH en présumant « trivial ». STOP+report + pivot dans la même seconde (ai-01 verbatim greenlight = pré-requis).

### Règle 2 — Pivot verbatim ai-01 = grain canonique pour G-VAR-3 break

**Tell** : un pivot ai-01 pré-emptif verbatim (dashboard/inbox) = grain canonique **SI** les 3 conditions sont réunies :
1. **Sous-domaine voisin** : même lake ou famille compatible (rebase propre entre grains, pas de rebase sale cross-lake)
2. **Substance genuinely distincte** : preuves/théorèmes différents, pas variantes scan-générées
3. **Dead-end source documenté** : verdict G.1 firsthand (ex. « Folk STRETCH polytope dure Fudenberg-Maskin »), pas « j'ai pas trouvé »

**Pattern appliqué c.750** : pivot `Folk.lean` → `grothendieck_lean pullback_union` dans même écosystème Lean = rebase propre, pas de churn cross-lake.

### Règle 3 — WSL Ubuntu = L743 ★★ Mathlib OOM remediation (HARD infra)

**Symptôme** : `INTERNAL PANIC: out of memory` à ~95% Mathlib progress sur Windows runner (8GB RAM cap, .NET GC conflict avec lake RSS, OOM-killer). **NOT a Lean verdict, recurring infra** — c.672/c.733/c.743/c.750 = 4 occurrences consolidées.

**Remediation WSL Ubuntu** :
```bash
# Écrire script via WSL heredoc (PAS cmd.exe quoting, ça corrompt $PATH)
wsl -d Ubuntu bash -c "cat > /tmp/wsl_build.sh <<'EOF'
export PATH=~/.elan/bin:\$PATH
cd /mnt/c/dev/<worktree>/MyIA.AI.Notebooks/SymbolicAI/Lean/<lake>
lake build <Module> 2>&1 | tail -30
EOF
chmod +x /tmp/wsl_build.sh && bash /tmp/wsl_build.sh"
```

**Build output attendu** : `Build completed successfully (N jobs)` — clean, no warnings.

**Anti-pattern** : tenter le build Windows une 5ᵉ fois en croisant les doigts. Migrer WSL dès la **1ère** occurrence L743. Fresh WSL build = ~30 min mais SUCCESS garanti ; .lake Windows OOM-killé = 0 olean, non-réutilisable.

### Règle 4 — Scope #2159 Phase 2 : 3 cibles, 1/3 par PR

| Cible | Statut | Source |
|-------|--------|--------|
| `pullback_pullback` (composée contravariante) | ✓ DÉJÀ PRÉSENT (`SieveLattice.lean:67`) | pré-existant |
| **`pullback_union`** | **✓ DONE (c.750 PR #7895)** | **cette PR** |
| `pullback_imap` (sous transformations naturelles) | DEFER (hors scope Phase 2) | post-Phase-2 |

**Convention** : `See #2159` partial (PAS `Closes #2159` car 1/3 cibles adressées ; `pullback_imap` est explicite DEFER). R4 = `Closes #N` seulement si PR résout entièrement l'issue.

### Règle 5 — `pullback_union` proof pattern (Mathlib Sites/Sieves dual)

**Pattern canonique 6 lignes** :
```lean
theorem pullback_union {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X) (S R : Sieve X) :
    Sieve.pullback f (S ⊔ R) = Sieve.pullback f S ⊔ Sieve.pullback f R := by
  ext Z g
  simp [Sieve.pullback]
```

**Why** : `Mathlib/CategoryTheory/Sites/Sieves.lean` fournit `pullback_inter` (line 835) mais PAS son dual `pullback_union`. La dualité treillis des cribles (`⊔` dual `⊓`) est incomplète tant que cette identité manque. `simp [Sieve.pullback]` unfold les deux définitions + simprobiscium auto-discharge le `∨`.

**Note** : ajouter `Sieve.union` comme simp arg est **inutile** (linter warning `unusedSimpArgs`) — `simp [Sieve.pullback]` suffit car la définition est inlined. Documenter le CALIBRATION tag = `ext + simp` (PAS `ext + simp + Sieve.union`).

### Pourquoi L750 ★★ et pas ★★★

La leçon est opérationnelle (5 règles distinctes avec pointeurs concrets vérifiables) mais les incidents fondateurs (STRETCH polytope dure, OOM Windows, 3/3 scope convention) restent **recoverable** individuellement :
- STRETCH polytope = pivot immédiat (coût 1 cycle)
- OOM Windows = WSL remediation (coût ~30 min)
- Scope 1/3 = convention R4 (coût 0)

Les `★★★` (L898 collision cross-lane, L721 stale tracker) coûtent des **heures** de travail perdu. L750 ★★ = pivot propre documenté + recovery infra connue.

**Voir aussi** : [proactive-coordination.md](proactive-coordination.md) section "Leçons ancrées (c.8087 L-coupling)" — L721★/L740★/L898★★★ ancrés par c.8088 (PR #8101) ; [git-workflow.md](git-workflow.md) section "PR Body Generation" — L677-L4 ★★ ancré par c.8089 (PR #8104). Sub-grain même audit L-coupling c.8087 #8099, target rule distincte (L788-L3 diversification authentique : Lean discipline ≠ audit methodology ≠ proactive coordination ≠ git workflow).

## Detail workflow

- Build local + cache get + DEMO_ID mapping + forensic interpretation + capture postmortem : [docs/lean/coordinator-workflow.md](../../docs/lean/coordinator-workflow.md)
- LLM endpoints providers : [docs/lean/llm-endpoints.md](../../docs/lean/llm-endpoints.md)
- Iterations F6-F11, B3 : [docs/lean/prover_iteration_history.md](../../docs/lean/prover_iteration_history.md)

## Voir aussi

- [anti-regression.md](anti-regression.md) — `grep -c sorry` avant/apres, pas de regression preuves
- [pr-review-discipline.md](pr-review-discipline.md) — Section B (4 elements Lean PR body)
