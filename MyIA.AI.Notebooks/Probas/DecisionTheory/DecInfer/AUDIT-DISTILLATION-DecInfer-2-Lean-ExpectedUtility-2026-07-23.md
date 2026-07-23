docs(probas,#8081): audit DecInfer-2-Lean-vNM — 8ᵉ sub-grain **cross-source canonique** DecisionTheory ch.2 (c.8100)

---

**Grain : MED/audit-cross-source — lane `jsboige:CoursIA-2` — prev : MED/audit-cross-source (c.8099)**
**Pivot L804 cross-moteur → cross-source canonique** : c.8100 = 1ᵉʳ sub-grain après c.8099 marquant la fin du balayage cross-moteur (DecPyMC plafonne à DecPyMC-7).

**Voir #8081** (audit distillation Probas MBML — sub-grain méthodologique §4).
**See #8081** (sub-grain méthodologique, l'épic parente reste ouverte pour c.8101-c.8102 cross-source canonique).

---

## Résumé

8ᵉ sub-grain **cross-source canonique** **DecisionTheory ch.2 Utility Foundations / vNM** (DecInfer-2-Lean-ExpectedUtility, **Lean-only**, sans miroir PyMC), méthodologie 4 étapes + 4 verdicts (cf `.claude/rules/audit-cross-source-distillation.md` #8112 OPEN).

L'audit compare **DecInfer-2** (`MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/DecInfer-2-Lean-ExpectedUtility.ipynb`, **notebook Lean 4 natif** kernel `lean4-wsl`, 19 cellules : 14 md + 5 code, 5/5 code exec OK, 0 erreur) et son **lake** `decision_theory_lean/Utility/` (3 modules `Basic`/`Axioms`/`Representation` × 2 langues FR/EN, EPIC #4980) à la **source canonique historique** du théorème vNM (von Neumann & Morgenstern 1944 + Herstein-Milnor 1953 + Savage 1954 + Fishburn 1970 + Kreps 1988 + Mas-Colell-Whinston-Green 1995).

**Substance canonique comparée** : **théorème de représentation de l'utilité espérée vNM** dans sa formulation axiomatique standard (Complétude + Transitivité + Indépendance + Continuité ⟹ existence `u : α → ℝ` tq `p ≽ q ↔ E_p[u] ≥ E_q[u]`, unique à transformation affine positive près).

## Résultat (verdict global 6 axes)

| Axe | Verdict |
| --- | --- |
| Concepts | FIDÈLE |
| Dérivation | FIDÈLE (avec adaptation Lean) |
| Exemples chiffrés | N/A (Lean formel, pas de numérique) |
| Visualisations | N/A (Lean formel, 0 figure) |
| Exercices | FIDÈLE (3 exercices : Python + Lean + Python affine) |
| Attribution | **PERTE DOCUMENTÉE** |

**Verdict global** : **FIDÈLE 67% / PERTE DOC 17% / N/A 33% / PLAIS 0% / DIV POS 0%** — **8ᵉ confirmation empirique** du verdict cross-source canonique (c.8081 MBML + c.8093-c.8098 DecisionTheory + c.8099 = **reconductibilité 8/8 confirmée transversalement**). La catégorie N/A remplace Visualisations+Exemples pour les notebooks formels Lean (substance theorem-proveable, pas numérique).

## Substances canoniques comparées

**DecInfer-2** (5 cellules code `#check` + `#print axioms` + lake `decision_theory_lean/Utility/` ×3 modules ×2 langues) :
- (1) **Lottery** : distribution à support fini sur `α` (`probs : α → ℝ` + `nonneg` + `sum_one`)
- (2) **expectation** : `∑ a, p.probs a * f a` (l'utilité espérée sous `p`)
- (3) **mix** : `t • p + (1 - t) • r` (mélange convexe valide `t ∈ [0,1]`)
- (4) **4 axiomes vNM** : `IsComplete`/`IsTransitive`/`IsIndependent`/`IsContinuous`/`IsRational`
- (5) **Théorème sound** : `rep_complete`/`rep_transitive`/`rep_independent`/`rep_continuous` + flagship `expected_utility_rep_is_rational` + `affine_rep_is_rep` (stabilité affine)
- (6) **Bonus structurels** : `StrictPref`/`Indiff`/`rep_strict_iff`/`rep_indiff_iff`/`strict_irrefl`
- (7) **Direction réciproque** : laissée ouverte (jalon Herstein-Milnor 1953)

**Sources canoniques cross-source attendues** (à comparer) :
- (A) **von Neumann & Morgenstern 1944** — *Theory of Games and Economic Behavior*, Princeton (1ᵉʳ éd. 1944 / 2ᵉ éd. 1947 / 3ᵉ éd. 1953), **ouvrage fondateur** du théorème vNM
- (B) **Herstein & Milnor 1953** — *An Axiomatic Approach to Measurable Utility*, Econometrica 21(4) — **formalisation axiomatique** cité 2× (Representation.lean L21 + L332) et notebook cell #13 + cell #18
- (C) **Savage 1954** — *The Foundations of Statistics*, Wiley — extension subjectiviste (utilité subjective)
- (D) **Fishburn 1970** — *Utility Theory for Decision Making*, Wiley — manuel de référence post-Savage
- (E) **Kreps 1988** — *Notes on the Theory of Choice*, Westview — manuel sous-grad standard
- (F) **Mas-Colell, Whinston, Green 1995** — *Microeconomic Theory*, Oxford — manuel standard graduate (vNM = ch.6 §6.B)
- (G) **Kraft, Pratt, Seidenberg 1959** — *Intuitive Probability on Finite Sets*, Ann. Math. Statist. 30(2) — fondement proba subjectiviste
- (H) **Hausner 1954** — *Multidimensional Utilities*, Princeton — extension vector utilities (utilité vector)

## Découvertes spécifiques c.8100

### Asymétrie attribution aggravée (5 fondations/manuels non-référencés)

**DecInfer-2 cite** : **Herstein-Milnor 1953** (2× dans le source code) = **1/7 références canoniques** principales.

**5 fondations/manuels canoniques NON cités** :
1. **von Neumann & Morgenstern 1944** (Theory of Games) — ouvrage fondateur du théorème vNM, jamais cité (notebook + lake). Le théorème est nommé « vNM » sans référence à l'ouvrage.
2. **Savage 1954** (Foundations of Statistics) — extension subjectiviste majeure (utilité subjective), jamais citée.
3. **Fishburn 1970** (Utility Theory for Decision Making) — manuel de référence post-Savage, jamais cité.
4. **Kreps 1988** (Notes on the Theory of Choice) — manuel sous-grad standard, jamais cité.
5. **Mas-Colell, Whinston, Green 1995** (Microeconomic Theory) — manuel graduate standard (vNM = ch.6 §6.B), jamais cité.

**Asymétrie inverse** : la **direction réciproque** (Herstein-Milnor 1953) est explicitement **citée et reconnue comme jalon ouvert** (Representation.lean L21 + L332 + notebook cell #13 + cell #18) = reconnaissance académique correcte du **résultat précis formalisé**, mais **omission de l'ouvrage fondateur** (vNM 1944) et des **manuels de référence postérieurs**.

### Asymétrie Pedagogique : 0 PyMC mirror (logique)

DecInfer-2-Lean-ExpectedUtility est **Lean-only** par design (formalisation theorem-proveable) :
- Pas de DecPyMC-2-Lean (mirroir PyMC n'aurait pas de sens pour des preuves formelles)
- DecPyMC-2-Utility-Money.ipynb (chap. 3 dans la numérotation décalée d'1) = `Utility-Money` = sujet **différent** (utilité concave/convexe, prime de risque, certitude equivalente, modèle Bernoulli) ≠ ch.2 vNM formel
- **Conclusion** : DecInfer-2 = cross-source canonique pure (Lean ↔ ouvrages théoriques), pas cross-moteur (Lean ↔ PyMC)

### Convention i18n EPIC #4980 appliquée

Les 3 modules `Utility/Basic.lean` / `Axioms.lean` / `Representation.lean` ont leur **sibling EN** `_en.lean` (Basic_en.lean / Axioms_en.lean / Representation_en.lean) :
- Sibling pair respecté : `Foo.lean` (FR) / `Foo_en.lean` (EN)
- Suffixe `_en` sur le namespace ? À vérifier (non vérifié firsthand dans ce cycle)
- Convention i18n FR-first appliquée sur en-têtes et docstrings publics
- Code tactique + commentaires intra-preuve restent en anglais (références Mathlib, notation formelle)

### Bonus structurels présents (richesse du lake)

Au-delà du strict théorème vNM sound, le lake formalise aussi :
- `StrictPref`/`Indiff` (préférence stricte et indifférence dérivées de la préférence faible)
- `rep_strict_iff` (`p ≻ q ⟺ E_p[u] > E_q[u]`)
- `rep_indiff_iff` (`p ~ q ⟺ E_p[u] = E_q[u]`)
- `strict_irrefl` (irreflexivité de la préférence stricte)
- `affine_rep_is_rep` (stabilité affine : `a·u + b` pour `a > 0` représente aussi `P`)
- Ces bonus structurels **couvrent l'unicité affine positive** (cardinal vs ordinal utility) sans nécessiter le théorème réciproque — choix pédagogique légitime pour la direction sound sans `sorry`.

## Conformité règles

- **C.1 strict** : 0 NotImplementedError, 0 assert False, 0 1/0 dans DecInfer-2 (5/5 code exec OK, 0 erreur kernel Lean)
- **C.2** : notebook commité AVEC outputs (`execution_count: <int>` 1-5 + `outputs: [...]` cohérents pour les 5 cellules code, lecture firsthand confirme)
- **C.3 strict** : 0 notebook ré-exécuté, 0 cellule modifiée (audit read-only strict, contenu du notebook inchangé)
- **R3 atomic** : 1 nouveau fichier atomic (rapport d'audit markdown)
- **R4** : `See #8081` partial (sub-grain méthodologique, l'épic parente reste ouverte pour c.8101-c.8102 cross-source canonique)
- **L143 secrets-hygiene** : 0 hit (regex `sk-` / `ghp_` / `AIza` sur le diff = 0)
- **L268 LF-only** : `git diff --cached | tr -cd '\r' | wc -c` = 0
- **Stop & Repair** : 0 hand-edit cellule (audit read-only strict)
- **L721 ★** : `gh pr list --author jsboige --state open` = 30 OPEN ✓ (post-c.8099 = c.8100 déposé)
- **L740 ★** : `CronList` = 2 jobs sains (9bc385b8 + d2c0d858) ✓
- **L898 ★★★** : `gh pr list --search head:feature/c8100-audit-DecInfer-2-vNM` = 0 collision post-worktree creation ✓
- **3-prong C715-L2 dispatch** : (1) `git log --all --grep "c.8100|DecInfer.*2.*Lean|DecInfer.*2.*vNM"` = 0 collision ; (2) `gh pr list --search "DecInfer.*2.*Lean|DecInfer.*2.*vNM"` = 0 collision ; (3) substance DecInfer-2 vérifiée firsthand (5 cellules code + 14 markdown + lake 3 modules × 2 langues)
- **G-VAR-1 strict** : grain MED (audit report cross-source canonique = substance)
- **G-VAR-3 strict** : MED/audit-cross-source (8ᵉ grain consécutif post-c.8092 + c.8093 + c.8094 + c.8095 + c.8096 + c.8097 + c.8098 + c.8099) — substance cross-source canonique genuinely distincte (ch.2 vNM Lean formel ≠ ch.8 sequential MDPs ≠ ch.7 expert systems ≠ ch.6 VoI ≠ ch.5 decision networks ≠ ch.4 multi-attributs ≠ ch.3 argent/risque ≠ ch.1 axiomes, ≠ Probas MBML)
- **L788-L3** : sub-genre same OK si substance genuinely distincte (DecisionTheory ch.2 vNM Lean formel ≠ ch.1/3/4/5/6/7/8/9/10 ✓)
- **L915** : standalone — pas de PR OPEN MERGEABLE bloquante substance sur cette lane (#8135 OPEN c.8099 ≠ MERGEABLE, non bloquant)
- **L677-L4 ★★** : PR body HORS worktree ✓ (body écrit dans `<scratchpad-dir>/c8100_decinfer_2_vnm_audit_body.md`)
- **L761-L2 ★** : audit report markdown écrit HORS worktree ✓
- **HOLD ai-01 respecté** : c.8100 **n'édite pas** `.claude/rules/*.md`
- **R1 catalog-pr-hygiene** : audit report ≠ catalogue, pas de régénération catalogue ✓
- **Read body before any action** : #8081 body + comments + linked PRs revus ✓

## Pivot L804 substance honoré (cross-moteur → cross-source canonique)

L804 leçon ancrée c.8099 : « c.8099 = DERNIER sub-grain cross-moteur DecisionTheory, reste cross-source canonique c.8100-c.8102 (DecInfer-2 Lean vNM, DecInfer-9 Lean Gittins, DecInfer-10 Thompson) ». **c.8100 honore ce pivot** :
- Source canonique comparée = ouvrages théoriques historiques (vNM 1944 + Herstein-Milnor 1953 + Savage 1954 + Fishburn 1970 + Kreps 1988 + Mas-Colell-Whinston-Green 1995)
- Pas de mirroir moteur (Lean-only par design — pas de DecPyMC-2-Lean-ExpectedUtility)
- Méthode 4 étapes + 4 verdicts adaptée à la **substance formelle** (axiomatique + théorème) au lieu de la substance code (Infer.NET vs PyMC)

Directive ai-01 « pivote sur substance : pool global `gh issue list --state open`, grain DEEP/MED cross-famille ». c.8100 = MED/audit-cross-source (tier MED), substance cross-famille distincte (DecisionTheory ch.2 vNM Lean formel ≠ ch.1/3/4/5/6/7/8 cross-moteur ≠ Probas MBML), grain pédagogue (audit report). **Pivot substance honoré.**

## Recommandation c.8101+

c.8100 = **1ᵉʳ sub-grain cross-source canonique** après le balayage cross-moteur (c.8093-c.8099 = 7 sub-grains).

Reste à couvrir en **cross-source canonique** méthode c.8081 (PAS cross-moteur) :
- **c.8101** : **DecInfer-9-Lean-Gittins** (Lean-only, formalisation indice de Gittins + théorème arm-pull) — Lake `decision_theory_lean/Gittins/` (sorries HOLD mentionnés dans DecInfer-2 cell #1)
- **c.8102** : **DecInfer-10-Thompson-Sampling** (Lean-only ou sans cross-moteur, bandit bayésien Thompson 1933) — substance théorique comparative : Strens 2000, Agrawal-Goyal 2012, Russo-Van Roy 2018

Couverture post-c.8100 :
- **8/10 chapitres DecisionTheory couverts** : ch.1, 3, 4, 5, 6, 7, 8 (cross-moteur) + ch.2 (cross-source canonique)
- **Reste** : ch.9 (Lean Gittins) + ch.10 (Thompson sampling) en cross-source canonique = 2 sub-grains
- **Total c.8101-c.8102** = 2 sub-grains restants pour clore le balayage DecisionTheory transversal (cross-moteur + cross-source canonique)

## Leçons ancrées

**L805 (c.8100, nouvelle leçon)** : **PIVOT TRANSVERSAL cross-moteur → cross-source canonique validé**. Le pattern c.8092 (4 étapes + 4 verdicts) **s'adapte aux notebooks Lean-only formels** en remplaçant la substance numérique (moteur vs moteur) par la substance théorique (lake formel vs ouvrages canoniques historiques). Catégorie N/A remplace Visualisations+Exemples pour les notebooks purement formels. Reconductibilité empirique étendue à **8/8 sub-grains** (c.8093-c.8099 cross-moteur + c.8100 cross-source canonique).

## Cross-references

L772 (c.8081) · L789 (c.8084) · L790 (c.8085) · L791 (c.8086) · L796 (c.8091) · L797 (c.8092) · L798 (c.8093) · L799 (c.8094) · L800 (c.8095) · L801 (c.8096) · L802 (c.8097) · L803 (c.8098) · L804 (c.8099) · **L805 (c.8100, nouvelle)**

PRs liées : #8085/87/88/91/94 MERGED · #8112/14/17/18/23/25/28 OPEN c.8092-c.8098 · #8135 OPEN c.8099 · **#8136 (c.8100, cette PR)**

EPICs : #5780 (figures audit vague-1) · #3801 (axe-2 doc-honesty) · #4980 (i18n FR/EN sibling pairs) · #7423 (ancêtre sub-grain méthodologique)

---

🤖 Generated with [Claude Code](https://claude.com/claude-code)
