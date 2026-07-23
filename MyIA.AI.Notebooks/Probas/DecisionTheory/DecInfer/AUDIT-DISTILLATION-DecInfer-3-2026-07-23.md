# Audit distillation DecInfer-3 vs DecPyMC-2 + sources canoniques (chapitre 3 : utilité de l'argent et aversion au risque)

**Date** : 2026-07-23
**Cycle** : c.8094 (sub-grain #8081 §4 cross-famille post-c.8093 cross-famille DecisionTheory)
**Méthode** : c.8092 rule `.claude/rules/audit-cross-source-distillation.md` — 4 étapes + 4 verdicts (FIDÈLE / PERTE DOCUMENTÉE / PERTE PAR COMPLAISANCE / DIVERGENCE POSITIVE)
**Pilote fondateur** : `DecInfer-3-Utility-Money.ipynb` (chapitre 3 = utilité de l'argent, post-vNM = extension risque/argent du cadrage ch.1)

---

## Étape 1 — Identifier la source canonique

| Question | Source identifiée |
|----------|-------------------|
| Quelle famille ? | `MyIA.AI.Notebooks/Probas/DecisionTheory/` |
| Quelle source canonique théorique ? | **Pas de MBML direct** — DecisionTheory ch.3 = prolongement risque/argent du cadrage vNM 1944 (ch.1 acquis) + **théorie risque** **Pratt 1964** (Arrow-Pratt coefficients) + **Arrow 1965** (Aversion au Risque) + **Bernoulli 1738** (résolution paradoxe St-Pétersbourg via utilité logarithmique) |
| Quel notebook DecInfer audité ? | `DecInfer-3-Utility-Money.ipynb` |
| Quel notebook miroir DecPyMC ? | `DecPyMC-2-Utility-Money.ipynb` (miroir 1:1 sur le sujet — note : numérotation PyMC décalée d'1 par rapport à DecInfer) |
| Linéage ? | README DecInfer ligne 76 confirme DecPyMC-2 = source de la figure reprise DecInfer-3 (mêmes worked examples Bernoulli 1738 / CARA / CRRA / Arrow-Pratt) |

**Note méthodologique** (répétée depuis c.8093 pour clarté) : unlike c.8081/84/85/86 (source canonique MBML chapters 3/1/2/7), DecInfer-3 n'a **pas** de source canonique tierce unique mais **un double-moteur interne** (DecInfer C# .NET vs DecPyMC Python) + un cadrage théorique classique post-vNM (Pratt 1964 + Arrow 1965 + Bernoulli 1738). L'audit adapte la méthode 4 étapes + 4 verdicts à ce contexte : les 2 moteurs sont les 2 "sources" comparées, et la cohérence avec le cadrage Pratt/Arrow/Bernoulli est l'ancrage théorique canonique.

**Cadrage acquis ch.1** : vNM 1944 + Von Neumann + Morgenstern (fondements axiomatiques ch.1) + représentation expected utility. **Cadrage spécifique ch.3** : Bernoulli 1738 (résolution paradoxe St-Pétersbourg) + CARA/CRRA (classes paramétriques de fonctions d'utilité) + Arrow-Pratt (coefficients ARA/RRA).

## Étape 2 — Lire les sources firsthand

### DecInfer-3 (50 cellules)
- **28 markdown** + **22 code** ; 22/22 code executed OK ; 0 `raise NotImplementedError` ✓ C.1 strict
- **3 exercices** (cells 21 dominance stochastique FSD/SSD, 46 profil de risque personnel, 48 application investissement) ✓ conforme `three-exercises-per-notebook.md`
- **3 exemples guides résolus** : cell 6 (St-Pétersbourg Monte Carlo `var rng = new Random(42); int N = 100000;` → équivalent certain ~4 EUR), cell 18 (Arrow-Pratt comparaison CARA vs CRRA sur 4 niveaux de richesse), cell 37 (profil de risque personnel — méthodologie d'elicitation)
- **1 visualisation factor graph** via `FactorGraphHelper.cs` cell 42 (factor graph inférence bayésienne §9)
- **9 sections principales** : §1 Paradoxe St-Pétersbourg · §2 Utilité marginale · §3 CARA/CRRA · §4 Coefficients Arrow-Pratt · §5 Equivalent Certain · §6 Dominance Stochastique · §7 Application Investissement · §8 Profil de Risque · §9 **Inférence Bayésienne Infer.NET**
- **Citations canoniques** : Pratt 6 / Arrow 6 / Bernoulli 7 / CARA 15 / CRRA 20 / Saint-Pétersbourg 3 (0 vNM/Von Neumann/Morgenstern — ch.3 = post-vNM = utilité risque, **référencement ch.1 implicite**)

### DecPyMC-2 (64 cellules)
- **36 markdown** + **28 code** ; 28/28 code executed OK ; 0 `raise NotImplementedError` ✓
- **3+ exercices** (cells 17 dominance stochastique FSD/SSD, 27 calibration CRRA, 62 profil de risque bayésien) ✓ conforme
- **Exemples guides résolus** : cell 7 (St-Pétersbourg Monte Carlo `np.random.seed(42); N = 100000` → CE ~4 EUR), cell 19 (Arrow-Pratt visualisation 2D), cell 37 (modèle Beta-Bernoulli conjugué classique)
- **21 PNG visualizations** (matplotlib + arviz traces) — bien plus riche visuellement que DecInfer-3
- **11 sections principales + §9bis bonus unique PyMC** : §1 St-Pétersbourg · §2 Utilité marginale · §3 CARA/CRRA · §4 Arrow-Pratt · §5 Equivalent Certain · §6 Dominance Stochastique · §7 Application · §8 Profil de Risque · §9 Inférence Bayésienne **modèle joint rho+kappa** · §9bis **Analyse paramétrique 2D** (heatmap rho vs kappa — bonus unique PyMC)
- **Citations canoniques** : Pratt **10** / Arrow **10** / Bernoulli 7 / CARA 12 / CRRA 19 / Saint-Pétersbourg **6** / Von Neumann 1 / Morgenstern 2 / MCMC 2 / PyMC **18** — **plus disert en attribution théorique** que DecInfer-3
- **Inférence bayésienne §9** : `pm.Beta("theta", alpha=2, beta=2)` + `pm.TruncatedNormal("rho", mu=2.5, sigma=1.0, lower=1.1, upper=6.0)` + `pm.HalfNormal(sigma=5.0)` + `pm.sample(draws=2000, ...)` + `pm.sample_posterior_predictive(...)` PPC — **modèle joint rho+kappa + posterior predictive check** (beaucoup plus sophistiqué que DecInfer-3 single-parameter Beta-Bernoulli)

## Étape 3 — Comparer axe par axe

| Axe | DecInfer-3 | DecPyMC-2 | Verdict |
|-----|------------|-----------|---------|
| **Concepts** | §1-9 toutes présentes symétriquement (St-Pétersbourg, utilité marginale, CARA, CRRA, Arrow-Pratt, équivalent certain, dominance stochastique FSD/SSD, application, profil de risque, inférence bayésienne) | Mêmes §1-9 + §9bis bonus unique analyse paramétrique 2D | **FIDÈLE** (couverture thématique complète, bonus PyMC légitime) |
| **Dérivation** | Coefficients Arrow-Pratt ARA/RRA dérivés formellement (cell 17 markdown + cell 18 code), dominance FSD/SSD expliquée (CDF comparison), inférence bayésienne Beta-Bernoulli conjugué formule prior→posterior explicitée cell 41 | Idem + dérivation modèle joint rho+kappa (prior informatif TruncatedNormal + PPC), analyse paramétrique 2D heatmap | **FIDÈLE** (cohérence dérivation, DecPyMC-2 ajoute sophistication bayésienne justifiée) |
| **Exemples chiffrés** | Cell 6 : St-Pétersbourg MC 100k samples → CE ~4 EUR ; cell 18 : CARA/CRRA comparaison numérique sur 4 niveaux de richesse (100/1000/10000/100000 EUR) ; cell 37 : profil de risque personnel méthodologie ; cell 40 : inférence bayésienne 3/10 choix → posterior Beta(5,9) | Cell 7 : St-Pétersbourg MC 100k samples → CE ~4 EUR ; cell 19 : Arrow-Pratt visualisation 2D ; cell 37 : Beta-Bernoulli conjugué modèle sample ; cell 51 : modèle joint rho+kappa inference posterior ; cell 54 : PPC validation | **FIDÈLE** (mêmes exemples canoniques résolus dans les 2 notebooks, DecPyMC-2 ajoute PPC bonus) |
| **Visualisations** | 1 factor graph .NET-specific via `FactorGraphHelper.cs` cell 42 (bonus .NET-specific) + tables ASCII comparaison Arrow-Pratt | 21 PNG outputs (matplotlib heatmaps 2D, arviz MCMC traces, posterior predictive plots) + comparaison Arrow-Pratt tabulaire | **DIVERGENCE POSITIVE** — chaque moteur exploite ses forces natives (factor graph .NET pour DecInfer-3, tracé PyMC + heatmap pour DecPyMC-2) |
| **Exercices** | 3 stubs `// TODO 1/2/3/4` cohérents : cell 21 dominance stochastique (FSD/SSD), cell 46 profil de risque personnel, cell 48 application investissement — chacun précédé d'un exemple guidé résolu | 3+ stubs `# TODO etudiant` : cell 17 dominance stochastique, cell 27 calibration CRRA, cell 62 profil de risque bayésien — chacun précédé d'un exemple guidé | **FIDÈLE** |
| **Attribution** | vNM/Von Neumann/Morgenstern **0** (ch.3 post-vNM, **référencement ch.1 implicite** mais non explicité) ; Pratt 6 / Arrow 6 / Bernoulli 7 (équivalent DecPyMC-2 sur Bernoulli) — **référencement théorique modéré** | vNM 1 / Von Neumann 1 / Morgenstern 2 (rappel ch.1 explicite) ; Pratt **10** / Arrow **10** / Bernoulli 7 (équivalent) / **Saint-Pétersbourg 6** (équivalent) / **MCMC 2** / **PyMC 18** — **référencement théorique ~2x plus riche** | **PERTE DOCUMENTÉE** — asymétrie d'attribution **significative** entre les 2 moteurs ch.3 : (a) DecInfer-3 ne référence **pas du tout** ch.1 vNM/Morgenstern explicitement (logique post-vNM mais **transition non explicitée**) ; (b) DecPyMC-2 plus disert sur fondements théoriques (~2x citations Pratt/Arrow, +Von Neumann, +Morgenstern). Différence non explicitée ni justifiée dans aucun des 2 notebooks |

## Étape 4 — Verdict par axe + verdict global

| Verdict | Axe |
|---------|-----|
| **FIDÈLE** | Concepts · Dérivation · Exemples chiffrés · Exercices |
| **PERTE DOCUMENTÉE** | Attribution (asymétrie DecInfer-3 vs DecPyMC-2 non explicitée — référencement ch.1 implicite côté DecInfer-3 + 2x plus de citations Pratt/Arrow côté DecPyMC-2) |
| **PERTE PAR COMPLAISANCE** | (0 trouvé) |
| **DIVERGENCE POSITIVE** | Visualisations (factor graph .NET-specific DecInfer-3 cell 42 + 21 PNG DecPyMC-2 — chaque moteur exploite ses forces natives) |

### Verdict global (synthèse)

**FIDÈLE 67% / PERTE DOCUMENTÉE 17% / PERTE PAR COMPLAISANCE 0% / DIVERGENCE POSITIVE 17%**

Calcul sur 6 axes pondérés également : FIDÈLE 4/6 + PERTE DOC 1/6 + PLAIS 0/6 + DIV POS 1/6.

**Note** : verdicts globaux **identiques** à c.8093 (FIDÈLE 67% / PERTE DOC 17% / PLAIS 0% / DIV POS 17%) — confirmation empirique que la méthodologie 4 étapes + 4 verdicts produit des verdicts **reconductibles** cross-chapitres (ch.1 et ch.3 DecisionTheory). La **substance** diffère (ch.3 = argent/risque/Bernoulli/Pratt/Arrow, ch.1 = utilité/vNM/Morgenstern), mais le **pattern** d'asymétrie attribution est identique (DecPyMC plus disert sur fondements théoriques).

## Reconductibilité cross-famille confirmée (deuxième application cross-chapitre)

Le pattern de c.8092 fonctionne **et est confirmé** sur c.8094. Différences méthodologiques mineures par rapport à c.8093 :
- **c.8093 (ch.1 Utility Foundations)** : substance = vNM/Morgenstern axioms + Bernoulli/CARA/CRRA intro
- **c.8094 (ch.3 Utility Money)** : substance = Bernoulli 1738 résolution St-Pétersbourg + Arrow-Pratt coefficients + inférence bayésienne du profil de risque (acquis ch.1 implicite)
- **Asymétrie attribution confirmée** sur les 2 chapitres (DecPyMC ~2x plus disert sur fondements théoriques)

**Recommandation pour c.8095+** : appliquer la même adaptation aux DecInfer-X restants :
- c.8095 : DecInfer-2 Lean vNM (mais Lean-only sans miroir PyMC → audit cross-source canonique, pas cross-moteur)
- c.8096 : DecInfer-4 Bayesian Decision Theory (à investiguer — possible miroir PyMC)
- c.8097 : DecInfer-9 Lean Gittins (Lean-only sans miroir PyMC)
- c.8098 : DecInfer-10 Thompson Sampling (à investiguer)

## Pourquoi c.8094 maintenant (post-c.8093, post-HOLD ai-01 FREEZE addendum pivot)

1. **Périmètre post-HOLD respecté** : c.8094 crée un **rapport d'audit** dans `MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/AUDIT-DISTILLATION-DecInfer-3-2026-07-23.md` (analogue aux c.8085/88/91/94 et c.8093) — **n'édite pas** `.claude/rules/*.md`. Le pattern HOLD ai-01 sur les éditions `.claude/rules/*.md` (sign-off user requis) ne s'applique pas aux rapports d'audit.

2. **Pivot substance ai-01 FREEZE addendum honoré** : directive ai-01 « pivote sur substance : pool global `gh issue list --state open`, grain DEEP/MED cross-famille ». c.8094 = MED/audit-cross-source (tier MED), substance cross-famille distincte (DecisionTheory ch.3 ≠ ch.1, ≠ Probas MBML), grain pédagogue (audit report). Conforme.

3. **Recommandation L798 (c.8093) honorée** : la leçon c.8093 dit explicitement « Recommandation c.8094+ : appliquer même adaptation aux DecInfer-X restants (DecInfer-2 Lean vNM, **DecInfer-3 argent**, DecInfer-9 Lean Gittins, DecInfer-10 Thompson Sampling) ». **DecInfer-3 argent = c.8094 cible directe.**

4. **Boucle vertueuse L792 close** : 5 promotions LNN dans rules existantes clôturées par c.8091 L796 + 1 nouvelle rule méthodologique c.8092 L797 ; c.8094 ouvre le **deuxième sub-grain** d'application cross-famille du pattern canonique (ch.1 → ch.3).

## Anti-patterns évités

- **Pas de hand-edit cellule notebook** (Stop & Repair) — audit read-only strict
- **Pas de ré-exécution Papermill** (C.3 strict) — lecture des `execution_count`/`outputs` existants uniquement
- **Pas de modification `.claude/rules/`** — HOLD ai-01 respecté (rapport dans `MyIA.AI.Notebooks/...`, hors périmètre HOLD)
- **Pas de `Closes #8081`** — sub-grain méthodologique, l'épic parente reste ouverte pour les autres tranches (DecisionTheory Ch.4+)
- **Pas de monoculture** — sub-grain méthodologique distinct de c.8087-c.8091 (≠ même genre `harness-hygiene`, ≠ même action `promotion LNN dans rule existante`) ET distinct de c.8093 (chapitre 3 ≠ chapitre 1, substance genuinely distincte per L788-L3) — diversification authentique post 5+1 grains consécutifs
- **Pas de duplication en prose** — rapport concis, structure 4 étapes + 4 verdicts, reconductibilité cross-chapitres documentée
- **Pas de régression pédagogique** — les notebooks DecInfer-3 et DecPyMC-2 restent inchangés (audit read-only), 0 modification de cellule, 0 régénération d'output
- **Pas de body dans le worktree** (L677-L4 ★★ freshly anchored c.8089) — body PR écrit dans `<scratchpad-dir>/c8094_decinfer_3_audit_body.md`, pas dans `c8094-audit-DecInfer-3-DecisionTheory/MyIA.AI.Notebooks/...`

## Cross-références

- **Issue #8081** — épic parente "audit distillation Probas MBML" (§4 recommande audit DecisionTheory séparé)
- **PR #8085** (c.8081) — pilote audit TrueSkill MERGED 2026-07-23
- **PR #8087** (c.8081+) — mapping 38 notebooks Probas MERGED 2026-07-23
- **PR #8088** (c.8084) — audit Murder Mystery Ch.1 MERGED 2026-07-23
- **PR #8091** (c.8085) — audit StudentSkills Ch.2 IRT MERGED 2026-07-23
- **PR #8094** (c.8086) — audit Crowdsourcing Ch.7 MERGED 2026-07-23
- **PR #8112** (c.8092) — règle méthodologique `.claude/rules/audit-cross-source-distillation.md` (HOLD pending user sign-off)
- **PR #8114** (c.8093) — premier audit cross-famille DecisionTheory ch.1 DecInfer-1 (L798 leçon ancrée)
- **PR #8115** (c.8094, cette PR) — deuxième audit cross-famille DecisionTheory ch.3 DecInfer-3
- **`.claude/rules/audit-cross-source-distillation.md`** (c.8092) — règle méthodologique 4 étapes + 4 verdicts appliquée ici (deuxième application cross-chapitre)
- **L772** (c.8081) — fondateur méthode audit cross-source
- **L789** (c.8084) — sub-genre same justifié (substance genuinely distincte)
- **L790** (c.8085) — DIVERGENCE POSITIVE pattern (à présent confirmé sur cross-moteur DecisionTheory ch.1 et ch.3)
- **L791** (c.8086) — adaptation cross-famille pattern
- **L796** (c.8091) — clôture boucle vertueuse L792
- **L797** (c.8092) — nouvelle rule méthodologique cross-famille
- **L798** (c.8093) — application pattern canonique sur DecisionTheory ch.1, recommande DecInfer-3 comme c.8094
- **L799** (c.8094, cette PR) — application pattern canonique sur DecisionTheory ch.3, verdicts identiques c.8093 (FIDÈLE 67% / PERTE DOC 17% / PLAIS 0% / DIV POS 17%) = reconductibilité cross-chapitres confirmée
- **L788-L3** — sub-genre same OK si substance genuinely distincte (DecisionTheory ch.3 ≠ ch.1 ✓)
- **L915** (c.764) — standalone : pas de PR OPEN MERGEABLE requise pour démarrer l'audit
- **L677-L4 ★★** — leçon ancrée par c.8089 (PR body HORS worktree) — cette PR applique
- **L761-L2 ★** — docs/permanent reports HORS worktree — cette PR applique
- **L898 ★★★** — pré-push collision guard vérifié post-worktree creation (`gh pr list --search head:feature/c8094-audit-DecInfer-3-DecisionTheory` = 0 collision)
- **EPIC #5780** — vague-1 figures audit (axe-1 visuel, distinct axe-3 distillation)
- **EPIC #3801** — registre axe-2 doc-honesty (markdown claim vs output)
- **EPIC #7423** — sub-grain méthodologique ancêtre (boucle vertueuse L792 close c.8091 L796)

---

🤖 Generated with [Claude Code](https://claude.com/claude-code)