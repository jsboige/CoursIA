# Audit distillation DecInfer-1 vs DecPyMC-1 + sources canoniques

**Date** : 2026-07-23
**Cycle** : c.8093 (sub-grain #8081 §4 cross-famille post-c.8092 rule méthodologique)
**Méthode** : c.8092 rule `.claude/rules/audit-cross-source-distillation.md` — 4 étapes + 4 verdicts
**Pilote fondateur** : `DecInfer-1-Utility-Foundations.ipynb` (1er DecInfer de l'arc 10 notebooks, le plus simple pour appliquer la méthode)

---

## Étape 1 — Identifier la source canonique

| Question | Source identifiée |
|----------|-------------------|
| Quelle famille ? | `MyIA.AI.Notebooks/Probas/DecisionTheory/` |
| Quelle source canonique théorique ? | **Pas de MBML direct** — DecisionTheory a un cadrage propre (axiomes vNM 1944 + théorie risque Pratt 1964 + Arrow 1965) ; cadrage README racine Probas § "De la distribution à l'utilité" |
| Quel notebook DecInfer audité ? | `DecInfer-1-Utility-Foundations.ipynb` |
| Quel notebook miroir DecPyMC ? | `DecPyMC-1-Utility-Foundations.ipynb` (numérotation parallèle 1-7) |
| Linéage ? | README DecInfer ligne 76 confirme DecPyMC-2 = source de la figure reprise DecInfer-1 ("Pratt 1964, Arrow 1965" comme cadrage théorique) |

**Note méthodologique** : unlike c.8081/84/85/86 (où la source canonique était MBML chapters 3/1/2/7), DecInfer-1 n'a **pas** de source canonique tierce unique mais **un double-moteur interne** (DecInfer C# .NET vs DecPyMC Python) + un cadrage théorique classique (vNM/Pratt/Arrow). L'audit adapte la méthode 4 étapes + 4 verdicts à ce contexte : les 2 moteurs sont les 2 "sources" comparées, et la cohérence avec vNM/Pratt/Arrow est l'ancrage théorique canonique.

## Étape 2 — Lire les sources firsthand

### DecInfer-1 (43 cellules)
- **27 markdown** + **16 code** ; 16/16 code executed OK ; 0 `raise NotImplementedError`
- **3 exercices** (cell 13 axiome indépendance, cell 25 décision séquentielle IRM, cell 41 CARA/CRRA primes) ✓ conforme `three-exercises-per-notebook.md`
- **3 exemples guides résolus** : cell 17 (diagnostic médical avec Infer.NET `engine.Infer<Bernoulli>`), cell 32 (loterie avec `engine.Infer<Gaussian>`), cell 38 (calibration CRRA par dichotomie sur ρ)
- **1 visualisation factor graph** via `FactorGraphHelper.cs` chargé cell 6 (cell 19 + 21 ShowFactorGraph diagnostic ; cell 34 + 36 factor graph loterie)
- **Citations canoniques** : vNM 2 / Von Neumann 5 / Morgenstern 5 / Pratt 1 / Arrow 2 / Bernoulli 7 / CARA 3 / CRRA 6 / Saint-Pétersbourg 2

### DecPyMC-1 (38 cellules)
- **26 markdown** + **12 code** ; 12/12 code executed OK ; 0 `raise NotImplementedError`
- **3 exercices** (cell 12 axiome indépendance, cell 26 loterie assurance PyMC, cell 35 CARA/CRRA primes) ✓ conforme
- **3 exemples guides résolus** : cell 16 (modèle de diagnostic PyMC avec MCMC), cell 19 (hiérarchique multi-sites MCMC non-conjugué), cell 24 (calibration CRRA), cell 32 (calibration CRRA par dichotomie)
- **Citations canoniques** : vNM 2 / Von Neumann 4 / Morgenstern 4 / Pratt 6 / Arrow 6 / Bernoulli 7 / CARA 3 / CRRA 6 / Saint-Pétersbourg 2

## Étape 3 — Comparer axe par axe

| Axe | DecInfer-1 | DecPyMC-1 | Verdict |
|-----|------------|-----------|---------|
| **Concepts** | Sections 1-8 (intro, loteries, axiomes, théorème, calibration, modélisation, exemple, exercice) — toutes présentes | Mêmes sections 1-8 (sauf §6 n'a pas factor graph .NET) | **FIDÈLE** |
| **Dérivation** | vNM axiomes 1-6 énoncés sans preuve formelle ; théorème représentation cité sans preuve (renvoyé DecInfer-2 Lean `ExpectedUtility` companion) | vNM axiomes 1-6 idem ; pas de companion Lean côté PyMC | **FIDÈLE** (cohérence DecInfer-2 Lean en aval) |
| **Exemples chiffrés** | Cell 17 (P(malade\|test+) = ~0.79 calculé) ; cell 32 (loterie 50/50 +1000/-500 = E[U]=√500+√-500 vs √250) ; cell 38 (5 CE testés 200/300/400/450/480 EUR → ρ résultats) | Cell 16 (même calcul P(malade\|test+)) ; cell 19 (MCMC hiérarchique) ; cell 32 (5 CE testés) | **FIDÈLE** |
| **Visualisations** | Factor graph via `FactorGraphHelper.cs` (ShowFactorGraph + display HTML) cell 19-21 et cell 34-36 = visualisation .NET-specific | Pas de factor graph PyMC (MCMC traces seulement — `arviz_trace_maintenance.png` au niveau DecPyMC README) | **DIVERGENCE POSITIVE** — visualisation .NET exploitée comme valeur ajoutée du moteur, sans équivalent PyMC direct |
| **Exercices** | 3 stubs `// TODO` (cell 13, 25, 41) ; cell 28 = example `// Calibration de l'utilite pour la decision d'assurance` (résolu, sert d'exemple guidé pour cell 41) | 3 stubs `# TODO` (cell 12, 26, 35) ; cell 24 = example `# Calibration...` (résolu) | **FIDÈLE** |
| **Attribution** | vNM/Morgenstern 10 mentions (5+5), Pratt 1, Arrow 2 — asymétrie : moins loquace sur les fondements théoriques | vNM/Morgenstern 8 mentions (4+4), Pratt 6, Arrow 6 — asymétrie inverse : plus loquace sur fondements théoriques | **PERTE DOCUMENTÉE** — asymétrie d'attribution entre les 2 moteurs : DecInfer-1 cite moins les sources canoniques (Pratt/Arrow 1+2) que DecPyMC-1 (Pratt/Arrow 6+6). Différence non explicitée ni justifiée dans aucun des 2 notebooks |

## Étape 4 — Verdict par axe + verdict global

| Verdict | Axe |
|---------|-----|
| **FIDÈLE** | Concepts · Dérivation · Exemples chiffrés · Exercices |
| **PERTE DOCUMENTÉE** | Attribution (asymétrie DecInfer vs DecPyMC non explicitée) |
| **PERTE PAR COMPLAISANCE** | (0 trouvé) |
| **DIVERGENCE POSITIVE** | Visualisations (factor graph .NET-specific, bonus légitime) |

### Verdict global (synthèse)

**FIDÈLE 67% / PERTE DOCUMENTÉE 17% / PERTE PAR COMPLAISANCE 0% / DIVERGENCE POSITIVE 17%**

Calcul sur 6 axes pondérés également : FIDÈLE 4/6 + PERTE DOC 1/6 + PLAIS 0/6 + DIV POS 1/6.

## Reconductibilité cross-famille

Le pattern de c.8092 fonctionne ici mais nécessite une **adaptation méthodologique** : là où c.8081-c.8086 comparaient 1 source canonique externe (MBML) avec N portages internes (Infer, PyMC), l'arc DecisionTheory compare 2 moteurs internes équivalents (DecInfer C# / DecPyMC Python) ancrés sur un cadrage théorique commun (vNM/Pratt/Arrow). La **substance** est distincte (DecisionTheory ≠ Probas MBML — c'est un audit **cross-moteur** plutôt qu'**cross-source canonique**), donc **sub-genre same justifié per L788-L3** : c.8081-c.8086 = audit cross-source canonique (MBML), c.8093 = audit cross-moteur (DecInfer vs DecPyMC). Le pattern 4 étapes + 4 verdicts reste valide.

**Recommandation pour les c.8094+ audits DecisionTheory** : appliquer la même adaptation — 2 moteurs internes comme sources comparées + ancrage théorique classique (vNM 1944 / Pratt 1964 / Arrow 1965 / Fishburn 1988 / Kreps 1988) comme référence canonique.

## Pourquoi c.8093 maintenant (post-c.8092, post-HOLD ai-01)

1. **Périmètre post-HOLD respecté** : c.8093 crée un **rapport d'audit** dans `MyIA.AI.Notebooks/Probas/DecisionTheory/DecInfer/AUDIT-DISTILLATION-DecInfer-1-2026-07-23.md` (analogue aux c.8085/88/91/94) — **n'édite pas** `.claude/rules/`. Le pattern HOLD ai-01 sur les éditions `.claude/rules/*.md` (sign-off user requis) ne s'applique pas.
2. **Pivot cross-famille strict** : G-VAR-3 rotation imposée après c.8087-c.8091 (5 MED/harness-hygiene consécutifs). c.8093 = MED/audit-cross-source, **substance cross-famille distincte** (DecisionTheory ≠ Probas MBML).
3. **Recommandation c.8081 §4 honorée** : issue #8081 §4 recommandait "audit DecisionTheory séparé à mener". c.8093 = première tranche de cette recommandation.
4. **Boucle vertueuse L792 (c.8087) close** : 5 orphelines cross-famille déjà clôturées par c.8088-c.8091 ; c.8093 ouvre le sous-grain suivant recommandé par la règle méthodologique c.8092.

## Anti-patterns évités

- **Pas de hand-edit cellule notebook** (Stop & Repair) — audit read-only strict
- **Pas de ré-exécution Papermill** (C.3 strict) — lecture des `execution_count`/`outputs` existants uniquement
- **Pas de modification `.claude/rules/`** — HOLD ai-01 respecté
- **Pas de `Closes #8081`** — sub-grain méthodologique, l'épic parente reste ouverte pour les autres tranches (DecisionTheory Ch.2+, Probas MBML extension)
- **Pas de monoculture** — c.8093 pivote cross-famille post-c.8087-c.8091 (5 MED/harness-hygiene consécutifs)
- **Pas de duplication en prose** — rapport concis, structure 4 étapes + 4 verdicts, reconductibilité documentée
- **Pas de régression pédagogique** — le notebook DecInfer-1 reste inchangé (audit read-only), 0 modification de cellule, 0 régénération d'output

## Cross-références

- **Issue #8081** — épic parente "audit distillation Probas MBML" (§4 recommande audit DecisionTheory séparé)
- **PR #8085** (c.8081) — pilote audit TrueSkill MERGED
- **PR #8087** (c.8081+) — mapping 38 notebooks Probas MBML MERGED
- **PR #8088** (c.8084) — audit Murder Mystery Ch.1 MERGED
- **PR #8091** (c.8085) — audit StudentSkills Ch.2 IRT MERGED
- **PR #8094** (c.8086) — audit Crowdsourcing Ch.7 MERGED
- **`.claude/rules/audit-cross-source-distillation.md`** (c.8092) — règle méthodologique 4 étapes + 4 verdicts appliquée ici
- **L772** (c.8081) — fondateur méthode audit cross-source
- **L789** (c.8084) — sub-genre same justifié (substance genuinely distincte)
- **L790** (c.8085) — DIVERGENCE POSITIVE pattern (à présent confirmé sur cross-moteur)
- **L791** (c.8086) — adaptation cross-famille pattern
- **L796** (c.8091) — clôture boucle vertueuse L792
- **L797** (c.8092) — nouvelle rule méthodologique cross-famille
- **L788-L3** — sub-genre same OK si substance genuinely distincte (DecisionTheory ≠ Probas MBML ✓)
- **L915** (c.764) — standalone : pas de PR OPEN MERGEABLE requise pour démarrer l'audit

---

🤖 Generated with [Claude Code](https://claude.com/claude-code)