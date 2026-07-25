# Audit fidélité distillation — Infer-4-Bayesian-Networks (2026-07-25)

**Notebook audité** : `MyIA.AI.Notebooks/Probas/Infer/Infer-4-Bayesian-Networks.ipynb` (66 cellules : 46 markdown, 20 code ; série Infer.NET 4/19).
**Lane** : po-2026 (c.742).
**Issue** : See #8081 (audit fidélité distillation Probas/Infer + PyMC vs sources canoniques MBML / Infer.NET repo).
**Méthode** : 4 axes × 4 verdicts (cf #8081). Comparaison firsthand du notebook contre les sources canoniques.

## Sources canoniques

| Source | URL / référence | Rôle pour Infer-4 |
|--------|-----------------|-------------------|
| *Model-Based Machine Learning* (Bishop & Winn) | https://mbmlbook.com/ | Ch.1 *A Murder Mystery* (variables discrètes, factor graphs, conditional independence) ; Ch.3 *Learning by Reasoning* (suspects) |
| Russell & Norvig, *AIMA* ch.14 « Probabilistic Reasoning » | — | Source canonique du réseau **Wet Grass / Sprinkler / Rain** (exemple utilisé par le notebook) |
| Infer.NET repo `Examples/` | https://github.com/dotnet/infer/tree/main/src/Examples | `BayesianNetwork` / `BayesPointMachine` / modèles hiérarchiques — Patterns `Variable.If`, `SetTo` |

**Note de framing (écart documenté, pas une perte)** : MBML Ch.1/3 utilise le fil narratif du **meurtre de Mr Black + 4 suspects**. Infer-4 choisit à la place le réseau **Wet Grass / Sprinkler / Rain** (Russell-Norvig, Koller-Friedman *Probabilistic Graphical Models*), un exemple *également canonique* mais d'une lignée de source différente. C'est un **choix pédagogique légitime** (Wet Grass est le running example le plus repris pour D-separation + explaining-away) — **documenté ici explicitement** (per #8081 « décision documentée pour PERTE DOCUMENTÉE »), ce n'est ni une omission ni une complaisance. Le corpus Probas possède déjà le fil Murder Mystery dans Infer-3 (audit #8088), donc la complémentarité Wet-Grass dans Infer-4 est cohérente avec la progression de la série.

## Verdict global

**FIDÈLE ~80% / PERTE DOCUMENTÉE 15% / PERTE PAR COMPLAISANCE POTENTIELLE 5%**

Le notebook est une **bonne distillation** : il exécute réellement les concepts distinctifs (pas seulement narrés), à l'inverse des findings `PERTE PAR COMPLAISANCE` typiques de #8081 (où une capability est nommée puis contournée).

### Verdict axe par axe

| Sous-système | Verdict | Preuve (firsthand) |
|--------------|---------|---------------------|
| **Définitions formelles** (DAG, CPT, factorisation chain rule) | **FIDÈLE** | cell[6] donne $P(X_1..X_n) = \prod P(X_i \mid \text{Parents}(X_i))$, table CPT complète cell[7] |
| **Explaining away** (capability distinctive de Bayesian nets) | **FIDÈLE** (exécuté, pas seulement décrit) | cell[23] décrit + cell[24] **exécute** (exec=8, 8 outputs) : ajoute `Rain=True` et montre `P(Sprinkler)` baisser. C'est exactement le finding anti-complaisance de #8081 — ici l'effet est *montré en direct*. |
| **D-separation** (3 structures : chain/fork/collider) | **FIDÈLE** (exécuté empiriquement) | cell[29] théorie + cell[30]/[33] **exécutent** 2 tests (exec=10/11, 7 outputs chacun) : vérifie l'indépendance conditionnelle par inférence Infer.NET — valide la théorie graphique contre le calcul numérique |
| **do() causal vs observation** (P(Y\|X) vs P(Y\|do(X))) | **FIDÈLE** (exécuté) | cell[38] implémente l'opérateur do() + cell[39] **exécute** (exec=13, 9 outputs) comparaison observationnel vs interventionnel |
| **BUGS Rats (modèle hiérarchique)** | **FIDÈLE** (exécuté, riche) | cell[46] framing + cell[48] **exécute** (exec=16, **57 outputs**) : 5 rats × 4 temps, paramètres individuels tirés d'une population. Modèle hiérarchique réellement tourné |
| **Réseau de diagnostic médical** (exemple guidé) | **FIDÈLE** (exécuté) | cell[55-59] (exec=18, 6 outputs) |
| **3+ exercices** (convention #2161) | **PRÉSENT (3 stubs C.1)** | cell[36] collider/explaining-away, cell[42] diagnostic médical, cell[64] extension fièvre — 3 exercices stubbés (TODO, `pass`), non résolus |
| **Attribution source MBML** | **PERTE DOCUMENTÉE** (framing) | Le notebook ne cite pas MBML dans ses cellules (utilise Russell-Norvig/Koller pour Wet Grass). Lignée MBML est dans le README Probas/Infer (ligne 882 : « Murder Mystery (Factor Graphs, MBML Ch1) ») mais pas dans Infer-4 lui-même — framing documenté ci-dessus, pas une omission de substance |
| **Dérivation itérative (dialogue MBML)** | **PERTE DOCUMENTÉE** (choix pédagogique) | MBML procède par *dialogue de dérivation* (l'étudiant construit le modèle au fur et à mesure). Infer-4 présente le modèle fini puis l'exécute. Choix légitime pour un notebook technique (la dérivation itérative vit dans Infer-3 Murder Mystery #8088), **documenté ici** per #8081 |
| **Convergence / diagnostiquer un échec d'inférence** | **PERTE PAR COMPLAISANCE POTENTIELLE (5%)** | Le notebook montre uniquement des inférences qui *convergent* (EP toujours réussit). MBML/Infer.NET docs insistent sur les pièges : **convergence lente/non-convergence** sur collider observé, **loopy belief propagation**, message-passing qui n'atteint pas l'optimum. Comme les findings Infer-8 (#8097 motivation EP) et PyMC-2 (#8341 boucle de critique), cette *capability* (diagnostiquer un échec d'inférence) est absente. Candidat follow-up : cellule montrant un collider mal-conditionné où EP diverge ou converge lentement + diagnostic (cf §6.1-style). **Non bloquant pour le verdict global** (le notebook est solide), mais c'est le seul axe où une PERTE PAR COMPLAISANCE est plausible. |

## Constat clé — la distillation est *exécutée*, pas contournée

Contrairement aux findings `PERTE PAR COMPLAISANCE` typiques de #8081 (capability nommée puis workaround dégradé), Infer-4 **fait tourner** ses capabilities distinctives : explaining-away est démontré numériquement (cell[24]), D-separation est validé empiriquement contre l'inférence (cell[30-33]), do() est implémenté et comparé (cell[39]), le hiérarchique BUGS Rats produit 57 outputs (cell[48]). C'est la signature d'une **bonne distillation** — la preuve d'exécution réelle est dans les outputs (tous 20 cells exec=1..20 séquentiel, 0 cellule non-exécutée, H.3 clean).

## Exécution / authenticité

- **Tous 20 code cells** portent `execution_count` 1..20 séquentiel + outputs cohérents (H.1/H.3 validés) — pas de cellule non-exécutée.
- **0** `raise NotImplementedError` / `assert False` / `1/0` (C.1 clean) — les 3 exercices utilisent `// TODO` + stubs `pass`-style conformes.
- Le notebook s'exécute sur Infer.NET C# .NET Interactive (règle F : kernel installable partout).

## Recommandation

- **Verdict global : FIDÈLE (~80%)** — distillation de qualité, capabilities exécutées et non contournées.
- **PERTE DOCUMENTÉE (15%)** : framing Russell-Norvig/Koller vs MBML Mr Black + dérivation itérative absente — tous deux légitimes et **documentés ici** (choix pédagogique, cohérents avec Infer-3 Murder Mystery #8088 pour le fil narratif MBML).
- **PERTE PAR COMPLAISANCE POTENTIELLE (5%)** : absence d'un exemple d'**échec/convergence problématique d'EP** (diagnostiquer un inférence qui ne converge pas) — candidat à un backfill dans un follow-up si la lane le souhaite (sous-issue dédiée), mais non bloquant pour la qualité actuelle du notebook.

**Pas de PR de backfill immédiate nécessaire** (le notebook est solide). Ce document constitue le livrable d'audit #8081 pour Infer-4 (acceptance criterion « verdict documenté »).

---

See #8081. Suite de c.8081 (mapping 38 NB #8087) + audits #8085 (TrueSkill), #8088 (Murder Mystery), #8091 (IRT), #8094/#8288 (Crowdsourcing), #8238 (BPM), #8114 (DecInfer-1). Infer-4 = première couverture de la série sur les réseaux bayésiens classiques (D-separation / explaining-away / do-operator).
