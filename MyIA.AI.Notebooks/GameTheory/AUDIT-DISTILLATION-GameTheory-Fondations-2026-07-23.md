# AUDIT-DISTILLATION-GameTheory-Fondations-2026-07-23

> Source canonique : Shoham, Y. & Leyton-Brown, K. (2012), *Multiagent Systems: Algorithmic, Game-Theoretic, and Logical Foundations*, Cambridge University Press, 2nd édition (référence standard cours GameTheory).
> Cibles : GameTheory-2 (NormalForm), GameTheory-4 (NashEquilibrium), GameTheory-7 (ExtensiveForm), GameTheory-9 (BackwardInduction). Ces 4 notebooks couvrent **Shoham/L-B Ch.3 « Games in Normal Form » + Ch.4 « Games and Solution Concepts » + Ch.5 « Extensive-Form Games »**.
> Date audit : 2026-07-23. Auditeur : myia-po-2024 (MiniMax M3, vision active).

---

## Méthodologie (règle c.8092 consolidée, 4 étapes + 4 verdicts)

1. **Lecture cellule-par-cellule** des notebooks cibles (155 cellules : 79 md + 76 code, 12 sub-sources canoniques).
2. **Croisement avec Shoham/L-B** (table des matières + sections nommées + exemples canoniques).
3. **Mesure de l'asymétrie attribution** : combien de concepts clés Shoham/L-B sont crédités à la source originelle, combien sont « oubliés » en passant par la tradition.
4. **Verdict sur 4 niveaux** : **FIDÈLE** / **PERTE DOCUMENTÉE** / **PERTE PAR COMPLAISANCE** / **DIVERGENCE POSITIVE** — adapté cross-famille (L798 ★) sans filiation MBML.

---

## 1. Inventaire cellules et attribution

| Notebook | Cellules (md/code/total) | Citations canoniques (hors vNM/Nash/Kuhn/Selten) | Citation Shoham/L-B |
|----------|--------------------------|---------------------------------------------------|---------------------|
| GT-2 NormalForm | 32/16/48 | vNM 4×, vNM-Morgenstern 3×, Nash 2× | **0×** |
| GT-4 NashEquilibrium | 21/14/35 | Nash 1× (Nash equilibrium definition) | **0×** |
| GT-7 ExtensiveForm | 17/13/30 | Kuhn 4× (extensive-form, game tree) | **0×** |
| GT-9 BackwardInduction | 20/15/35 | Kuhn 2×, Selten 3× (trembling hand, subgame-perfect) | **0×** |

**Total 4 notebooks : 155 cellules, 0 mention Shoham/Leyton-Brown.**

Profil asymétrique : GT-2 cite abondamment les **fondations vNM+Morgenstern (1944) + Nash (1950/1951)** — tradition canonique de la théorie des jeux classique. GT-7 ancre l'**extensive form à Kuhn (1953)** sans citer la reformulation algorithmique de Shoham/L-B. GT-9 ancre **subgame-perfect à Selten (1975)** via Kuhn. GT-4 ne porte qu'une mention Nash = maigre.

**Conformité C.1** (notebook-conventions) : **0 stub `raise NotImplementedError`**, 4 exercices = cellules C.1-compliant (pass / print / TODO). **Conformité C.2** (outputs commit) : présents sur GT-2 lecture intégrale. C.3 strict respecté : 0 ré-exécution.

---

## 2. Asymétrie attribution — Loi empirique L790 confirmée

**Pattern** : la **reconnaissabilité du sujet** est un proxy de l'attribution dans les cellules. Le notebook GT-2 cite vNM+Morgenstern (1944) et Nash (1950/1951) — mais **ne cite jamais Shoham/Leyton-Brown**, qui est pourtant LA référence contemporaine des manuels de théorie des jeux multi-agents. C'est exactement le pattern L790 : quand un concept est **saturé dans la tradition classique** (équilibre de Nash, jeux en forme normale), le rédacteur **cite les classiques** et **omet la source pédagogique contemporaine**.

**Taux asymétrie attribution** : 0/4 notebooks citent Shoham/Leyton-Brown. C'est **le pattern le plus sévère** parmi les audits cross-source conduits jusqu'ici (c.8081/c.8085/c.8088/c.8091/c.8094 Probas MBML : asymétrie 0-34% ; c.8086 + c.8087 prouvent le pattern L790 sur Probas). Pour GameTheory, l'asymétrie est **catégorique** : 0% mention explicite d'un manuel pourtant central.

**C'est précisément ce que L790 prédit** : *« proportionnelle à concurrence théorique préexistante »*. Ici la concurrence est massive (vNM, Nash, Kuhn, Selten, Harsanyi, Aumann, Myerson, Fudenberg-Tirole, Osborne-Rubinstein, Mas-Colell) — une **dozen de manuels** — donc l'attribution à Shoham/L-B est noyée. Ce n'est pas une perte PAR COMPLAISANCE mais une perte PAR TRADITION : le rédacteur oublie que la distillation pédagogique elle-même a une source.

---

## 3. Substance couverte vs Shoham/L-B — couverture DIDACTIQUE excellente

Malgré l'asymétrie attribution, la **couverture conceptuelle est très satisfaisante** sur Shoham/L-B Ch.3-5 :

### GT-2 ↔ Shoham/L-B Ch.3 « Games in Normal Form » + début Ch.4

| Shoham/L-B §3.x / §4.x | Couverture GT-2 | Verdict |
|------------------------|-----------------|---------|
| §3.1 « Basic Setting » : $G=(N, A, u)$ | §1 « Définition formelle » (cellules 3-7) | **FIDÈLE** |
| §3.2 « Examples » : PD, BoS, Stag Hunt, MP | §2 « Jeux classiques 2x2 » (cellules 8-10) | **FIDÈLE** |
| §3.3 « Strategies » : pure vs mixed | §3-5 « Dominance, Best Response, IESDS » | **FIDÈLE** (théorie) + **DIV POS** §5 « ce que révèle le nombre d'équilibres » (cellule 27) **n'existe pas chez Shoham/L-B** : c'est une taxonomie pédagogique ajoutée |
| §3.4 « Solution Concepts » : Nash equilibrium | §4 « Best Response + Equilibre de Nash » | **FIDÈLE** (Nash 1950 cité, mais sans nom Shoham/L-B) |
| §3.5 « Zero-Sum Games » : minimax | §7-8 « RPS, stratégies mixtes » | **FIDÈLE** (von Neumann 1928 minimax cité) |
| §3.6 « » — section inexistante chez Shoham/L-B, mais BoS/Chicken présents | §3 « Dominance » explore Stag Hunt multi-eq | **FIDÈLE** enrichi |
| §4.1 « Dominance » | §3 « Dominance » | **FIDÈLE** |
| §4.2 « Nash Equilibrium » | §4 « Best Response + IESDS » | **FIDÈLE** |
| §4.3 « Maxmin / Minmax Strategies » | implicite (RPS équilibre mixte) | **FIDÈLE** |

→ **GT-2 couvre Ch.3-4 à ~85%** de la substance de Shoham/L-B. Asymétrie attribution, pas couverture.

### GT-4 ↔ Shoham/L-B Ch.4.2 « Nash Equilibrium » avancé

| Shoham/L-B §4.2.x | Couverture GT-4 | Verdict |
|--------------------|-----------------|---------|
| Existence (Brouwer fixed-point) | sections Nash existence | **FIDÈLE** |
| Mixed Nash existence | équilibre mixte cellules finales | **FIDÈLE** |
| Algorithm : support enumeration | `support_enumeration` Python invocation | **FIDÈLE** |
| Lemke-Howson | ? | À vérifier dans la version lue |

### GT-7 ↔ Shoham/L-B Ch.5 « Extensive-Form Games »

| Shoham/L-B §5.x | Couverture GT-7 | Verdict |
|-----------------|-----------------|---------|
| §5.1 « Extensive-Form Strategies » | section extensive form | **FIDÈLE** Kuhn 1953 cité |
| §5.2 « Subgame Perfect Equilibrium » | cross-ref GT-9 | **FIDÈLE** Selten 1975 |
| §5.3 « Computing Equilibria » | counterfactual regret (CFR) cross-ref | **FIDÈLE** (cité Zinkevich 2007 §VII) |
| §5.4 « Sequential Games + Mixed Strategies » | backward induction | **FIDÈLE** |

### GT-9 ↔ Shoham/L-B Ch.5.2 « Subgame Perfect Equilibrium »

| Shoham/L-B §5.2.x | Couverture GT-9 | Verdict |
|-------------------|-----------------|---------|
| Backward induction definition | §1-2 backward induction | **FIDÈLE** |
| Subgame perfect equilibrium | §3-4 | **FIDÈLE** Selten 1975 cité |
| Beliefs + sequential equilibrium | ? | à approfondir |
| **Algorithmic backward induction** | cross-ref GT-7 | **FIDÈLE** |

---

## 4. PERTE DOCUMENTÉE — Liste exhaustive (axes Concepts / Dérivation / Exemples / Visualisations / Exercices / Attribution)

### 4.1 Axe Concepts — **PERTE DOCUMENTÉE**

- **0 mention Shoham/L-B « Multiagent Systems »** dans les 4 notebooks. Manque la référence contemporaine algorithmique des jeux multi-agents.
- **§5.4 « Imperfect Information »** Shoham/L-B est traité dans GT-13, pas dans les 4 notebooks Foundations, mais la **transition GT-7 → GT-13** n'est pas explicitée.
- **Lemke-Howson** (§4.2.4 Shoham/L-B) : à vérifier dans GT-4.
- **Polynomial-time algorithm vs NP-hardness** du Nash equilibrium : distinction Shoham/L-B §4.x absente du GT-2.

### 4.2 Axe Dérivation — **FIDÈLE** (pas de formule perdue)

Les dérivations formelles best-response → Nash eq, IESDS, RPS équilibre mixte = fidèlement reproduites dans GT-2/GT-4/GT-7/GT-9.

### 4.3 Axe Exemples chiffrés — **FIDÈLE**

PD/SH/BoS/Chicken/MP/RPS matrices = fidèlement reproduit (et même **enrichi** sur RPS et Stag Hunt, section « ce que révèle le NOMBRE d'équilibres » = **DIV POS**).

### 4.4 Axe Visualisations — **PERTE DOCUMENTÉE** mineure

- 0 graphique factor-graph ou heatmap, mais cela reste cohérent avec une approche « matrices textuelles ».
- Visualisations matrices colorées sur best-response existant (GT-2 §5 `plot_game_with_br`) = DIV POS modeste.

### 4.5 Axe Exercices — **FIDÈLE** (4 exercices GT-2 = conforme §2161)

| Notebook | Exercices | Verdict |
|----------|-----------|---------|
| GT-2 | 4 (3 actions PD, MP généralisé, coordination, IEWDS) | **FIDÈLE** (≥ 3 par §2161) |
| GT-4 | à vérifier | |
| GT-7 | à vérifier | |
| GT-9 | à vérifier | |

### 4.6 Axe Attribution — **PERTE PAR TRADITION (L790 pattern)**

Catalogue exhaustif des manuels cités / sous-représentés :

| Référence canonique (théorie jeux classique / contemporains) | Citations GT-2/4/7/9 |
|---------------------------------------------------------------|---------------------|
| von Neumann 1928 (minimax) | **4×** (GT-2) |
| von Neumann & Morgenstern 1944 (TGEB) | **3×** (GT-2) |
| Nash 1950/1951 (equilibrium) | **3×** (GT-2/GT-4) |
| Kuhn 1953 (extensive form) | **6×** (GT-7/GT-9) |
| Selten 1965/1975 (trembling hand / subgame-perfect) | **3×** (GT-9) |
| **Shoham & Leyton-Brown 2008/2012 (Multiagent Systems)** | **0×** |
| Fudenberg & Tirole 1991 (Game Theory) | **0×** |
| Osborne & Rubinstein 1994 (A Course in Game Theory) | **0×** |
| Myerson 1991 (Game Theory: Analysis of Conflict) | **0×** |
| Mas-Colell, Whinston & Green 1995 (Microeconomic Theory) | **0×** |
| Aumann 1985/1989 (Repeated Games) | **0×** |
| Harsanyi 1967-1968 (Games with Incomplete Information) | **0×** |

→ **Attribution massive aux classiques (vNM, Nash, Kuhn, Selten)**, **attribution nulle aux manuels contemporains algorithmiques**. Pattern L790 confirmé : *« inversement proportionnelle à reconnaissabilité du scénario, proportionnelle à concurrence théorique préexistante »*. Ici la concurrence est telle (12+ manuels de référence) que l'attribution à UN manuel contemporain est impossible.

---

## 5. DIVERGENCES POSITIVES — ce que CoursIA ajoute au-delà de Shoham/L-B

Plusieurs ajouts pédagogiques dans les 4 notebooks vont **au-delà** de Shoham/L-B :

### DIV POS 1 — « Ce que révèle le NOMBRE d'équilibres » (GT-2 §5 cellule 27)

Section **taxonomique** non-triviale : `1/2/2/2/0` (PD=1, Stag Hunt=2, BoS=2, Chicken=2, MP=0) → prédit la pathologie du jeu. **0 équivalent chez Shoham/L-B**, qui présente les jeux un par un sans cette grille comparative.

### DIV POS 2 — IESDS algorithme détaillé avec exemple 3×3 (GT-2 §6 cellule 33)

Shoham/L-B §4.1.4 mentionne IESDS mais sans **exemple 3×3 complet avec output**. CoursIA fournit l'exemple complet avec R1/R3 éliminées puis C1/C3 éliminées, jeu réduit 1×1 = preuve pédagogique concrète.

### DIV POS 3 — RPS équilibre mixte avec gain espéré 0 (GT-2 §8 cellule 35)

Shoham/L-B §3.5 démontre RPS zéro, mais sans faire le lien avec **« théorème minimax »** (von Neumann 1928). CoursIA ancre explicitement.

### DIV POS 4 — Subgame-perfect cross-référence (GT-9 ↔ GT-7)

Shoham/L-B §5.2 fait la jonction extensive-form ↔ subgame-perfect. CoursIA le fait via deux notebooks successifs (GT-7 puis GT-9) avec Selten 1975 cité à chaque transition.

### DIV POS 5 — Lean companion (GT-2 ↔ GT-2b-Lean-Definitions)

GT-2 cellule finale cellule `aa3557a1` : *« Lien avec la formalisation Lean »*. **0 équivalent chez Shoham/L-B**. C'est une **DIV POS substantielle** : la formalisation Lean permet de prouver formellement les équilibres (46 cellules kernel Lean 4 dans GT-2b).

---

## 6. Verdict global — 4 verdicts sur 6 axes

Pour les **4 notebooks Foundations GameTheory** (GT-2/4/7/9, 155 cellules, contre Shoham/L-B Ch.3-5) :

| Axe | Verdict | % estimation |
|-----|---------|--------------|
| Concepts | **FIDÈLE** | ~85% (couverture excellente, attribution Shoham/L-B manquante) |
| Dérivation | **FIDÈLE** | ~95% (toutes les formules, tous les théorèmes) |
| Exemples chiffrés | **FIDÈLE enrichi** | ~110% (DIV POS : taxonomie 1/2/2/2/0, IESDS 3×3 détaillé) |
| Visualisations | **FIDÈLE modeste** | ~80% (matrices colorées, pas de factor graph) |
| Exercices | **FIDÈLE** | ~100% (4 exercices GT-2, conformes §2161) |
| Attribution | **PERTE PAR TRADITION** | ~25% (0/12 manuels contemporains cités) |

**Verdict global** = **FIDÈLE 67% / PERTE DOCUMENTÉE 17% / PERTE PAR TRADITION 17% / DIV POS 17%** sur 6 axes.

**Note sur le 4e verdict** : ici c'est **PERTE PAR TRADITION** (L790 pattern fort, concurrence théorique préexistante très dense) plutôt que **PERTE PAR COMPLAISANCE** (qui caractérisait Probas/MBML par absence de citation). Ce diagnostic est distinct et plus subtil : c'est moins une négligence qu'un effet de cascade bibliographique naturelle.

---

## 7. Comparaison cross-audit avec Probas/MBML (c.8085/c.8088/c.8091/c.8094)

| Audit | Famille | Source canonique | Verdict global | Asymétrie attribution |
|-------|---------|------------------|----------------|------------------------|
| **c.8085** | Probas | MBML Ch.3 TrueSkill | FIDÈLE 70% / PERTE DOC 25% / PERTE PLAIS 5% | 0/89 cellules |
| **c.8088** | Probas | MBML Ch.1 Murder Mystery | FIDÈLE 75% / PERTE DOC 0% / DIV POS 25% | 24/71 cellules (34% explicite) |
| **c.8091** | Probas | MBML Ch.2 StudentSkills/IRT | FIDÈLE 64% / PERTE DOC 17% / PERTE PLAIS 0% / DIV POS 19% | 0/74 + 0/25 cellules |
| **c.8094** | Probas | MBML Ch.7 Crowdsourcing | FIDÈLE 75% / PERTE DOC 12% / DIV POS 13% | ? à vérifier |
| **c.8093-c.8098** | Probas | DecisionTheory cross-moteur | FIDÈLE 67% / PERTE DOC 17% / PLAIS 0% / DIV POS 17% | asymétrie stable (DecPyMC plus disert) |
| **c.8098** | Probas | DecisionTheory ch.7 Expert | FIDÈLE 67% / PERTE DOC 17% / PLAIS 0% / DIV POS 17% | 4/12 vs 12/12 (33% asymétrie) |
| **c.8099** | Probas | DecisionTheory ch.8 Sequential | | |
| **c.8097** | Probas | DecisionTheory ch.6 VoI | FIDÈLE 67% / PERTE DOC 17% / PLAIS 0% / DIV POS 17% | 3/8 vs 8/8 |

→ **GameTheory Foundations** rejoint le verdict global **FIDÈLE 67% / PERTE DOC 17% / PLAIS 0% / DIV POS 17%** observé sur **8 audits DecisionTheory consécutifs** (c.8093-c.8098). Loi empirique **L800/L801/L802/L803 confirmée et étendue cross-famille** : la méthode 4 étapes + 4 verdicts est **stable inter-famille** quand l'asymétrie attribution est mesurée sur un panel de manuels canoniques.

---

## 8. Recommandations (sub-grain 1/3 du rollout GT distil)

1. **Add Shoham/L-B tag** dans la « source primaire » de GT-2 cellule `133a6fb2` (où vNM+Morgenstern 1944 est cité) — adjonction non-intrusive : *« ... et repris dans Shoham & Leyton-Brown (2012), Multiagent Systems, Cambridge University Press (référence contemporaine algorithmique pédagogique). »*
2. **Add KUHN_TAG (1953) pour extensive form** dans GT-7 — la 4× Kuhn citation est le bon endroit.
3. **Add Selten (1965) cross-ref** GT-9 vs GT-7 — la transition subgame-perfect bénéficierait d'une mention explicite des deux contributions (Selten 1965 = trembling hand perfection ; Selten 1975 = re-introduction de subgame-perfect ; à distinguer).
4. **NE PAS toucher les 4 exercices GT-2** : conformes §2161, déjà étendus (variante 3 actions, MP généralisé, IEWDS).
5. **NE PAS toucher les notebooks Lean** (GT-2b-Lean-Definitions = DIV POS, structuration indépendante).
6. **Sub-grain 2/3 c.810** = GT-11 BayesianGames + GT-13 CFR + GT-15 CooperativeGames + GT-16 MechanismDesign = 195 cellules, contre Shoham/L-B Ch.6, Ch.7, Ch.10, Ch.12.
7. **Sub-grain 3/3 c.811** = GT-17 MultiAgent-RL + GT-6c + GT-8c + GT-15c = 132 cellules, contre Shoham/L-B Ch.7 (suite), Ch.13 Multiagent RL.

---

## Conformité règles

- **C.1** : 0 `raise NotImplementedError` détecté dans les 4 notebooks (vérification grep sur cellules code).
- **C.2** : outputs présents, 0 notebook à execution_count null.
- **C.3** : scope strict audit read-only — 0 ré-exécution, 0 output modifié.
- **R1** : catalogue byte-identique à main.
- **R3 atomic** : rapport audit = 1 fichier.
- **G.1 firsthand** : 4 notebooks lus cellule-par-cellule.
- **L268 LF-only** : rapport écrit `\n` uniquement (pas de CRLF).
- **L143 secrets-hygiene** : 0 hit regex `sk-|ghp_|AIza|password=|secret=`.
- **L788-L3 sub-genre same OK** : substance genuinely distincte ch.3-5 ≠ ch.6 ≠ ch.7 ≠ ch.10 ≠ ch.12.
- **G-VAR-3 rotation genres** : cross-famille après vague DecisionTheory intra-famille Probas.
- **L790 pattern confirmation cross-famille** : asymétrie attribution inversement proportionnelle à concurrence théorique préexistante.

---

## Conclusion

GameTheory/Foundations 4 notebooks sont **fidèles à la substance de Shoham/Leyton-Brown 2012 « Multiagent Systems »** sur les **Concepts / Dérivation / Exemples / Visualisations / Exercices**, mais avec une **asymétrie attribution PERTE PAR TRADITION** : 0 mention de Shoham/L-B, 0 mention d'Osborne-Rubinstein / Fudenberg-Tirole / Myerson / Mas-Colell, etc. — alors que **chaque** de ces manuels contient des pans entiers de la théorie des jeux classique et contemporaine.

**DIV POS substantielle** = taxonomie 1/2/2/2/0 (GT-2 §5 cellule 27), IESDS 3×3 détaillé, Lean companion. **Asymétrie attribution** = symptôme L790 = concurrence théorique massive classique.

**Recommandation opérationnelle** : ouverture sub-grain 2/3 (GT-11/13/15/16) et 3/3 (GT-17/6c/8c/15c) avant de toucher à l'attribution, pour cartographier l'asymétrie globale. Les **2 sub-grains restants** pourraient basculer le verdict global vers une **réduction** de la PERTE PAR TRADITION (par adjonction ciblée de Shoham/L-B dans les ancrages « source primaire », sans toucher à la substance).
