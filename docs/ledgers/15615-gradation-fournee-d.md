# Ledger — Issue #15615 (gradation GameTheory, fournée D : blocs 16 à 20)

> **Bornage strict** : ce ledger couvre les **carnets des blocs 16, 17, 18, 19 et 20** de la série GameTheory sur `origin/main` au 2026-10-11 (head `cfa6bbaea4ca`). Il poursuit la fournée A (`15615-gradation-fournee-a.md`, PR #20288 — carnets 01/04/05), la fournée B (`15615-gradation-fournee-b.md`, PR #20289 — blocs 06-10), la fournée C (`15615-gradation-fournee-c.md`, PR #20294 — blocs 11-15) et la strate « Fondations » ([15615-gradation-foundations.md](15615-gradation-foundations.md), carnets 02 + 03). **La série s'arrête au bloc 20** : cette fournée clôt le périmètre de l'audit.

## Origine

Issue #15615 — audit de gradation, plan en fournées A-D posté au fil. Fournée D annoncée « blocs 16-25, ~26 carnets » au cadrage ; **l'arbre au 2026-10-11 en porte 24** (16×8, 17×7, 18×3, 19×1, 20×5) et aucun carnet au-delà du bloc 20 — l'arbre fait foi, même règle qu'en fournées A, B et C.

## Méthode

Identique aux ledgers précédents : prérequis déclarés (section dédiée ou front-matter, extraits verbatim), concepts introduits (première section définissante), difficulté sur l'échelle **Basse / Moyenne / Haute / Très haute** (combinatoire du sujet + longueur comme proxy), jumeau (Py/C# ou principal/Lean).

## Tableau de gradation — fournée D (blocs 16-20)

| # | Carnet | Prérequis déclarés | Concepts introduits | Cells | Diff. | Jumeau |
|---|---|---|---|---:|---|---|
| 16 | [GameTheory-16-MechanismDesign-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16-MechanismDesign-Python.ipynb) | « Notebooks 1-13, notamment 11-BayesianGames » ; types/croyances/BNE ; bases PL — 65 min | Théorie des mécanismes (« théorie des jeux inversée ») : principe de révélation, enchères 1er/2nd prix + équivalence des revenus, VCG et paiements d'externalité, **non-monotonie du revenu VCG** (Conitzer-Sandholm), Othman-Sandholm §4.6 (« Better with Byzantine », Prop 6), Gale-Shapley, théorèmes d'impossibilité **Gibbard-Satterthwaite** et **Myerson-Satterthwaite**, 4 exercices | 52 (16 code) | **Très haute** | Oui (C#) |
| 16-cs | [GameTheory-16-MechanismDesign-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16-MechanismDesign-CSharp.ipynb) | Aucune déclarée (twin) | Twin C# : révélation, enchères, VCG (règle de Clarke), Gale-Shapley, double auction ; pont vers la version Python, parité #4956 | 24 (9 code) | Haute | Oui (Py) |
| 16b | [GameTheory-16b-Automated-Mechanism-Design-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16b-Automated-Mechanism-Design-Python.ipynb) | GT-16 (Vickrey/VCG) ; types bayésiens (GT-11) ; Python (itertools) — 35 min | **Automated Mechanism Design** (Conitzer-Sandholm) : le mécanisme devient variable de décision ; triplet générateur / vérification séparée / témoin d'impossibilité sur domaine fini ; « AMD n'est pas la strate 7 » ; chantier B3 #12205 | 17 (7 code) | Haute | Non |
| 16c | [GameTheory-16c-Extraction-de-Revenu-DSIC-IR-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16c-Extraction-de-Revenu-DSIC-IR-Python.ipynb) | Aucune déclarée — prolonge 16b (organes hérités) | La dimension paiement que le générateur de 16b n'énumérait pas : extraction de revenu au premier meilleur sous DSIC+IR ; couture du témoin d'impossibilité, deux lectures d'IR qui ne se rencontrent pas | 23 (7 code) | Haute | Non |
| 16d | [GameTheory-16d-Echange-de-Reins-Lean-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16d-Echange-de-Reins-Lean-Python.ipynb) | Aucune déclarée — mécanisme réel autonome | L'échange de reins comme institution : graphe de compatibilité et cycles, chaînes de donneurs altruistes, lecture directe des sources, arbitrage cardinalité/équité, pont cross-domain, 4 exercices | 25 (8 code) | Haute | Non |
| 16e | [GameTheory-16e-LLM-Players-Othman-Sandholm-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16e-LLM-Players-Othman-Sandholm-Python.ipynb) | Aucune déclarée — importe le mécanisme de GT-16 §4.6 | **Pilote LLM hétérogènes** sur Othman-Sandholm Prop 6 : protocole pré-enregistré (gelé avant tout appel), schéma provider-neutral, politiques scriptées comme contrôles, familles LLM réelles (models.myia.io), exécution condition × profil × seed × agent, contrefactuel homogène, scénario hostile (permutation d'une règle), verdict H0/H1 | 42 (15 code) | **Très haute** | Non |
| 16f-Py | [GameTheory-16f-Munkres-Assignment-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16f-Munkres-Assignment-Python.ipynb) | Aucune déclarée — hommage Munkres († 30/07/2026) | **Algorithme de Kuhn-Munkres** (méthode hongroise) : implémentation pédagogique, lecture par dualité linéaire, pont vers le jeu d'affectation de **Shapley-Shubik**, confrontation Gale-Shapley vs Kuhn-Munkres (deux notions d'optimum), 3 exercices | 28 (10 code) | Haute | Oui (16f-Lean) |
| 16f-Lean | [GameTheory-16f-Lean-Assignment-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16f-Lean-Assignment-Lean.ipynb) | Aucune déclarée — compagnon natif du 16f-Py | Le lake `assignment_lean` lu par son certificat (kernel lean4) : valeur d'affectation, couple dual `DualFeasible`, **dualité faible**, **certificat à gap nul**, charpente de correction `KuhnMunkres`, resserrement hongrois `dualFeasible_tighten` en action, 3 exercices avec anti-pièges | 39 (13 code) | **Très haute** | Oui (16f-Py) |
| 17 | [GameTheory-17-MultiAgent-RL-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17-MultiAgent-RL-Python.ipynb) | « Notebooks 1-14, notions de base en RL » — 55 min | MARL : self-play naïf et ses échecs, AlphaGo/AlphaZero, Fictitious Play (Brown 1951) + exploitabilité, NFSP (Heinrich-Silver 2016), PSRO (Lanctot 2017), OpenSpiel à grande échelle (XFP sur Kuhn Poker), **AlphaZero : self-play + MCTS**, 4 exercices | 38 (12 code) | **Très haute** | Oui (C#) |
| 17-cs | [GameTheory-17-MultiAgent-RL-CSharp](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17-MultiAgent-RL-CSharp.ipynb) | Aucune déclarée (twin, from-scratch) | Twin C# : self-play/FP/NFSP/PSRO sur RPS, verdict SOTA de portabilité, comparaison des 4 méthodes ; annexe **pont .NET → PythonNet → OpenSpiel** (#10459) | 26 (12 code) | Haute | Oui (Py) |
| 17b | [GameTheory-17b-Asymmetric-Information-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17b-Asymmetric-Information-Python.ipynb) | « Espérance conditionnelle, équilibre de Nash, utilité espérée et jeux bayésiens » — 90 min | Information asymétrique : quatre réponses institutionnelles à une même maladie ; **Akerlof** (point fixe de participation), **Spence** (signal coûteux, single-crossing), **Rothschild-Stiglitz** (screening concurrentiel, cream-skimming), **Wilson/Miyazaki/Spence** (anticipation bornée), 9 exercices, limites « établit / n'établit pas » | 26 (11 code) | Haute | Non |
| 17c-Lean | [GameTheory-17c-Lean-Lemons-Certificat-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17c-Lean-Lemons-Certificat-Lean.ipynb) | Aucune déclarée — exécute le lake `asymmetric_information_lean` | Le marché des lemons : **certificat formel exécuté** (Lean 4 sans Mathlib) : trois régimes et un point fixe, seuil de pooling caractérisé exactement, balayage du prior, spirale d'Akerlof en mouvement, « preuve par le silence », 3 exercices en échelle | 35 (12 code) | **Très haute** | Non (17b voisin) |
| 17d-Lean | [GameTheory-17d-Lean-Screening-Signaling-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17d-Lean-Screening-Signaling-Lean.ipynb) | Aucune déclarée — compagnon de 17c (quatre autres modules du lake) | Screening (RS 1976 : le témoin perd sur les deux types, non-existence conditionnelle), signaling (Spence 1973 : single-crossing encodé dans un `match`, bornes de Riley), équilibres anticipatoires (Wilson/Miyazaki/Spence : cross-subsidy), pont bayésien vers le BNE | 29 (11 code) | Haute | Non (17c voisin) |
| 17e | [GameTheory-17e-Bayesian-Persuasion-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17e-Bayesian-Persuasion-Python.ipynb) | Aucune déclarée (« strate 7, notebook 25 ») — ~45 min | **Persuasion bayésienne** : deux méthodes concurrentes — programme linéaire sur la loi jointe vs **concavification** sur une grille du simplexe ; trois instances (procureur, contrôle négatif, trois états), contrôle de convergence, seuil où l'information cesse de payer, 3 exercices | 36 (14 code) | Haute | Non |
| 17f | [GameTheory-17f-Market-to-Balance-Sheet-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-17f-Market-to-Balance-Sheet-Python.ipynb) | Aucune déclarée — « 17b prérequis direct » | La **face assureur** de 17b : le contrat (α, β) lu depuis le bilan — prime pure et chargement maximal, crédibilité **Bühlmann-Straub**, ruine **Cramér-Lundberg**, questionnaire de souscription en équivalent **EVSI**, 4 exercices | 27 (10 code) | Haute | Non |
| 18 | [GameTheory-18-Open-Games-et-Lentilles-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-18-Open-Games-et-Lentilles-Python.ipynb) | Aucune déclarée | **Open games et lentilles** (Hedges) : view/update et lois get-put/put-get (avec falsification), composition en série et meilleure réponse composée, boucle où l'update modifie le global, 3 exercices | 27 (11 code) | Haute | Non |
| 18b | [GameTheory-18b-Casser-la-Composition-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-18b-Casser-la-Composition-Python.ipynb) | Aucune déclarée — prolonge 18 | **Casser la composition** : multivocité du plateau (la sélection brise), frontière de contraction de la boucle, régime exact de la boucle GT-18 (jamais contractante), verdict par surface, questions ouvertes | 25 (8 code) | Haute | Non |
| 18c | [GameTheory-18c-Humour-Banc-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-18c-Humour-Banc-Python.ipynb) | Aucune déclarée | **Banc de calibration humour** — le plus gros carnet de la fournée : forme partagée vs stimulus, matrices de confusion naïve/par partage/LLM, **corpus Argumentum** (167 scénarios fetchés + 120 blagues annotées), test de circularité (#13306 : 60 consommés / 107 tenus à l'écart, disjonction prouvée), paires minimales « unfun » (split gelé), verdict SOTA, bilan acceptance #12756 | 65 (33 code) | **Très haute** | Non |
| 19 | [GameTheory-19-Abstraction-a-Dette-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-19-Abstraction-a-Dette-Python.ipynb) | GT-13 (information imparfaite) ; stratégie mixte, exploitabilité, regret — 35 min | **L'abstraction à dette mesurable** (Kroer-Sandholm) : « qu'ai-je le droit d'oublier ? » — abstraire/résoudre/retransporter avec exploitabilité bornée, trois exemples guidés (fusion, atlas des paires, courbe de dette), frontière honnête | 17 (7 code) | Haute | Non |
| 20 | [GameTheory-20-Chemin-Minimal-Robinson-Goforth-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-20-Chemin-Minimal-Robinson-Goforth-Python.ipynb) | Aucune déclarée — Loi II du deuxième voyage | Le **chemin minimal entre jeux** (Robinson-Goforth) : univers fini re-dérivé, six swaps générateurs (permutaèdre des chambres), **constructeur et vérificateur séparé** (témoin), compter les géodésiques, traverser les murs, épaisseur des chambres, 4 exercices | 44 (17 code) | **Très haute** | Oui (20b, 20c) |
| 20b | [GameTheory-20b-Chemin-Minimal-Temoins-Impossibilite-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-20b-Chemin-Minimal-Temoins-Impossibilite-Python.ipynb) | Aucune déclarée — conventions reprises de GT-20 | Le **témoin d'impossibilité** (question duale de 20) : structure produit des chambres, certificat analytique, vérification BFS tronqué, inventaire des triplets IMPOSSIBLE, frontière et bornes, 3 exercices | 30 (13 code) | Haute | Oui (20) |
| 20c | [GameTheory-20c-Chemin-Minimal-3x2-Ordinal-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-20c-Chemin-Minimal-3x2-Ordinal-Python.ipynb) | Aucune déclarée — seconde attestation (ex-24/24b) | **Second substrat** — jeux ordinaux 3×2 : nombres de Fubini (720 tables strictes, 4 683 ordres faibles), trois familles de générateurs, diamètres mesurés, le verdict 2×2 survit au modèle fermé, **généralisation réfutée** (77 760 raccourcis), lemme de décomposition contrôlé par BFS, contrôle négatif, 292 864 géodésiques | 32 (15 code) | Haute | Oui (20) |
| 20d | [GameTheory-20d-Loi-II-Translateur-Life-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-20d-Loi-II-Translateur-Life-Python.ipynb) | Aucune déclarée — seconde jambe de la Loi II | **Synthétiser un translateur Life** : vérificateur indépendant, générateur par énumération exhaustive bornée, cas sans témoin (impossibilité physique), leçon de scope du certificat, contrôle positif (témoin faux injecté), 3 exercices | 25 (10 code) | Haute | Non |
| 20e | [GameTheory-20e-Perplexite-Structurelle-Hashlife-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-20e-Perplexite-Structurelle-Hashlife-Python.ipynb) | Aucune déclarée — consomme `scripts/hashlife` (tranche 3, #19227) | **Perplexité structurelle Hashlife** : instrument `k_trajectory.py`, pentes mesurées en log-log, pourquoi les périodiques courts sont classés PROGRAM-PERIODIC-COLLAPSED, le test Turing-complet qui manque (OTCA, Spartan), verdict falsifiable, bornes de taille de programme | 18 (5 code) | Haute | Non |

**Totaux** : 24 carnets — 750 (286 code). Répartition difficulté : 7 Très haute (16, 16e, 16f-Lean, 17, 17c-Lean, 18c, 20), 17 Haute — la série termine sur le plateau maximal entamé en fournée C. La série s'arrête au bloc 20 : **l'audit est clos sur son périmètre complet**.

## Observations

### Le bloc 16 est le troisième continent de la série

8 carnets sur 24 — derrière le bloc 06 (13, fournée B) et le bloc 15 (9, fournée C), devant tout le reste. Autour du 16-Python, la famille s'étend en sept directions : twin C#, AMD (16b), extraction de revenu (16c), mécanisme réel institutionnel (16d, reins), joueurs LLM réels (16e), affectation optimale en paire algorithmique + certificat formel (16f-Py/16f-Lean). C'est le seul bloc de la série où un même objet (le mécanisme) est décliné jusqu'au pilote empirique **et** au certificat Lean.

### 18c est le plus gros carnet de la série après 13-Py et 15-Py

65, dont 33 code — banc de calibration humour, corpus Argumentum fetché en direct (167 scénarios, 7 catégories) et 120 blagues annotées, test de circularité à la #13306 (scénarios tenus à l'écart, disjonction prouvée), paires minimales avec split gelé avant mesure, verdict SOTA écrit. C'est aussi la **distillation d'un sous-module** (Argumentum) dans la série — écho de 15e/15f (projet étudiant, article) en fournée C, mais à plus grande échelle.

### Le bloc 17 formalise l'information asymétrique de bout en bout

Le lake `asymmetric_information_lean` (Lean 4 **sans Mathlib**) est couvert par deux compagnons : 17c (certificat d'Akerlof : seuil de pooling exact, spirale) et 17d (les quatre autres modules : screening, signaling, anticipation). 17b en pose la version Python pédagogique (4 familles de modèles, 9 exercices), 17e ouvre la persuasion bayésienne (LP vs concavification), 17f referme côté assureur (Bühlmann-Straub, Cramér-Lundberg, EVSI). Cinq carnets qui se citent mutuellement — le maillage le plus dense de la série.

### La série clôt sur l'épistémologie de l'expérimentation

Le bloc 20 (cinq carnets) n'introduit plus de théorie des jeux : il met à l'épreuve la **Loi II du deuxième voyage** (« recoordonner + passer du vérificateur au constructeur »). Constructeur/vérificateur séparés (20), témoin d'impossibilité (20b), second substrat avec généralisation réfutée (20c), translateur synthétisé sur Life (20d), perplexité structurelle comme instrument (20e, tranche 3 de #19227). Le 19, juste avant, pose la dette de représentation mesurable (Kroer-Sandholm). La série finit en méthodologie — cohérent avec un parcours qui a débuté par des jeux 2×2.

### Croix de renum / libellés pour #16231/#14944 (hors scope gradation)

La fournée D porte la **plus forte densité d'en-têtes pré-renum de la série** — 7 carnets sur 24 :

1. **16-cs** : H1 « GameTheory-16-MechanismDesign-Python (C#) » — le titre hérité du twin Python n'a pas perdu son « Python ».
2. **16f-Lean** : H1 « GameTheory 23b » et nav « << 27-Munkres-Assignment (track principal) » — numéros pré-renum (le fichier est 16f, la cible de la nav est le bon fichier sous un mauvais libellé).
3. **16f-Py** : H1 « GameTheory-23 » — pré-renum.
4. **17e** : H1 « GameTheory-25 » + « strate 7, notebook 25 » — pré-renum.
5. **18c** : H1 « GameTheory-24 » — pré-renum.
6. **20b** : H1 « GameTheory 24b » — pré-renum ; 20c le confirme en écrivant « ex-24/24b », donc la renum est connue du bloc, seuls les H1 n'ont pas suivi.
7. **20d** : H1 « GameTheory-21 » — pré-renum.

À noter : la nav de 16f-Lean pointe le **bon fichier** sous le mauvais libellé — les liens sont sains, seuls les numéros affichés datent d'avant #18001.

### Prérequis déclarés : le track principal garde ses plages, les compagnons ne déclarent rien

Seuls 16, 16b, 17, 17b et 19 déclarent des prérequis (plages « 1-13 », « 1-14 » ou renvois ciblés GT-16/GT-11/GT-13) — prolongeant le constat des fournées B et C. Les carnets 16c-16f, 17c-17f, 18-20 fonctionnent en compagnons autodéclarés par leur navigation (« conventions reprises de GT-20 », « 17b prérequis direct »), robuste à la lecture humaine mais invisible pour un auditeur de prérequis automatisé.

## Hors périmètre

- **Aucune fournée suivante** : la série s'arrête au bloc 20, l'audit de gradation est clos sur ses quatre fournées + strate Fondations — **99 carnets au total** (Fondations 15 + A 12 + B 27 + C 21 + D 24), périmètre intégralement couvert. La série a grandi de 6 carnets depuis la renum #18001 (93 à sa date du 2026-09-29), tous absorbés par les fournées C et D.
- **Tableau consolidé** des 99 carnets : conditionné à l'arbitrage #18001 (cf. ledger Fondations), à livrer comme étape finale de l'issue.

## Source des données

- Lecture firsthand des 24 carnets (front-matter + section 1 + navigation) via `git show origin/main:<carnet>` au 2026-10-11, head `cfa6bbaea4ca`.
- Statistiques cellules : extraction JSON par script de session (kernelspec, comptes code/markdown, headers, sections Prérequis).
- Comptage de périmètre : `git ls-tree origin/main MyIA.AI.Notebooks/GameTheory/` filtré blocs 16-20 (16×8, 17×7, 18×3, 19×1, 20×5).

## Voir aussi

- #15615 — issue pivot (plan en fournées A-D)
- `15615-gradation-fournee-a.md` (PR #20288) — carnets 01/04/05
- `15615-gradation-fournee-b.md` (PR #20289) — blocs 06-10
- `15615-gradation-fournee-c.md` (PR #20294) — blocs 11-15
- [15615-gradation-foundations.md](15615-gradation-foundations.md) — carnets 02 + 03 (PR #18195)
- #16231 / #14944 — renum et colonne canonique (destinataires des croix, 7 occurrences en fournée D)
- #18001 — PR `rename GameTheory — 93 carnets` (mergée 2026-09-29), condition du tableau consolidé
