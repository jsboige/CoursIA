# Grille de preuves du projet collectif — Trading algorithmique (socle RNCP41881)

[← QuantConnect](../README.md)

Cadre : certification **RNCP41881 — Expert en finance de marché**. Le syllabus TimeSpice 2026/2027 (M1 BDDSF Oct26, UE05.F) alloue les 17 h 30 du cours à trois compétences affichées sous leur **codage historique** RNCP37437 : `RNCP37437BC02C2.1` (analyse macroéconomique et identification des phases du cycle, 7 h), `RNCP37437BC01C1.5` (valorisation algorithmique d'un produit dérivé, 7 h), `RNCP37437BC01C1.1` (veille scientifique, technologique, économique, réglementaire et environnementale, 3 h 30), plus deux attendus transversaux (risques, restitution). RNCP37437 est **inactive et remplacée par RNCP41881** ; les codes historiques TimeSpice sont conservés dans les supports sans normalisation silencieuse (cf issue #16239).

Référentiels : [RNCP41881](https://www.francecompetences.fr/recherche/rncp/41881/) · [RNCP37437 (inactive)](https://www.francecompetences.fr/recherche/rncp/37437/)

---

## 1. Principe : une preuve par compétence, un artefact par preuve

Une compétence ne se déclare pas, elle se **montre**. Chaque ligne de la grille (§2) associe une compétence à un **artefact précis du groupe** : une section datée du rapport, un notebook exécutable, des lignes du registre de veille. Deux règles découlent de ce principe :

- « Vu en cours » n'est pas une preuve. L'artefact doit être **produit par le groupe** — un notebook du corpus rejoué tel quel ne prouve rien.
- L'artefact doit être **vérifiable sans son auteur** : un lecteur peut l'ouvrir, l'exécuter, ou recompter ses lignes. Ce qui n'est pas vérifiable sans l'auteur n'entre pas dans la grille.

La grille sert dans les deux sens : les étudiants savent exactement ce qui sera examiné ; l'enseignant a un lieu unique de vérification. Elle ne note pas — la traduction en note vit dans le pipeline de notation par cohorte (§6). Elle établit **ce qui est vérifiable**.

## 2. Mapping compétences → artefacts du projet

| Compétence (code historique) | Preuve attendue — artefact précis du groupe | Où s'appuyer dans le corpus | Vérification |
|---|---|---|---|
| **Analyse macro et phases du cycle** (`RNCP37437BC02C2.1`, 7 h) | Section « Diagnostic macro » du rapport : diagnostic **sourcé** du régime actuel (indicateurs nommés, avec dates), hypothèse **falsifiable** d'évolution (quel constat l'infirmerait), conséquences **explicites** pour la stratégie (ligne d'allocation ou budget de risque) | [QC-Py-28b-Macro-Cycle-Regimes](../Python/QC-Py-28b-Macro-Cycle-Regimes.ipynb) : moteur composite borné, taxonomie NBER avancés/concomitants, règle tabulée + override STRESS | Chaque indicateur a une source et une date ; l'hypothèse désigne son propre test ; la conséquence se lit dans le code (paramètre ou garde-fou), pas seulement dans la prose |
| **Valorisation d'un dérivé** (`RNCP37437BC01C1.5`, 7 h) | Notebook comparatif **reproductible sur un même instrument** : Black-Scholes, arbre binomial, Monte-Carlo ; erreur / convergence / temps de calcul mesurés ; lecture marché-liquidité | `QC-Py-06b` (PR #16263) et `QC-Py-29` (PR #16358) : parité put-call, convergence CRR, IC Monte-Carlo, put américain, grecques, scénario de liquidité falsifiable | Le notebook s'exécute de bout en bout ; les trois méthodes portent sur le **même** contrat ; les chiffres cités au rapport sont les outputs du notebook — un écart retoque la preuve |
| **Veille** (`RNCP37437BC01C1.1`, 3 h 30) | Registre à 7 colonnes daté (publication **et** consultation) + au moins 3 synthèses à impact explicite + traçabilité inverse des hypothèses de marché | `docs/PROTOCOLE_VEILLE.md` (PR #16324) : typologie 4 familles, grille qualité binaire 4/5, statuts Intégré / Surveillé / Écarté | Critères §6 du protocole : registre rempli **sur la fenêtre du projet** (pas post-hoc), chaque hypothèse de marché remonte à une entrée datée du registre |
| **Risques de marché et de liquidité** (transversal) | Coûts / slippage / turnover **mesurés dans le backtest final** ; un indicateur ou scénario de liquidité **falsifiable, distinct du risque de marché** ; un stress documenté | Corpus QuantConnect (coûts, slippage, dimensionnement) ; scénario crossover de liquidité de `QC-Py-29` (PR #16358) | Les métriques de coûts figurent dans le tableau final, pas en annexe ; le scénario de liquidité a un chiffre avant/après et un seuil de rejet explicite |
| **Restitution claire et argumentée** (transversal) | Soutenance structurée hypothèse → données → code → résultats → limites ; graphiques lisibles (axes, unités, source des données) | Déroulé et barre de vérification : §5 ci-dessous | Chaque figure projetée répond à « d'où viennent ces données ? » sans hésitation |

## 3. Exigences minimales du projet — non négociables de soutenance

Un projet qui manque **un seul** de ces éléments n'est pas soutenable, quelle que soit la qualité du reste :

1. **Benchmark explicite** : la stratégie comparée à une alternative passive (achat-conservation de l'actif ou du sous-jacent) **sur la même fenêtre**.
2. **Coûts et slippage modélisés** : aucun backtest à coût nul ; le tableau final montre l'effet des coûts (avec et sans).
3. **Métriques standard + fenêtre précise** : Sharpe, CAGR, drawdown maximal, turnover, avec dates de début/fin et période de warm-up explicitée.
4. **Validation hors échantillon ou sous-périodes** : au moins une découpe temporelle que la stratégie n'a pas vue pendant sa mise au point — idéalement reliée aux régimes du diagnostic macro (une sous-période de stress).
5. **Analyse de sensibilité** : au moins un paramètre critique varié (période de signal, seuil, budget de risque) avec l'effet sur les métriques, pas seulement la direction.
6. **Limites honnêtes** : une section dédiée à ce que le backtest **ne prouve pas** — sur-apprentissage résiduel, hypothèses de remplissage des ordres, fenêtre unique, liquidité simulée.

## 4. Contribution individuelle — traçable avant, vérifiée pendant

**Avant la soutenance** : le rapport contient un **tableau de répartition** (membre × artefact — qui a produit quel module, quelle section, quelles entrées de veille). Les commits signés font foi quand ils existent ; le tableau sinon. Un artefact de la grille (§2) sans nom devant lui est une preuve orpheline.

**Pendant la soutenance**, trois gestes de vérification :

1. **Section possédée** : chaque membre présente au moins une section qu'il a produite, en profondeur — pas en lecture de transparents.
2. **Compréhension croisée** : chaque membre doit pouvoir expliquer **une figure qu'il n'a pas produite** — axes, données sources, conclusion. La barre n'est pas la maîtrise du code d'autrui mais la cohérence : savoir ce que la figure montre et pourquoi elle suffit (ou ne suffit pas) à la conclusion du groupe.
3. **Geste en direct** : sur un output du notebook, l'enseignant propose une variation mineure (« si les coûts doublent ? si la fenêtre hors échantillon avance de six mois ? ») ; le membre interrogé prédit le **sens** de l'effet. L'exécution en direct n'est pas exigée — la prédiction argumentée l'est.

Ces critères sont **publics** (ce document) : l'évaluation vérifie ce qui est annoncé, elle ne piège pas.

## 5. Soutenance — déroulé et barre de vérification

| Temps | Section | Artefact projeté | Critère de réussite | Signal d'échec |
|---|---|---|---|---|
| ~5 min | Hypothèse | Diagnostic macro + registre de veille | Hypothèse falsifiable reliée à une entrée datée du registre | « On pense que ça va monter », sans source ni test |
| ~5 min | Données | Fenêtres, univers, warm-up | Périmètre daté, sources nommées | « Les données de QuantConnect », sans plus |
| ~10 min | Code | Notebook / algorithme | Les non-négociables de §3 visibles dans le code ou ses outputs | Backtest sans coûts, sensibilité absente |
| ~10 min | Résultats | Tableau final + benchmark + hors échantillon | Les chiffres du rapport sont les outputs du notebook | Chiffres divergents entre rapport et notebook |
| ~5 min | Limites | Section limites du rapport | Au moins deux limites spécifiques à CE projet | « Pas de limites », ou limites génériques recyclables partout |

## 6. Barème et garde anti-arbitraire

Cette grille définit les **critères vérifiables** ; la traduction en note — collective pour le projet, individuelle pour la vérification §4 — vit dans le pipeline de notation par cohorte : moteur générique [GradeBookApp](../../../GradeBookApp/configs/README.md), configurations privées par cohorte. La garde anti-arbitraire tient en une ligne : **un critère qui n'est pas vérifiable au sens de §1 n'entre pas au barème**. Si un correcteur veut noter quelque chose que cette grille ne permet pas de vérifier, la grille doit d'abord être amendée (et versionnée) — pas contournée.

## 7. Anti-patterns de l'évaluateur

- **Preuve par affirmation** : « on a fait la veille » sans registre daté — la grille ne crédite que l'artefact.
- **Artefact hors projet** : un notebook du corpus rejoué comme preuve — la preuve est un artefact du groupe (§1).
- **Chiffres divergents** : le rapport et le notebook ne disent pas la même chose — retoquer la ligne concernée, pas « arrondir ».
- **Soutenance en solo** : un membre parle pour le groupe — le geste de compréhension croisée (§4.2) est là pour ça.
- **Limites décoratives** : « le marché est incertain » — une limite est spécifique (quelle hypothèse, quelle fenêtre, quel coût).

See #16239 (livrable 4 — grille de preuves ; livrable 1 : QC-Py-28b, PR #16332 ; livrable 2 : QC-Py-06b, PR #16263, et QC-Py-29, PR #16358 ; livrable 3 : protocole de veille, PR #16324).
