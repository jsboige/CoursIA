# Hoel vs Pearl sur ICT-32 — verdict de la confrontation (c.1111)

Issue : [#19508](https://github.com/jsboige/CoursIA/issues/19508) — `feat(ict,#16620)` P6 reporté. Suite de l'EPIC [#16620](https://github.com/jsboige/CoursIA/issues/16620) (« Digestion causalité — cap Shap XAI + fair-ML causal + jonction XAI↔Pearl », CLOSED 06/10, P1-P5 livrés) ; le P6 confrontait l'apportionment de Hoel (information effective, `Causal Emergence 2.0`, arXiv:2503.13395) à la décomposition contrefactuelle de Pearl (do-calculus, ATE, CDE) sur le substrat de [ICT-32](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/IIT/ICT-Series/ICT-32-StratificationCausaleLife-Python.ipynb). Ce mémo tranche avec des chiffres firsthand.

## 1. Les deux notions mesurent des objets distincts

**Hoel — apportionment et effectiveness** (Hoel, 2025, *Causal Emergence 2.0*) :

- Sur une TPM $P(Y \mid X)$ où $X$ parcourt un alphabet fini, on définit le **déterminisme** $\det = \sum_x \max_{y} P(y \mid x) / n$, la **dégénérescence** $\deg = \left( \sum_y \max_x P(y \mid x) - 1 \right) / (n - 1)$, et l'**effectiveness** $\mathrm{eff} = \det - \deg$, normalisée dans $[0, 1]$.
- L'**information effective** $EI = \mathrm{eff} \cdot \log_2 n$ mesure, en bits, le gain d'un état sur l'aléa uniforme.
- L'**apportionment glouton** `greedy_apportionment` cherche la partition qui maximise l'effectiveness — l'échelle où le système est le mieux décrit causalement.
- L'output est **une mesure globale** : effectiveness = « à quel point chaque cause détermine-t-elle son effet, et à quel point les causes sont-elles distinguables par leur effet ».

**Pearl — contrefactuels le long d'un chemin causal** (Pearl, 2009, *Causality*) :

- Sur un **DAG** $G = (V, E)$ avec des variables observées, l'**effet total moyen** $\mathrm{ATE} = \mathbb{E}[Y \mid do(X = 1)] - \mathbb{E}[Y \mid do(X = 0)]$ isole la contribution de $X$ sur $Y$.
- Le **back-door criterion** ajuste sur un ensemble $Z$ qui bloque les chemins non-causaux : $P(Y \mid do(X)) = \sum_z P(Y \mid X, z) P(z)$.
- L'**effet direct contrôlé** $\mathrm{CDE}_{x, z}(Y)$ fixe $X = x$ et $Z = z$, regarde la distribution de $Y$.
- L'output est **une mesure contrefactuelle** : la variation de $Y$ quand on fixe $X$, intégrée sur les parents.

**Le point de jonction nominal** : Hoel et Pearl mesurent tous deux « combien l'état du système détermine-t-il son avenir », Pearl en contrôlant un sous-ensemble de causes, Hoel en agrégeant toute la transition. **Mais** Hoel agrège sur tout $X$ sans intervention ; Pearl découpe l'effet en chemins par des $do(\cdot)$.

## 2. Le substrat d'ICT-32 est déterministe — la distinction s'effondre

Le substrat canonique d'ICT-32 est la fonction successeur de B3/S23 sur un tore $k \times k$ : pour toute grille $G_t$, $G_{t+1}$ est **une fonction déterministe** $\delta(G_t)$. Conséquences :

1. **$P(Y \mid X)$ est une distribution delta** : pour tout $X = G_t$, $P(Y = \delta(X) \mid X) = 1$ et toutes les autres valeurs ont probabilité 0.
2. **$\mathrm{ATE} = P(Y \mid X = 1) - P(Y \mid X = 0)$** se réduit à la comparaison de **deux valeurs déterministes** — pas d'intégration de bruit, pas de variance contrefactuelle, pas d'incertitude sur l'effet.
3. **$\det = 1$ sur toute trajectoire isolée** : le déterminisme Hoel atteint son maximum (mesuré : `det = 1.000` sur le glider 64 états, ligne 6 d'ICT-32).
4. **L'apportionment `greedy_apportionment` rend $\mathrm{EC} = 0$ en une passe** sur une trajectoire isolée (mesuré, ligne 11 d'ICT-32 : `EC = 0.000`) : aucune macro ne bat le micro parce que le micro est déterministe, point.

Sur un substrat déterministe, **Hoel et Pearl coïncident trivialement** : les deux mesurent la même fonction successeur $\delta$, l'un en agrégeant, l'autre en contrôlant ; les deux retournent la même dynamique, la même réponse au $do(\cdot)$. **La confrontation n'a rien à apprendre** : on compare deux notations pour la même chose.

## 3. Le seul objet où Hoel et Pearl pourraient diverger : la dégénérescence d'ensemble

ICT-32 mesure aussi un objet où Hoel est non-trivial : la TPM **d'ensemble** `torus_ensemble_tpm(k)` qui mappe chaque graine $G_t$ à son successeur **observé** parmi les $2^{k^2}$ graines. Cette TPM agrège la règle sur tout le tore — et c'est elle qui révèle la dégénérescence (12 des 16 graines du tore $2 \times 2$ mènent à la grille vide, $\deg = 0.672$, $\mathrm{eff} = 0.328$ ; ligne 14 d'ICT-32).

**Mais** cette TPM agrège des graines **distinctes** vers le même successeur. Ce n'est pas une TPM au sens d'une chaîne de Markov temporelle (où l'état au temps $t+1$ ne dépend que de l'état au temps $t$, ce qui est trivialement vérifié) : c'est une TPM **sur l'ensemble des conditions initiales**, qui révèle la non-injectivité de la règle $\delta$.

**Pearl sur cette TPM** : on peut la voir comme un DAG $G : X \to Y$ où les 16 graines $X$ sont les causes et les 5 successeurs $Y$ sont les effets. L'ATE de Pearl se réduit à : $E[Y \mid do(X = x)] = \delta(x)$, intégré sur $x \in \{0, 1\}^{4}$. C'est l'identité. **Aucun chemin causal à décomposer** : le DAG a deux nœuds et un arc, $\deg_{\text{Pearl}} = 1$ (chaque cause va à un effet), il n'y a pas de *confounding* au sens de Pearl puisque $X$ est la cause **unique**.

**Hoel sur cette même TPM** : effectiveness $= 0.328$, dégénérescence $= 0.672$, plusieurs $X$ partagent leur successeur. Mais c'est une mesure **d'ensemble**, pas contrefactuelle — Hoel mesure « est-ce que la fonction est injective », pas « est-ce qu'une intervention sur $X$ change $Y$ ».

**La confrontation ne tient toujours pas** : Hoel mesure la concentration de la fonction successeur, Pearl découperait des chemins causaux. Sur le tore $2 \times 2$, il n'y a qu'un chemin par arête du DAG, et ce chemin est trivialement déterministe.

## 4. Pourquoi ICT-32 cite déjà `do(...)-granulé` (ICT-9, ICT-19) — sans Pearl explicite

ICT-9 et ICT-19 utilisent **une notion opérationnelle de $do(\cdot)$** : l'ablation d'une cellule (ICT-9 sur Gray-Scott, ICT-19 sur le même substrat) et la mesure du recouvrement post-intervention. Ce geste est exactement l'**intervention Pearl** $do(G_1 = \emptyset)$ — et il a un sens parce que la **stochasticité** vient du substrat (Gray-Scott est continu, l'ablation coupe le motif de manière reproductible).

ICT-32 sur le Jeu de la Vie n'a **pas** cette propriété : B3/S23 est binaire et déterministe, l'ablation d'une cellule est une fonction déterministe vers un successeur déterministe. ICT-31 le constate honnêtement (ligne 132 du README ICT-Series) : « GOL est le **seul non-réparateur** — une cellule retirée détruit le glider sans régénération ».

**ICT-33** ouvre la stochasticité par les *random soups* : la TPM empirique devient stochastique ($\det = 0.334$ au lieu de $1.000$ ; ligne 134 du README), et la partition par destin devient un objet mesuré (au lieu d'un squelette). C'est **sur ICT-33** qu'une confrontation Hoel/Pearl deviendrait non-triviale — la stochasticité rend l'ATE non-trivial et permet le back-door adjustment sur des sous-graphes.

## 5. Verdict

La confrontation Hoel vs Pearl **ne tient pas** sur le substrat d'ICT-32 :

- Le substrat est **déterministe** ($P(Y \mid X) = \delta$ distribution delta), donc Hoel (mesure d'aggregation) et Pearl (mesure contrefactuelle) coïncident trivialement.
- Il n'y a pas de DAG non-trivial (deux nœuds, un arc) : la décomposition en chemins de Pearl n'a rien à décomposer.
- La seule grandeur Hoel non-triviale (la dégénérescence d'ensemble) **est** la non-injectivité de la règle — un objet qui n'a pas d'analogue contrefactuel direct, parce que les « causes » multiples sont des conditions initiales distinctes, pas des chemins causaux.

**Recommandation** : clore #19508 par l'option « ne tient pas » du body — une phrase dans le README de la série ICT qui le constate, et ce mémo comme traçabilité. Si la confrontation devient intéressante, **ICT-33** (random soups, stochasticité bathopée) est le substrat où elle mérite d'être posée : $\det = 0.334$, plusieurs causes vers plusieurs effets, le back-door devient un objet à optimiser. Mais c'est un autre grain, et le présent mémo est le constat borné.

## 6. Critère de fermeture de #19508

L'issue est ouverte jusqu'à décision tranchée par **écrit** sur l'issue ou par PR matérialisant la décision. **Ce mémo tranche par « ne tient pas » avec preuve** :

1. Le substrat est déterministe (mesuré sur ICT-32, $\det = 1.000$ par trajectory, $\det = 1.000$ par graine avec dégénérescence triviale).
2. Le DAG réduit à `G : X → Y` n'a rien à décomposer.
3. La dégénérescence Hoel d'ensemble est un objet non-contrefactuel.
4. ICT-33 (random soups, $\det = 0.334$) est le substrat où la question devient non-triviale — ailleurs que dans le scope de cette P6.

Une fois ce PR mergé (README amendé d'une phrase + ce mémo archivé), l'option `See #19508` côté EPIC #16620 peut sortir du pour l'audit, et l'option « ne tient pas » peut être marquée sur l'issue. La clôture effective reste au coord/adjoint.

## Sources first-hand

- `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-32-StratificationCausaleLife-Python.ipynb` (lecture intégrale ; sorties mesurent $\det = 1.000$, $\deg = 0.672$, $\mathrm{eff} = 0.328$ sur tore $2 \times 2$).
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/causal_emergence.py` (lecture intégrale ; module `greedy_apportionment`, `partition_profile`, `causal_profile`).
- `MyIA.AI.Notebooks/IIT/ICT-Series/README.md` (l.132-134 — la triade ICT-31/32/33 et le constat « GOL non-réparateur »).
- `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-31-ContrasteTroisSubstrats-Python.ipynb` (le constat que $G$, le seul transporteur, est aussi le seul sans régénération post-ablation).
- `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-33-SoupCollisions-Python.ipynb` (le passage à la stochasticité : $\det = 0.334$ sur random soups).
- Body de #19508 (l'option « ne tient pas » est explicite : « *si elle ne tient pas : une phrase dans le README de la série ICT qui le dit et pourquoi, puis fermeture de l'issue.* »).

## Chevauchement de claims

Pas de claim tiers sur #19508 (vérifié 06/10 20:30Z). Claim posé (cid 6024717935, 06/10 20:30Z, paths scoped : `docs/research/c1111-hoel-pearl-*.md`, `MyIA.AI.Notebooks/IIT/ICT-Series/README.md`). Pas de PR ouverte sur ce périmètre.

## Convention honnête

**Aucun engagement d'exécution de P6 ailleurs que sur ICT-32** dans ce mémo. La confrontation pourrait redevenir intéressante sur ICT-33 (substrat stochastique), mais c'est un autre grain, hors scope de cette P6.