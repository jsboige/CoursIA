# Percolation — du géant du tore à la géométrie de l'amas critique

[↑ Applications](../README.md)

On garde chaque arête d'un réseau avec une probabilité $p$, indépendamment des autres. En dessous d'un seuil, le réseau reste en morceaux. Au-dessus, une composante géante absorbe l'essentiel des sommets. La sous-série mesure cette transition sur des tores finis, en Python, et formalise en Lean 4 ce qui se prouve sur un graphe fini. Elle part du régime supercritique, s'installe au point critique, confronte la mesure au théorème de *supercritical sharpness*, puis mesure la forme de l'amas critique.

Les carnets suivent une même règle : un tore fini n'est pas le réseau infini de la théorie. Les valeurs de la littérature servent de cible, chaque mesure est rapportée avec son écart, et un carnet peut conclure qu'il ne mesure pas ce qu'il visait. La sous-série s'adresse à des étudiants de master qui connaissent les graphes, les probabilités discrètes et l'ajustement d'une droite en échelle log-log. Les carnets Lean demandent une première lecture d'énoncés Lean 4.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : suivez le parcours principal dans l'ordre des numéros. Percolation-01 se lit sans prérequis de physique statistique.
- **Vous creusez un palier** : la section « Approfondissements » décrit les extensions de taille du palier 03 et les exercices de chaque carnet.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » sépare ce que le lake prouve de ce que le théorème de référence énonce, et dit ce que les mesures laissent ouvert.

## Parcours principal — Master

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Percolation-01 — Le géant au-dessus du seuil](Percolation-01-Supercritique-Python.ipynb) | La percolation de liens sur un tore carré de 22 × 22 sommets, dont le seuil exact sur le plan infini est $p_c = 1/2$. Trois régimes, vus sur une figure puis mesurés : la fraction du géant vaut `0.167`, `0.695` puis `0.947` pour $p$ = 0,40, 0,50 et 0,60. La queue finie de l'origine, $P(5 \le \lvert C_o\rvert < \infty)$, vaut `0.690`, `0.403` puis `0.003` : elle s'éteint au-dessus du seuil. Un réseau hexagonal, de seuil plus haut, confirme le phénomène à distance réduite égale du seuil. Le carnet sépare trois niveaux de preuve : le théorème, le proxy fini, l'analogie. | Master : graphes, composantes connexes. Outils : numpy, networkx, matplotlib. | Exercices : courbe du géant, profil isopérimétrique, degré 3. |
| 02 | [Percolation-02 — Le noyau fini de percolation, prouvé en Lean 4](Percolation-02-Lean.ipynb) | La lecture du lake `percolation_lean` depuis le noyau Lean, par `#check`, `#print axioms` et `#eval`. Le vocabulaire : arêtes ouvertes, ensembles fermés, composante, frontière. L'inégalité de Harris–Kleitman sous la mesure uniforme ($p = 1/2$) : deux événements croissants sont positivement corrélés. La connexité est un événement croissant, donc les connexions s'entraînent. Le profil de frontière calculé sur le triangle $C_3$ (toujours `2`) et sur le carré $C_4$ (`2` pour deux sommets voisins, `4` pour deux sommets opposés). Les preuves ne dépendent que des trois axiomes standard. | Master : lecture d'énoncés Lean 4. Noyau Lean 4. | Exercices : audit d'axiomes, frontière du triangle, configuration complète. |
| 03 | [Percolation-03 — Au point critique : exposants finis et loi de taille](Percolation-03-Critique-Python.ipynb) | Un balayage de tores de côté $L$ = 8 à 64, de cinq valeurs de $p$ autour de 1/2 et de 32 graines. La densité du géant à $p_c$ suit $L^{-\beta/\nu}$ : l'ajustement donne `0.0995` pour une cible de 5/48 ≈ 0,1042, avec un $R^2$ de `0.9436`, sous le seuil que le carnet s'était fixé. L'exposant $\tau'$ de la distribution des tailles reste hors de sa bande, mais décroît vers sa cible quand $L$ grandit (`2.281` à `2.135`). Le seuil fini $p_c(L)$ monte vers 1/2 : `0.4527`, `0.4737`, `0.4885`. Le carnet tient le compte de ses critères d'acceptation, atteints ou non. | Master : lois d'échelle, régression log-log. Outils : numpy, networkx, scipy, matplotlib. | [03b](Percolation-03b-Critique-L128-L256.ipynb) et [03c](Percolation-03c-Critique-L512.ipynb) : les mêmes mesures à plus grande taille. |
| 04 | Percolation-04 — Sharpness : [la mesure en Python](Percolation-04-Sharpness-Python.ipynb) et [la preuve finie en Lean 4](Percolation-04-Sharpness-Lean.ipynb) | **Python** : 1024 simulations sur des tores de côté 64 à 512. La queue $\Psi(n) = P(\lvert C_o\rvert \ge n)$, son taux de décroissance $\alpha(L, p)$, puis la confrontation à la loi $\alpha \sim (p - 1/2)$ tirée du théorème de sharpness supercritique. Le verdict est négatif sur ce balayage : les pentes log-log sortent entre `-1.068` et `-1.393`, là où la cible vaut 1. **Lean** : le module `Sharpness` prouve une inégalité de sharpness finie par comptage. La part des configurations qui confinent la composante d'un sommet à $k$ sommets est bornée par une somme de $2^{-\lvert\delta A\rvert}$ sur les candidats $A$. Il ajoute la forme mixte de Harris–Kleitman : un événement croissant et un événement décroissant sont anti-corrélés. Témoins calculés : au plus `2` configurations sur 8 pour le triangle, `4` sur 16 pour le carré. | Master : queues de distribution ; lecture d'énoncés Lean 4. Outils : numpy, networkx, scipy, matplotlib ; noyau Lean 4. | Exercices du carnet Lean : frontière pleine, anti-corrélation, exactitude de la borne. |
| 05 | [Percolation-05 — La géométrie de l'amas critique : dimension fractale et effondrement d'échelle](Percolation-05-Dimension-Fractale-Effondrement-Python.ipynb) | Un union-find écrit à la main, confronté à `scipy.sparse.csgraph` : aucun désaccord sur 60 instances. La dimension fractale par deux routes indépendantes : la masse à $p_c$ (`1.8726`, erreur bootstrap `0.0138`) et le comptage de boîtes (`1.8659`), pour une valeur citée de 91/48 ≈ 1,8958. L'effondrement d'échelle rendu mesurable par une dispersion : le minimum tombe à $\nu^* = 1{,}375$ (`0.0287`), contre `0.0945` à $\nu = 2$. Une seconde route, la pente en $p_c$, donne $\nu$ = `1.3201` une fois $d_f$ retiré. Le contrôle croisé $d_f = 2 - \beta/\nu$ relie ces mesures à celles du palier 03. | Master : physique statistique, lois d'échelle. Outils : numpy, scipy, matplotlib. | Exercices : $d_f$ hors du point critique, rôle de la normalisation, susceptibilité. |

## Approfondissements — Master et Recherche

### Autour de 03 : la même mesure à plus grande taille

Les exposants du palier 03 sont mesurés sur des tores trop petits pour atteindre leur valeur asymptotique. Les carnets 03b et 03c reprennent le même protocole, avec les mêmes graines, et ajoutent des tailles.

- [03b — Extensions L = 128 et L = 256](Percolation-03b-Critique-L128-L256.ipynb). L'ajustement de $\beta/\nu$ passe à six tailles et donne `0.1081`, avec un $R^2$ de `0.9643`. Le seuil fini poursuit sa montée, jusqu'à `0.4984` à $L = 256$. L'exposant $\tau'$, lui, ne converge pas : `2.163` puis `2.183`.
- [03c — Extension à L = 512](Percolation-03c-Critique-L512.ipynb). Sur sept tailles, $\beta/\nu$ vaut `0.1079` ($R^2$ de `0.9773`, erreur type `0.0074`) : la mesure est stabilisée, à portée de la cible. L'exposant $\tau'$ s'écarte au contraire (`2.913` à $L = 512$). Le carnet en tire la leçon : un exposant qui bouge quand on change la taille du réseau n'est pas encore mesuré.

Ils se lisent ensemble : c'est la même mesure à deux ordres de grandeur du réseau.

### Autour de 04 : compter et échantillonner

Le palier 04 est porté par une paire de carnets jumeaux. Le carnet Lean compte exactement des configurations sur de petits graphes ; le carnet Python échantillonne de grands tores. Le premier prouve une inégalité, le second échoue à retrouver une loi d'échelle sur la fenêtre mesurée. Ses limites sont écrites : seuils $n$ trop petits devant la taille du géant, ajustement à un seul exposant, tailles bornées à $L = 512$.

### Exercices des carnets

- **Percolation-01** : tracer la fraction du géant en fonction de $p$, tester le profil isopérimétrique en dimension 3, comparer le degré 3 au degré 4.
- **Percolation-02** : auditer les axiomes de la corrélation des connexions, calculer la frontière d'une paire du triangle, appliquer le lemme isopérimétrique en configuration complète.
- **Percolation-03** : fraction d'arêtes ouvertes, dispersion de la fraction du géant, sensibilité de $\tau'$ à la fenêtre d'ajustement.
- **Percolation-04 (Lean)** : frontière pleine d'une paire adjacente, hypothèses de l'anti-corrélation, exactitude de la borne sur le triangle.
- **Percolation-05** : dimension fractale au-dessus du seuil, effondrement sans la correction $L^{d_f}$, exposant $\gamma/\nu$ par la susceptibilité.

Les cellules d'exercice s'exécutent sans erreur tant qu'elles ne sont pas complétées.

## Installation — pratique, tous niveaux

Les carnets Python tournent sur le noyau `python3`, sans GPU.

```bash
python -m pip install jupyterlab ipykernel numpy scipy networkx matplotlib
jupyter lab MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-01-Supercritique-Python.ipynb
```

Les tirages sont semés. Les balayages de grande taille prennent plusieurs minutes : le carnet 03c simule des tores de 512 × 512 sommets, et le carnet 04 Python imprime `267.4s` pour ses 1024 simulations.

Les carnets Lean demandent Lean 4 et le lake [`percolation_lean/`](percolation_lean/), qui dépend de Mathlib. Ils déclarent un noyau Lean propre au lake, démarré depuis sa racine. Sur un autre poste, installez le noyau Lean 4 générique puis exécutez le carnet depuis le répertoire du lake : la procédure est décrite dans [l'installation Linux et macOS](../../../../docs/reference/setup-linux-macos.md) et dans [la référence des noyaux](../../../../docs/reference/kernels-runtime.md).

## Pour aller plus loin — Recherche

**Formalisations Lean.** Le lake [`percolation_lean/`](percolation_lean/) porte un noyau fini de percolation prouvé sans `sorry` : configurations d'arêtes, connexité, composantes, frontière isopérimétrique finie, inégalité de sharpness finie (`card_smallClusterEvent_le`). Ses modules sont `Basic`, `Connectivity`, `Components`, `Boundary`, `Examples` et `Sharpness`, chacun avec un jumeau anglais. Le socle reste uniforme ($p = 1/2$, mesure de comptage) et fini. Le cas Bernoulli-$p$ général, la grille infinie et l'existence d'un seuil critique sont hors de sa portée.

**Le théorème et son proxy.** Le résultat de référence borne, pour la percolation supercritique sur un graphe transitif infini, la probabilité que l'origine appartienne à un amas fini de grande taille. Les carnets mesurent un proxy sur tore fini, où « fini » se lit « qui ne s'enroule pas ». Aucun ne démontre le théorème, et le palier 04 dit que sa fenêtre de mesure ne permet pas d'en retrouver la loi d'échelle.

**Ce qui reste ouvert dans les mesures.** L'exposant $\tau'$ n'est stabilisé à aucune taille atteinte. L'exposant $1/\nu$ tiré du seuil fini est ajusté sur trois tailles seulement, loin de l'asymptote. Le palier 05 retrouve $\nu$ par deux routes, mais la valeur dépend de la dimension fractale utilisée pour normaliser : `1.375`, `1.400` ou `1.425` selon qu'elle est citée ou mesurée.

**Une analogie, pas une identité.** Percolation-01 et Percolation-03 relèvent un pont de structure avec le modèle d'adoption collective de la série [ICT](../../../IIT/ICT-Series/README.md) : une variable continue, et un changement de nature du plus grand objet quand elle franchit un seuil. Les deux modèles restent distincts.

**D'où viennent les exposants exacts.** Percolation-05 rappelle que la percolation en dimension 2 est une limite du modèle de Potts, et que ses exposants ont été obtenus par la théorie des champs conformes puis étayés par les processus SLE. Les carnets citent ces valeurs ; ils ne les dérivent pas.

## Ressources — tous niveaux

- *Introduction to Percolation Theory* (2ᵉ éd., 1994) : le manuel de référence que citent les carnets 01 et 03, pour les seuils et les exposants exacts.
- H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*, Comm. Math. Phys. 74, 41–59 (1980).
- Diskin, Easo, Radhakrishnan, Sudakov, Tassion, *Supercritical sharpness of percolation*, arXiv:2603.03257 (math.PR, CC-BY 4.0) : le théorème de la section 3.0 des carnets 01 et 04.

[↑ Applications](../README.md) · [Série Probas](../../README.md) · [Catalogue du dépôt](../../../../COURSE_CATALOG.generated.md)
