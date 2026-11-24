# Intégrales — calculer une intégrale de Feynman, et dire ce qu'on a certifié

[↑ Physique](../README.md)

Les corrections radiatives de la physique des particules se ramènent à des intégrales à boucles. Cette sous-série en calcule plusieurs, des plus simples aux premières qui résistent : le triangle scalaire à une boucle, le diagramme « sunrise » à deux boucles, la bulle qui diverge, puis la courbe elliptique cachée dans le sunrise. Chaque intégrale est calculée par plusieurs voies, en haute précision, et chaque voie est contrôlée contre les autres.

L'enjeu est autant la méthode que le résultat. Les carnets pratiquent trois règles. Un outil se valide contre une valeur connue avant de servir : c'est la « vérité plantée ». Une constante ne se cherche que dans un ensemble déclaré à l'avance, et un échec s'écrit « pas de forme fermée identifiée ». Un contrôle doit prouver qu'il sait échouer. Aucun bagage en théorie quantique des champs n'est requis : la représentation paramétrique est dérivée dans le premier carnet. Il faut être à l'aise avec les intégrales multiples et les changements de variables.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : suivez le parcours principal dans l'ordre des numéros. Intégrales-01 pose le vocabulaire et les trois règles de méthode.
- **Vous creusez un palier** : la section « Approfondissements » décrit, carnet par carnet, les contrôles, les refus documentés et les exercices.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » dit ce qui est identifié sans être dérivé, ce qui est cité sans être reproduit, et où la série s'arrête.

## Parcours principal — Licence avancée et Master

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Intégrales-01 — L'intégrale triangle scalaire à une boucle](Integrales-01-Triangle-Scalaire-Python.ipynb) | La représentation de Feynman du triangle, dérivée pas à pas. Trois voies de calcul du même nombre : quadrature sur le simplexe, substitution qui change le simplexe en rectangle, intégration exacte d'une variable. Elles rendent toutes `1.3427652838373602509494` pour $J(1, 2, 2{,}5)$. Sur la famille isocèle, une forme fermée est identifiée, $J(1,1,2-2\cos\psi) = 2\,\mathrm{Cl}_2(\psi)/\sin\psi$, puis vérifiée sur six angles à la précision de travail. Deux cas sont exacts : $2G$ (constante de Catalan) à 90° et $\frac{4}{\sqrt 3}\mathrm{Cl}_2(\pi/3)$ à 60°. | Licence avancée : intégrales multiples, changements de variables. Outils : mpmath, numpy, matplotlib. | Les contrôles qui mordent et la portée du mot « certifié » (voir « Autour de 01 »). |
| 02 | [Intégrales-02 — Le diagramme sunrise à masses égales : la sortie des polylogarithmes](Integrales-02-Sunrise-Masses-Egales-Python.ipynb) | Le sunrise à masses égales en dimension 2 : deux boucles, et le même polynôme que le triangle. Quatre voies de calcul s'accordent : deux coïncident chiffre à chiffre, la voie de Cheng–Wu suit à `1.37e-20`, la voie hyperbolique à `8.94e-16`. À moment nul, l'intégrale vaut `2.343907238689458890602`, exactement la valeur $J(1,1,1)$ du carnet 01 : cette ancre contrôle toute la paramétrisation. La voie hyperbolique montre où se loge la structure elliptique. | Master : le carnet 01. Outil : mpmath. | Le facteur 2 attrapé par l'ancre et le refus d'identifier une forme fermée (voir « Autour de 02 »). |
| 03 | [Intégrales-03 — La bulle et la première divergence](Integrales-03-Bulle-Premiere-Divergence-Python.ipynb) · [jumeau C#](Integrales-03-Bulle-Premiere-Divergence-CSharp.ipynb) | Deux propagateurs en dimension 4 : la plus petite intégrale qui diverge. Coupée à une échelle $\Lambda$, elle croît comme $\pi^2 \ln \Lambda^2$. Le coefficient $\pi^2$ est mesuré avec un écart relatif de l'ordre de $7 \times 10^{-14}$. La constante finie vaut aussi $\pi^2$ ; elle est rattachée à une intégrale calculable à la main, $\int_0^1 \ln\frac{1}{x(1-x)}\,dx = 2$, et mesurée à $3 \times 10^{-25}$. Une soustraction donne enfin une quantité finie qui dépend d'une échelle, $B_R(\mu^2) = \pi^2(1 + \ln \mu^2)$. | Master : coordonnées sphériques en dimension 4. Outils : mpmath, pandas. | Deux écarts de nature différente, à ne pas confondre (voir « Autour de 03 »). |
| 04 | [Intégrales-04 — Le rung elliptique du sunrise](Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb) | Retour au sunrise, pour faire sortir sa courbe elliptique du calcul. L'intégrale interne se fait en fonctions élémentaires. Il reste une intégrale sur la quartique $y^2 = b(\chi)\,c(\chi)$, dont les racines sont explicites. Les périodes de la courbe sont mesurées par quadrature, puis ramenées à l'intégrale elliptique complète $K$ : pour $s = 9$, le module vaut `0.00806504495005` et le rapport des périodes est retrouvé avec un écart relatif de `6.61e-18`. Ce rapport varie avec $s$ : la courbe dépend de l'échelle. | Master : les carnets 01 et 02, notions sur les intégrales elliptiques. Outil : mpmath. | Les deux dégénérescences de la courbe et le module « naïf » (voir « Autour de 04 »). |

## Approfondissements — Master et Recherche

La sous-série n'a pas de palier lettré. Ses approfondissements sont des sections des carnets.

### Autour de 01 : des contrôles qui mordent

Les trois voies du carnet partent de la même représentation de Feynman. Leur accord détecte une erreur de mise en œuvre, comme un jacobien faux, et non une erreur commune de paramétrisation. Le carnet l'écrit, puis ajoute des contrôles qui portent sur l'objet lui-même.

Le premier valide l'outil avant de s'en servir. La fonction de Clausen s'obtient dans mpmath par `clsin(2, z)`, et deux appels voisins rendent autre chose. La cellule la vérifie contre des valeurs connues avant toute identification. Le second est un contrôle négatif : un mauvais appariement doit échouer, et il échoue avec un écart relatif de `0.3333`. Son point aveugle est nommé : à l'angle de 90°, les deux appariements coïncident, et un contrôle en ce seul point serait passé.

La section 7 du carnet fixe la portée du mot « certifié ». La précision arbitraire n'est pas une arithmétique à bornes d'erreur garanties. La forme fermée est identifiée numériquement, sa dérivation analytique n'est pas donnée.

### Autour de 02 : le facteur 2 et le refus d'identification

En coordonnées hyperboliques, le domaine naturel ne couvre que la moitié de l'intégrale. Le facteur 2 manquant est attrapé parce que l'ancre à moment nul fournit une valeur de référence indépendante.

Le carnet tente ensuite d'identifier une forme fermée, dans deux familles déclarées avant la recherche. Aucune ne tient : le coefficient attendu dérive dans la première, la limite ne converge pas dans la seconde. Le carnet conclut « pas de forme fermée identifiée » plutôt que d'arranger une coïncidence à trois chiffres. La nature elliptique de l'objet est établie, sa valeur fermée ne l'est pas.

### Autour de 03 : un artefact constant, un écart qui décroît

Deux écarts apparaissent dans le calcul de la bulle, et ils n'ont pas la même cause. Le premier vient de la quadrature : une règle qui enjambe le point anguleux $k = p$ laisse une erreur de `0.0002077`, identique à toutes les coupures. Un contrôle à quatre cases montre que changer de variable n'y change rien, et que séparer le point anguleux suffit. Le second est physique : la forme fermée s'écarte de la voie directe d'environ 3,3 % à $\Lambda = 2$, puis de 0,10 % à $\Lambda = 8$, en décroissant comme $1/\Lambda^2$.

Le carnet vérifie aussi la mesure de la sphère avant de s'en servir, et documente un refus : la constante finie ne contient ni la constante d'Euler ni $\ln 4\pi$, qui appartiennent à un autre schéma de régularisation.

### Autour de 04 : dégénérescences et module « naïf »

Deux limites bornent la famille de courbes. Quand $s$ tend vers 0, une racine s'échappe à l'infini et l'intégrale rejoint la valeur d'ancrage du carnet 01. Quand $s$ tend vers l'infini, deux racines se rejoignent, et le module suit la loi $k^2 \sim 16/s^3$, contrôlée jusqu'à $s = 10^8$.

Le module testé au carnet 02 est mesuré comme différent de celui de la quartique. Le carnet le présente comme une mesure sur deux courbes apparentées, pas comme une correction. La forme fermée de la littérature, en dilogarithmes elliptiques, est citée sans être reproduite.

### Exercices des carnets

- **Intégrales-01** : l'inégalité de Cauchy–Schwarz et les cinématiques réalisables, les deux limites dégénérées de la famille isocèle, le protocole complet d'identification sur la constante 2.
- **Intégrales-02** : les exposants paramétriques en dimension 4, la monotonie de $I(s)$, le facteur 2 de la voie hyperbolique.
- **Intégrales-03** : la dépendance en $p^2$, la bulle en dimension 3, la forme radiale retrouvée par différences finies.
- **Intégrales-04** : la formule interne sur d'autres paramètres, la réduction à $K$ pour $s = 36$, les racines pour $s = 10^8$.

Les cellules d'exercice s'exécutent sans erreur tant qu'elles ne sont pas complétées.

## Installation — pratique, tous niveaux

Les carnets tournent sur le noyau `python3`, sans GPU. Le calcul repose sur `mpmath`, en précision arbitraire. `numpy` et `matplotlib` servent au carnet 01, `pandas` au carnet 03.

```bash
python -m pip install jupyterlab ipykernel mpmath numpy matplotlib pandas
jupyter lab MyIA.AI.Notebooks/Physique/Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb
```

Les carnets sont déterministes : aucun tirage aléatoire. L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Physique](../README.md).

## Pour aller plus loin — Recherche

**Identifié, pas dérivé.** La forme fermée du triangle isocèle est certifiée numériquement. Sa dérivation analytique reste ouverte : le carnet 01 consigne une tentative par substitution trigonométrique, qui réussit à 60° et échoue ailleurs.

**Cité, pas reproduit.** La forme fermée du sunrise existe dans la littérature (Adams, Bogner et Weinzierl). Les carnets 02 et 04 la citent et s'arrêtent avant : ils établissent la courbe, ses périodes et ses limites, pas la valeur fermée de l'intégrale.

**Sans bornes garanties.** Les accords affichés sont des accords en précision arbitraire. Une arithmétique à bornes d'erreur certifiées est un prolongement, comme l'étude du régime de type temps, avec ses seuils.

**L'étage suivant.** Le classement que suit la série va des polylogarithmes aux courbes elliptiques, puis aux surfaces K3 et aux variétés de Calabi–Yau. Ces deux derniers étages demandent des graphes à trois boucles ; la série s'arrête à l'étage elliptique.

**Ponts.** [Marches-01](../../Probas/Applications/Marches-01-Retour-Polya-Watson-Python.ipynb) calcule aussi une fonction de Green, sur un réseau discret, avec les mêmes règles de méthode. [Numérique](../Numerique/README.md) applique la même discipline à des schémas numériques. [Jauge-01](../Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) ouvre l'arc des symétries et des champs de jauge.

## Ressources — tous niveaux

- G. 't Hooft, M. Veltman, *Scalar one-loop integrals*, Nucl. Phys. B **153**, 365 (1979).
- G. Passarino, M. Veltman, *One-loop corrections for $e^+e^-$ annihilation into $\mu^+\mu^-$ in the Weinberg model*, Nucl. Phys. B **160**, 151 (1979).
- L. Lewin, *Polylogarithms and Associated Functions*, North-Holland (1981) : la fonction de Clausen.
- L. Adams, C. Bogner, S. Weinzierl, *The two-loop sunrise graph with arbitrary masses*, [arXiv:1302.7004](https://arxiv.org/abs/1302.7004), et *The two-loop sunrise graph in two space-time dimensions with arbitrary masses in terms of elliptic dilogarithms*, [arXiv:1405.5640](https://arxiv.org/abs/1405.5640).
- M. D. Schwartz, *Claude-shaped science* (2026) : l'essai qui rapporte la famille d'intégrales dont ces objets sont tirés ; article associé [arXiv:2601.02484](https://arxiv.org/abs/2601.02484).
- [BootLoops](https://github.com/BootLoops-ai) (MIT / CC-BY-4.0) : l'outillage d'intégrales certifiées d'où viennent les trois règles de méthode. Les carnets re-dérivent leurs calculs et n'en importent aucun code.

[↑ Physique](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
