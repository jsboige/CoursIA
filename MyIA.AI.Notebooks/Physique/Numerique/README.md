# Numérique — mesurer un schéma, dire ce qu'une preuve prouve

[↑ Physique](../README.md)

Un schéma numérique pour une loi de conservation peut être juste sur le papier et mal programmé, ou l'inverse. Cette sous-série mesure ce qu'un solveur fait réellement : la vitesse d'un choc, un taux de convergence, la conservation d'une masse. Chaque mesure est comparée à une solution exacte. Les carnets disent ensuite, lacune par lacune, ce qui relève de la mesure et ce qui demanderait une preuve formelle. Aucun n'écrit « vérifié de bout en bout ».

Le premier carnet s'adresse à un étudiant de licence qui connaît Python, les dérivées partielles et l'intégration. Le second sort de Python : il compile du C et suppose quelques notions sur les équations hyperboliques linéaires. Le pilote C y est fourni et commenté.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par Numérique-01. Une équation, un choc, deux schémas à comparer.
- **Vous creusez un palier** : la section « Approfondissements » décrit la partie de chaque carnet qui sépare la mesure de la preuve, et les exercices.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme les questions ouvertes sur la preuve de correction d'un schéma.

## Parcours principal — Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Numérique-01 — Équation de Burgers : volumes finis, solveur de Riemann, et ce qu'une preuve prouve](Numerique-01-Burgers-Volumes-Finis-Python.ipynb) · [version C#](Numerique-01-Burgers-Volumes-Finis-CSharp.ipynb) | Les caractéristiques et la formation d'un choc. La condition de Rankine-Hugoniot, dérivée de la forme intégrale : vitesse `0.5` pour les états $u_L = 1$ et $u_R = 0$. Les schémas de Godunov et de Rusanov sous condition CFL, comparés à la solution exacte du problème de Riemann. Le taux de convergence en norme L1, mesuré par régression : ordre `0.99` sur le choc, entre `0.75` et `0.79` sur la raréfaction. Le temps de formation du choc, $t^* = 1/\pi$, retrouvé sur les caractéristiques avec un écart relatif de `1.64e-06`. | Licence : Python, dérivées partielles, intégration. Outils : numpy, matplotlib. | La table des lacunes du carnet, puis ses exercices (voir « Autour de 01 »). |
| 02 | [Numérique-02 — Maxwell en relativité : les noyaux C vérifiés d'un dépôt amont, mesurés](Numerique-02-Maxwell-Relativiste-Volumes-Finis-C.ipynb) | Un fichier C du dépôt amont `lanyonai/GeneralRelativisticMaxwell`, téléchargé à une empreinte SHA-256 épinglée et compilé tel quel. Le carnet écrit le pilote, qui n'ajoute aucune formule physique. Sur une tranche plate, la masse est conservée, l'état propre $D_y = cB_z$ est préservé exactement, et la vitesse de propagation mesurée vaut `1.000000000000` pour l'onde droite, `-1.000000000000` pour l'onde gauche. La convergence est d'ordre 1 : ordres locaux de `0.745` à `0.948`, pente ajustée `0.8611`. La diffusion numérique se lit dans le maximum de $D_y$, tombé à `0.659254` pour $N = 64$. | Licence avancée : équations hyperboliques linéaires ; lire du C aide. Outils : compilateur C, numpy, matplotlib. | L'origine de la diffusion et la limite de l'instrument de mesure (voir « Autour de 02 »). |

## Approfondissements — Licence avancée et Master

La sous-série n'a pas de palier lettré. Ses approfondissements sont des parties des carnets.

### Autour de 01 : ce qu'une preuve formelle établirait

La dernière partie de Numérique-01 dresse une table des lacunes. Une preuve formelle portant sur l'équation continue ne dit rien du schéma discret, et une preuve du schéma ne dit rien du code exécuté. Le carnet écrit un verdict par lacune : ce qui est mesuré ici, ce qui est seulement rapporté, ce qui reste à démontrer.

Les exercices prolongent les mesures : un schéma d'ordre deux sur l'advection linéaire, un solveur de Riemann pour le flux $f(u) = u^3/3$, la largeur du choc de Godunov, la décroissance de l'entropie discrète.

La [version C#](Numerique-01-Burgers-Volumes-Finis-CSharp.ipynb) du carnet rejoue les mêmes mesures avec la seule bibliothèque de base .NET : mêmes nombres d'entrée et de sortie, figures remplacées par des sorties texte, et chaque valeur citée portée par une assertion exécutable — le carnet s'arrête si une exécution s'écarte du jumeau Python.

### Autour de 02 : « vérifié » ne veut pas dire « relié »

Le dépôt amont prouve en Lean une transcription des équations, et livre par ailleurs du C sans programme principal. Numérique-02 mesure ce C. Il relève qu'aucune déclaration ne rattache les théorèmes au code compilé. Sa dernière partie sépare par écrit ce qui est mesuré dans le carnet, ce qui est rapporté de l'inventaire du dépôt amont, et ce qui reste hors de portée.

Deux résultats de méthode s'y ajoutent. Les vitesses d'onde du schéma valent $\pm(\alpha c + \lvert\beta_x\rvert)$ quel que soit le sens réel de propagation : c'est ce choix, celui de la famille Lax-Friedrichs, qui produit la diffusion observée. Et l'instrument de mesure a un domaine de validité : à $t = 0{,}8$, le déphasage dépasse un demi-tour et la vitesse brute devient fausse (`-0.248780487805`).

Les exercices cherchent la limite de Courant du schéma, testent si la sous-résolution explique l'ordre local trop faible à $N = 64$, et réparent la mesure de vitesse en développant la phase.

## Installation — pratique, tous niveaux

Les carnets tournent sur le noyau `python3`, sans GPU. Ils sont déterministes : aucune graine, chaque exécution rejoue les mêmes nombres.

```bash
python -m pip install jupyterlab ipykernel numpy matplotlib
jupyter lab MyIA.AI.Notebooks/Physique/Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb
```

Numérique-02 demande en plus :

- un **compilateur C**. Le carnet cherche `cc`, `gcc` ou `clang` sur la machine, puis `gcc` dans WSL (Ubuntu) sur un poste Windows. Sans compilateur, il s'arrête sur une erreur explicite au lieu de produire une sortie de repli ;
- un **accès réseau**, pour télécharger le fichier amont. Le carnet vérifie son empreinte SHA-256 avant de le compiler.

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Physique](../README.md).

## Pour aller plus loin — Recherche

**Questions ouvertes.** Numérique-01 en nomme trois : ce que contiennent exactement les théorèmes formels disponibles sur l'équation de Burgers, comment prouver la correction d'un schéma comme celui de Godunov, et comment relier une preuve au code exécuté. Numérique-02 montre un cas concret de la troisième.

**Cadre de méthode.** Le document [gorard-lanyonai-etape3.md](../../../docs/reference/gorard-lanyonai-etape3.md) explique ce que les preuves du dépôt amont établissent, et pourquoi elles ne portent pas sur le C.

**Prolongement numérique.** Après le premier exercice de Numérique-01, on peut passer aux schémas d'ordre 2 et mesurer ce que l'ordre ajoute près du choc. La raréfaction, où l'ordre mesuré reste voisin de `0.75`, est le bon terrain d'essai.

**Ponts.** [Jauge-01](../Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) traite la conservation du côté des symétries. [Intégrales](../Integrales/README.md) applique la même discipline de contrôle à des intégrales de haute précision.

## Ressources — tous niveaux

- Dépôt amont de Numérique-02 : `lanyonai/GeneralRelativisticMaxwell`, licence MIT, fichier `implementations/gr_maxwell_1d.c`. Le carnet imprime l'empreinte du fichier qu'il compile.
- [gorard-lanyonai-etape3.md](../../../docs/reference/gorard-lanyonai-etape3.md) : cadre de méthode sur la portée des preuves formelles en analyse numérique.

[↑ Physique](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
