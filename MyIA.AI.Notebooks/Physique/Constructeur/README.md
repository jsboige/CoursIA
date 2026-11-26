# Constructeur — les lois comme tâches possibles ou impossibles

[↑ Physique](../README.md)

Une loi physique s'énonce d'habitude comme une dynamique : un état, une équation de mouvement, des conditions initiales. La théorie du constructeur (Deutsch 2013 ; Deutsch & Marletto 2015) part d'ailleurs. Elle dit quelles transformations sont **possibles**, lesquelles sont **impossibles**, et pourquoi. Cette sous-série présente ce changement de point de vue sur des systèmes jouets, en Python, sans calcul lourd.

Elle s'adresse à un lecteur qui connaît les bases de Python et qui a déjà rencontré une loi de conservation. La dernière partie du carnet manipule deux qubits et une mesure d'intrication : des notions d'algèbre linéaire aident à la suivre, mais le code est donné et commenté. Les autres sous-séries de [Physique](../README.md) font calculer contre une référence exacte ; celle-ci est conceptuelle et leur sert de contrepoint.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : lisez le carnet du parcours principal dans l'ordre. Chaque notion est suivie d'une courte cellule qui l'illustre.
- **Vous creusez** : la section « Approfondissements » décrit le témoin de non-classicité simulé et les exercices.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » dit ce que le carnet laisse de côté et où lire les tests proposés pour cette théorie.

## Parcours principal — Découverte

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Constructeur-01 — Les lois comme tâches](Constructeur-01-Lois-Comme-Taches-Python.ipynb) · [version C#](Constructeur-01-Lois-Comme-Taches-CSharp.ipynb) | Le vocabulaire sur l'exemple d'un dé : substrat, état, attribut, tâche, constructeur. Le passage de la dynamique aux principes. La conservation de l'énergie lue comme l'impossibilité d'un moteur perpétuel. L'information définie par son support (permutations et copie possibles), d'où le non-clonage : le bit classique passe le test, le qubit inconnu ne le passe pas. Enfin un témoin de non-classicité simulé, où un médiateur quantique intrique deux sondes et un médiateur classique n'en intrique aucune. | Licence : Python de base. La dernière partie suppose des notions de qubit et d'intrication. | Les exercices du carnet, puis [Jauge-01](../Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) pour une conservation mesurée. |

## Approfondissements — Licence et Master

La sous-série n'a pas de palier lettré. Ses approfondissements sont dans le carnet lui-même.

### Autour de 01 : le témoin de non-classicité

Le carnet simule l'idée d'un test proposé pour la gravité. Deux sondes quantiques n'interagissent que par un médiateur. Si elles ressortent intriquées, le médiateur ne peut pas être classique. La cellule mesure l'intrication par la négativité : `0.500` avec un médiateur quantique, `0.000` avec un médiateur classique. Entre les deux, la négativité décroît de `0.318` à `0.038` quand la part classique du médiateur passe de 0,25 à 0,75.

Le médiateur du carnet est un modèle choisi, une interaction de type Ising. Ce n'est pas la gravité : le calcul illustre le raisonnement, il ne tranche aucune question expérimentale.

### Autour de 01 : exercices et auto-évaluation

Les trois exercices demandent d'écrire la fonction qui dit si un constructeur accomplit une tâche, de tester si un objet « reste le même » après l'avoir accomplie, et de vérifier le principe d'interopérabilité (deux supports d'information composés forment encore un support). Les cellules s'exécutent sans erreur tant qu'elles ne sont pas complétées. Une section « Vérifiez votre compréhension » pose ensuite trois questions, avec leurs réponses repliées.

## Installation — pratique, tous niveaux

Le carnet tourne sur le noyau `python3` et n'importe que `numpy`. Aucun GPU n'est requis.

```bash
python -m pip install jupyterlab ipykernel numpy
jupyter lab MyIA.AI.Notebooks/Physique/Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb
```

Le jumeau C# suit le même plan et rend les mêmes nombres (négativité `0.500` / `0.000`, puis `0.318` · `0.155` · `0.038`). Il tourne sur le noyau `.net-csharp` (.NET Interactive) et n'utilise que la bibliothèque standard : aucun paquet NuGet, aucune dépendance externe — les matrices 4×4 et leurs valeurs propres y sont calculées à la main (rotations de Jacobi).

```bash
dotnet tool install --global Microsoft.dotnet-interactive
dotnet interactive jupyter install
jupyter lab MyIA.AI.Notebooks/Physique/Constructeur/Constructeur-01-Lois-Comme-Taches-CSharp.ipynb
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Physique](../README.md).

## Pour aller plus loin — Recherche

**Ce que le carnet laisse de côté.** Il ne démontre pas le non-clonage, dont l'énoncé et la preuve demandent la théorie quantique. Il ne traite ni la deuxième loi de la thermodynamique, ni la causalité en tant que telle : seule la localité est abordée.

**Relire une conservation.** [Jauge-01](../Jauge/Jauge-01-Theoreme-Noether-Python.ipynb) mesure une quantité conservée et montre qu'elle disparaît quand la symétrie est rompue. On peut la relire dans le langage de cette sous-série, comme un énoncé de tâche impossible.

**Localité et structure causale.** Le principe de localité (« une transformation qui agit sur A seul ne peut changer B ») a un contrepoint dans la série [IIT / ICT-Series](../../IIT/ICT-Series/README.md), qui étudie les structures causales.

**Tests proposés.** L'article *Tests of constructor theory* (arXiv:2606.07352) recense les expériences envisagées, dont celle que le carnet simule.

## Ressources — tous niveaux

- D. Deutsch, *The Philosophy of Constructor Theory*, Synthese 190(18), 2013 — [arXiv:1210.7439](https://arxiv.org/abs/1210.7439).
- D. Deutsch, C. Marletto, *The Constructor Theory of Information*, Proc. R. Soc. A 471(2174), 2015 — [arXiv:1405.5563](https://arxiv.org/abs/1405.5563).
- C. Marletto, D. Deutsch et coll., *Tests of constructor theory*, 2026 — [arXiv:2606.07352](https://arxiv.org/abs/2606.07352).
- Site du projet : <https://www.constructortheory.org/>.

[↑ Physique](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
