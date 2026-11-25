# Contrôle par interprétabilité — direction du refus

[↑ GenAI Security](../README.md)

## Ouverture — ce que cette série enseigne (Découverte)

Un modèle « aligné » refuse certaines requêtes — mais où ce refus vit-il dans les poids, et que se passe-t-il quand on l'abîme ? Cette série enseigne à **mesurer** le contrôle plutôt qu'à le supposer : extraire une direction de refus par différence de moyennes sur un témoin synthétique, l'ablater (brute vs centrée), doser un steering signé, et observer ce qui survit à un finetuning qui contredit l'alignement.

**À qui elle s'adresse.** Un lecteur curieux de l'interprétabilité mécanique qui veut voir la chaîne complète — direction, ablation, steering, finetuning, unlearning — sur un modèle assez petit pour être compris de bout en bout. Les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous découvrez le contrôle par interprétabilité** : lisez le carnet unique de la série, de haut en bas.
- **Vous creusez un palier** : cette série n'en porte aucun (voir [Approfondissements](#approfondissements-découverte)).
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche).

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| — | [Control-Refusal-Direction](Control-Refusal-Direction.ipynb) | Sur un transformeur témoin de 2 blocs (70 809 paramètres) entraîné dans le carnet : direction du refus par différence de moyennes (d-prime intra-classe 27.45), ablation directionnelle brute vs centrée avec son contrôle à direction aléatoire, dose-réponse de steering signé sur 9 valeurs (soustraire = jailbreak, ajouter = refus des requêtes bénignes), finetuning shallow à 10 exemples contradictoires qui effondre le refus tandis que la représentation survit (cosiné 0.837), tableau forget/retain des 5 interventions et simulation du biais d'évaluation awareness. Trois exercices C.1. | Découverte | [GenAI Security](../README.md) |

## Approfondissements (Découverte)

Cette série ne porte aucun approfondissement lettré : un seul carnet, la gradation n'y ouvre pas de palier. Rien n'est perdu ici — il n'y a rien à replier.

## Sous-séries (Découverte)

Cette série n'en contient pas. Elle est elle-même une sous-série de [GenAI Security](../README.md), l'axe « contrôle par interprétabilité » (sub-grain #16758, sources canoniques R11 et R14 citées dans le README parent).

## Installation

- **Python 3.10+** avec `numpy` et `torch` : tout est exécuté localement, sans GPU requis, sans LLM externe, sans téléchargement — le témoin est entraîné dans le carnet (CUDA si disponible, CPU sinon).
- Le passage à une famille open-weights réelle est déclaré `RECOVERABLE-MACHINE` dans le carnet.

## Pour aller plus loin — niveau Recherche

- **Le verdict du carnet** : « Un modèle aligné n'est pas un modèle verrouillé ; la seule défense réaliste est de mesurer, pas de supposer. »
- **Les sources canoniques** (R11 — *The 2026 Singapore Consensus on Global AI Safety Research Priorities* ; R14 — *Open Problems in Mechanistic Interpretability*) sont archivées hors dépôt et citées dans le [README parent](../README.md).
- **L'axe frère** : la surveillance d'agents plus forts par des agents plus faibles se mesure dans [Oversight](../Oversight/README.md).

## Ressources

- [GenAI Security — README de la section](../README.md) : les cinq axes, sources canoniques, acceptance commune.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
