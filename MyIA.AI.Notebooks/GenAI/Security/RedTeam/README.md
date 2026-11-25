# Red team au-delà de l'injection

[↑ GenAI Security](../README.md)

## Ouverture — ce que cette série enseigne (Découverte)

L'injection est l'attaque la plus visible des systèmes GenAI, mais pas la seule porte. Cette série enseigne à red-teamer les **quatre autres familles** que l'injection ne couvre pas — jailbreaks par reconstruction de cadre, empoisonnement par les données, chaîne d'approvisionnement, évasion de bac à sable — chacune avec son organe de mesure et son taux mesuré sur du matériel réel ou from scratch.

**À qui elle s'adresse.** Un lecteur qui veut passer de la démonstration d'attaque à sa **mesure** : un taux, un contrôle, une limite honnête — plutôt qu'un exemple spectaculaire. Les prérequis exacts sont en [Installation](#installation).

## Comment lire ce README (Découverte)

Un README de série se lit à plusieurs vitesses : le parcours principal par les numéros nus, l'approfondissement par les lettres, la recherche en cours par les sous-séries et la section « Pour aller plus loin ». Le principe est exposé à la racine du dépôt, dans [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture).

- **Vous découvrez le red team au-delà de l'injection** : lisez le carnet unique de la série, de haut en bas.
- **Vous creusez un palier** : cette série n'en porte aucun (voir [Approfondissements](#approfondissements-découverte)).
- **Vous cherchez la recherche en cours** : allez directement à [« Pour aller plus loin »](#pour-aller-plus-loin--niveau-recherche).

## Parcours principal (Découverte)

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| — | [RedTeam-Beyond-Injection](RedTeam-Beyond-Injection.ipynb) | Quatre familles mesurées une par une : jailbreaks (six gabarits d'attaque × deux cibles de politique bénignes contre `qwen2.5:7b` servi en local, 1/12 réussi), empoisonnement (détournement d'un TF-IDF from scratch par trois documents piégés, backdoor d'un classifieur de sentiment — déclencheur de 0 % à 100 % avec contrôle), chaîne d'approvisionnement (typosquatting par distance de Levenshtein, 5/5 détectés ; intégrité SHA-256), bac à sable (allow-list de mission + prison de chemins opposées à huit tentatives, 6/8 bloquées). Trois exercices C.1. | Découverte | [GenAI Security](../README.md) |

## Approfondissements (Découverte)

Cette série ne porte aucun approfondissement lettré : un seul carnet, la gradation n'y ouvre pas de palier. Rien n'est perdu ici — il n'y a rien à replier.

## Sous-séries (Découverte)

Cette série n'en contient pas. Elle est elle-même une sous-série de [GenAI Security](../README.md), l'axe « red team opérationnelle » (pli 3 de #19543, thème 9).

## Installation

- **Python 3.10+** avec `scikit-learn` et `matplotlib` : les sections 2 à 4 sont auto-contenues (bibliothèque standard + scikit-learn), aucune clé ni service requis.
- **Ollama local** pour la section jailbreak : `qwen2.5:7b` servi en local — sans lui, cette section est `RECOVERABLE-LOCAL`, les trois autres se rejouent.

## Pour aller plus loin — niveau Recherche

- **Le verdict du carnet** : « L'injection est l'attaque la plus visible, mais pas la seule porte : ce carnet a mesuré quatre autres familles — jailbreak par reconstruction de cadre, empoisonnement par les données, chaîne d'approvisionnement, évasion de bac à sable — chacune avec son organe et son taux. »
- **Le jumeau de red team de prompts** de la série Texte : [09b_Prompt_Security_RedTeam](../../Texte/09b_Prompt_Security_RedTeam.ipynb).
- **Les axes frères de la section** : la défense par construction ([Capability](../Capability/README.md)), la surface d'attaque de la couche outils ([Tooling](../Tooling/README.md)).

## Ressources

- [GenAI Security — README de la section](../README.md) : les cinq axes, sources canoniques, acceptance commune.
- [Choisir sa vitesse de lecture](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) : le principe des parcours à plusieurs vitesses, à la racine du dépôt.
