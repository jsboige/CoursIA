# Échelle de difficulté — `D1` … `D4`

La difficulté d'un carnet est **ce que l'étudiant doit fournir** pour le suivre.
Elle ne se confond pas avec la dimension recherche ([dimension-recherche.md](dimension-recherche.md)) :
un carnet peut être difficile et n'être qu'une technique établie.

## Les trois critères

Chaque critère est noté de `1` à `4`. Les définitions sont écrites pour être
**opposables** : deux lecteurs qui lisent le même carnet doivent attribuer la
même note.

### `prerequis` — ce que l'étudiant doit savoir déjà

| Note | Définition |
|---|---|
| `P1` | Aucun prérequis hors Python et NumPy : le carnet est **auto-contenu**, il enseigne tout ce dont il a besoin. |
| `P2` | Une notion de niveau **licence** (probabilités, algèbre linéaire, optimisation) **ou** un prérequis explicite **dans la série** (un carnet antérieur cité dans la section « Prérequis »). |
| `P3` | Un **formalisme hors série** : CRF, HMM, PCFG, SHT, optimisation convexe… — un concept que le corpus n'enseigne nulle part ailleurs, et que le carnet ne peut donc pas supposer connu. |
| `P4` | Deux formalismes hors série cumulés, ou un formalisme hors série **plus** une notion de licence rarement maîtrisée. |

> `P4` est réservé : la série pilote ne l'atteint pas. Il existe pour que l'échelle
> ne soit pas bornée par le corpus que l'on a qualifié.

### `outillage` — ce que l'étudiant doit faire marcher

| Note | Définition |
|---|---|
| `O1` | Outils du langage seulement : Python, NumPy, matplotlib. Aucun paquet du domaine. |
| `O2` | Une **bibliothèque du domaine** (NLTK, spaCy, scikit-learn, hmmlearn, seqeval, sklearn-crfsuite) : l'étudiant doit savoir l'appeler, la configurer, et **lire ses sorties**. |
| `O3` | `O2` **plus** une installation à la charge de l'étudiant (modèle spaCy téléchargé, données NLTK téléchargées) ou un outillage tiers supplémentaire. |
| `O4` | Outillage cumulé : installation **et** service externe, exécution WSL, GPU, ou cloud. |

### `autonomie` — ce que l'étudiant doit produire

| Note | Définition |
|---|---|
| `A1` | Lire, exécuter, commenter une sortie. Rien à produire. |
| `A2` | **Adapter** — un paramètre, une formule, un prédicteur — et le vérifier sur un témoin chiffré. |
| `A3` | **Implémenter** soi-même un algorithme (de zéro, gradient compris), ou **construire une mesure** (protocole, ablation, banc) sur des données que l'on maîtrise. |
| `A4` | **Construire un banc dont le verdict n'est pas connu d'avance** — une hypothèse à tester, un témoin négatif, un résultat qui peut ne pas venir. |

## La règle de dérivation

```
niveau = max(prerequis, autonomie)
```

**Un seul rang** : le niveau est le plus contraignant des deux critères qui
pèsent sur le **raisonnement** demandé — les prérequis (peut-on suivre ?) et
l'autonomie (que faut-il produire ?).

**L'outillage n'entre pas dans le niveau.** C'est un **coût d'accès** : il
conditionne l'entrée dans la série, pas la difficulté du contenu. Un carnet
conceptuellement simple mais qui demande de télécharger un modèle reste facile ;
un carnet conceptuellement exigeant qui tourne sur NumPy seul reste difficile.
L'outillage est **enregistré** dans le profil et signalé dans la justification —
c'est le lecteur qui décide s'il peut l'absorber.

> Pourquoi pas le maximum des trois ? Un carnet qui exige un téléchargement de modèle
> (`O3`) verrait son niveau monter d'un rang alors que rien de plus difficile
> n'est demandé au raisonnement. L'outillage se note à part, sur sa propre
> colonne : c'est ce qui permet à un parcours de dire « ce carnet-ci demande
> spaCy installé ».

L'organe **recalcule** cette règle et refuse un manifeste qui la contredit :

```
[ERROR] niveau MyIA.AI.Notebooks/NLP/01_....ipynb : niveau D2 incompatible
        avec la regle max(prerequis, autonomie) (prerequis=1, autonomie=2) -> D2
```

## Les quatre niveaux

| Niveau | Ce qu'il décrit | Exemples (série pilote `NLP`) |
|---|---|---|
| `D1` | Initiation : lire, exécuter, commenter. Aucun prérequis, aucun outil du domaine. | *aucun carnet de la série pilote* |
| `D2` | Autonome : adapter une formule, vérifier sur un témoin chiffré, avec une notion de licence ou un prérequis de série. | 01, 02, 06, 07, 10 |
| `D3` | Avancé : implémenter un algorithme de zéro, ou assumer un formalisme hors série. | 03, 04, 05, 08, 09 |
| `D4` | Expert : construire le banc soi-même, avec un verdict qui n'est pas connu d'avance. | 11 |

La série pilote ne contient **aucun `D1`** : tous ses carnets demandent au moins
une adaptation et une vérification. C'est un fait mesuré, pas un choix de
présentation — l'échelle ne se remplit pas de niveaux vides pour paraître
complète.

## Ce que l'échelle ne dit pas

- **Elle ne dit pas si le carnet est sain.** Un carnet au substrat dégénéré
  ([#24282](https://github.com/jsboige/CoursIA/issues/24282)) peut être très
  facile et n'enseigner rien : sa difficulté est basse, sa qualité est nulle.
  Ce sont deux jugements séparés, sur deux axes.
- **Elle ne se déduit d'aucun scan.** [#24292](https://github.com/jsboige/CoursIA/issues/24292)
  a montré qu'un inventaire fondé sur des mots-clés ne mesure pas ce qu'il
  prétend mesurer (39 carnets touchés, aucun vrai cas D4). Les valeurs sont
  donc **déclarées et justifiées, carnet par carnet**, et l'organe vérifie la
  forme, la dérivation et la fraîcheur — jamais le jugement.
- **Elle ne se déduit pas de la densité de prose.** Une densité sous le
  plancher de 1200 ([#13410](https://github.com/jsboige/CoursIA/issues/13410))
  signale un carnet à **enrichir**, pas un carnet à reclasser : l'organe la
  signale en avertissement, et elle ne fait échouer aucune vérification.

## Ce qui est **mesuré** dans le profil

Le manifeste enregistre, pour chaque carnet, des mesures relues sur l'arbre
par l'organe :

| Mesure | Source | Pourquoi elle est dans le profil |
|---|---|---|
| `exercices` | `count_exercises.py` | le contrat pédagogique (3 exercices) |
| `cellules_code`, `cellules_md` | lecture du carnet | la taille du travail |
| `prose_chars`, `densite` | `pedagogy_density.py` | le rapport entre ce qui est donné et ce qui est exécuté |
| `kernel` | `generate_catalog.py` | l'environnement réel |
| `exigences` (`api`, `gpu`, `cloud`, `wsl`) | `generate_catalog.py` | les ressources à déclarer |

Ces mesures ne **décident** d'aucun niveau : elles documentent le profil, et
leur divergence avec l'arbre (un carnet modifié depuis sa qualification) est
une **dérive** que l'organe refuse.

## Voir aussi

- [dimension-recherche.md](dimension-recherche.md) — l'autre axe.
- [manifest.json](manifest.json) — la donnée.
- [pilot-nlp.md](pilot-nlp.md) — la série pilote.
- [README.md](README.md) — l'organisation du répertoire et l'organe.
