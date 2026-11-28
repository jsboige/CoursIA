---
pagetitle: "Sciences et calcul"
---

[← Parcours de notebooks](../README.md)

# Sciences et calcul

Comment passer d'une question scientifique à un calcul que l'on peut contrôler ? Ce parcours rassemble quatre portes d'entrée : les mathématiques construisent des objets et des méthodes ; la physique et la biologie proposent des modèles de phénomènes ; les sciences de l'information étudient ce qu'une machine peut représenter, transmettre et calculer. Les disciplines restent distinctes : un calcul exact, une simulation et une preuve ne répondent pas nécessairement à la même question.

## Comment lire ce README

Choisissez une discipline et ouvrez sa première étape. Les parcours sont indépendants : revenez ensuite aux rapprochements proposés dans les approfondissements.

## Choisir son entrée

| Parcours | Ce qu'on y apprend | Prérequis | Première étape |
|---|---|---|---|
| **Mathématiques** | Calcul symbolique et numérique, équations différentielles, comparaison entre solution exacte, approximation et énoncé formel. | Dérivées et intégration ; Python pour les exemples numériques. | Le pilote de calcul scientifique est en cours de préparation. En attendant, le [triangle scalaire](../Physique/Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb) présente des intégrales et plusieurs voies de calcul. |
| **Physique** | Lois de conservation, symétries, intégrales et information quantique : confronter un modèle à un calcul et à ses limites. | Python et calcul différentiel pour débuter ; algèbre linéaire ou mécanique selon la branche. | [Parcours Physique](../Physique/README.md), puis [équation de Burgers et volumes finis](../Physique/Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb). |
| **Biologie** | Croissance des populations, épidémies et structures moléculaires : contrôler un modèle du vivant par une référence indépendante. | Python et équations différentielles pour les dynamiques ; géométrie spatiale pour les structures. | [Bio & Médecine](../BioMedecine/README.md), puis [populations et épidémies](../BioMedecine/Dynamiques/Dynamiques-01-Populations-et-Epidemies-Python.ipynb). |
| **Information et calcul** | Entropie, compression, canaux bruités, automates et complexité : mesurer l'information et le coût des opérations. | Python et probabilités élémentaires pour l'entrée par l'entropie. | [Information et calcul](../InformationCalcul/README.md), puis [entropie et information mutuelle](../InformationCalcul/InformationTheory/InformationTheory-01-Entropie-Et-Information-Mutuelle.ipynb). |

## Approfondissements — relier les parcours

Une équation différentielle relie les dynamiques de population aux modèles physiques : les carnets invitent à comparer une solution de référence et une approximation, sans confondre accord numérique et preuve générale. L'information fournit une autre perspective sur les mêmes questions de représentation et de mesure ; les applications quantiques relient notamment algèbre linéaire, physique et théorie de l'information.

Les séries liées restent à leurs emplacements actuels pendant la construction de ce hub. Le pilote mathématique n'est pas encore une entrée publiée sur la branche principale ; les preuves Lean restent dans leurs séries et sont reliées depuis les sujets qu'elles éclairent, sans déplacement de leurs bibliothèques.
