# `_archive/` — carnets retirés de la série 03-DeepLearning

Les carnets de ce dossier ne sont **ni rendus, ni maintenus, ni ré-exécutés**. Leur contenu a été absorbé par un carnet vivant de la série. Ils sont conservés **tels quels**, à titre de provenance : on peut encore les ouvrir pour vérifier ce qui était publié à une date donnée, mais ce ne sont plus des supports de cours.

Convention appliquée : [`docs/reference/_archive-convention.md`](../../../../../docs/reference/_archive-convention.md) — quatre critères d'éligibilité (verdict consigné, zéro référence, zéro import, successeur nommé) et en-tête de disposition par section.

## Registre

| Carnet | Verdict | Remplacé par | Verdict consigné dans |
|---|---|---|---|
| `3.9d-Compression-Distillation-from-scratch.ipynb` | `ABSORBED` — la distillation était enseignée deux fois dans la série : [3.7](../3.7-Distillation-Maitre-Eleve.ipynb) portait déjà la KD et la vérification du facteur `T²`, 3.9d portait le terrain canonique de la compression (ResNet-20 maître / ResNet-8 élève sur CIFAR-10) | [3.7-Distillation-Maitre-Eleve.ipynb](../3.7-Distillation-Maitre-Eleve.ipynb) — terrain, loss, hints FitNets, balayage de température et exercices absorbés ; les acquis propres à 3.7 (facteur `T²` vérifié sur le gradient, calibration ECE, taille et latence, articulation quantification / distillation / KL-RLHF) y sont conservés | PR « #22395 étape 2 », consigne user du 2026-10-25 (fusion des deux carnets, un seul enseignement de la KD) |

## Disposition par section — `3.9d`

Chaque cellule de l'archive a une destination nommée dans le carnet qui la remplace. Aucune section n'a été supprimée sans que sa substance soit reprise ; les deux seules exceptions sont explicitées en fin de tableau.

| Section de 3.9d | Destination dans 3.7 | Nature |
|---|---|---|
| Titre, « Le contrat de ce notebook » | Titre et « Le contrat de ce carnet » réécrits : les quatre questions du contrat d'origine sont conservées (gain à budget égal, rôle de `T`, hints, coût) et deux sont ajoutées (facteur `T²`, calibration) | réécrit |
| Imports, graine, `DEV`, `EPOCHS`, `SEEDS`, `T_DEFAULT`, `ALPHA` | §0 — verbatim | repris tel quel |
| §1 loss de distillation + démonstration du *dark knowledge* (masse non-cible 0,086 → 0,609 entre `T=1` et `T=4`) + Lecture | §1 — verbatim ; seul le renvoi qui pointait vers 3.7 devient un renvoi interne à la vérification du facteur `T²` | repris tel quel |
| §2 terrain (CIFAR-10, `ResNetCifar`, 272 474 / 78 042 paramètres, recette SGD/cosine/crop+flip) | §2 — verbatim | repris tel quel |
| `run_student` | §2 — **étendu** : paramètre `tchr` (maître de substitution, pour l'exercice 5) et retour du modèle entraîné en quatrième position (pour mesurer l'ECE sans réentraîner) | étendu |
| Entraînement du maître | §3 — verbatim | repris tel quel |
| §3 témoin from scratch (3 graines) | §3 — verbatim | repris tel quel |
| §4 KD logit (3 graines) | §4 — verbatim | repris tel quel |
| §5 hints FitNets (`forward_with_hint`, ordre de grandeur des composantes, `runs_hint`, `delta_sigma`, figure des courbes) | §5 — verbatim | repris tel quel |
| Lecture du gain (écart en unités de σ, par graine) | §5 — verbatim | repris tel quel |
| §6 température (`T ∈ {1, 2, 4, 8}`) et sa Lecture | §7 — verbatim, décalé d'un rang par l'insertion de la calibration en §6 | repris tel quel |
| Tableau final (exactitude, paramètres) | §8 — **étendu** : colonnes ECE, taille sérialisée et latence ajoutées à côté de l'exactitude et des paramètres | étendu |
| Lecture finale, Résumé | §8 et « Résumé » remaniés : les chiffres sont ceux de la **ré-exécution** du carnet fusionné (le terrain et les graines sont identiques, la mesure est refaite, pas recopiée) | réécrit |
| Exercice « étiquettes rares » | Exercice 2 — verbatim, hors le renvoi à 3.7 devenu un renvoi interne | repris tel quel |
| Exercice « hint cosinus » | Exercice 3 — verbatim | repris tel quel |
| Exercice « température `T = 16` » | Exercice 4 — verbatim | repris tel quel |
| « Pour aller plus loin » | Remplacé par la bibliographie et les renvois de la série : ses liens vers 3.7 et 3.6 seraient devenus des auto-renvois ou des doublons de la navigation du carnet fusionné | **non repris, remplacé** |

**Les deux exceptions, nommées :**

1. **« Pour aller plus loin »** — remplacé, non copié : la liste de liens de 3.9d pointait vers 3.7 (désormais le carnet hôte) et vers des carnets déjà cités dans la navigation du haut. La bibliographie (Hinton 2015, Romero 2015) et le renvoi vers 3.9a / 3.9b / 3.9e / 3.9g sont conservés, eux, dans la section finale du carnet fusionné.
2. **La numérotation des sections et des exercices** — décalée : la calibration s'insère en §6 et devient l'exercice 1 du carnet fusionné (le dosage α, propre à 3.7). Les trois exercices de 3.9d deviennent les exercices 2, 3 et 4 ; le carnet en compte cinq.

## Ce qui a été absorbé **dans l'autre sens**

3.9d n'est pas la seule source de cette fusion. Le carnet 3.7 d'origine (MLP sur Fashion-MNIST, budget de 1 500 étiquettes, protocole 5 folds × 4 graines) a été **remplacé** par le terrain de 3.9d, plus fort : le verdict `INCONCLUSIVE` du protocole Fashion-MNIST (gain par exemple net, gain d'exactitude sous le seuil de 2σ) est remplacé par une mesure à +12,6 σ sur trois graines. Ce qui a été **conservé** de 3.7 dans la fusion, et qui n'existait pas dans 3.9d :

- la **vérification numérique du facteur `T²`** sur le gradient de la KL (§1, « Le facteur `T²` — vérifié, pas récité ») ;
- le **test apparié par exemple** (statistique de Diebold–Mariano sur les pertes CE), qui distingue « l'écart moyen de perte est réel » de « l'exactitude progresse de façon reproductible » (§5) ;
- la **calibration** (erreur de calibration attendue, ECE) mesurée sur les modèles déjà entraînés (§6) ;
- les axes **taille sérialisée et latence** dans le tableau de compression (§8) ;
- l'articulation **quantification / distillation / KL de régularisation RLHF** (§9) ;
- les exercices **dosage α** et **mauvais maître** (exercices 1 et 5).

## Vérification

- Archive **byte-identique** à sa version d'origine sur `main` (`git mv`, aucun octet modifié, aucune ré-exécution) — le carnet conserve donc les sorties de son exécution d'origine, y compris la bannière `papermill` de son `metadata`.
- Référents mis à jour **dans ce même geste** : `_quarto.yml` (l'entrée 3.9d est retirée, ce registre est listé à sa place), la ligne « Compléments » et la table des blocs de [`3.9-Compression-Quantization-FP.ipynb`](../3.9-Compression-Quantization-FP.ipynb), et quatre renvois en prose de [`3.9g`](../3.9g-Compression-Comparatif-A-vs-B.ipynb).
- **Liens internes du carnet archivé : figés, volontairement.** Le carnet est conservé octet pour octet, donc ses liens relatifs (`3.7-…`, `3.9a-…`, `../../../GenAI/…`) désignent depuis ce dossier des chemins d'un cran trop haut. Ils ne sont pas réécrits : le faire casserait la propriété de provenance ci-dessus, et la convention `_archive/` demande de ne pas réécrire les chemins relatifs d'un fichier archivé (critère 4 — la résurrection sans réécriture). Pour les suivre, préfixer d'un `../` (`../3.7-Distillation-Maitre-Eleve.ipynb`, `../../../../GenAI/…`), ou passer par le carnet vivant : la table de disposition ci-dessus nomme la destination de chaque section.
- Référent restant, **hors du périmètre de cette lane** : le [`README.md` de la série](../README.md) cite encore 3.9d en deux endroits — ligne 46 (la ligne de table du carnet) et ligne 126 (la note d'exécution GPU). Ce README est arbitré à `po-2023:CoursIA`, qui porte la PR de README finale après les trois étapes de #22395 : la correction y est signalée plutôt qu'appliquée depuis ici, et cette PR ne le modifie pas.
