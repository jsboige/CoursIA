# Provenance — App-31 RCPSP/max : faisabilité, cycles et bornes

## Travail étudiant distillé

- **Auteurs** : Arthur Gallier et Nicolas Naegelen
- **Projet** : *Ordonnancement industriel (RCPSP)*, groupe B4, EPITA SCIA, Programmation par Contraintes 2026
- **Dépôt source** : <https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/tree/main/B4-Gallier-Naegelen>
- **Historique** : [PR #51](https://github.com/jsboigeEpita/2026-Epita-Programmation-par-Contraintes/pull/51)
- **Commit intégré** : `8b91a736` — *feat(B4): RCPSP (+max, multi-mode) en CP-SAT + baseline GA*
- **Snapshot audité** : `b5f3f0351dbd41f3a76f047cf02e9c93e81192f3`
- **Licence source** : MIT, copyright 2026, *EPITA SCIA - Programmation par Contraintes (students and teaching staff)*

Le rendu étudiant réunit un parseur PSPLIB écrit à la main, un modèle CP-SAT du RCPSP, une
baseline par algorithme génétique (SGS série, croisement PPX préservant les précédences), un
banc d'essai sur j30/j60/j120, une comparaison exact contre métaheuristique, une étude de
stratégies de branchement, une section RCPSP/max et une section multi-mode. Cette amplitude
est le geste central de l'hommage.

**Ce projet traite une question que CoursIA laisse explicitement ouverte.** Le notebook
`Planners-8-Temporal-Csharp` conclut sa section RCPSP par : « la comparaison avec l'optimum
known d'un benchmark (ex: PSPLIB) est laissée en exercice ». B4 a fait cet exercice.

## Vérification indépendante des résultats source

Avant toute distillation, les dix makespans publiés par le banc d'essai étudiant ont été
recalculés avec un modèle CP-SAT réécrit de zéro pour cet audit. **Les dix valeurs sont
exactes** et retrouvées à l'identique, toutes certifiées `OPTIMAL`. En particulier, la
résolution d'une instance j120 en une fraction de seconde, qui pouvait surprendre, est
confirmée : elle est mesurée à 0,07 s ici. Les temps de cette vérification sont reportés dans
la table `OBSERVATIONS_PSPLIB` du notebook (colonne `temps_verification_s`) et dans
`provenance.json` ; ils s'échelonnent de 0,03 s à 0,08 s. Aucun résultat numérique du rendu
source n'est mis en cause par cet audit.

## Réécriture et collecte CoursIA

App-31 ne copie aucun module, cellule, texte, figure, sortie ni capture étudiante. Ne sont
notamment pas repris : le parseur `.sm`, le schéma de génération série `serial_sgs`, le
croisement `ppx_crossover` et la boucle génétique, le dictionnaire `BKS_J30`, les cellules de
modèle CP-SAT, les cellules de visualisation et les instances de démonstration. Les réseaux
temporels, les détecteurs de cycle, les modèles, validateurs, expériences et figures d'App-31
sont des réécritures CoursIA indépendantes, sur des instances générées dans le notebook avec
des graines fixes.

Le notebook exécuté produit :

- `provenance.json` — identité structurelle SHA-256 des instances générées, environnement et
  démonstration du contrat de repli sur bornes certifiées ;
- `temporal_regimes.csv` — classification faisable / infaisable temporellement / infaisable en
  ressources, avec le témoin de cycle lorsqu'il existe ;
- `bounds_ladder.json` — hiérarchie de bornes (chemin critique, borne de charge, borne solveur)
  et niveau de preuve associé à chaque instance.

Commande de reproduction depuis la racine CoursIA :

```powershell
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/Search/Applications/Hybrid/App-31-RCPSP-Max-Feasibility-Bounds.ipynb --timeout 900 --verbose
```

## Instances PSPLIB : observées, non redistribuées

La bibliothèque PSPLIB (TU München) n'est **pas** redistribuée par CoursIA. Les dix instances
que le banc d'essai source sélectionne effectivement sont identifiées ci-dessous par empreinte
SHA-256, avec les mesures recalculées pour cet audit. Le notebook rejoue le *phénomène* sur des
instances générées, jamais sur ces fichiers.

| Instance | SHA-256 (tronqué) | Chemin critique | Optimum recalculé |
|---|---|---|---|
| `j30/j3010_1`   | `4fae4197791f2ee8` | 41  | 42  |
| `j30/j3010_10`  | `5b704056bfd6531d` | 37  | 41  |
| `j30/j3010_2`   | `108f260686ec9353` | 52  | 56  |
| `j30/j3010_3`   | `de28125e10ed4379` | 61  | 62  |
| `j30/j3010_4`   | `5526e62c26ae880e` | 53  | 58  |
| `j60/j6010_1`   | `9c400697268fac68` | 85  | 85  |
| `j60/j6010_10`  | `11793a5c0a25c3a1` | 73  | 73  |
| `j60/j6010_2`   | `bd14308ea049193b` | 62  | 62  |
| `j120/j12010_1` | `99dd309553f879c2` | 111 | 111 |
| `j120/j12010_10`| `6620267bb2135837` | 66  | 66  |

## Le point de protocole que cette distillation mûrit

Le banc d'essai source choisit ses instances par `sorted(glob(...))[:k]`. En ordre
lexicographique, `j3010_*` précède `j301_*` parce que le chiffre `0` (0x30) précède le
souligné `_` (0x5F). La table de références est clavetée sur `j301_*` : la jointure ne trouve
donc rien et la colonne d'écart reste vide sur les dix lignes publiées. Le protocole est ici en
cause, jamais les auteurs — les makespans, eux, sont exacts.

App-29 a déjà doté CoursIA d'un contrat qui **refuse** une jointure dont l'identité ne
correspond pas. App-31 en traite la question complémentaire : **sur quoi se rabattre quand la
référence externe manque légitimement ?** La réponse proposée est une hiérarchie de bornes
calculables sans référence — chemin critique et borne de charge — de sorte qu'une jointure
absente dégrade vers une garantie plus faible mais mesurée, au lieu d'une colonne vide.

## Ce que cette distillation ajoute au rendu source

La section RCPSP/max du rendu pose le modèle général par décalages généralisés
`start[j] - start[i] >= delta`, formellement correct et capable de porter des lags maximaux.
L'instance de démonstration et le récit n'exercent toutefois qu'un décalage *minimum négatif*,
c'est-à-dire un assouplissement, jamais un lag *maximal*. Or le lag maximal est exactement ce
qui fait la spécificité du RCPSP/max : il s'encode par un arc inverse, introduit un cycle dans
le digraphe temporel, et fait basculer la **faisabilité** elle-même dans NP-difficile
(Bartusch, Möhring et Radermacher, 1988), alors qu'en RCPSP pur l'ordonnancement série est
toujours réalisable. App-31 construit ce phénomène, le détecte en temps polynomial par
recherche de cycle de poids positif, et sépare les trois régimes d'infaisabilité.

Aucune de ces notions n'existait dans CoursIA : `RCPSP/max`, `time lag`, `Bartusch` et
`resource strength` y comptaient zéro occurrence avant ce notebook.

## Niveaux de preuve et limites

- `OPTIMAL` signifie que le solveur a certifié l'incumbent ; `FEASIBLE` reste une solution
  valide mais non certifiée ; `INFEASIBLE` sous budget fini n'est concluant que si le solveur
  le déclare, jamais par épuisement du temps.
- L'infaisabilité **temporelle** est certifiée en temps polynomial par un cycle de poids
  positif, indépendamment de tout solveur. L'infaisabilité **en ressources** ne l'est pas.
- Les expériences portent sur de petites instances synthétiques déterministes. Elles enseignent
  un protocole ; elles ne constituent ni une étude de performance ni une revalidation de PSPLIB.
- Les mesures PSPLIB du tableau ci-dessus sont des observations d'audit sur un snapshot daté,
  reproductibles à partir de la bibliothèque d'origine, non redistribuées ici.
