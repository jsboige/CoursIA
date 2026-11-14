# InformationQuantique — états mixtes, séparabilité et distillabilité

Sous-série Physique de la collection [MyIA.AI.Notebooks](../../README.md), ouverte par l'issue
[#26489](https://github.com/jsboige/CoursIA/issues/26489). Elle prend un objet que la sous-série
[Chaînes](../Chaines/README.md) ne traite pas : non
pas un *état pur* maximalement intriqué, mais un **état mixte** — un objet dont on ne peut pas dire
qu'il est « intriqué » ou « séparable » sans passer par un critère.

Le patron reste **Mesuré / Cité / Ouvert**, avec une répartition propre à cette sous-série : tout
ce que le code du carnet calcule est **Mesuré** (pages réduites, négativités, bornes PPT obtenues
par bissection, seuil de la récurrence de Bennett, distillation par filtrage local, seuil et indice
de brisage d'un canal) ; les critères et leurs résultats — Peres 1996, Horodecki 1996,
Bennett et al. 1996, Horodecki-Shor-Ruskai 2003 — sont **Cités** ; et la question « tous les états
NPT sont-ils distillables ? », comme le fait que PPT ne suffit plus en dimension 3 et au-delà, sont
**Ouverts**. Les publications utilisées sont archivées au gisement partagé avant écriture et citées
avec leur chemin exact ; aucun PDF n'est versionné dans le dépôt.

| Carnet | Ce qu'on y apprend | Outils |
|---|---|---|
| [InfoQuant-01 — États mixtes, intrication, PPT et distillabilité](InfoQuant-01-Etats-Mixtures-Intrication-PPT-Distillabilite-Python.ipynb) | Construire matrices de densité, pages réduites et purifications ; voir le critère de la page réduite échouer sur un état mixte ; mesurer la borne séparable d'un témoin d'intrication ; mesurer par bissection les bornes PPT des familles de Werner et isotrope ; lire la fraction de singlet, la récurrence de Bennett et le filtrage local ; décider par la matrice de Choi si un canal brise l'intrication, et mesurer son indice de brisage. | numpy |

## Comment lire ce README — Découverte

- **Vous découvrez** : commencez par le carnet lui-même. Chaque section part d'un objet
  manipulable — une matrice de densité, une transposition partielle, un filtre — et finit sur une
  valeur lue dans la sortie de la cellule qui précède.
- **Vous approfondissez** : les six exercices sont là pour cela. Ils ne demandent pas de
  réinventer les critères : ils demandent de **les employer sur un état qu'on n'a pas encore
  regardé**, puis de dire ce que la mesure prouve et ce qu'elle ne prouve pas.
- **Vous explorez les fondements** : la fin du carnet liste la question encore ouverte, et le
  dossier `Références` donne les sources primaires à relire si vous voulez la formulation
  d'origine plutôt que son résumé.

## Approfondissements

- **Le lien avec la sous-série Chaînes** : [Chaînes-01](../Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb)
  emploie « intrication » dans un autre sens — un lien entre deux systèmes dans un état **pur**,
  soumis à un plafond de lisibilité. Les deux carnets partagent le mot, pas l'objet ; les lire de
  suite lève la confusion.
- **Le pont vers la preuve formelle** : [Lean-13b — CHSH et Tsirelson](../../SymbolicAI/Lean/Lean-13b-CHSH-Tsirelson-Native.ipynb)
  traite la non-localité par un organe de preuve, là où le présent carnet la traite par le calcul
  numérique d'un témoin.
- **L'organe le plus proche dans le dépôt** : [Constructeur-01](../Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb)
  contient une fonction `negativite(rho)`, à comparer avec la section sur le critère PPT.

## Ce que la sous-série ne prétend pas

Elle ne prétend pas produire un exemple d'état PPT **intriqué** : cela demande un critère que le
carnet n'implémente pas, et le carnet le dit explicitement plutôt que de le contourner. Elle ne
calcule pas non plus l'indice de brisage par puissance tensorielle, distinct de l'indice par
itération qu'elle mesure.

[Retour à la série Physique](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
