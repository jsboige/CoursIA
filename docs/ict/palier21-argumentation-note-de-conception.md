# Palier 21 — « Argumentation et croyances » — note de conception (capstone strate 6)

> **État : Phase 1.** Cette note est la phase 1 demandée par #23777 : elle établit le
> design, elle n'écrit ni ne modifie aucun carnet. Le carnet vient après lecture par le
> coordinateur de la note postée en commentaire sur #23777.
>
> Carte : #20298 (palier 21). Jambes : #7742 (C3, morphogenèse rhétorique),
> #13041 (recollement sur lectures réelles), #7291 (horizon altérité, **hors périmètre**).

## 0. Ce que cette note tranche

| Question de #23777 | Réponse courte |
|---|---|
| La chaîne de bout en bout | Texte argumentatif réel → codage AF → lectures hétérogènes → trajectoire de croyance → ordre causal. Cinq maillons, dont quatre déjà branchés (§2). |
| Les organes consommés | Huit organes, tous invoqués par leur module ; le capstone n'en réimplémente aucun (§3). |
| Le corpus, provenance, licence | Quatre tiers ; deux items nommables et deux témoins appariés non vendorés ; LGPL-3.0 pour le code Argumentum, CC BY-SA 4.0 pour son corpus éditorial (§4). |
| Le gate et son témoin négatif | Le gate pré-enregistré est **à moitié réfuté par la mesure** : la jambe σ ne discrimine pas au format actuel. Le capstone le re-découpe et garde trois témoins qui peuvent rougir (§5). |
| La place dans la carte | Le capstone **devient** la tête du palier 21 et ne prend **aucun numéro nouveau** ; la consolidation des trois carnets de graine en accrétions est proposée à #20298, pas exécutée ici (§6). |

## 1. Plateau mesuré

`origin/main` = `e6d89a810`, 2026-10-31. Tout ce qui suit a été vérifié à cette tête.

| Objet | État mesuré |
|---|---|
| Graine strate 6 | Trois carnets exécutés présents : `ICT-Argumentation-BeliefTrajectories-Python`, `‑QBFAcceptance‑Python`, `‑TruthMaintenance‑Python`. |
| Organes argumentation | `ict/argumentation.py` : `DungAF`, `grounded_labeling`, `preferred_extensions`, `belief_trajectory`, `state_signature`, `belief_transition_matrix`, `discourse_irreversibility`, `RefusDeMesure` + quatre `REFUS_CODES`, `segmenter_enonces`, `est_codable`, `verdict_canaux`. |
| Organes de mesure | `ict/time_arrow.py` (`entropy_production`, `trajectory_asymmetry`), `ict/mdl.py` (`two_part_code`, `tpm_description_length`), `ict/compression.py` (`compressed_length`), `ict/spectral.py`. |
| Parité Tweety | 212 cas, par `labelling_from_extension` (#23665, MERGED) ; l'organe native exige JDK 17 + JAR et **n'est pas disponible sur cette machine** — le témoin de parité est donc à router, pas à rejouer localement. |
| Recollement lectures réelles | `SymbolicAI/Argument_Analysis/Argumentation-Obs-04-Recollement-Strate6-Python.ipynb`, 54 cellules dont 21 de code, `execution_count` nul : 0. Livré par #13070 sous #13041 (issue close). |
| Gating de la tranche 3 | **Levé.** Les trois issues que l'audit du 22/10 listait comme OPEN sont MERGED : #21636 (grounded contre Tweety), #21650 (codage AF des deux discours), #21663 (jonction Argumentum). |
| Jambe C3 (#7742) | OPEN, corpus à quatre tiers défini, plan d'expérience à quatre items, trois prédictions falsifiables écrites. Bloquée non plus sur le branchement mais sur la passphrase du tier chiffré (question au registre). |

## 2. La chaîne de bout en bout

Le capstone n'est pas une démonstration de plus sur un graphe jouet : c'est le premier
point où les cinq maillons sont tenus **dans le même carnet, sur le même texte**.

| # | Maillon | Ce qui est consommé | Ce que le capstone y ajoute |
|---|---|---|---|
| 1 | **Tronc EPITA d'analyse argumentative** | `SymbolicAI/Argument_Analysis` : Toulmin, Walton, sophismes, dialogues protocolisés, JTMS/ATMS, orchestration d'agents à plugins (#18390, OPEN). | Rien — c'est le texte d'entrée et le vocabulaire de codage. |
| 2 | **AIF et sémantique de Dung** | `Argumentation-Onto-01-AIF-OWL2-Python`, `Argumentation-03-Dung-AF-Semantics-Python`, `ict.argumentation`. | L'AF est codé argument par argument **depuis le texte**, l'ordre d'arrivée étant l'ordre du texte. |
| 3 | **Corpus Argumentum réel** | Sous-module #4960, `Argumentation-02b-Argumentum-Cards-Python`. | C'est le passage au réel que la graine n'a pas fait : les objets du corpus, pas des exemples choisis. |
| 4 | **Lectures hétérogènes** | Les quatre lectures de #13041 (RDF, LEX, STRUCT, GRAPH) et la glue hors échantillon de `Obs-04`. | La trajectoire de croyance est lue par quatre lectures concurrentes, et la glue décide **où** elles ne s'accordent pas. |
| 5 | **Ordre argumentatif causal** | #7742, tranche 1 : σ de l'ordre du récit contre contre-factuel permuté ; budget de retour ; spectre. | La mesure porte sur la **trajectoire**, pas sur un catalogue de figures. |

Le maillon 5 est celui qui fait du palier 21 un palier et non une juxtaposition : sans lui,
1–4 décrivent un texte ; avec lui, ils décrivent une **transition stabilisée par la
rhétorique**, ce qui est l'objet de la strate 6.

## 3. Les organes consommés — cinq questions organ-first

Les cinq questions de `organ-first-implementation`, répondues une fois pour le capstone.

| # | Question | Réponse |
|---|---|---|
| 1 | Quelle série possède déjà la sémantique ? | `SymbolicAI/Argument_Analysis` pour le codage, les sémantiques de Dung et le recollement ; `IIT/ICT-Series/ict/` pour la trajectoire, la flèche du temps et la longueur de description. **Deux séries, aucune réimplémentation.** |
| 2 | Peut-on invoquer le module réel ? | Oui, par import direct : `ict.argumentation`, `ict.time_arrow`, `ict.mdl`, `ict.compression`, `ict.spectral`. Aucun de ces organes n'est recopié dans le carnet. |
| 3 | Que faut-il exporter / refactorer dans la série source ? | Rien d'obligatoire. Un seul point d'interface à ajouter : une fonction d'assemblage qui rend, pour une trajectoire donnée, le triplet **(σ, K, ordre)** en un appel — aujourd'hui trois imports et trois formats de retour. Elle vit dans `ict/`, pas dans le carnet. |
| 4 | Quel témoin négatif l'organe natif fournit-il ? | Quatre, listés en §5, dont un qui a **déjà rougi** (σ sur les graphes nuls) et un qui rougit par construction (`RefusDeMesure`). |
| 5 | Quelle autre série vérifie indépendamment ? | Tweety comme second oracle (`Argumentation-00-Setup-Tweety`, 212 cas, #23665), et Argumentum comme second oracle du codage (#21663). Deux oracles pour un même codage : c'est la vérification indépendante. |

**Ce que le capstone ne fait pas** : recoder un solveur de Dung, recoder une sémantique de
labelling, recoder un estimateur de production d'entropie, ni recoder un compresseur. Une
copie pédagogique déclarée n'est même pas nécessaire ici : tous les organes sont invoquables.

## 4. Le corpus, sa provenance et sa licence

Le corpus est celui de #7742, inchangé. Quatre tiers, avec la forme qu'ils prennent dans le
dépôt — cette table est la référence, elle ne se recompose pas.

| Tier | Contenu | Forme dans le dépôt | Licence / droits |
|---|---|---|---|
| Public en clair | Œuvres du domaine public — La Fontaine, tier fables | Texte versionné | Domaine public |
| Nommable chiffré | Anschluss 1938, Matsui 1933 (transcriptions circulant librement) | `*.json.gz.enc`, passphrase remise au cours | Exception nominative écrite dans #7742, et **seulement** ces trois sources |
| Référence + fetch runtime | Chaplin, *Le Dictateur* 1940 — discours final et meeting de Hynkel | **Jamais vendorés** ; `fetch_method` + chemin, texte récupéré à l'exécution | Roy Export S.A.S. — le texte n'entre pas dans le dépôt |
| Hors CoursIA | Le reste du corpus EPITA | Reste chez EPITA, chiffré, **non énuméré** | — |

**Le code Argumentum est sous LGPL-3.0** (`LICENSE` du sous-module), **son corpus éditorial
sous CC BY-SA 4.0** (`LICENSE-CONTENT.md`, périmètre énuméré fichier par fichier et non
déduit d'un répertoire). Les deux licences sont distinctes et le sous-module le dit lui-même :
un fichier hors de la liste du §1 de `LICENSE-CONTENT.md` **n'est pas** sous CC BY-SA.
Le capstone cite cette distinction dans son propre en-tête, parce qu'il consomme les deux.

**Le corpus réel, en volume mesuré** (sous-module à `9038690d`, le gitlink épinglé par `main`) :
`Cards` porte 803 fichiers, dont 7 fichiers de texte sous CC BY-SA — 12 976 438 octets au total,
soit 13,0 Mo en décimal. Le plus lourd est
`Cards/Fallacies/Argumentum Fallacies - Taxonomy.csv` (1526 lignes, 4 178 565 octets, 104 champs en
ligne 1), suivi des deux ontologies (`docs/ontology/argumentum.owl`, 96 069 lignes, 5 993 701 octets).
Les sept fichiers du périmètre sont stables d'un pin à l'autre : sur l'intervalle qui sépare le
commit les précédant (`d257443d`) du gitlink, une seule variation les touche — la taxonomie des
vertus, de six octets — et les 53 fichiers que cet intervalle modifie par ailleurs sont des
mindmaps (`Cards/Fallacies/Mindmaps/**`), hors du périmètre CC BY-SA.
La provenance du corpus éditorial est nommée dans sa propre licence :
`LICENSE-CONTENT.md:91`, « le corpus est l'œuvre de Jean-Sylvain Boige et des contributeurs
du projet Argumentum ». Le capstone consomme donc un corpus dont le dépôt détient les droits,
et les deux fichiers explicitement exclus de CC BY-SA (`regles.md` / `rules.md`, et
`Cards/Rules/Argumentum Rules - Cards.old.csv`) ne sont pas lus comme corpus.

**Ce que le chiffrement achète, et qu'il ne faut pas sur-vendre** : de la
**non-indexabilité**, pas de la confidentialité — la passphrase doit atteindre les étudiants,
donc elle est de fait publique. Cette formulation figure telle quelle dans le README du
répertoire de corpus (#7742), et le capstone ne la reformule pas plus favorablement.

## 5. Le gate — et ce qui est déjà rouge

### 5.1 La prédiction pré-enregistrée

La strate 6 porte une dette d'irréversibilité du discours : un régime qui bascule les
croyances **à sens unique** est irréversible (σ élevé) tout en restant **compressible**
(slogans, K faible) ; un régime délibératif met à jour réversiblement (σ faible) avec une
nuance incompressible (K élevé). C'est la prédiction pré-enregistrée de la strate, et c'est
elle que le capstone doit mesurer sur un corpus réel.

### 5.2 Ce que la mesure dit déjà, et qui contredit la moitié de cette prédiction

Un audit contradictoire daté du 2026-10-22 (commentaire sur #7742) a mesuré le carnet de
graine cellule par cellule. Trois constats, tous vérifiables dans les sorties committées :

1. **σ vaut exactement 0 sur les 30 graphes nuls**, et environ 2e-06 à 2,8e-07 sur les
   régimes réels (cellules 19, 24, 34) : c'est du bruit flottant. Un null sans dispersion
   n'a **aucune résolution** — le `z = +inf` de la cellule 15 veut dire « pas de nuage »,
   pas « hors du nuage ». Les cellules 21 et 24 disent elles-mêmes « σ non discriminant ».
2. **`attack_adjacency_symmetric()` efface la direction des attaques avant le calcul du
   spectre** (cellule 12). Or la direction est précisément ce qui sépare un régime populiste
   d'un régime délibératif : le PASS de P-disc-2 ne porte donc que sur des graphes non
   orientés.
3. **`belief_return_budget` ne sort que `1.0000` ou `0.0000`** (cellules 14, 20, 26, 34) :
   c'est un indicateur binaire, pas un budget. La prose sur les « budgets élevés » ne porte
   que ce binaire. Et P-disc-3 a été testée autrement que pré-enregistrée (départ sur un π
   bruité, `B_monoculture` jamais mesuré, seuil `B_div < 0.05` non pré-enregistré — porté par
   #17211).

### 5.3 Le gate re-découpé

Conséquence : **la jambe σ de la prédiction est traitée comme réfutée au format actuel, pas
comme provisoirement bruitée.** C'est un livrable, pas un échec — #23777 l'écrit : « un
résultat négatif est un livrable à part entière ; il ne se reformule pas en résultat partiel ».

Le gate du capstone tient donc sur trois lectures, dont deux que la mesure a déjà
discriminantes et une en ré-établissement :

| Jambe | Instrument | Statut mesuré |
|---|---|---|
| Irréversibilité (σ) | `ict.time_arrow.entropy_production`, `discourse_irreversibility` | **Non discriminante à la taille disponible** ; ré-essayée seulement là où un null avec dispersion existe, sinon rapportée comme non résolue. |
| Compressibilité (K) | `ict.mdl.tpm_description_length`, `ict.compression.compressed_length` | Instrument disponible ; la discrimination reste à mesurer, elle est un des résultats attendus du capstone. |
| Ordre causal | σ de l'ordre du récit contre contre-factuel permuté (#7742 tranche 1) ; longueur de description à ordre de Markov croissant (`fit_markov_order`) | Contrôle de sensibilité à l'ordre **retenu** ; à petite taille c'est l'ordre et la longueur de description qui séparent, pas σ. |

Ce re-découpage n'est pas une invention de cette note : le carnet de graine l'écrit lui-même,
en tête de son bandeau d'ouverture (cellule 1) — « la discrimination passe à **K (code MDL deux
parties)** et à la **trajectoire à ordre fixe** ; l'issue de l'englobement est une
**chronologie** (la clause de clôture arrivée en dernier décide), pas une topologie ». La
cellule 27 nomme le même fait sur le spécimen : « dans les deux récits, la bascule terminale
est opérée par l'énoncé arrivé en dernier ». Le capstone **prend acte** de ce déplacement
d'instrument et le porte dans son gate au lieu de continuer à lire σ.

**Aucune des trois n'est agrégée en un scalaire.** La leçon de `dissolution-scalaires.md`
tient : quatre phénomènes de complexités distinctes ne se réduisent pas à un nombre unique ;
le gate est un **triplet**, pas une note.

### 5.4 Les témoins négatifs qui peuvent rougir

Un gate sans témoin négatif n'est pas un gate. Quatre, chacun avec sa condition de rouge :

| Témoin | Attendu | Ce qui le fait rougir |
|---|---|---|
| **Fragment Hynkel** (meeting, contenu propositionnel nul, deux canaux contradictoires) | `RefusDeMesure[CANAUX_CONTRADICTOIRES]` ou `[AUCUN_ENONCE_CODABLE]` — **un type de sortie, pas un seuil** | Tout score émis (σ, K ou budget) le réfute, y compris un score bas. Un détecteur de mots-clés produira un nombre ici. |
| **Discours final de Chaplin** (englobement de contenu **inversé**) | Même structure, **signe inversé** de la variété parcourue | *Rien détecté* = détecteur de mots-clés ; *même signe que les cas réels* = lecture du décor. |
| **Graphes nuls** (contrôle apparié) | σ = 0 exactement, **et un null avec dispersion** | Un null sans dispersion rend `z` infini et donc la lecture σ **vide** — c'est déjà arrivé, c'est le constat §5.2.1. |
| **Recollement** (glue contre meilleur spécialiste, hors échantillon) | La glue bat le meilleur spécialiste **sur la zone disputée** | Une glue qui gagne globalement et perd sur la zone disputée est le résultat synthétique d'ICT-34, et il compte comme non-transfert. |

Le corpus porte de quoi faire rougir ces quatre-là **avant** de conclure quoi que ce soit sur
le régime populiste : c'est l'ordre de montée du plan d'expérience de #7742 (fables, puis les
deux témoins, puis les cas historiques). Le capstone respecte cet ordre — il ne mesure pas le
cas historique en premier.

## 6. Place dans la carte, et ce que le capstone retire de la numérotation

**Le capstone devient la tête du palier 21.** La carte du 2026-10-11 donne à ce palier
« Argumentation et croyances » la tête `ICT-Argumentation` ; le capstone prend cette place,
parce qu'il est le seul carnet du palier qui tienne les cinq maillons ensemble.

**Il ne prend aucun numéro.** C'est la consigne du 2026-10-31 : un carnet ICT nouveau ou
déplacé ne prend pas le numéro qui suit le maximum, il rejoint le palier qu'il sert, et les
derniers numéros sont pour la strate 7. Le capstone rejoint le palier 21.

**Ce qu'il retire de la numérotation** : les trois carnets de graine cessent d'être « la
graine, en trois carnets » et deviennent les **accrétions** du palier — le capstone les
consomme, il ne les duplique pas. Concrètement, un lecteur de la série n'a plus à décider
lequel des trois ouvrir en premier : il ouvre la tête.

**Ce que cette note ne fait pas** : le renommage et le déplacement des trois carnets de graine
relèvent de #20298, et #23777 les met explicitement hors périmètre. La note **propose** la
consolidation, elle ne l'exécute pas.

## 7. Mouvement — esquisse du carnet (Phase 2, après lecture de cette note)

1. **Le corpus d'abord, pas le modèle.** Charger le tier fables (domaine public), coder l'AF
   argument par argument, ordre d'arrivée = ordre du texte. Un cas, une trajectoire.
2. **Les quatre lectures** sur la même trajectoire, et la glue hors échantillon : où les
   lectures se contredisent, et ce que la glue récupère que le meilleur spécialiste perd.
3. **Les quatre témoins négatifs de §5.4**, avant tout cas historique. Ceux qui rougissent
   rougissent ici.
4. **Le triplet (σ, K, ordre)** sur les cas réels, avec le null apparié et sa dispersion
   rapportée explicitement — c'est la réparation du constat §5.2.1.
5. **Trois exercices** (aucune erreur volontaire, stubs `pass` / `print` / `return None`) :
   construire un AF délibératif que les mesures classeraient irréversibiliste (l'exercice
   existe déjà en graine et reste le bon), lire un refus de mesure comme un résultat, et
   choisir entre deux lectures concurrentes sur une entrée disputée.

## 8. Non-touché (délibéré)

- **#7291** (horizon altérité, GATED) — hors périmètre de #23777.
- **Le déplacement des trois carnets de graine** — #20298.
- **Le corpus contemporain / polémique** — reste chez EPITA, chiffré, non énuméré ; il ne se
  cite pas, même dans cette note.
- **Tweety** — le capstone consomme la parité mesurée (212 cas) ; il ne rejoue pas la JVM,
  absente de cette machine, et le dit au lieu de sauter le point en silence.
- **Aucun carnet n'est créé ni modifié par ce document.**

## 9. Ré-exécution

Le carnet de Phase 2 sera exécuté de bout en bout et committé avec ses sorties (C.2), trois
exercices, aucune erreur volontaire. Les deux items Chaplin sont récupérés à l'exécution par
`fetch_method` : leur indisponibilité est un `RefusDeMesure[SOURCE_INDISPONIBLE]`, pas un zéro.

## 10. Questions ouvertes

1. **La magnitude du recollement n'est pas stable, le signe l'est.** Deux mesures publiées du
   même protocole donnent : au pin `1bc80e5d` (08/09) 56,6 % contre 49,7 % sur la zone
   disputée ; sur `main` aujourd'hui 54,7 % contre 47,4 % (344 entrées). Le verdict — la glue
   bat le meilleur spécialiste, et la majorité brute nuit — est identique aux deux pins. Le
   capstone consomme donc **le protocole, pas le nombre**, et rapporte les deux mesures plutôt
   qu'une seule. Reste à établir la cause de l'écart (ré-exécution, découpage des folds,
   version des estimateurs) : c'est un diagnostic de dérive à faire en Phase 2, pas à supposer ici.
2. **La passphrase `ICT_S6B_PASSPHRASE`** n'est pas encore parvenue à cette lane (question au
   registre). Sans elle, les deux items du tier chiffré restent `SOURCE_INDISPONIBLE`, et le
   carnet peut néanmoins livrer les maillons 1–4 sur le tier public plus les deux témoins.
3. **Faut-il une fonction d'assemblage `(σ, K, ordre)` dans `ict/`** (§3, question 3), ou trois
   appels dans le carnet ? La note recommande la fonction, parce qu'un triplet mesuré trois
   fois de trois façons dans un carnet est trois occasions de divergence. Décision au
   coordinateur, elle engage `ict/` et pas seulement le carnet.
