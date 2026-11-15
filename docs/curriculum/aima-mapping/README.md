# Cartographie du parcours sur les tables des matières d'AIMA (3e et 4e édition)

Ce dossier contient les **données** de la correspondance entre le parcours
piloté du dépôt ([`aima-walk.md`](../aima-walk.md)) et les tables des matières
des deux éditions d'*Artificial Intelligence : A Modern Approach* de Russell et
Norvig, archivées dans le gisement bibliographique partagé.

Issue de référence : #24997 (EPIC #24993).

## Ce que contient ce dossier

|Fichier|Contenu|
|---|---|
| `aima3e-toc.csv` | Table des matières de la 3e édition : parties, chapitres, sections, avec l'ancre PDF de chaque ligne |
| `aima4e-toc.csv` | Table des matières de la 4e édition, même format |
| `aima-editions-correspondance.csv` | Correspondance section par section entre les deux éditions (statut et similarité) |
| `aima-walk-sections.csv` | Couverture : section du livre → phase du parcours → carnets → codes de compétence |
| `aima-walk-chapitres.csv` | Couverture au niveau chapitre : chapitre cité par le parcours → pendant en 3e, motif, décalage de numérotation |
| `aima-hors-livre.csv` | Ce que le parcours déclare lui-même comme dépassant le livre |
| `aima-mapping-resume.json` | Résumé chiffré de la correspondance |

Les **PDF ne sont jamais copiés dans le dépôt** (règle `bibliography-hygiene`) :
chaque ligne porte le numéro de page PDF où son titre est vérifiable, ce qui
suffit à la recontrôler contre l'archive.

## Méthode

### Extraction

- **3e édition** : le PDF porte un signet (outline) à trois niveaux. Chaque
  entrée du signet donne directement sa page PDF ; le titre est ensuite
  vérifié **sur cette page**. Les sept **intitulés de partie** ne figurent
  nulle part comme titre de page dans le livre : ils sont ancrés dans la table
  des matières imprimée, où le numéro romain est seul sur sa ligne et
  l'intitulé juste dessous.
- **4e édition** : le PDF n'a pas de signet. La table des matières est lue dans
  le texte des pages liminaires, puis chaque entrée est ancrée dans le corps du
  livre par un balayage séquentiel (l'ordre de la table est l'ordre du livre).

Les deux tables sont donc **vérifiables ligne à ligne** : le titre d'une ligne
est celui qui figure à la page PDF indiquée.

### Correspondance entre les deux éditions

Trois passes, dans cet ordre :

1. **Identité de titre** — titres normalisés (ligatures, apostrophes, tirets) ;
   l'appariement est exact.
2. **Renommages déclarés** — la 4e édition a renommé un certain nombre de
   sections (« Games » → « Game Theory », « Alpha–Beta Pruning » → « Heuristic
   Alpha–Beta Tree Search », etc.). Ces renommages sont **déclarés explicitement**
   dans le script, motif à motif, et non déduits d'une similarité automatique.
3. **Reformulations** — pour le reste, la similarité est le maximum du rapport
   de séquence et du Jaccard sur jetons significatifs, au-dessus d'un seuil, à
   condition que les deux titres partagent au moins deux jetons significatifs
   et qu'aucun des deux ne soit générique (« Introduction », « Applications »,
   « Summary », « Learning Algorithms »…).

Les chapitres sont appariés par **vote de sections** (un chapitre de la 4e est
jumeau du chapitre de la 3e qui partage le plus de sections), puis la table des
correspondances **déclarées** corrige le tir : fusions, scissions et décalages
de numérotation ne se déduisent pas d'un vote.

### Couverture du parcours

Le parcours cite ses chapitres par leur numéro dans la 4e édition. La
couverture est donc résolue en 4e, puis ramenée au pendant 3e par la
correspondance : une section de la 3e est dite couverte lorsque la phase qui
couvre son jumeau 4e la couvre.

## Reproduction

```bash
python scripts/research/aima_mapping.py toc   --out-dir docs/curriculum/aima-mapping
python scripts/research/aima_mapping.py map   --out-dir docs/curriculum/aima-mapping
python scripts/research/aima_mapping.py check --out-dir docs/curriculum/aima-mapping
```

`toc` extrait et vérifie les deux tables des matières, `map` produit la
correspondance et la couverture, `check` contrôle la cohérence interne — que
chaque ligne de couverture renvoie à une section présente dans la table —
sans rouvrir les PDF (la re-vérification des ancres est le rôle de `toc`).
Les PDF sont lus depuis `G:\Mon Drive\MyIA\IA\Bibliographie IA\AI` (option
`--bib-dir` pour un autre emplacement).

## Correspondance section → phase → carnets → compétences

`aima-walk-sections.csv` porte, pour chaque section des deux éditions :

- `phases` — la ou les phases du parcours qui la couvrent ;
- `carnets` — les carnets que ces phases ouvrent ;
- `competences` — les codes RCA / RCE / AI4K12 attaches à ces étapes, lus dans
  [`aima-walk-competences.md`](../aima-walk-competences.md) ;
- `couvert` — `oui` si une phase la prend en charge, `non` sinon ;
- `page_pdf` — l'ancre de vérification.

Le parcours ne couvre pas le livre entier : il en prend un chemin, et ce chemin
est ce que le tableau enregistre. Les chapitres couverts sont ceux que le
parcours cite ; les chapitres entiers qu'il ne cite pas apparaissent avec
`couvert = non` sur toutes leurs sections.

## Sections sans couverture

La liste complète et à jour est dans `aima-walk-sections.csv` (filtre
`edition = 4e`, `niveau = section`, `couvert = non`). Elle se lit par chapitre :

|Chapitre 4e|Sections non couvertes|
|---|---|
| 1 — Introduction | 1.1 à 1.5 |
| 2 — Intelligent Agents | 2.1 à 2.4 |
| 9 — Inference in First-Order Logic | 9.1 à 9.5 |
| 13 — Probabilistic Reasoning | 13.1 à 13.5 |
| 14 — Probabilistic Reasoning over Time | 14.1 à 14.5 |
| 15 — Probabilistic Programming | 15.1 à 15.4 |
| 17 — Reinforcement Learning | 17.1 à 17.5 |
| 18 — Multiagent Systems | 18.1 à 18.4 |
| 19 — Learning from Examples | 19.1 à 19.9 |
| 20 — Learning Probabilistic Models | 20.1 à 20.3 |
| 25 — Computer Vision | 25.1 à 25.7 |
| 26 — Robotics | 26.1 à 26.10 |
| 27 — Philosophy, Ethics, and Safety of AI | 27.1 à 27.3 |
| 28 — The Future of AI | 28.1 et 28.2 |

Les chapitres 3 à 8, 10 à 12, 16, 21 à 24 sont intégralement couverts.

## Ce qui dépasse le livre

Le parcours ne prétend pas suivre le livre ; il le dépasse en des points
nommés, et il **marque lui-même** ces dépassements dans son texte.
`aima-hors-livre.csv` les relève, avec une colonne `nature` qui distingue
deux choses que le parcours écrit autrement mais qui ne se confondent pas :

- **`hors_livre`** — le passage sort du livre : il n'a pas de chapitre
  correspondant ;
- **`jonction`** — le passage reste rattaché à un chapitre du livre, mais il est
  **relu** par le dépôt dans ses termes modernes.

### Dépassements (`nature = hors_livre`)

- **Phase 2, étape 5** — l'ouverture sur les métaheuristiques composées (série
  MetaGeneticSharp) est déclarée « au-delà d'AIMA » ;
- **Épilogue, étape 25** — la théorie de l'information intégrée est déclarée
  « hors AIMA, propre au dépôt ».

Deux débordements sont en outre portés par les en-têtes de phase, dans la
colonne `hors_livre` de `aima-walk-chapitres.csv` :

- **Phase 7** — l'approfondissement multi-agents est déclaré au-delà du seul
  chapitre 5 (« ch. 5 approfondi + théorie des jeux ») ;
- **Phase 10** — les carnets Langage et LLM sont déclarés « actualisés » par
  rapport aux chapitres 23 et 24 de la 4e édition.

### Relectures (`nature = jonction`)

- **Phase 6, étape 14** — le do-calculus et les contre-factuels sont présentés
  comme « la jonction moderne d'AIMA ch. 16 » ;
- **Phase 10, étape 24** — les modèles de raisonnement sont présentés comme
  « ce qu'AIMA appelait agents logiques, relu en 2026 ».

La distinction n'est pas cosmétique : une relecture reste adossée à un
chapitre du livre et se retrouve dans la correspondance ; un dépassement n'a
rien à quoi se comparer.

## Ce qui change entre les 3e et 4e éditions

C'est le point qui change le parcours : une même phase ne lit pas les mêmes
sections selon l'édition. Les différences ci-dessous sont **déclarées** dans
le script et reportées dans `aima-walk-chapitres.csv` (colonnes `origine` et
`motif`), chacune adossée au nombre de sections communes relevées.

### Fusions

- Les chapitres 10 (« Classical Planning ») et 11 (« Planning and Acting in the
  Real World ») de la 3e **deviennent un seul chapitre 11** (« Automated
  Planning ») dans la 4e. La Phase 8 du parcours, qui cite « ch. 10-11 », couvre
  donc les deux chapitres de la 3e par une seule citation.
- Les chapitres 22 (« Natural Language Processing ») et 23 (« NLP for
  Communication ») de la 3e **deviennent le chapitre 23** (« Natural Language
  Processing ») de la 4e. La Phase 10 cite « ch. 23-24 » et couvre les deux
  chapitres de la 3e.

### Scission

- Le chapitre 17 de la 3e (« Making Complex Decisions ») est scindé : le
  multiagent devient le **chapitre 18** de la 4e (« Multiagent Systems »), à
  côté d'un chapitre 17 réduit aux bandits et aux MDP.

### Chapitres propres à la 4e édition

- **15 — Probabilistic Programming** : la programmation probabiliste n'existe
  pas dans la 3e.
- **21 — Deep Learning** : le deep learning n'existe pas dans la 3e. La Phase 9
  cite « ch. 21-22 » ; son pendant côté 3e est donc uniquement le chapitre 21
  (renforcement learning), la 4e ajoutant le deep learning en amont.
- **24 — Deep Learning for Natural Language Processing** : idem, la Phase 10.

### Chapitre propre à la 3e édition, absent de la 4e

- Le **chapitre 19 de la 3e** (« Knowledge in Learning » : formulation logique
  de l'apprentissage, EBL, informations de pertinence, ILP) **n'existe pas** en
  4e. Aucun parcours fondé sur la 4e ne peut donc y conduire ; il faut le dire
  plutôt que de laisser croire à une correspondance.

### Décalages de numérotation

Le parcours cite ses chapitres en numérotation 4e. Les chapitres qui suivent
sont décalés :

- Knowledge Representation : 3e ch. 12 → 4e ch. 10 (décalage de deux chapitres,
  dû aux fusions des chapitres de planification).
- Quantifying Uncertainty : 3e ch. 13 → 4e ch. 12 (décalage de un chapitre).
- Reinforcement Learning : 3e ch. 21 → 4e ch. 22 (décalage de moins un
  chapitre, le deep learning 4e s intercalant).

La colonne `decalage` de `aima-walk-chapitres.csv` porte la valeur mesurée,
et `decalage` est vide quand la correspondance est une fusion : un décalage
n'a alors pas de sens unique.

### Structuration des annexes de chapitre

La 3e édition **agrège** en une seule section de fin de chapitre le sommaire,
les notes bibliographiques et les exercices (« Summary, Bibliographical and
Historical Notes, Exercises »). La 4e les **liste séparément** en lignes de
table des matières. Ces lignes ne sont pas des sections de contenu : elles sont
classées en `backmatter` et exclues du décompte des sections, faute de quoi
la 3e apparaîtrait avoir environ un quart de sections de plus que la 4e.

### Conséquence pour la lecture du parcours

Une phase qui cite « ch. 21-22 » ne lit pas les mêmes choses selon l'édition :
côté 4e elle ouvre le deep learning **et** le renforcement learning ; côté 3e
elle n'ouvre que le renforcement learning. C'est la raison d'être de la
correspondance : sans elle, le parcours ne peut pas être lu « par rapport au
livre » sans dire lequel.
