# Schéma de motifs et de réactions de Game of Life — tranches 1-4 de #15635

Le moteur cellulaire de #15571 cherche un motif en énumérant des cellules dans
une boîte, puis en encodant son évolution en SAT. Son espace de recherche croît
avec la surface, la période et la cardinalité, et il ignore tout ce que la
communauté Life sait déjà des briques connues (still lifes, catalyseurs,
oscillateurs, collisions de gliders, tronçons de pistes Herschel).

Cette tranche ajoute la couche **symbolique** qui manquait : un format
machine-readable pour décrire des *motifs/composants* et des *réactions*, avec
la propriété qui la rend utile — **aucune métadonnée déclarée n'est acceptée sur
confiance**. Chaque champ numérique est re-dérivé par replay dans le moteur Life
du dépôt (`scripts/lean/life_synthesize.py`) et comparé à ce que le document
prétend. Un écart est un refus, pas un avertissement.

Le module est [`scripts/lean/life_components.py`](../../scripts/lean/life_components.py) ;
le catalogue curé est [`scripts/lean/life_components_fixture.json`](../../scripts/lean/life_components_fixture.json).

## Ce que la tranche couvre — et ce qu'elle ne couvre pas

| Section de #15635 | État |
|---|---|
| §1 schéma minimal versionné (motifs + réactions) | **livré** |
| §2 catalogue reproductible réduit, rejoué indépendamment | **livré** |
| §3 générateur de contraintes compositionnelles | **livré** ([`life_compose.py`](../../scripts/lean/life_compose.py)) |
| §4 démonstrateur multi-composants + ablations de pruning | **livré** (objectifs, verdicts, ablations ci-dessous) |

Le schéma porte les champs que #15635 nomme pour §1, mais **tous ne sont pas
encore validés mécaniquement** — la distinction est explicite ci-dessous.

## Motif : ce qui est mesuré

Un motif déclare son identifiant, sa provenance, ses cellules canoniques, sa
règle, sa période, sa translation par période, sa population, sa boîte initiale,
son enveloppe sur un cycle et ses symétries autorisées. Sont **recalculés par
replay** puis comparés :

- la **période** — la plus petite `p` telle que `evolve^p T` soit `T` à
  translation près (une période déclarée trop grande est refusée : elle n'est pas
  la période du motif, c'est un de ses multiples) ;
- la **translation** par période, et par conséquent la direction et la vitesse ;
- la **population**, la **boîte initiale**, l'**enveloppe** sur un cycle ;
- la **catégorie** (`still_life` / `oscillator` / `spaceship`), dérivée de la
  période et de la translation plutôt que crue sur parole ;
- la **forme canonique** des cellules (translation ramenée à l'origine, liste
  triée) ;
- les **phases** déclarées, si le document en porte.

Le champ `rule` n'accepte que `B3/S23` : c'est la seule règle que le moteur du
dépôt implémente, et prétendre en valider une autre serait une preuve non
fournie.

## Canonicalisation : normaliser sans fusionner

Deux formes sont « le même objet » si l'une s'obtient à partir de l'autre par
une symétrie **qui préserve son vecteur de translation**. Cette restriction
n'est pas cosmétique : sous le groupe diédral complet, les quatre orientations
d'un glider se confondraient, et la direction de vol — précisément ce qu'une
réaction compositionnelle doit contraindre — disparaîtrait.

| Translation | Symétries admissibles |
|---|---|
| `(0, 0)` (still life, oscillateur) | groupe diédral complet |
| `(1, -1)` (glider du dépôt) | `T`, `D2` |
| `(-1, -1)` (`glider_mirror`) | `T`, `D1` |
| `(-2, 0)` (`lwss`) | `T`, `My` |

Conséquence testée : `glider` et `glider_mirror` ont la même forme à une
réflexion près mais des translations opposées — `same_object` répond **faux**.
Déclarer une symétrie inadmissible est un refus.

## Réaction : ce qui est mesuré

Une réaction déclare ses réactifs et produits (placements de motifs, ou cellules
brutes quand le produit n'est pas un objet catalogué), ses ports, son décalage
temporel, son temps de stabilisation, sa région occupée, ses zones de clearance,
sa nature et sa provenance. Sont **recalculés par replay de l'évolution jointe** :

- le **produit** : l'état à `t = stabilization_time` doit égaler exactement le
  produit déclaré, et être **stable** (`step(état) == état`). Une réaction dont
  le produit est mobile est hors du domaine de ce validateur — c'est une limite
  assumée, pas un silence ;
- les **zones de clearance** : aucune cellule vivante ne doit y passer, à aucun
  pas de la fenêtre. C'est le contrôle négatif de l'absence d'interaction
  parasite ;
- la **région occupée** : boîte englobante de tout ce qui a vécu pendant la
  fenêtre ;
- la **nature** (`consumable` / `reusable` / `catalytic`) : mesurée par survie
  d'un réactif dans l'état final, à translation près.

Les **ports** sont validés structurellement (nom, direction non nulle, position
dans la région occupée). Leur *sémantique de compatibilité* — quel port de quel
composant peut en rencontrer un autre, à quelle phase — est livrée par la
couche compositionnelle de §3 (section « Ports » ci-dessous).

## Le catalogue curé

Six motifs et trois réactions, tous **rejoués** à chaque validation :

| Motif | Catégorie | Période | Translation | Population | Enveloppe |
|---|---|---:|---|---:|---|
| `block` | still_life | 1 | `(0, 0)` | 4 | 2×2 |
| `blinker` | oscillator | 2 | `(0, 0)` | 3 | 3×3 |
| `toad` | oscillator | 2 | `(0, 0)` | 6 | 4×4 |
| `glider` | spaceship | 4 | `(1, -1)` | 5 | 3×3 |
| `glider_mirror` | spaceship | 4 | `(-1, -1)` | 5 | 3×3 |
| `lwss` | spaceship | 4 | `(-2, 0)` | 9 | 5×4 |

| Réaction | Nature | Stabilisation | Produit mesuré |
|---|---|---:|---|
| `glider_pair_annihilation` | consumable | 12 | vide (annihilation complète) |
| `glider_pair_two_blocks` | consumable | 5 | deux `block` |
| `block_catalyses_glider` | catalytic | 8 | un `block` (le réactif poussé de `(4,2)` à `(2,3)`, zéro débris) |

La troisième réaction est délibérément **non triviale** : le produit n'est pas la
forme du réactif, donc « le bloc survit » est une mesure qui discrimine. Un cas
où le produit serait exactement la forme du catalyseur serait vrai par
construction et ne prouverait rien.

Elle a été **re-mesurée en tranche 3** à partir du dernier état pur de
l'approche naturelle du glider (phase 3, bloc à `(4,2)`) : le placement de la
tranche 1+2 (phase 0, bloc `(3,0)`) démarrait au milieu de l'interaction et
était inatteignable par dérive pure — sa precondition porte désormais
l'exigence d'atteignabilité, et le détail est dans la section « Deux leçons
mesurées » ci-dessous.

## La couche compositionnelle — tranche 3

Le module [`scripts/lean/life_compose.py`](../../scripts/lean/life_compose.py)
cherche des **compositions d'événements** du catalogue : un objectif borné
(`Goal`) déclare des comptages finaux minimaux, des événements requis, des
plafonds (événements, composants, gliders), un horizon et une surface ; le
moteur énumère les placements d'événements qui satisfont toutes les contraintes
simultanément, puis **certifie** chaque témoin candidat par replay indépendant
dans le moteur du dépôt. Le modèle de recherche est propositionnel, exact et
borné :

- un **spawn** `(motif, ancre, phase)` vit sur une trajectoire fermée
  `cells_at(t)`, vérifiée cellule à cellule contre `step()` pour chaque motif,
  chaque phase, trois ancres, 13 pas — zéro écart. Le compteur de périodes
  dépend de la phase de départ (`(p0 + t) // P`, pas `t // P`) : un glider
  `p0=3` à `t=1` a déjà une période complète écoulée ;
- un **événement** `(réaction, offset, t_fire, bindings)` occupe la fenêtre
  temporelle `[t_fire, t_fire + stabilisation]` et la région spatiale de la
  réaction translatée ; ses réactifs consommés disparaissent de l'état, ses
  produits naissent avec leur propre trajectoire ;
- la scène composée n'est **pas simulée pendant la recherche** : elle est
  reconstruite et rejouée intégralement à la certification seulement. C'est ce
  qui rend `FOUND` fiable alors que la recherche raisonne sur une abstraction.

### Ports : la sémantique de compatibilité (R2)

Le port d'un réactif **mobile** porte les signes de la translation par période
(le glider : `(1,-1)`) — la direction le long de laquelle il peut *atteindre*
son placement par dérive pure. Le port d'un réactif **statique** porte l'axe du
connecteur (le bloc : `(-1,0)` vers la ligne d'approche). La famille R2 rejette
tout binding dont la direction de spawn n'est pas celle du port déclaré :
direction opposée (le mobile s'éloigne), axe statique sur un réactif mobile,
translation orthogonale à la ligne du motif.

### Congruence de phase à l'arrivée (R4)

Un réactif mobile doit arriver dans la **phase déclarée** de la réaction, sinon
la fenêtre ne correspond pas au replay mesuré : `p0 = (phase_déclarée −
t_fire) mod P`. Sur les quatre phases de départ possibles d'un glider,
exactement une satisfait la congruence — le test de non-régression l'exige.

### Fenêtres spatiales (R3)

Deux événements aux fenêtres spatiales chevauchantes, ou dont un objet vivant
passe à moins de 3 (Chebyshev) des cellules d'une fenêtre étrangère, sont
rejetés — avec une exception structurelle : un produit est *par construction*
la dernière image de la fenêtre de son propre événement, il n'est jamais
confronté à elle (le replay aux bornes exactes couvre déjà cette transition).
Le seuil 3 n'est pas un réglage, c'est la mesure ci-dessous.

### Dédup d'états (R1)

La clé d'état est le **multiset des spawns et des événements complets**
(réaction, offset, `t_fire`, réactifs liés décrits par leur géométrie et leur
temps de naissance) : les objets vivants en découlent, et **l'ordre de tir des
épisodes indépendants n'y figure pas** — il n'est pas sémantique (`certify`
calcule la scène pas à pas comme une union de fenêtres indexées par le temps,
et un réactif n'est lié qu'une fois ; `goal_reached` compte des identifiants de
réaction).

Deux clés plus grossières ont produit des **faux négatifs de complétude**,
mesurés : une clé indépendante de la position avalait le produit d'un second
épisode né ailleurs ; une clé réduite à la *signature des vivants + nombre
d'événements* confondait deux scènes aux mêmes produits à des **temps de tir
différents** — sous ablation de R4, un état non certifiant partageant la clé du
témoin était déplié d'abord, le témoin était dédupliqué, et la recherche
concluait `IMPOSSIBLE_BOUNDED` alors qu'un témoin existait. Un verdict
d'impossibilité qui peut être faux n'est pas un verdict.

La clé est donc le **garde-fou de complétude** du module. Honnêtement mesuré :
sur les trois instances du démonstrateur elle ne mord **jamais** (`r1_state_dedup`
= 0) — il n'y a pas d'état régénéré à collapser dans cet ordre de parcours —,
et l'ablation de R1 est par conséquent **neutre**. La clé grossière affichait
274 nœuds là où la clé saine en explore 10 901 : sa réduction était achetée par
des confusions non fondées, pas par du travail évité. La sensibilité de la clé
à l'ancre, au temps de tir et à l'ordre est figée par un test dédié.

### Deux leçons mesurées, figées en tests de non-régression

1. **Non-interaction.** Deux ensembles de cellules à distance de Chebyshev ≥ 3
   n'interagissent jamais ; à distance 2, tout dépend du contenu. Deux blocs
   gap-1 sont stables, mais un glider à distance 2 d'un bloc engendre des
   naissances croisées — une cellule morte voit 2 voisins d'un objet plus 1 de
   l'autre. Le seuil 3 de R3 est cette mesure, pas une heuristique.
2. **Atteignabilité du placement déclaré.** Le placement tranche 1+2 de
   `block_catalyses_glider` démarrait au milieu de l'interaction : l'approche
   naturelle du glider annihile tout (population 0). La réaction a été
   re-mesurée au **dernier état pur** de l'approche (glider phase 3, bloc
   `(4,2)`), et une famille catalytique propre a été vérifiée le long de la
   diagonale d'arrivée (offsets `x+y=6` du coin : `(4,2)`, `(5,1)`, `(6,0)`,
   `(7,-1)` — tous donnent « bloc seul survit, glider absorbé, zéro débris »).
   La déclaration curée est désormais atteignable ; le placement historique est
   le contrôle négatif du test d'atteignabilité.

### Impossibilité de la réutilisation stricte — cause racine

L'objectif `two_blocks_catalyse` (réutiliser **strictement** les blocs produits
par la paire comme catalyseurs d'une seconde réaction) est `IMPOSSIBLE_BOUNDED`
pour une raison physique mesurée, pas un échec de recherche : le produit de
`glider_pair_two_blocks` est une paire de blocs gap-1 ; tout épisode catalytique
qui lie l'un des blocs met l'autre à Chebyshev 2, et le recul du bloc pendant
la transmutation fait naître des cellules dans la colonne du gap (naissances
croisées mesurées à `t=19`). Le replay exact rejette donc chaque candidat —
l'épuisement **est** la bonne réponse, et le compteur `replay_rejected ≥ 1`
l'atteste. La variante `two_blocks_catalyse_free` (le second épisode apporte
son propre bloc de catalyste) est `FOUND`.

## Démonstrateur — tranche 4

### Verdicts mesurés (base, 3 répétitions, passe séquentielle)

| Objectif | Verdict | Nœuds | Candidats | Replays rejetés | Temps | Pic mémoire |
|---|---|---:|---:|---:|---|---:|
| `two_blocks` | **FOUND** — 2 blocs en 25 pas (témoin identique ×3) | 2 | 2 | 0 | 0.004 s | 66 Kio |
| `two_blocks_catalyse` | **IMPOSSIBLE_BOUNDED** | 1 227 | 5 208 | 1 176 | 187-204 s | 1.5 Mio |
| `two_blocks_catalyse_free` | **FOUND** — 3 blocs en 61 pas, 19 cellules initiales | 10 901 | 101 | 9 | 12.6-13.4 s | 16.5 Mio |

### Ablations des familles d'élagage (3 répétitions ; la certification n'est jamais ablatable)

Budget de nœuds : 20 000 (`two_blocks`, variante libre), 4 000 (stricte — la
base y épuise à 1 227 nœuds).

| Objectif | Famille ablatée | Verdict | Nœuds | Candidats | Temps |
|---|---|---|---:|---:|---|
| `two_blocks` | — (base) | FOUND | 2 | 2 | 0.004 s |
| | R1 dédup | FOUND | 2 | 2 | 0.004 s |
| | R2 ports | FOUND | 3 | 15 | 0.02 s |
| | R3 fenêtres | FOUND | 2 | 2 | 0.004 s |
| | R4 congruence | FOUND | 2 | 1 | 0.004 s |
| `two_blocks_catalyse` | — (base) | IMPOSSIBLE_BOUNDED | 1 227 | 5 208 | 187-204 s |
| | R1 dédup | IMPOSSIBLE_BOUNDED | 1 227 | 5 208 | 181-209 s |
| | R2 ports | IMPOSSIBLE_BOUNDED | 3 588 | 31 057 | 353-357 s |
| | R3 fenêtres | IMPOSSIBLE_BOUNDED | 2 403 | 5 208 | 212-241 s |
| | R4 congruence | TIMEOUT | 4 001 | 3 111 | 385-442 s |
| `two_blocks_catalyse_free` | — (base) | FOUND | 10 901 | 101 | 12.6-13.4 s |
| | R1 dédup | FOUND | 10 901 | 101 | 12.5-12.6 s |
| | R2 ports | TIMEOUT | 20 001 | 263 | 25.7-27.0 s |
| | R3 fenêtres | FOUND | 14 720 | 101 | 4.5-4.9 s |
| | R4 congruence | TIMEOUT | 20 001 | 41 | 14.6-15.5 s |

**Lecture honnête des ablations :**

- **R2 (ports) et R4 (congruence de phase) sont décisives** : les désactiver
  fait perdre le témoin de la variante libre au plafond de nœuds (20 001 nœuds
  sans certification) et double le coût de la stricte.
- **R3 (fenêtres) ne change aucun verdict**, et son ablation est même *plus
  rapide* sur la variante libre (4.5 s contre 12.6 s) : son calcul de fenêtres
  coûte plus qu'il ne rapporte sur ces instances bornées. Sa raison d'être est
  la sûreté du modèle (rejeter les compositions aux fenêtres chevauchantes
  avant le replay) ; la certification reste le filet, couvert par un contrôle
  négatif dédié.
- **R1 (dédup) est neutre ici** : la clé saine ne collide jamais (0 collapse
  mesuré). Elle n'en est pas moins le garde-fou de complétude — sa version
  grossière produisait des faux `IMPOSSIBLE_BOUNDED` (mesuré, testé).
- Aucune ablation ne produit un verdict `IMPOSSIBLE_BOUNDED` sur un objectif
  `FOUND` : retirer un filtre élargit l'espace, le pire cas est le plafond
  (`TIMEOUT`). La propriété est structurelle — et le faux négatif mesuré sous
  ablation de R4 venait précisément d'une clé de dédup qui la violait en
  avalant un état du chemin-témoin.

### Comparaison avec la baseline cellulaire (#15571)

Le même dépôt sait chercher des still lifes par énumération de cellules :
`synthesize(1, (0,0), 5, 8)` énumère **1 807 780 candidats** en **58 s** par
répétition sur la même cible (81 still lifes, cible trouvée, contenu identique
sur les trois répétitions ; 70-77 s sous la charge des trois rapports complets
lancés en parallèle). La couche compositionnelle répond à ses objectifs en
millièmes à dizaines de secondes, avec des espaces de recherche comptés en
centaines de candidats : elle n'énumère pas des cellules, elle énumère des
**placements d'événements connus** — c'est le levier attendu de la couche
symbolique.

La comparaison est honnête seulement si l'on distingue les deux questions : la
baseline établit une **existence** (parmi tous les still lifes de ≤ 8 cellules
d'une boîte 5×5, la cible est là) et paie l'énumération complète de cet espace,
alors que le compositionnel **construit** la cible (deux gliders dont on sait
qu'ils s'annihilent en deux blocs) sans être confiné à une boîte. Le gain n'est
donc pas « le même problème résolu plus vite », c'est le prix de la
connaissance : quand le catalogue connaît les briques, il ne cherche plus des
cellules ; quand il ne les connaît pas, la baseline reste l'arbitre.

## Provenance : trois natures d'information, distinguées

Le critère 8 de #15635 demande de ne pas confondre trois choses. Le catalogue
les sépare champ par champ :

1. **Faits importés** — la nomenclature et l'existence des objets (`block`,
   `blinker`, `toad`, `lwss`) viennent de sources Life explicites, nommées dans
   le champ `provenance.source`. Les objets mathématiques eux-mêmes sont du
   domaine public ; ce qui est « importé » est le nom, pas une donnée.
2. **Propriétés revalidées** — période, translation, population, enveloppe,
   produit, stabilisation, clearance, survie. Elles ne sont pas importées : elles
   sont mesurées par le moteur du dépôt, à chaque exécution. Le `glider` n'est
   même pas importé du tout : il est celui que `life_synthesize.py` redécouvre
   par énumération bornée (Loi II, EPIC #12205).
3. **Choix de conception propres à CoursIA** — le format du schéma, la règle
   d'admissibilité des symétries, l'exigence de stabilité du produit, la
   convention de placement des phases (forme normalisée placée à l'offset
   déclaré). Ces choix sont des décisions, pas des faits, et sont énoncés ici
   comme tels.

## Reproduction

```
python scripts/lean/life_components.py --fixture scripts/lean/life_components_fixture.json
python scripts/lean/life_components.py --fixture scripts/lean/life_components_fixture.json --json
python scripts/lean/life_compose.py --objective two_blocks_catalyse_free
python scripts/lean/life_compose.py --objective two_blocks --full-report --json
python scripts/lean/life_compose.py --objective two_blocks_catalyse --full-report --node-budget 20000 --json
python -m pytest scripts/lean/tests/test_life_components.py -q
python -m pytest scripts/lean/tests/test_life_compose.py -q
```

Le validateur sort `0` si toutes les métadonnées déclarées correspondent au
replay, `1` sinon, avec le champ fautif nommé. Les tests falsifient une
métadonnée à la fois (période, translation, population, boîte, enveloppe,
catégorie, symétrie, phases, vitesse, provenance, produit, stabilisation,
clearance, nature, région, ports, version de schéma) et exigent le refus.

See #15635 · See #15571 · See #12205
