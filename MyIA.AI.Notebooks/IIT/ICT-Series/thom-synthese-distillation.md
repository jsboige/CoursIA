# Thom 1991 — Sémiophysique : distillation pour les strates 6 et 7

> **Statut.** Document de synthèse transversal, grade **C-documentaire**
> (consolidation, pas de nouveau dispatch). Consolidé depuis la lecture ciblée
> de René Thom, *Esquisse d'une sémiophysique : physique aristotélicienne et
> théorie des catastrophes* (1991, chapitres 1 à 8 — cf. *HORS-scope*
> pour la limite de cette lecture).
> **Objet.** Exposer le **socle théorique** sur lequel les strates 6
> (langage / circulation de prégnances) et 7 (genres comme espaces de
> possibles extensibles) de la série ICT peuvent s'appuyer sans réinventer.
> **Discipline.** Synthèse consolidante. Aucune nouvelle dépendance
> expérimentale. Les concepts sont nommés, situés dans l'ouvrage, et reliés
> à l'usage qu'en fait (ou pourrait en faire) la série — sans confondre
> le grade A du cadre mathématique (catastrophes, dynamiques lentes-rapides)
> avec le grade C d'une lecture « ICT candidate » (cf. rectification
> A2 de [#7733](https://github.com/jsboige/CoursIA/issues/7733)).
> See [#4588](https://github.com/jsboige/CoursIA/issues/4588)
> (Epic umbrella ICT), [#7739](https://github.com/jsboige/CoursIA/issues/7739)
> (issue-source de cette distillation).

## Pourquoi cette distillation

La série ICT a déjà rencontré Thom — mais en **pointillés** :

- [ICT-10-CatastropheGrammar](ICT-10-CatastropheGrammar.ipynb)
  nomme explicitement la **catastrophe fronce**, le **métathéorème** et le
  **lacet de prédation** (cycle d'hystérésis à 2 catastrophes avec
  perception J et capture K, aire signée non nulle, représentant interne
  `p̂`).
- [ICT-12-ValenceFieldsAndAnimats](ICT-12-ValenceFieldsAndAnimats.ipynb)
  prolonge en mesurant les rôles actantiels (capture, évasion, irréversibilité,
  switching) — l'animat anticipateur `p̂` y gagne en balistique, perd en
  erratique.
- [ICT-0-Framing](ICT-0-Framing.md)
  cite le lacet de prédation, le cycle d'hystérésis, l'échappement
  d'horlogerie, les cusps et le métathéorème — toujours dans le sillage de
  Thom.

Ces points de contact dessinent un **socle cohérent** mais ne le **montrent
pas comme un tout**. Le présent document rassemble ce socle — sans le
reformuler en un nouveau formalisme — pour les strates à venir :

- **Strate 6** (langage / circulation de prégnances) : universalisme
  linguistique, valence Tesnière, transitivité prototypique = prédation,
  genres, hypergenres.
- **Strate 7** (genres comme espaces de possibles extensibles) :
  prototypicalité, invention de l'instrument, fronces et excisions,
  opérations catégorielles (factitif, aspect, marque, conflit de
  prégnances).

Ces deux strates **n'ont pas encore de notebook**. Ce document leur fournit
le vocabulaire de référence — à charge pour les notebooks futurs de le
**mesurer**, pas seulement de le nommer.

## L'ossature thomienne en quatre objets

L'ouvrage tient en quatre gestes emboîtés que la série ICT peut déjà
récupérer — avec le distinguo explicite matrice (c.728y+34) vs synthèse
(le présent document) :

| Objet | Sens thomien | Référence ICT existante | Usage en strate 6/7 |
|---|---|---|---|
| **Saillance** $s$ | Ce qui est perceptiblement présent dans l'écoulement | conceptuel, déjà nommé | socle strate 6 (Nom = saillance 0-valent) |
| **Prégnance** $\pi$ | Ce qui donne de l'importance (charge, valence) | conceptuel, déjà nommé | socle strate 6 (Verbe = prégnance 1-4 actants) |
| **Représentation** $q$ | Ce que le système croit de la cause/du futur ; `p̂` = cas simple (croyance réduite à un point) | [ICT-10](ICT-10-CatastropheGrammar.ipynb), [ICT-12](ICT-12-ValenceFieldsAndAnimats.ipynb), [ICT-14](ICT-14-FreeEnergySurprise.ipynb) | déjà mesurée (cf. lacet de prédation Ch.4 §C) |
| **Workspace** $W$ | Ce qui rend des composantes disponibles à d'autres mécanismes | [ICT-24](ICT-24-WorkspaceIgnition.ipynb) (livré Gates 22-23, dissociation documentée) | transversal |

Le présent document ne reproduit pas la matrice
[`docs/ict/dissociations-matrix.md`](../../../docs/ict/dissociations-matrix.md)
(c.728y+34, [#7734](https://github.com/jsboige/CoursIA/issues/7734)) —
qui est **opérationnelle, par-claim, verdict sobre + portée explicite**. La
distillation Thom est **socle théorique transverse** : elle rassemble
les concepts qu'une matrice par-strate pourrait au besoin ré-arborer.

## Socle strate 6 — langage, prégnances, genres

### Ch.6 §F — La phrase nucléaire et la valence (Tesnière)

Thom s'appuie sur la **valence** de Lucien Tesnière (0 à 4 actants) comme
descripteur de la phrase nucléaire. La phrase canonique est une **structure
de prégnances** : un verbe distribue ses actants selon un patron
prégnant (transitif à 2 actants, ditransitif à 3, etc.).

> « Il y a deux types fondamentaux de phrases : les phrases *état* (verbe
> d'état, 1 actant) et les phrases *événement* (verbe d'action, ≥2 actants). »
> — Thom 1991, Ch.6 §F.

**Usage ICT strate 6.** La phrase nucléaire devient une **catastrophe
fondamentale** : un verbe transitif prototypique (SVO) est un lacet de
prédation à 2 catastrophes (perception J + capture K), généralisation directe
du lacet de mesure d'ICT-10. La valence compte les actants saillants que la
prégnance du verbe met en jeu — son augmentation = extension du couloir
d'action, sa diminution = restriction.

### Ch.8 §A — Universalisme linguistique : Nom, Verbe, transitivité

> « Le Nom correspond à une saillance 0-valent ; le Verbe à une prégnance
> de valence 1 à 4. »
> — Thom 1991, Ch.8 §A.

La **transitivité prototypique** est la **prédation** : un agent (saillant,
actant source), une action (prégnance verbale), un patient (saillant,
actant cible). Règle opératoire : *si l'un des actants disparaît, c'est
l'objet* O. L'adverbe est une prégnance sur des opérateurs universels
(« vite », « ici », « toujours » = modulation de la catégorie).

**Usage ICT strate 6.** Les animats d'ICT-12 sont déjà actantiels :
réactif (sujet 1-valent, sans anticipation) vs anticipateur `p̂` (sujet
1-valent + représentant interne 2-valent). Le passage **valence 1 → 2**
est précisément le gain que représente l'anticipation — mesuré régime-
dépendamment, jamais universellement.

### Ch.8 §B — Genres : matière, crible, espèces

> « Les genres sont la matière qui passe à travers un crible dont les trous
> sont des espèces. »
> — Thom 1991, Ch.8 §B (citation Aristote, *Metaphysique* ∆ 1024b).

L'**incommunicabilité des genres** (deux genres ne partagent pas
d'espèce) est une propriété du crible, pas une convention. Le **point triple**
du diagramme des éléments (gaz / liquide / solide) en est un cas concret :
les transitions ne se font pas « gratuitement » entre les trois genres —
elles passent par des points critiques (changement d'état), donc des
catastrophes.

**Usage ICT strate 6.** Les **classes de drift Argumentum** (IN_SYNC,
SRC_DRIFT, TRAD_DRIFT, MISSING_LANG, ORPHAN_ROW, mesurées dans
[ICT-Argumentation-BeliefTrajectories](ICT-Argumentation-BeliefTrajectories.ipynb))
sont des **espèces** au sens de Thom — elles ne se confondent pas, et leurs
transitions sont des catastrophes : passage IN_SYNC → SRC_DRIFT = une
scission (le corpus se dédouble), TRAD_DRIFT → MISSING_LANG = une
disparition (l'espèce cible n'est plus instanciée).

### Ch.8 §C — Hypergenres et opérations catégorielles

L'**extension d'un concept** est un **hypergenre** (couleur, odeur, son
sont des hypergenres par rapport aux couleurs, odeurs, sons individuels).
Le **prototype moineau** (vs aberrant aigle ou autruche) organise le genre
par prégnance centrale, et les **marques linguistiques** sont des
prégnances indifférenciées (le genre commun reste actif sans être
redistingué).

Les opérations catégorielles prennent un sens catastrophiste précis :

| Opération | Sens catastrophiste | Conséquence observable |
|---|---|---|
| **Factitif** (« faire faire ») | **Fronce double** | l'agent devient patient d'une action dont il est aussi la source |
| **Aspect perfectif** | Focalisation sur la **dernière arête** de la trajectoire | la phase de transition (la catastrophe) est seule gardée |
| **Aspect imperfectif** | Focalisation sur le **milieu de l'arête** | la prégnance de la phase d'attente |
| **Lavage** | **Catastrophe d'excision** | élimination d'une singularité locale sans changement du régime global |
| **Conflit de prégnances** | Bifurcation entre deux hypergenres (eau pure ↔ saleté) | bascule du genre par restructuration de la prégnance |

**Usage ICT strate 6.** Ces opérations donnent un **vocabulaire non
ambigu** pour caractériser les transformations mesurées dans les
notebooks argumentatifs et de dissociation (cf. matrice c.728y+34) :
quand deux croyances $\Phi$ et $F$ covarient et que $K$ diverge, le
factitif mesure une **fronce double** entre états ; l'aspect perfectif
explique pourquoi la trajectoire d'une **dissociation** ne montre que le
point de rupture (pas la transition continue sous-jacente).

### Ch.8 §D-E — Ternarité peircéenne, phrase nucléaire et privation du verbe

Le §D prolonge le socle strate 6 en décrivant **l'énonciation elle-même**
comme un effet figuratif : « l'énonciation d'un message est l'effet
figuratif dû à une prégnance investissant le sujet ». Thom emprunte à
Peirce une **ternarité** qui décrit les trois stades de la levée d'une
prégnance par le langage :

| Stade peircéen | Description thomienne |
|---|---|
| **Primarité** | intrusion de la prégnance excitant le psychè (le choc initial) |
| **Secondarité** | énonciation du *type* de prégnance investissante (identification sensorielle) |
| **Ternarité** | reconnaissance de la *source* de la prégnance et sa conceptualisation |

Exemple canonique de Thom : « Ça sent le brûlé » — *ça* = primarité,
*ça sent* = secondarité, *le brûlé* = ternarité (conceptualisation de la
source). La **phrase nucléaire** y est lue comme un **vecteur de
prégnance** : l'esprit « plie » sous l'impact de la prégnance, puis se
redresse en la renvoyant sur un *alter ego*, ce qui le libère de
l'investissement et restaure son autonomie.

**L'intellect comme préprogramme.** Thom modélise l'intellect comme un
**préprogramme — un obstacle —** qui soumet un flux informatif (ayant sa
source dans une catastrophe extérieure) à une **scission** le transformant
en l'émission d'une phrase nucléaire. Métaphore des quilles : le flux est
une boule lancée sur des quilles figurant les parties du discours (N, V) ;
la quille atteinte la première est le **verbe V**, dont la chute
ritualisée entraîne, en nombre égal à sa **valence**, les quilles N
voisines — puis les déictiques / anaphoriques nécessaires à la
localisation des actants (S, O). C'est la **même structure** que le
préprogramme morphologique d'ICT-13 (Axelrod) : un obstacle qui scinde un
flux en une forme typée.

**La capture prédation, matrice de la transitivité.** Le §D referme le
cercle ouvert au Ch.4 §C : la phrase transitive prototypique (« Le chat
mange la souris ») mobilise la **catastrophe fronce** du lacet de
prédation. Dans le plan de contrôle $Ouv$, la capture est l'arc orienté
$\alpha K \omega$ où $K$ est le point de capture (Fig. 8.8) ; cette
trajectoire canalisée symbolise le **téléos de l'acte** et
l'**intentionnalité de l'agent**. Le verbe, excité, **sécrète ses deux
actants** comme contre-images dans la surface critique : l'actant au
minimum le plus bas est l'**agent**, celui au minimum métastable le
**patient** (*objectum est supra subjectum*). La genèse de la phrase
épouse donc la géométrie de la prédation — d'où le sous-titre du présent
document : *phrase = embryogénèse* (la scission verbale est une scission
de singularité, isomorphe à la duplication des cycles plans de la
blastula, Ch.4 §D).

**Privation du verbe.** Thom reprend à Aristote l'idée que l'acte crée
chez ses actants des états de **privation** (στερητικὰς διαθέσεις) : le
verbe excité est chroniquement
en état de privation — il a besoin de substantifs pour réaliser sa
signification (sauf à l'**impératif**, où l'on retrouve le caractère
comminatoire du signal animal). Il sature cette privation en évoquant des
actants, lesquels, excités, entrent eux-mêmes en privation. Le **nom
propre** est autonome (il transporte la localisation de son réfèrent) ;
le **nom commun** est en privation (il doit déterminer pour l'auditeur la
localisation spatio-temporelle de son réfèrent). Cette cascade de
privations rattache le verbe à la **privation = métastabilité** du Ch.7
§D (cf. *Pont transverse* ci-dessous) : le verbe est le siège métastable
qui ne se stabilise qu'en saturant sa valence.

**Le continu de Seiler.** H. Seiler ordonne les universaux linguistiques
sur un axe **prédicativité–indicativité**, que Thom identifie à l'axe
**saillance–prégnance**. Le prédicat met en cause un genre aux *eidè*
fixes (l'assertion suffit à le caractériser) ; les actants liés par
valence — les noms — ne sont pas localisés a priori, d'où la nécessité
des **déictiques** pour fixer cette localisation indéterminée. Les
**techniques** de Seiler sont des sous-continus héritant de la même
polarité (ex. le grand syntagme d'épithètes du Ch.2 §E : une marche de la
prédicativité vers l'indicativité).

**Usage ICT strate 6.** (i) L'intellect-préprogramme donne un cadre pour
relire les **préprogrammes morphologiques** d'ICT-13 : un obstacle qui
scinde un flux en une forme typée, isomorphe entre morphodynamique
stratégique et génération syntaxique. (ii) La cascade de privations du
verbe est l'analogue linguistique de la **triade moyen / fin / enjeu**
d'ICT-18b : on ne mesure pas la fin directement, on mesure le coût de
s'en approcher — de même, le verbe ne se réalise qu'en saturant sa
privation par ses actants. (iii) Le continu prédicativité–indicativité
est une projection 1D de l'espace $(s, q, \pi, W)$ : la prédicativité
(prégnance, $\pi$) du côté du genre aux *eidè* fixes, l'indicativité
(saillance, $s$) du côté de la localisation à fixer. (iv) L'acquisition
du langage (espace de genre plastique creusé en bassins de potentiel par
des représentants prototypiques — sang/rouge, lait/blanc, feuillage/vert
— puis rigidifié après l'âge critique en préprogramme) fournit un
**modèle ontogénétique** pour la formation des attracteurs dans
l'hypergenre (cf. §C).

> **Honnêteté grade C.** La correspondance *phrase transitive =
> catastrophe de prédation* est un **modèle** thomien, pas une loi
> linguistique : la transitivité est *prototypique* (il existe des
> verbes intransitifs, des patients qui résistent). Le statut
> VOS-émissif / SOV-réceptif est une typologie proposée par Thom,
> contestée par la typologie dominante. Ces propositions sont
> enregistrées comme **vocabulaire candidat** pour les notebooks strate
> 6, soumises à leur mesure.

## Socle transversal — la dynamique aristotélicienne : téléologie et section σ (Ch.6 §B, §D-E)

Le chapitre 6 (« La dynamique aristotélicienne comme sémiophysique »,
p.153-164) est le cœur ontologique de la lecture thomienne : c'est là que
Thom **formalise le pont entre Aristote et la théorie des catastrophes**.
Jusqu'ici le document n'en retenait que la liste des **8 axiomes** et la
mention finale de la « section $\sigma$ » (cf. §Ponts transverses). Cette
section en distille la **dérivation** — comment Thom passe du vocabulaire
aristotélicien (téléologie, homéomères) à l'objet géométrique mesurable
(la section $\sigma$ et son ensemble de catastrophe $K$) — et ce que cela
change pour la lecture ICT.

### Le triptyque τέλoς / τέλειν / τελευτή — distinguer l'organisateur, l'accompli, la fin

Toute entité « d'ici-bas » a une naissance (γένεσις) et une fin (ϕθoρά) ;
son graphe temporel finit « en général en un sommet unique, la fin
(τελευτή) » (Ch.6 §B, p.155). Thom insiste sur une **ambiguïté
fondatrice** qu'Aristote « ne souffre guère, mais qui souvent fait
problème » : le mot τέλoς oscille entre **trois** acceptions qu'il faut
distinguer :

- **τέλειον / τέλειν** — l'état « parfait », l'âge adulte, là où « la
  fonction "temps" a son maximum » (p.155). C'est un **sommet
  d'intensité**, pas une terminaison.
- **τελευτή** — la **terminaison** effective, la mort de l'entité
  (ϕθoρά). Le point final du graphe.
- **τέλoς** — ni l'un ni l'autre : le **centre organisateur**.

La citation fondatrice (Ch.6 §B, p.155), in extenso :

> « La citation [1] semble indiquer que le τέλoς est en quelque sorte le
> point central de l'existence d'une entité ou d'un acte : il en détermine
> en effet l'antérieur (τò πρότερον) et le postérieur (τò ἕφεξῆς). Selon
> le point de vue catastrophiste, le τέλoς pourrait être ainsi considéré
> comme le **centre organisateur d'un champ morphogénétique** d'êtres et
> d'événements se déployant selon la temporalité. En ce cas le τέλoς
> devrait être toujours distinct de la terminaison (τελευτή). »

**Conséquence épistémique pour ICT.** Le pont « recouvrabilité →
agentivité » (ICT-9, #8077 pont 2) et la triade moyen / fin / enjeu
(ICT-18b, cf. §Ponts transverses « Privation = métastabilité ») reposent
sur une fin **mesurable**. Thom fournit la distinction qui évite
l'erreur de catégorie : la « fin » qu'on mesure n'est **jamais** la
τελευτή (terminaison — par définition non observable avant qu'elle
n'arrive), c'est le **τέλoς** comme centre organisateur. On n'observe pas
la fin, on observe le **coût de s'en approcher** (le moyen, σ de
production d'entropie). C'est exactement la structure du verdict
« privation structurée » : la τελευτή absente est une forme prégnante qui
**plie** la trajectoire autour de son absence — un τέλoς, pas une
terminaison.

### Homéomère / anhoméomère, puis la section σ — la forme naît de la discontinuité

Thom construit ensuite l'objet géométrique. Une entité $H$ est
**homéomère** si « toute partie $c$ de $H$ est considérée comme étant
sémantiquement […] équivalente à $H$ » (Ch.6 §D, p.157) — substrat
d'apparence homogène, « intrinsèquement "informes" » : eau, huile, sang,
graisse. Une entité **anhoméomère** présente des « discontinuités
qualitatives : il a donc une forme, un *situs partium* ». Aristote
distingue ici le **tout** (πᾶν, homéomère) de la **totalité** (ὅλον,
corps vivant à « parties canoniques » séparées par des surfaces). Thom en
tire la proposition qui boucle la controverse Cuvier / Geoffroy (cf.
§Ponts transverses Ch.5) :

> « L'ensemble catastrophique est un support indispensable de la forme
> (μορφή). Les parties en acte de l'entité sont limitées par les
> anhoméomères. » (Ch.6 §D, p.157-158)

Vient alors **la définition formelle** (Ch.6 §E, p.158) — l'objet que le
§Ponts transverses cite sans le dériver :

> « Si l'on désigne par $Y$ l'espace des "états internes locaux" de la
> matière, l'"état" d'une entité $A$, de support $|A|$ pourrait être
> défini par une **section $\sigma : |A| \to Y$** du produit fibré
> $|A| \times Y \to |A|$. Cette section est **continue pour un
> homéomère** ; pour un anhoméomère, elle est **discontinue sur un
> ensemble $K$ de "points de catastrophe"** ; cet ensemble $K$ définit
> l'organisation morphologique de l'entité $A$ (toute partie en acte de
> $A$ a sa frontière dans $K$). »

Ainsi $\sigma$ est **continue** là où la matière est homogène (homéomère,
informe, en puissance) et **se brise** sur $K$ là où apparaît la forme
(anhoméomère, en acte). Les homéomères portent des *dunameis*
(puissances) qui « se réalisen[t] en acte sur les anhoméomères sièges
des travaux et des activités (ἔργα καὶ πράξεις) » (p.158) : l'**acte se
localise sur une surface de contact** — l'articulation entre deux os (le
« conflit entre les deux "lieux" »), ou le poumon comme interface
air/sang.

**Conséquence pour la strate 6 (factorisation 4-objets).** La distinction
homéomère / anhoméomère est l'ancêtre ontologique de la dissociation
**saillance / prégnance** d'ICT : l'homéomère est le substrat continu,
sans singularité — la saillance $s_t$ « perceptiblement présente »; et
l'anhoméomère ($K$) est là où se condensent les prégnances — les
singularités qui donnent leur forme aux π et $q$. Les **5 dissociations
canoniques** de la matrice #7734, relues comme des « endroits où
$\sigma$ casse » (cf. §Ponts transverses « Axiomatique »), ne sont donc
pas une métaphore : ce sont des **discontinuités de section** au sens
formel de Thom. Et les ponts falsifiables de #8077 opèrent précisément
sur ces anhoméomères — les surfaces de contact où l'acte (usage causal,
diffusion, généralisation) se localise et devient mesurable.

### Limite de la lecture (honnêteté grade C)

Thom **formalise** $\sigma : |A| \to Y$ géométriquement (produit fibré,
section, ensemble de catastrophe $K$) mais ne la **quantifie** jamais
numériquement — $Y$ et $K$ sont des objets de la géométrie
différentielle, pas des vecteurs mesurables. La transposition ICT ($\sigma$
→ dissociations scalaires mesurables, $K$ → singularités dans un espace
de proxies $s, q, \pi, W$) est **nôtre**, pas thomienne (rectification A2
#7733 : le grade A du cadre géométrique $\neq$ le grade C d'une lecture
candidate). Le lien est une **analogie contrôlée**, pas une dérivation :
Thom fournit le vocabulaire formel (section continue/discontinue,
catastrophe-set comme support de la forme) qui légitime le *geste*
mesurant — mais la mesure elle-même appartient au registre ICT.

## Socle strate 7 — genres comme espaces de possibles extensibles

### Ch.8 §B (bis) — Genres = préprogramme

> « Un genre est un préprogramme. »
> — Thom 1991, Ch.8 §B (recouplant Ch.3 §B sur les préprogrammes morphogènes).

Le **préprogramme** (Ch.3 §B) est une forme saillante dans un écoulement
fluide, dont le mouvement provoque des morphologies archétypes (Turing
1952, mais lu par Thom comme une grammaire des formes et non une théorie
de la stabilité). Les 4 singularités archétypes (min, scission,
confluence, disparition — point critique quadratique non dégénéré) sont
les **quatre opérateurs de la grammaire** ; un genre est un préprogramme
au sens où il contraint l'espace des trajectoires morphologiquement
admissibles.

**Usage ICT strate 7.** Les classes de stratégies d'Axelrod (ICT-13 :
AllC, AllD, TFT, GTFT, Pavlov, Grim) sont des **préprogrammes** au sens
thomien : ce sont des attracteurs morphologiques du dilemme itéré, et
leurs **bassins d'invasion** (mesurés dans Gate 4) sont les **régions du
morphospace stratégique** où chacun peut être engendré. La dissociation
entre **score cumulé** et **robustesse à l'invasion** (Gate 3, Noise
Gate) est précisément la séparation entre deux lectures du **même**
préprogramme — l'une en termes de saillance (score), l'autre en termes
de prégnance (résistance).

### Ch.8 §C (bis) — Extension d'un concept = hypergenre

L'**extension** d'un concept (passer de « moineau » à « oiseau ») est un
**hypergenre** : on relâche le crible en multipliant les espèces
admises, mais la **prégnance centrale reste** (la capacité de voler, la
structure plume, etc.). Le prototype moineau fonctionne comme un
**attracteur dans l'hypergenre** ; les prototypes aberrants (aigle,
autruche) sont des **états excités** — non pathologiques, mais tendus.

**Usage ICT strate 7.** L'**émergence causale** d'ICT-5 (Hoel, 2025) est
exactement une opération d'hypergenre : on relâche la contrainte micro
(les TPM par neurone) pour accéder à la TPM macro, et le **score
d'émergence** mesure à quel point le relâchement préserve l'information
causale. Quand le score est élevé, l'hypergenre « macro-échelle »
contient la même prégnance causale que le micro ; quand il est bas, le
micro est un préprogramme et le macro est un **hypergenre divergent**.

### Ch.3 §A-§B — Les quatre interactions et la notion de préprogramme

Ch.3 ouvre la **théorie générale des interactions dans une ontologie
intelligible** (§A) en classifiant les quatre modes d'action possibles
entre saillances (s) et prégnances (π) :

| # | Interaction | Sens | Exemple thomien |
|---|-------------|------|-----------------|
| 1 | s ⇄ s | Collision : compétition pour l'espace de deux formes saillantes | Deux boules sur l'axe Ox (Fig. 3.1) |
| 2 | s → π | **Préprogramme** : action d'une prégnance sur une autre via une forme saillante | Robinet (canalisation d'un flux) |
| 3 | π → s | Effets figuratifs : investissement d'une forme par une prégnance | Contagion microbienne, lumière diffusée |
| 4 | π ⇄ π | Interaction entre prégnances de même espace substrat | Quantification d'un champ, conflit d'espèces |

Le **préprogramme** (§B) est l'objet conceptuel central de Ch.3. C'est une
**forme saillante plongée dans un écoulement** dont la position peut
provoquer dans cet écoulement une ou plusieurs **morphologies
archétypes** — les quatre singularités élémentaires de la fig. 3.3 :
**naissance** (1, indice 0), **scission dichotomique** (2, indice 1),
**confluence dichotomique** (3, indice n−1), **disparition** (4, indice n).
Thom en déduit un **métathéorème** : « pour presque tout chemin joignant
deux points de l'espace Q des paramètres, le graphe associé ne comporte
que ces quatre types de singularités » — conséquence de l'hypothèse de
continuité pour les variétés de niveau d'une fonction réelle lisse F à n
variables traversant un point critique générique (quadratique non
dégénéré).

> « Si l'on s'intéresse uniquement au "nombre" des courants issus de
> l'obstacle, c'est-à-dire au nombre cardinal des composantes connexes
> de l'ensemble où la densité est strictement positive, alors à tout
> chemin dans l'espace Q va correspondre un graphe, associant [...] un
> ensemble discret de points sur un axe. »
> — Thom 1991, Ch.3 §B.

**L'importance "philosophique" de ce métathéorème** est qu'il permet un
contrôle de la **génération et de la corruption des entités** (selon la
terminologie aristotélicienne) en réduisant l'individualité à la seule
**connexité topologique du substrat**. La forme presque effaçable (une
forme F de ℝⁿ effaçable par homéomorphisme h + δh) devient le
**carrefour morphogénétique** : cylindre (canalisation), bouteille
(stockage sphérique après singularité de type 2), crible (scission
qualitative), culotte (confluence).

**Usage ICT strate 7.** Le **préprogramme** est le concept qui **réconcilie
matière et technique** dans l'ontologie thomienne : un préprogramme est à
la fois une forme saillante (substrat biologique) et un geste technique
(le geste qui exploite le flux). Pour la série ICT, les **modèles internes**
(`p̂` d'ICT-10/12, $\epsilon$-machine d'ICT-17) peuvent être lus comme des
**préprogrammes** au sens large : ils opèrent sur le flux de perception
pour en extraire une morphologie archétypale (naissance/scission/
confluence/disparition des entités perçues). Le **métathéorème** rappelle
qu'on n'a pas besoin d'inventer un formalisme par régime : les quatre
catastrophes élémentaires suffisent à indexer la grammaire des
transitions — d'où la **catastrophe fronce** (ICT-10) et la **cuspide
duale** (ICT-12c) déjà mesurées.

### Ch.3 §C — Singularités archétypes : naissance, scission, confluence, disparition

§C exemplifie chaque singularité par un **morphisme technique** :

- **Naissance** (1) : source, eau qui sourd d'un réseau souterrain
  convergent ; entonnoir = dispositif qui crée une source à partir d'un
  flux diffus.
- **Scission** (2) : crible — sépare particules fines / grosses selon la
  taille de la maille.
- **Confluence** (3) : « culotte » — jonction de deux écoulements
  qualitativement différents, entropiquement favorable (couper le vin
  d'eau).
- **Disparition** (4) : Oued Draa descendant vers le sud de l'Atlas
  marocain, annihilé par absorption du sable et évaporation.

§C explicite aussi la **réversibilité** : « si on peut provoquer une
singularité, on peut aussi provoquer la singularité opposée (obtenue en
renversant la flèche du temps). » Le **robinet** est l'exemple canonique :
ouvert → naissance d'un flux, fermé → mort d'un flux. « Le caractère
réversible de l'opération se voit dans la nature hamiltonienne du
mouvement (une rotation du corps transformée en translation par le fil
de la vis). »

**Usage ICT strate 6.** Le **verbe transitif** SVO est structurellement
une singularité archétype : l'agent fait **naître** ou **disparaître** un
patient (causativité), ou le **scinde** (distributivité), ou le **confond**
avec un autre (conjugaison). Tesnière (Ch.6 §F) range ces opérations
dans la valence verbale ; Thom les range dans les quatre singularités.
L'**isomorphie** des deux taxonomies est ce qui rend la strate 6 mesurable
depuis la strate 7 : un verbe à 4 actants est une catastrophe d'ordre
supérieur (papillon, ombilic hyperbolique) qui se déploie selon les
quatre mêmes singularités archétypes.

### Ch.3 §E-§F — Roue de moulin et cycle de Van der Pol-Liénard

§E et §F établissent le **cycle d'hystérésis** (cf. lacet de prédation)
comme **moteur universel** de la technique. Le cas paradigmatique est la
**roue de moulin à une pale** :

- Pale immergée : phase d'**entraînement** (le courant fournit de
  l'énergie).
- Pale émergée : phase de **dissipation** (frottements, travaux sur l'axe).

Le schéma est celui de la **corde de violon vibrant sous l'archet** :
lorsque la vitesse transversale u est de même sens que la vitesse v de
l'archet, fort coefficient de frottement → la corde reçoit de l'énergie ;
lorsqu'elle revient en sens inverse, faible coefficient → la corde perd
relativement moins. Le gain net entretient la vibration.

> « Le même schéma est valable pour l'échappement d'horlogerie (dispositif
> inventé par l'Homme au Moyen Âge, bien avant toute théorie mécanique). »
> — Thom 1991, Ch.3 §F.

§F reformule la **théorie de Van der Pol-Liénard** : on part d'une
dynamique gradient g rapide qui, lorsque 4u + 27v < 0, donne naissance à
une **bimodalité** à l'intérieur de la parabole semi-cubique. La
dynamique lente est Yλ, gradient du polynôme par rapport à la **métrique
hyperbolique** dx − λ dv. La **bifurcation de Hopf** classique apparaît
à λ = 1 (attracteur → cycle attracteur), et le cycle se déforme
continûment dans le **cycle d'hystérésis** associé à la fronce pour
λ ∈ [1−ε, 0]. F. et M. Diener (note 5) ont observé que pour 1 > λ > 0,
le champ présente, outre le cycle attractif issu de la bifurcation de
Hopf, des « **rivières** qui préfigurent les **variétés stables** du cycle
d'hystérésis » — image topologique d'une anticipation structurelle.

**Usage ICT strate 5-7.** Le **cycle d'hystérésis** est l'objet mesuré par
[ICT-10-CatastropheGrammar](ICT-10-CatastropheGrammar.ipynb)
(lacet de prédation = cycle à 2 catastrophes J/K) et
[ICT-12c-PregnanceAnimat](ICT-12c-PregnanceAnimat.ipynb)
(prégnance = potentiel gradient). Les **« rivières »** de Diener sont une
**anticipation visuelle** du cycle d'hystérésis : même quand l'attracteur
ponctuel est encore stable, les courbes stables du futur cycle
d'hystérésis sont déjà présentes dans le flot. C'est l'image la plus
précise que Thom donne du **représentant interne `p̂`** : le prédateur
qui perçoit sa proie ne calcule pas sa trajectoire future, il **voit déjà**
les rivières qui y mènent. Cette lecture thomienne de `p̂` complète
l'ICT-14 (énergie libre = bilan computationnel) sans la contredire.

### Ch.3 §H — Coïncidence des coplis et activité finalisée

§H introduit la **règle des coplis** (notion due à José Argémi, note 6) :
pour que deux processus (antérieur et postérieur) soient concaténés en un
seul dispositif finalisé, il faut que les **points coplis** (projections
verticales des points plis) coïncident sur une même horizontale. Le
**canal de dérivation** (§G-I) en est l'exemple technique : le barrage
rétroflux CH + HB ferme partiellement le cours normal, la chute GC est la
catastrophe, et la pale FC est entraînée par la chute. La coïncidence
des coplis G et F en C **exprime la finalité** du processus antérieur
(rectangle CHBG) par rapport au processus postérieur (FCDE, partie
efficiente).

> « Si l'on dit que "la fin justifie les moyens", on devra ici préciser
> que, selon une optique "phylo et ontogénétique", "la fin sécrète ses
> moyens". »
> — Thom 1991, Ch.3 §H.

§H donne ensuite le **scénario de duplication du cycle** : comme tout
champ de vecteurs du plan ℝ² admettant une trajectoire fermée admet au
moins un point singulier intérieur (Poincaré), la scission du cycle Γ de
foyer O exige la scission préalable de la singularité 0. Deux scénarios :

1. **Scénario dégénéré** : O s'annule au premier ordre, puis scission
   en deux attracteurs + un répulseur. « Peu satisfaisant » en raison du
   caractère dégénéré.
2. **Scénario élégant** : la singularité O va sur le **cycle-bord**
   lui-même, flot déformé en **pinceau** (équation x² + y² − 2λx = 0,
   λ > 0, pinceau linéaire de cercles tangents à Oy en O). Le
   **prolongement analytique par réflexion** donne le nouveau cycle
   symétrique. Le gradient du potentiel méromorphe 1/z a des courbes
   W = cste qui sont le pinceau orthogonal. Le **ménage à quatre**
   (a, a')(b, b') permet deux scissions : (a, b)(a', b') ou (a, a')(b, b') —
   Thom propose ce schéma comme **modèle de la scission de la double
   hélice de l'ADN**.

**Usage ICT strate 7.** La **coïncidence des coplis** est le **substrat
morphologique de la finalisation** : un dispositif est finalisé quand
ses points plis coïncident. C'est l'image la plus opératoire que Thom
donne de la **téléologie aristotélicienne** (Ch.6 §B). Pour la série
ICT, cette structure est mesurable : un système dont les deux
catastrophes (perception J, capture K) ont leurs coplis confondus en un
même point de l'espace de contrôle est un **système finalisé** — un
**prédateur** au sens plein. ICT-10 mesure déjà l'**aire signée du lacet**
(qui s'annule pour un système dégénéré non-finalisé et devient non-nulle
dès que les deux catastrophes sont distinctes) ; la coïncidence des
coplis ajoute un **critère projectif** — les deux catastrophes doivent
non seulement être distinctes, mais **alignées verticalement** dans
l'espace de contrôle.

### Ch.3 §I — Modèles algébriques de la duplication : scission du cycle par le cylindre parabolique

§I formalise la coïncidence des coplis par une **construction
géométrique** : on ajoute une dimension z et on forme le **cylindre
parabolique** Z d'équation z − x² = 0 ; la projection π : Z → ℝ²
induite par (x, y, z) → (x, y) envoie la **contre-image** π⁻¹ d'un
cercle Γ du pinceau en une **figure en huit** qui réalise le double
cycle concaténé. (Sur Z < 0, il faut renverser le sens du flot induit.)

Le **double cycle d'hystérésis** de la fig. 3.11 provient, en Théorie
des Catastrophes élémentaires, de la **singularité papillon** (potentiel
x⁶ + ...). Pour réaliser la coïncidence des coplis, il faut donner une
**section rectiligne** dans le plan (u, v, w) qui contient la courbe
« papillon » et qui passe par le **point double axial**.

§I conclut en évoquant la **scission en dimension ≥ 3** : dans un espace
de dimension ≥ 3, la scission d'un cycle devient beaucoup plus facile,
car elle ne nécessite plus la scission préliminaire des singularités
ponctuelles (Coullet-Gambaudo-Tresser, note 7). « Cette scission
préliminaire, nous le verrons au chapitre 5, est en liaison avec
l'existence du génome. »

**Usage ICT strate 7.** Le **passage en dimension supérieure** explique
pourquoi la **scission cellulaire** (mitose) est plus facile à modéliser
en 3D qu'en 2D — mais Thom prévient que la scission 2D est ce qui
**ancre** la structure (le génome comme « scission préliminaire »).
Pour ICT, c'est un argument **anti-réductionniste** : réduire
l'embryologie à un automate 2D perdrait la profondeur où la scission
devient générique. Les **modèles internes** ICT qui s'expriment dans un
espace de croyances de dimension finie (p̂ ∈ ℝ pour ICT-10/12, K
multi-proxy pour ICT-17) doivent se demander à quelle **dimension
critique** la scission cesse d'exiger un mécanisme dédié — et c'est une
**mesure falsifiable** (transition de phase du nombre de cycles
concaténés en fonction de la dimension de croyance).

### Ch.3 §J — Contraintes génétiques et théorie des catastrophes

§J revient sur l'objection de Pontecorvo (Institut Wistar, 1968) : dans
la théorie des morphogénèses de la Théorie des Catastrophes
élémentaires, la mémoire (l'effet du passé) ne joue aucun rôle, ces
morphologies étant « indépendantes du substrat ». Or toute la
morphologie en Biologie est fondée sur un effet de mémoire (génétique) —
comme le prouve l'impossibilité de la génération spontanée.

La réponse de Thom distingue deux régimes :

- **Morphologies génériques** : ne nécessitent qu'un concours « naturel »
  de circonstances pour se réaliser. Existent en Embryologie. « Pas
  canalisées », donc explicables par un schéma catastrophiste standard.
- **Coïncidence des coplis** : exige une **contrainte non générique** sur
  le substrat, dont un effet du passé très strict, peut-être (mais pas
  nécessairement) attribuable à des structures moléculaires spécifiques.
  L'exemple du fleuve qui, par érosion, se canalise lui-même entre ses
  rives, montre que des effets de canalisation peuvent apparaître
  « naturellement », après un temps assez long d'activité fonctionnelle.
  Thom cite S. Butler, *Life as a Habit* (note 9).

> « On peut voir l'effet d'une suite de transformations [...] chaque
> cycle se subdivisant dichotomiquement. »
> — Thom 1991, Ch.3 §J.

**Usage ICT strate 7.** La distinction **morphologie générique vs
morphologie canalisée** est ce qui permet à Thom de **récupérer** la
biologie sans abandonner la Théorie des Catastrophes : les **phénotypes
fréquents** sont génériques (4 singularités archétypes), les **phénotypes
rare-assujettis-à-une-filiation** sont canalisés (coïncidence des
coplis). C'est l'image la plus claire que Thom donne de l'**hérédité** :
non pas un « code » au sens informatique, mais une **histoire**
d'habitudes morphologiques qui se sont stabilisées par canalisation.
L'**usage pour ICT** est de distinguer, dans la mesure d'émergence
(ICT-5, Hoel 2025), ce qui est **générique** (le macro préserve le micro
par construction) de ce qui est **canalisé** (le macro exige une
mémoire accumulée). Le score d'émergence devient alors un **estimateur
du degré de canalisation** : un score élevé sur un système sans mémoire
= généricité ; un score élevé sur un système avec mémoire = canalisation
par coïncidence des coplis.

### Limite de la lecture (honnêteté grade C)

Cette section distille les §A à §J du chapitre 3 (à l'exception de §G
*« L'art imite la nature »* et §K *« Invention de l'instrument »*, déjà
couverts dans la section strate 7 précédente, lignes 418 et 441). Comme
pour les autres strates, ce qui est exposé est le **socle théorique** —
à charge pour les futurs notebooks ICT de **mesurer** les concepts
nommés :

- Le **préprogramme** (§B) n'est pas mesuré tel quel dans la série ICT.
  Le notebook candidat pourrait tester la **connexité topologique du
  substrat** (composantes connexes de l'ensemble de sortie en fonction
  de la position de l'obstacle) sur un flux de données réelles.
- Les **quatre singularités archétypes** (§C) sont un **index de grammaire**
  — aucun notebook ICT ne les a encore explicitement testées comme telles
  (le lacet de prédation Ch.4 §C est une application du fronce, pas une
  grammaire des 4 singularités).
- Le **cycle de Van der Pol-Liénard** (§F) et les **« rivières »** de
  Diener sont une **anticipation visuelle** du cycle d'hystérésis :
  aucun notebook ICT ne mesure cette propriété (présence de courbes
  stables préfiguratrices d'un futur cycle attractif).
- La **règle des coplis** (§H) n'est pas exploitée en ICT — le critère
  projectif (coplis confondus) ajoute une **dimension mesurable** au
  verdict « aire signée non nulle » d'ICT-10.
- Le **scénario de scission 2D vs 3D** (§I) appelle une **mesure
  falsifiable** de la dimension critique de scission — transition de
  phase du nombre de cycles concaténés en fonction de la dimension de
  croyance.

Les notebooks futurs qui s'en saisiront devront **mesurer** (cf. règle F :
*vrai outil SOTA, jamais workaround dégradé*), pas seulement nommer.

### Ch.3 §K — Invention de l'instrument

Le cas paradigmatique est celui du chimpanzé face à la banane inaccessible
(Köhler) : la banane est un attracteur saillant, le bâton est l'instrument
qui **plie** la trajectoire pour la rendre atteignable. Thom y voit une
**plication affective de la forme** : la forme « banane » acquiert une
valence (manger) qui dépasse sa position spatiale, et le bâton devient
**moyen** au sens d'Adorno — *« le moyen bascule en une fin en soi »*.
Le chimpanzé ne « calcule » pas le bâton, il en fait l'**instrument**
parce que la banane est prégnante.

> « L'heuristique en tant que science n'existe pas. »
> — Thom 1991, Ch.3 §K (note finale).

**Usage ICT strate 7.** Les **modèles internes** mesurés dans la série
(`p̂` d'ICT-10/12/14, $\epsilon$-machine d'ICT-17, end-state prototypique
d'ICT-13) sont des **instruments au sens de Thom** — des plications
affectives de la forme du monde vers une trajectoire admissible. Mesurer
quand un modèle interne *gagne* (ICT-12 balistique, ICT-14 sinus bruité)
ou *perd* (ICT-12 erratique, anticipation sur source bruitée) revient à
caractériser les **régimes** où l'instrument vaut — et c'est la promesse
d'un **langage commun** entre les strates 1-5 et 6-7.

### Ch.3 §G — L'art imite la nature (Aristote)

Aristote (cité par Thom) : *« l'art imite la nature »* — mais Thom ajoute
que l'imitation est **morphologique**, pas littérale. Une horloge à
échappement imite le **cycle d'hystérésis** (la corde de violon, la roue
de moulin) ; un gouvernail imite la **cuspide duale** hache/lame (Ch.3 §D
: *« Toute la morphologie opératoire des organes prédateurs entourant la
bouche est fondée sur ce principe »*).

**Usage ICT strate 7.** Les **artefacts techniques** mesurés dans la
série (instrument de Bateson dans le cycle d'hystérésis, échappement
d'horlogerie, cuspide duale) ne sont pas des métaphores — ce sont des
**imitations morphologiques** au sens thomien. Le **bridging** ICT-12
(réactif vs anticipateur) devient mesurable comme une **comparaison de
plicatures affectives** : qui a la banane inaccessible ? Le réactif en
faisant persister la trajectoire, l'anticipateur en internalisant le point
d'interception.

## Socle transversal — la dynamique de prédation (Ch.4 §C) et l'origine du représentant interne `p̂`

Le lacet de prédation n'est pas un schéma isolé : il est, dans la
*Sémiophysique*, le lieu où Thom **invente le représentant interne `p̂`** —
l'objet qui deviendra, dans la série ICT, le scalaire ponctuel dont toute
la généalogie de la représentation interne
([#7735](https://github.com/jsboige/CoursIA/issues/7735)) retrace
l'insuffisance progressive (ICT-10 → ICT-17). Lire Ch.4 §C, c'est lire la
**source** de `p̂` — et constater qu'elle est d'emblée plus riche (et plus
exigeante) que le « scalaire » qu'en retient le notebook.

### Le lacet « revisited » — deux cycles concaténés, pas un

Le lacet de prédation de *SSM* (Thom 1972) était un seul cycle d'hystérésis
dans le plan de contrôle $Ouv$ de la fronce : cercle $r$ ($u^2+v^2=1$),
parabole semi-cubique $B$ ($4u^3+27v^2=0$), points $J$ (perception) et $K$
(capture), deux actants $P$ (prédateur) et $p$ (proie). En 1991, Thom
**revisite** ce schéma en le **dédoublant** :

> On sera amené à faire précéder le cycle d'hystérésis $JjKk$ de capture
> proprement dit d'un cycle préliminaire, noté $RrJ_1 j$.
> — Thom 1991, Ch.4 §C.

Les deux cycles sont **concaténés** selon la *règle de coïncidence des
coplis* (Ch.3 §H) — règle qui exprime l'**asservissement finalisé** du
premier cycle (reconnaissance) au second (capture). Le point $R$ désigne
le **« réveil » du prédateur** :

> Quand le prédateur se réveille (en $R$), il est affamé [...] cette
> période de recherche est représentée par l'arc $RJ$ du cercle $r
> [...] Ainsi se trouve représenté l'**état de privation** cher à
> Aristote. Ce modèle a l'avantage de refléter le caractère essentiellement
> **discontinu** du réveil, opposé à la transition relativement
> **continue** de l'assoupissement (sur l'arc $K_1 s$).
> — Thom 1991, Ch.4 §C.

**Pour la série ICT.** Le dédoublement perception/capture en deux cycles
aux caractères temporels opposés (réveil *discontinu* en $R$,
assoupissement *continu* sur l'arc $K_1 s$) est la structure que mesure
[ICT-10-CatastropheGrammar](ICT-10-CatastropheGrammar.ipynb) :
périodicité du lacet, aire signée non nulle, verdict régime-dépendant
(gagne en balistique, perd en erratique, perd sur source bruitée — 5/5 sur
trajectoire lisse). La *discontinuité du réveil* est la signature
catastrophique que le notebook détecte comme bascule entre les deux cycles.

### Le représentant interne `p̂` — anticiper, c'est précéder

C'est ici que Thom introduit explicitement le représentant interne :

> La proie réelle $p$ a un représentant interne $\hat{p}$ dans l'état
> métabolique du prédateur. En un certain sens, $\hat{p}$ **anticipe** le
> mouvement de $p$ à l'extérieur de l'organisme [...] mais en principe,
> $\hat{p}$ doit toujours se trouver **en avance** de $p$ dans le sens des
> $v$ positifs : $v(\hat{p}) > v(p)$. En fait, $\hat{p}$ représente $p$
> dans ses activités motrices et métaboliques.
> — Thom 1991, Ch.4 §C.

Le passage de la proie $p$ par les **instants catastrophiques**
(reconnaissance, localisation, capture spatiale, digestion stomacale)
agit comme un **« préprogramme d'ouverture »** sur le flux d'écoulement du
prédateur, et l'évolution quasi synchrone de $p$ et $\hat{p}$ à travers la
blastula physiologique (BP) constitue le « champ » global de
l'alimentation — la **« chréode »** de la capture et de l'assimilation
d'une proie. Anatomiquement, Thom situe cette commande dans le **système
nerveux** : partie **centrale** pour le trajet externe de la proie
(reconnaissance, poursuite, capture), partie **végétative** pour le trajet
interne (digestion).

> — Thom 1991, Ch.4 §C (cf. aussi Ch.3 §B sur le préprogramme morphogène).

**Pour la série ICT — trois conséquences épistémiques** pour la généalogie
[#7735](https://github.com/jsboige/CoursIA/issues/7735) :

1. **`p̂` naît prédicatif, pas descriptif.** Thom ne définit pas $\hat{p}$
   comme un « reflet » de $p$ : il le définit par la **condition d'avance**
   $v(\hat{p}) > v(p)$. Un $\hat{p}$ qui n'anticipe pas n'est pas un
   $\hat{p}$. La série ICT hérite de cette exigence : ICT-10 mesure la
   capacité d'anticipation (balle balistique vs erratique), pas la simple
   corrélation $\hat{p} \leftrightarrow p$.
2. **`p̂` est métabolique ET moteur — pas un scalaire.** Thom inscrit
   $\hat{p}$ dans l'état métabolique global de l'organisme prédateur, et
   lui fait porter les activités motrices. La dissipation de $\hat{p}$ vers
   l'état causal (Crutchfield, ICT-17) est déjà en germe : $\hat{p}$ chez
   Thom est une **dynamique**, pas un scalaire. Le scalaire $\hat{p}$ de
   ICT-10 est une **réduction** — à charge pour ICT-14/16/17 d'en mesurer
   l'insuffisance (c'est exactement l'histoire que raconte
   [#7735](https://github.com/jsboige/CoursIA/issues/7735)).
3. **Les catastrophes sont des préprogrammes.** Les instants
   catastrophiques de $p$ commandent les sauts de $\hat{p}$ : ce n'est pas
   la trajectoire lisse de $p$ qui gouverne, mais ses **discontinuités**.
   Pont naturel vers le préprogramme morphogène (Ch.3 §B) et, au-delà,
   vers la lecture d'$\hat{p}$ comme **préfaisceau** — la dissociation
   ICT-15b montre que le choix du proxy *est* un choix de préfaisceau (cf.
   [synthese-invariants](../../../docs/ict/synthese-invariants-dissociations-obstructions.md)).

### Limite de la lecture (honnêteté grade C)

Thom **n'identifie jamais** $\hat{p}$ à un scalaire quantifiable, ni ne
spécifie la métrique de l'« avance » $v(\hat{p}) > v(p)$ en dehors de la
géométrie de la fronce. La transposition ICT — mesurer l'anticipation
comme écart temporel ou informationnel sur trajectoire simulée — est
**nôtre**, pas thomienne (rectification A2
[#7733](https://github.com/jsboige/CoursIA/issues/7733) : ne pas confondre
le grade A du cadre catastrophique avec le grade C d'une lecture
candidate). Le lacet de prédation reste un **cadre morphologique** ; ce
que la série en mesure est une **instanciation numérique** dont le lien au
formalisme de Thom est d'analogie contrôlée, pas de dérivation.

## Socle transversal — Ch.5 §E-G : régulation physiologique, préprogramme génétique et géométrie du système nerveux

Le Plan Général d'Organisation ne s'arrête pas à la controverse
Cuvier/Geoffroy (§A-D, cf. §Ponts transverses). Les §E-G étendent la
blastula physiologique dans trois directions directement fécondes pour
la strate 7 : la régulation physiologique comme concaténation de cycles,
le génome comme **canalisateur d'attracteur** (non comme code), et la
géométrie du système nerveux comme lecture locale du plan BP.

### §E — La proie dans l'organisme : cycles concaténés et proie fictive anticipante

Thom prolonge le lacet de prédation (Ch.4 §C) en une chaîne
physiologique complète : (1) catastrophe de perception en arête $ST$
(reconnaissance/localisation), (2) poursuite jusqu'à capture en bouche
$O$, (3) mandication-digestion-assimilation, (4) excrétion. Cette
commande successive des cycles se représente par un **segment
diagonal** ($T \to (2)$, $O \to (3)$, etc.) : une **onde d'activité
accompagne le trajet de la proie dans l'organisme**.

> « Dans le cycle (2) […], il y a une proie "fictive" décrivant un cycle
> parallèle à (2). Cette proie fictive anticipe en quelque sorte (dans
> le SNC) le mouvement de la proie réelle. » — Thom 1991, Ch.5 §E
> (p. 127).

Le SNC, localisé en principe en $T$, a des **prolongements
fonctionnels** dans les circuits (2)(3) — parasympathique pour (3).
L'anticipation est donc *structurelle*, non accessoire : le
représentant interne $\hat{p}$ du Ch.4 §C trouve ici sa généralisation —
une **proie fictive centrale précède chaque cycle réel**. Certaines
activités sont discontinues (prédation), d'autres **permanentes**
(vasculaire : cœur gauche au centre du cycle (2), cœur droit au centre
du cycle (3)).

### §E (bis) — Le génome canalise l'attracteur, il ne code pas

Thom est explicite : le rôle du génome se réduit à **« canaliser » le
déploiement de l'attracteur du métabolisme**, en spécifiant les
amplitudes relatives des oscillateurs — modulation **largement
extra-génétique**, sans codage concret et précis. La Génétique
traditionnelle joue vis-à-vis de l'embryologie « le même rôle néfaste
que la pédagogie vis-à-vis de l'enseignement : [… elle] se borne en
fait à déployer un catalogue d'erreurs que l'évolution normale
évitera soigneusement » (Ch.5 §E, p. 128-129).

Conséquence épistémologique : une **pathologie est souvent une
simplification** du processus normal — un attracteur de faible
dimension prenant la place d'un attracteur complexe (crise épileptique
vis-à-vis de l'EEG, cf. A. Mandell cité par Thom). Le génome est un
« dépôt culturel de modes de fabrication », guère plus nécessaire à
l'embryogénèse « que les livres de cuisine ne le sont aux réalisations
gastronomiques d'un grand chef ».

### §F — Plans généraux d'organisation : métamérie, modulation, milieux

La métamérie (segmentation périodique de période $T$ : $h(m{-}T)=h(m)$)
est l'archétype de l'organisation répétée (Annélides). Thom insiste :
les **mutations homéotiques** (aristopaedia de la Drosophile) ne
démontrent **pas** un code ontogénétique discret — ce sont des **erreurs
de la modulation** de la métamérie, à valeur céphalisante ou
caudalisante, que l'on peut réaliser ou corriger par traitements de choc
sur les disques imaginaux. Seul élément discret : la **ségrégation des
cellules imaginales en disques disjoints** recevant un champ.

Les milieux de la biosphère se ramènent aux interfaces des trois
éléments aristotéliciens terre/eau/air (point triple = eaux peu
profondes). Le PGO y est **imposé par les contraintes de locomotion** :
l'aérien pur impose la symétrie bilatérale (lutte contre la pesanteur) ;
le benthique (poussée d'Archimède) libère la plasticité (Mollusques,
trois à quatre PGO distincts). La céphalisation et le « retournement »
Invertébré→Vertébré (A. Serres) suivent : endosquelette (chorde) → tube
nerveux dorsal induit → bipédie. L'origine des Vertébrés reste ouverte
(S. Løvtrup : Mollusque benthique → enfouissement → axe continu/chorde
→ sortie terrestre → céphalisation).

### §G — Géométrie du système nerveux : le plan BP comme quotient de l'espace de contrôle

Thom propose de lire les grandes structures du SNC sur le plan $R$ de la
BP, interprété comme un **quotient de l'espace de contrôle $U$** d'un
modèle catastrophique universel ($U$ = quotient fibré d'un espace
$\Omega$ d'activités métaboliques locales). Pour les animaux à symétrie
bilatérale, l'application $h = p \circ q \circ s$ (Ch.4 §G3) — qui
associe à tout point de l'organisme son activité physiologique locale —
admet le **plan de symétrie comme ensemble critique $Z$** ; l'image
$h(Z)$ est une courbe du plan BP.

- **Zone dorsale** : $h(Z)$ coïncide avec la diagonale $NTJ$ de la BP
  complétée. En section de moelle, la contre-image donne les arcs $JS$
  (dynamique lente) = **peau en attente d'un stimulus virtuel**, et les
  arcs $S_gT$ / $ST$ (dynamique rapide) = **sensations**, trajets
  neuraux. La dynamique en $S$ n'est pas un point-col mais un
  **double cusp** (gradient de $x+y$) — d'où les communications en
  chiasme à travers $T$ (évitement douloureux → contraction
  controlatérale).
- **Céphalisation** : la tête (cerveau-prédateur, *« Quis custodiet
  ipsos custodes ? »*) doit revenir à un exosquelette (crâne).
  L'archétype d'une vertèbre = périmètre du circuit concaténé pré-oral +
  post-oral ; le passage à la boîte crânienne (sphère = bord d'une
  boule) exige la **rétraction de l'arc ventral** sur le dorsal —
  corrélativement, la décussation des pyramides (moteur) et le chiasme
  des nerfs optiques (vision).

### Usage ICT strate 7 — préprogramme, champ en attente, pathologie-attracteur

1. **Génome = préprogramme, non code.** Thom confirme
   opérationnellement la notion de **préprogramme** centrale en strate 7
   (§Ch.8 §B (bis) *Genres = préprogramme*) : le génome « canalise
   l'attracteur » du métabolisme sans codage précis. La lecture
   [ICT-13](ICT-13-AxelrodStrategicMorphodynamics.ipynb)
   (préprogrammes morphologiques du dilemme itéré) et l'opposition
   discret/champ s'enracinent ici : un **préprogramme est un profil
   d'amplitudes d'oscillateurs**, non une suite d'instructions.
2. **Peau en attente = champ réceptif.** L'arc lent $JS$ = « peau en
   attente d'un stimulus virtuel » est l'archétype thomien du
   **couple saillance-prégnance** : la surface réceptive est un champ
   *prêt à être investi* par une prégnance (stimulus saillant) qui s'y
   propagera. Un substrat n'est pas passif, il est **pré-formé** par les
   arcs lents qui l'attendent. Pont
   [ICT-14](ICT-14-FreeEnergySurprise.ipynb)
   (représentation = capture d'un saillant par un champ réceptif).
3. **Pathologie = collapsus d'attracteur.** « Une pathologie est une
   simplification : un attracteur de faible dimension prenant la place
   d'un attracteur complexe » offre une lecture thomienne des
   **dissociations** : la dissociation comme **régime où la dynamique
   réelle s'effondre sur un attracteur appauvri** (un proxy isolé mesuré
   plutôt que le champ complet). Pont
   [#7734](https://github.com/jsboige/CoursIA/issues/7734) : un verdict
   « dissociation » peut se relire comme l'écart entre l'attracteur
   complet attendu et l'attracteur faible observé.
4. **SNS = espace de contrôle quotienté.** Lire le SNC comme un
   quotient $h(Z)$ de l'espace de contrôle local fournit un cadre pour
   [ICT-19b](ICT-19b-EnjeuBattery-Raffinement.ipynb)
   / [ICT-24](ICT-24-WorkspaceIgnition.ipynb)
   : un **workspace** $W$ est, morphologiquement, une projection-quotient
   qui sélectionne quelles activités locales deviennent globalement
   communicables (arcs rapides $S_gT$) et lesquelles restent locales
   (arcs lents $JS$). L'ignition documentée d'ICT-24 est l'**activation
   d'une communication transverse en chiasme** à travers un nœud $T$.

### Limite de la lecture (honnêteté grade C)

Thom **ne quantifie jamais** $h = p \circ q \circ s$ ni la métrique du
« double cusp » en $S$ ; la géométrie du SNC reste un **modèle
topologique qualitatif** (grade A pour le cadre catastrophique, grade C
pour son application au réel neural). La génétique moderne
(épigénétique, réseaux de gènes) **dépasse** la formule thomienne du
génome-« dépôt culturel » — nous en retenons l'intuition (le génome
module un attracteur métabolique) sans en faire une thèse moléculaire.
Les ponts ICT ci-dessus sont **candidats** (rectification A2
[#7733](https://github.com/jsboige/CoursIA/issues/7733)) : un
préprogramme comme « profil d'amplitudes » est une **hypothèse de
lecture**, pas une définition mesurée.

## Socle transversal — Ch.7 §A-F : substance, logos, et le continu contre le discret

Les Ponts transverses ci-après ne couvrent que Ch.7 §B (ABP/FBM) et §D
(privation = métastabilité). Les §A, §E et §F — l'ontologie
substantialiste, la hiérarchie des anhoméomères, le *logos* et
l'incommunicabilité des genres — restent le socle philosophique non
encore distillé, directement fécond pour la strate 7.

### §A — Aristote topologue : le continu (συνεχές) contre le discret

La thèse centrale de Thom sur l'aristotélisme : la révolte d'Aristote
contre Platon est celle du **topologue contre l'arithméticien**,
l'apôtre du qualitatif contre le quantitatif. Platon (vieillissant, ou
ses épigones) voulait une générativité **discrète** (la suite des
entiers) : le point étant un pur zéro, il fallait l'« épaissir » en
**longueur insécable** (ἄτομος γραμμή), principe générateur de la
droite. Aristote refuse — au nom de la **divisibilité du continu**
(συνεχές), il rejette les « lignes insécables ».

> « Aristote postule à la base la notion de continu (συνεχές), et c'est
> au nom de la divisibilité du continu qu'il va refuser les "lignes
> insécables". » — Thom 1991, Ch.7 §A (p. 174-175).

Conséquence ontologique : Aristote **bannit l'espace** (au sens
cartésien). L'étendue est un **prédicat de la substance** (le *topos*) ;
jamais la substance/matière n'est un prédicat de l'étendue. Ce bannissement
l'oblige à **multiplier les matières** : chaque type de changement
(μεταβολή), chaque genre (γένος) nécessite une matière spécifique — mais
toutes sont des continus. La matière première (πρώτη ὕλη) est définie
comme **sujet de toute opposition de contraires**.

### §A (bis) — Réponse à Parménide, origine de l'homéomère, et la « petite phrase »

La proposition « X est — simultanément — à la fois A et non-A » n'est pas
contradictoire : elle **impose le caractère étendu de X**. Un chat noir
**et** blanc n'est pas booléen ; il se partage en parties (noire, blanche)
chacune booléenne. Thom y voit l'**origine de la notion d'homéomère** :
le substrat étendu qui admet une prédication localement booléenne. Pont
vers Ch.5 §A-D (Cuvier/Geoffroy) : l'homéomère thomien s'enracine ici.

La discussion sur l'infini (ἄπειρον, ΦIII 207b) conduit à la **« petite
phrase »** — la clef, selon Thom, de quasi-tout le système aristotélicien :

> « Car l'infini est entouré comme une matière interne ; c'est la forme
> qui enveloppe. » — Physique ΦIII 7, 207a 35, cité par Thom 1991,
> Ch.7 §A (p. 177).

Une entité corporelle a un support $|X|$ en général **boule fermée** dont
le bord est l'enveloppe $\partial|X|$ (une sphère). C'est l'origine
catastrophiste de la dualité ABP/FBM (Acte-Bord-Puissance /
Forme-Bord-Matière) traitée au Pont transverse §Ch.7 §B. Thom note
qu'Aristote avait déjà perçu la distinction topologique **ouvert/fermé**
(« un tout borné non en soi, mais par une borne extérieure à lui-même » =
ouvert borné ; « les extrémités d'un corps et de son enveloppe sont les
mêmes » = adhérence de l'adhérence = l'adhérence, Kuratowski).

**Discret vs continu, formulation nette** : pour Aristote, tout ce qui
relève du nombre a de la matière (ἔχει ὕλην, *Met* A 8, 1074a 34) —
**« il n'y a pas de discret pur, tout être discret est réalisé par une
figure continue »**. Pont ICT strate 7 : la série ICT traite des
représentations (continus de champs) dont les **instantiations mesurées
sont discrètes** (spikes, tokens, grilles) ; le principe thomien dit que
le discret observé est toujours porté par un continu sous-jacent —
l'inverse du réductionnisme « tout est discret ».

### §F — Logos des homéomères, quiddité, et l'incommunicabilité des genres

Les homéomères (qualités phénoménologiques locales, sans forme spatiale)
portent un **logos** — défini par Aristote comme l'**ensemble des actes
et réactions que peut présenter l'homéomère soumis à diverses
perturbations**. Thom note la définition « peu operative » : on n'est
jamais sûr de connaître toutes les perturbations, notamment celles
définissant l'essence. La **quiddité** (τò τί ἧν εἶναι) de l'œuf, en
lecture moderne, serait le patrimoine génétique qui forme l'adulte
parfait (τέλειον) — « tout le mystère de l'Embryologie est dans le
passage de la forme invisible de l'homéomère germinal à la forme visible
(μορφή) de l'organisme achevé ».

**L'incommunicabilité des genres** (Oὐκ ἔστιν εἰς ἄλλο γένος μετάβασις,
*De Caelo* II 268b 1) : on ne peut aller **continûment** d'un genre à un
autre (transformer une couleur en une odeur). Mais le **substrat est
capturé par l'espace de genre** dans la prédication — envoyé au centre
organisateur (point prototypique du genre), puis réparti conformément à
l'εἶδος prédiquée. Les genres s'organisent donc comme **espèces d'un
hypergenre** par partage d'un substrat commun (ex. l'hypergenre des
qualités sensorielles : odeur/couleur/son), itérables deux à trois
échelons.

> « Le genre se comporte comme un "préprogramme", modifiable par
> l'accident local. C'est un acte bord d'une puissance, mais qui crée
> chez ses actants des dispositions privatives (στερητικὰς διαθέσεις),
> lesquelles peuvent, en passant à l'état de puissance, se déployer en
> actes secondaires. » — Thom 1991, Ch.7 §E-F (p. 193).

### Usage ICT strate 7 — discret-porté-par-continu, logos comme spectre, genre comme préprogramme

1. **Discret observé, continu sous-jacent.** Le principe thomien (« tout
   être discret est réalisé par une figure continue ») offre un cadre de
   lecture pour [ICT-17](ICT-17-EpsilonMachine.ipynb)
   (machine-ε : un automate discret extrait d'un processus continu) et
   [ICT-17b](ICT-17b-Grokking-CompressionProgress.ipynb)
   (grokking = compression progressive) : la **mesure discrète** (tokens,
   classes, états-ε) est toujours une section d'un **champ continu**
   sous-jacent. Un verdict de dissociation peut se relire comme l'écart
   entre la description discrète mesurée et le continu qui la porte.
2. **Logos = spectre de réactions.** Le *logos* thomien (ensemble des
   actes/réactions aux perturbations) est structurellement un
   **spectre** — ce qu'on mesure en
   [ICT-15b-SensitivityCanonicity](ICT-15b-SensitivityCanonicity.ipynb)
   (sensibilité locale $s(f)$) : un proxy n'est pas défini par une
   valeur ponctuelle mais par son **comportement sous perturbation**.
   Pont vers Huang 2019 $s(f) \geq \sqrt{\deg(f)}$ (cf. matrice #7734
   ICT-15b).
3. **Genre = préprogramme + dispositions privatives.** Thom confirme et
   approfondit la lecture strate-7 « genre = préprogramme » (déjà au
   §Ch.8 §B (bis)) : un genre est un **obstacle au flux génétique** qui
   capture et oriente le substrat, **modifiable par accident local**, et
   créant des **στερητικὰς διαθέσεις** (dispositions privatives) chez
   ses actants. Pont
   [ICT-13](ICT-13-AxelrodStrategicMorphodynamics.ipynb) :
   les préprogrammes morphologiques du dilemme itéré sont des
   **genres** au sens thomien — des obstacles-crible qui sélectionnent
   quelles stratégies (substrat) peuvent s'exprimer, laissant des
   **dispositions privatives** (stratégies inhibées) prêtes à se déployer.
4. **Hypergenre = space-of-genera.** L'incommunicabilité des genres +
   leur organisation en hypergenres par substrat commun fournit le
   cadre pour les **espaces de possibles extensibles** de la strate 7
   (§Ch.8 §C (bis) *Extension d'un concept = hypergenre*) : un
   hypergenre n'est pas un genre de plus, c'est l'**espace de genre**
   qui rend les genres incommunicables entre eux tout en les connectant
   par un substrat partagé.

### Limite de la lecture (honnêteté grade C)

Thom **ne formalise pas** le *logos* en un opérateur mesurable ni
l'hypergenre en une structure catégorielle précise — ces notions restent
**philosophiques** (grade C-documentaire). La « petite phrase » ΦIII 7
207a 35 est une **interprétation thomienne** d'Aristote, débattue par les
spécialistes (Hamelin y voit une « pure métaphore » ; Cherniss, cité par
Thom, une « métaphore à signification fondamentale »). Les ponts ICT
ci-dessus (logos = spectre, genre = préprogramme-obstacle) sont
**candidats** (rectification A2
[#7733](https://github.com/jsboige/CoursIA/issues/7733)) : ils proposent
une lecture, ils ne dérivent pas la mesure du formalisme. L'ontologie
substantialiste d'Aristote (bannissement de l'espace, multiplication des
matières) est un **cadre conceptuel**, pas un modèle opérationnel — la
série ICT l'emprunte pour son vocabulaire (substrat, saillance,
prégnance, genre), non comme théorème.

## Ponts transverses (déjà opérationnels)

Ces concepts Thom ne sont pas seulement un socle pour les strates à venir —
certains sont **déjà actifs** dans la série, et le présent document les
rend visibles comme tels.

### Lacet de prédation (Ch.4 §C) — ICT-10

Le **lacet de prédation revisited** est le modèle canonique : cercle $r$
pour le prédateur, points $J$ (perception) et $K$ (capture), parabole
semi-cubique $B$ pour la barrière de capture, **représentant interne**
$\hat{p}$ avec $v(\hat{p}) > v(p)$. Argémi : *coïncidence des coplis*.
Van der Pol : projection $p \to p = $ segment paramétré par $\lambda$.

**Référence :** [ICT-10-CatastropheGrammar](ICT-10-CatastropheGrammar.ipynb) — déjà mesuré, multi-graine (5/5 sur trajectoire lisse), verdict régime-dépendant (gagne en balistique, perd en erratique, perd sur source bruitée).

### Blastula physiologique (Ch.4 §D) — ICT-9 + ICT-19b

La **BP** (Ch.4 §D) est un graphe IST-FOGLAE + EQ-OMTBI dont le cycle
chemin germinal passe par les feuillets germinaux via Van der Pol. La
duplication des cycles plans = scission de singularité + prolongement
analytique + réplication ADN. L'embryologie vertébrée Amphibiens (cercle
blastula 4.15, métrique hyperbolique Van der Pol, blastopore, neurulation,
Affensattelpunkt chorde, métamérie, somites) est une **concaténation de
cycles d'hystérésis** — Thom y voit un théorème de Poincaré : la scission
d'un cycle correspond à la scission d'une singularité.

**Référence :** [ICT-9-AgencyRegeneration](ICT-9-AgencyRegeneration.ipynb) (régénération Gray-Scott comme morphogenèse), [ICT-19b-EnjeuBattery-Raffinement](ICT-19b-EnjeuBattery-Raffinement.ipynb) (`repair_gain` +0.82±0.27 sur S4).

### Plan Général d'Organisation (Ch.5) — controverse Cuvier / Geoffroy

> Distillation étendue §E-G (régulation physiologique, préprogramme
> génétique, géométrie du SNC) au §Socle transversal
> [Ch.5 §E-G](#socle-transversal--ch5-e-g--régulation-physiologique-préprogramme-génétique-et-géométrie-du-système-nerveux)
> ci-dessus. Le présent pont ne couvre que les §A-D (Cuvier/Geoffroy).

La controverse 1830 entre Cuvier (conditions d'existence) et Geoffroy
Saint-Hilaire (principe de connexion des parties) est relue par Thom :
**homéomère** (3D strate, sans forme) vs **anhoméomère** (lieu des ἒργα
καì πράξεις). L'application $\Phi : O \to (U, K)$ projette l'organisme
vers ses conditions d'existence $(U)$ et ses connexions $(K)$. Citation
clef : Geoffroy *« la matière est homogène dans son principe »* — Thom y
voit une allusion au couple **saillance-prégnance** (matière = saillance
continue, forme = prégnance des singularités).

**Usage ICT strate 7.** L'opération $\Phi : O \to (U, K)$ est
structurellement analogue à l'**opérateur d'émergence** de Hoel : une
projection qui relâche la contrainte micro vers une lecture macro. La
différence est qu'on ne s'intéresse pas ici à l'information effective
préservée, mais à la **forme des discontinuités** (les anhoméomères) que
la projection met au jour.

### Axiomatique aristotélicienne (Ch.6) — 8 axiomes

Les **8 axiomes I-VIII** de la dynamique aristotélicienne : entités
(οὐσίαι), substrat (ὑποκείμενον), localité (ϑA ∩ ϑB = ∅), transformations
naturelles (κατὰ ϕύσιν), accidents (συμβεβηκός), τέλoς vs τελευτή
(finalité vs achèvement), section $\sigma : |A| \to Y$ (continue ou
discontinue sur $K$). Thom y voit une **axiomatique matérielle**, pas
formelle — ce qui se mesure, c'est la **continuité** ou la **discontinuité
de la section**.

**Usage ICT strate 6.** Les **5 dissociations canoniques** rendues
visibles par l'ossature 4-objets (matrice c.728y+34, §5) sont des
**discontinuités de section $\sigma$** : saillant sans importance
($s \neq 0, \pi = 0$), important mais mal prédit ($\pi$ haut, $q$ loin),
bien représenté non globalement accessible ($q$ bon, $W$ sélectif),
globalement diffusé tout en étant faux ($W$ large, $q$ faux),
fortement compressé non causalement utilisé ($K$ basse, effet causal nul).
Chacune est un **endroit où $\sigma$ casse** — et c'est précisément ce
qu'on observe dans les notebooks.

### ABP / FBM (Ch.7 §B) — Acte, Bord, Puissance / Forme, Bord, Matière

> « L'acte est bord de la puissance. »
> « La forme est bord de la matière. »
> — Aristote, cité par Thom 1991, Ch.7 §B.

**Matière = boule ouverte** (sans bord) ; **sphère = bord = forme**. La
**définition** (ὁρισμός) est le bord de la notion. L'acte est ce qui
transforme la puissance en effectuation — donc ce qui apparaît au bord
de la matière.

**Usage ICT strate 7.** Le **workspace $W$** d'ICT-24 peut être relu
comme l'opérateur qui définit le **bord de l'acte** : ce qui rend une
composante disponible à d'autres mécanismes est précisément ce qui en
fait un **acte** au sens d'ABP. La dissociation documentée (pics
emergence_gain ≠ événements d'ignition) est l'écart entre la **forme**
(FBM, ce qui est mesuré au bord) et la **matière** (ABP, ce qui est
effectué au bord).

### Privation = métastabilité (Ch.7 §D)

> « La privation est l'entrée en métastabilité. »
> — Thom 1991, Ch.7 §D (cf. citation Aristote *καì γὰρ ἡ στέρησις
> εἶδός πώς ἐστιν*, ΦII 1, 193b, 19).

La privation (στέρησις) **est** une forme — la forme de ce qui manque,
qui organise la trajectoire autour de son absence. C'est exactement le
**lacet de prédation** d'ICT-10 : la proie absente (la banane inaccessible)
est une forme prégnante qui **plie** la trajectoire du prédateur.

**Usage ICT strate 7.** La **triade moyen / fin / enjeu** d'ICT-18b
(moyen = production d'entropie $\sigma$, fin = compétence de Levin) est
une opération de **privation structurée** : on ne mesure pas la fin
directement (elle n'est pas là), on mesure le **coût de s'en approcher**
(le moyen). Le verdict `P2 DISSOCIATION` capture l'écart entre la forme
de la fin et la matière de son effectuation.

## Distinguo discipline — pas de montée automatique en obstruction

Cette distillation reste au **grade C-documentaire** :

- Le **cadre mathématique** (catastrophes, dynamiques lentes-rapides,
  cuspides, fronces, plis) est au **grade A** : formalisé, mesurable,
  reproductible. Cf. [ICT-10](ICT-10-CatastropheGrammar.ipynb)
  qui opère sur la fronce et le lacet de prédation avec des bancs
  multi-graines et des contrôles adverses.
- La **lecture ICT** (les dissociations sont des obstructions cohomologiques,
  les genres sont des hypergenres, les prototypes sont des attracteurs dans
  l'hypergenre) est **candidate** — elle est **proposée**, pas démontrée.
  Elle doit rester **prudente** sur deux points :

  1. **Pas de montée automatique** dissociation → obstruction cohomologique,
     sauf prérequis vérifiés (Kochen-Specker [#7290](https://github.com/jsboige/CoursIA/issues/7290),
     Arrow `social_choice_lean`, scalaire falsifié cross-substrat).
     Cf. rectification A2 de
     [#7733](https://github.com/jsboige/CoursIA/issues/7733) et la
     grille 3-régimes
     [`docs/ict/synthese-invariants-dissociations-obstructions.md`](../../../docs/ict/synthese-invariants-dissociations-obstructions.md)
     ([#7399](https://github.com/jsboige/CoursIA/issues/7399)).
  2. **Pas de confusion des grades** : « la phrase transitive prototypique
     est une prédation » est un **modèle** (au sens où la série l'utilise
     pour ICT-12), pas une **loi linguistique**. La transitivité est
     *prototypique* — il existe des verbes intransitifs, des patients qui
     résistent, des actants qui disparaissent. Le « prototypique » est
     précisément le **préprogramme** de Thom, pas la **loi universelle**.

## Distinguo matrice #7734 vs distillation Thom

Les deux documents sont **complémentaires, non redondants** :

| Document | Grade | Objet | Portée |
|---|---|---|---|
| [`docs/ict/dissociations-matrix.md`](../../../docs/ict/dissociations-matrix.md) ([#7734](https://github.com/jsboige/CoursIA/issues/7734)) | C-documentaire | Matrice opérationnelle : 33 claims × verdict sobre × portée explicite, ossaturée par `(s, q, π, W)` | Par-claim (per-claim, verdict per-ligne) |
| **Le présent document** ([#7739](https://github.com/jsboige/CoursIA/issues/7739)) | C-documentaire | Distillation théorique : socle Thom 1991 pour strates 6/7 | Transversale (référence à charger avant d'écrire les notebooks strates 6/7) |

**Pourquoi les deux.** La matrice répond à *où en est la mesure, dans quel
régime, avec quelle confiance*. La distillation répond à *quel vocabulaire
théorique la mesure peut-elle invoquer sans réinventer*. La matrice
pourrait au besoin ré-arborer dans ses lignes les distinctions de la
distillation (saillance vs prégnance, valence Tesnière, opérations
catastrophistes), mais elle ne le fait pas aujourd'hui — ce serait une
extension, pas une redite.

## Liens

### Cross-références Thom 1991 par chapitre

- **Ch.1 — La théorie des catastrophes** : cf. usages
  [ICT-10](ICT-10-CatastropheGrammar.ipynb)
  (fronce, métathéorème, lacet de prédation).
- **Ch.2 — Le langage** : cf. §Strate 6 ci-dessus (universalisme
  linguistique, valence Tesnière, transitivité prototypique).
- **Ch.3 — Modélisation mathématique et Philosophie** : cf. §Strate 6
  (généralisation, invention de l'instrument) + usages
  [ICT-12](ICT-12-ValenceFieldsAndAnimats.ipynb)
  (coplis, prolongement analytique).
- **Ch.4 — Embryologie et dynamique** : cf. §Socle transversal
  [Ch.4 §C](#socle-transversal--la-dynamique-de-prédation-ch4-c-et-lorigine-du-représentant-interne-p)
  (lacet de prédation revisited, représentant interne `p̂`, origine de la
  généalogie #7735) et §Ponts transverses (blastula BP).
- **Ch.5 — Plan Général d'Organisation** : cf. §Socle transversal
  [Ch.5 §E-G](#socle-transversal--ch5-e-g--régulation-physiologique-préprogramme-génétique-et-géométrie-du-système-nerveux)
  (régulation physiologique, préprogramme, SNC) et §Ponts transverses
  (Cuvier / Geoffroy, homéomère / anhoméomère).
- **Ch.6 — Axiomatique aristotélicienne** : cf. §Socle transversal
  [Ch.6 §B/§D-E] (téléologie, section $\sigma$) et §Ponts transverses
  (8 axiomes).
- **Ch.7 — Continu et discret** : cf. §Socle transversal [Ch.7 §A-F]
  (substance, continu/discret, « petite phrase » ABP/FBM, logos,
  genre = préprogramme) et §Ponts transverses (ABP/FBM opérationnel,
  privation = métastabilité).
- **Ch.8 — Perspectives aristotéliciennes en théorie du langage** :
  cf. §Strate 6 (universalisme, genres, hypergenres, opérations
  catégorielles ; §D-E ternarité peircéenne, phrase nucléaire comme
  vecteur de prégnance, capture-prédation fronce, privation du verbe,
  continu de Seiler) + §Strate 7 (extension d'un concept = hypergenre).

### Documents de la série ICT

- [ICT-0-Framing](ICT-0-Framing.md)
  §Strate 2 (morphogenèse dynamique, catastrophes) — référence de base.
- [ICT-0-Annexe-IntegratedComplexityTheory](ICT-0-Annexe-IntegratedComplexityTheory.md)
  — fondements théoriques complémentaires.
- [ICT-10](ICT-10-CatastropheGrammar.ipynb)
  — catastrophe fronce + lacet de prédation + `p̂`.
- [ICT-12](ICT-12-ValenceFieldsAndAnimats.ipynb)
  — animats actantiels, mesure de la valence.
- [ICT-13](ICT-13-AxelrodStrategicMorphodynamics.ipynb)
  — préprogrammes morphologiques du dilemme itéré.
- [ICT-14](ICT-14-FreeEnergySurprise.ipynb)
  — jambe représentationnelle (surprise, free energy).
- [ICT-17b](ICT-17b-Grokking-CompressionProgress.ipynb)
  — compression progressive et dissociations.
- [ICT-18b](ICT-18b-ReversibilityBudget.ipynb)
  — triade moyen / fin / enjeu, dissociation $\sigma$ / Levin.
- [ICT-19b](ICT-19b-EnjeuBattery-Raffinement.ipynb)
  — Gray-Scott S4, mesure espace de champ.
- [ICT-24](ICT-24-WorkspaceIgnition.ipynb)
  — workspace $W$ (Gates 22-23 livrés, dissociation documentée).
- [ICT-Argumentation-BeliefTrajectories](ICT-Argumentation-BeliefTrajectories.ipynb)
  — 5 classes Argumentum (espèces thomiennes).

### Documents de synthèse

- [`docs/ict/dissociations-matrix.md`](../../../docs/ict/dissociations-matrix.md)
  ([#7734](https://github.com/jsboige/CoursIA/issues/7734), c.728y+34) —
  matrice opérationnelle des dissociations (per-claim).
- [`docs/ict/synthese-invariants-dissociations-obstructions.md`](../../../docs/ict/synthese-invariants-dissociations-obstructions.md)
  ([#7399](https://github.com/jsboige/CoursIA/issues/7399)) — grille
  3-régimes (invariants / dissociations / obstructions).
- [`docs/grothendieckian-lens.md`](../../../docs/grothendieckian-lens.md)
  ([#7299](https://github.com/jsboige/CoursIA/issues/7299)) — langage
  cohomologique (grade A) + lecture ICT (grade C, cf. A2).

### Issues

- Epic umbrella : [#4588](https://github.com/jsboige/CoursIA/issues/4588)
- Issue-source de cette distillation :
  [#7739](https://github.com/jsboige/CoursIA/issues/7739)
- Rectification A2 (H¹ érigé impossibilité → candidat obstruction) :
  [#7733](https://github.com/jsboige/CoursIA/issues/7733)
- Matrice des dissociations (c.728y+34) :
  [#7734](https://github.com/jsboige/CoursIA/issues/7734)
- Grille 3-régimes : [#7399](https://github.com/jsboige/CoursIA/issues/7399)
- N1 obstruction comme objet expérimental :
  [#7395](https://github.com/jsboige/CoursIA/issues/7395)
- N2 trajectoires de représentations :
  [#7396](https://github.com/jsboige/CoursIA/issues/7396)

## HORS-scope résiduel

Cette distillation est **circonscrite aux strates 6 et 7** telles
qu'anticipées dans l'Epic umbrella. Trois zones restent à lire ou à
exploiter :

- **Thom Ch.1, Ch.2 lus mais non exploités directement** ici — Ch.1
  (introduction à la théorie des catastrophes) est en partie couvert par
  [ICT-10](ICT-10-CatastropheGrammar.ipynb),
  Ch.2 (le langage) est exploité en strate 6 mais son contenu propre
  (formalisme des schémas linguistiques) reste à creuser.
- **Ch.5 §E-G** (régulation physiologique, préprogramme génétique,
  géométrie du SNC) — **distillés** au §Socle transversal Ch.5 §E-G
  ci-dessus. Le sous-titre « §H homéomères étendus » de l'inventaire
  initial ne correspond pas à une section distincte de la source : les
  homéomères y sont traités en §A-D (Cuvier/Geoffroy) et la physiologie
  en §E-G, sans §H séparé (lecture honnête, G.9).
- **Ch.7 §G-K** (substance / logos) — **distillé en §Socle transversal
  [Ch.7 §A-F] ci-dessus**. *Honnêteté G.9* : l'inventaire initial (issue
  #7739) étiquetait cette tranche « §G-K (substance/logos) », mais la
  lecture *firsthand* montre que Ch.7 ne contient que **§A-F** (pas de
  §G-K distinct) ; le matériel substance/logos se trouve en §A, §E, §F,
  désormais distillé. Aucune section §G-K fabriquée.
- **Ch.8 §D-E** (ternarité peircéenne, phrase nucléaire, privation du
  verbe, continu de Seiler) — **couvert** au §Strate 6.

**Non-priorité assumée.** Cette distillation n'est pas un théorème ni une
unification ; elle est un **socle de vocabulaire**. Les notebooks futurs
des strates 6 et 7 restent à écrire — et c'est **leur** mesure, pas
cette distillation, qui validera ou non la fécondité du vocabulaire
emprunté à Thom.

---

*Document de synthèse consolidant la lecture ciblée de Thom 1991 —
issue-source [#7739](https://github.com/jsboige/CoursIA/issues/7739) ·
Epic umbrella [#4588](https://github.com/jsboige/CoursIA/issues/4588) ·
cohérent avec la dette de rigueur [#7733](https://github.com/jsboige/CoursIA/issues/7733)
(rectification A2) et la matrice opérationnelle [#7734](https://github.com/jsboige/CoursIA/issues/7734) (c.728y+34).*
