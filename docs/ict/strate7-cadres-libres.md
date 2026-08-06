# ICT — Cadrage strate 7 D1 — variables libres bien choisies, free coordinates de 2e ordre, jeu évolutif G_t et mécanisme M

> **Statut.** Document de cadrage formel, grade **C-documentaire** (cadrage, pas de dispatch expérimental). Consolide la **jambe D1** de la strate 7, à côté de la jambe D2 (5 bancs d'essai contrôlés [#7746](https://github.com/jsboige/CoursIA/issues/7746) — MERGED, ICT-26 → ICT-30) et de la jambe D3 ([#7747](https://github.com/jsboige/CoursIA/issues/7747) — cadrage narratif *boussole de la strate 7*, livré en PR [#9579](https://github.com/jsboige/CoursIA/pull/9579) MERGED c.1243, [`strate7-boussole-myth.md`](strate7-boussole-myth.md)). D1 et D3 sont **complémentaires, pas redondants** : D1 fixe *le formalisme* (variables libres, jeu évolutif, 6 proxys, dette d'irréversibilité), D3 fixe *la boussole narrative* (deux cascades d'investissement performatif, les trois verbes comme variables libres, mechanism design schmidhuberesque). Le présent document tient au grade C : **nommé sans démonstration**, posé pour cadrer, jamais revendiqué comme résultat.
>
> **Objet.** Documenter (a) **l'objet de la strate 7** : les *free coordinates* / *freebits de second ordre* — l'incertitude sur l'**espace lui-même** (vs l'incertitude sur une valeur dans un espace fixé, qui est le freebit d'Aaronson), (b) **le jeu évolutif** `G_t = (N, L_t, S_t, A_t, U_t, P_t)` et son **mécanisme** `M` qui décide ce qui devient public, (c) les **6 proxys mesurables** qui rendent la strate 7 falsifiable (pas un horizon, un **banc d'essai**), (d) la **discipline des variables libres bien choisies** — self-référence ≠ performativité, la qualité du choix est composante de la performativité, et (e) le **reframe épistémique honnête** : on ne ramène pas un scalaire, on ramène une *forme meilleure pour la même question*.
>
> **Discipline.** Cadrage grade C, **AUCUNE nouvelle dépendance expérimentale** n'est créée. Les ancres citées (notebooks ICT-26 → ICT-30, modules `grothendieck_lean`, fichiers `docs/ict/`, PRs [#9579](https://github.com/jsboige/CoursIA/pull/9579) [#9551](https://github.com/jsboige/CoursIA/pull/9551) [#9547](https://github.com/jsboige/CoursIA/pull/9547) [#9546](https://github.com/jsboige/CoursIA/pull/9546)) sont sur `origin/main` au moment de la rédaction. Le document **ne propose pas** de test direct de la strate 7 — les bancs existent déjà (D2) et la tresse de la strate 7 a été cartographiée horizontalement (D1 livré en aval de la tresse, mais logiquement en amont de la pose des bancs : *laisser la mer monter, banc par banc*). Issue-source : [#7745](https://github.com/jsboige/CoursIA/issues/7745). See [#4588](https://github.com/jsboige/CoursIA/issues/4588) (Epic umbrella ICT). *Part of* [#7395](https://github.com/jsboige/CoursIA/issues/7395) (méta-proxy ICT).
>
> **Avertissement méthodologique.** La strate 7 est la plus spéculative et la plus risquée : on y touche à **ce qui rend l'agent capable de redéfinir l'espace dans lequel il agit**. Le cadrage assume explicitement cette difficulté (le scalaire avait la mauvaise forme, cf. §0) et **ne livre pas** la strate 7 comme résultat : la pose des 6 proxys est une **grille de falsifiabilité** (qui rend dicibles des *NON-résultats* honnêtes), pas un cahier des charges pour démontrer une thèse. Cf. [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) §« Ce que ce document n'est pas » — on ne confond pas une grille avec un verdict.

## 0. Le reframe épistémique (le scalaire avait la mauvaise forme)

La strate 7 de la série ICT a été ouverte pour répondre à une question *simple* : **existe-t-il un scalaire de la conscience ?** (cf. [#4588](https://github.com/jsboige/CoursIA/issues/4588) arc initial). La réponse actuelle, après les strates 1 → 6 et leurs falsifications successives, est **non — non pas parce que la conscience n'existe pas, mais parce que la forme scalaire était la mauvaise forme**. Cf. [`dissolution-scalaires.md`](dissolution-scalaires.md) : la dissolution successive de Φ / F / K a montré que les trois candidats scalaires *covarient* (τ = +1.00) ou *divergent* (K bipolaire puis tri-polaire, cf. dissolution-scalaires §palier 5), c'est-à-dire **ne se laissent pas réduire à un seul**. La leçon n'est pas « tout se vaut » : c'est **« le scalaire avait la mauvaise forme »**.

Le reframe de la strate 7, posé par [#7745](https://github.com/jsboige/CoursIA/issues/7745), est alors :

> *Le scalaire se dissout en faisceau de proxys ; la coordonnée libre est la forme qui restait à nommer.*

Ce n'est **pas** s'être perdu dans la spéculation. C'est avoir trouvé **une meilleure réponse à la même question** : la question « qu'est-ce qui distingue un système qui est *sujet* d'un système qui ne l'est pas ? » admet une réponse **catégorielle** (l'agent dispose d'une coordonnée libre qu'il *peut* prolonger) là où une réponse **scalaire** (l'agent a un certain niveau de Φ) n'admet que des réponses falsifiées. Le présent document prend ce reframe comme point de départ et installe la **forme** — pas la thèse — qui le rend lisible.

## 1. L'objet : free coordinates / freebits de 2e ordre

### 1.1 Au-dessus du freebit d'Aaronson

Scott Aaronson (cf. *« The Ghost in the Quantum Turing Machine »*, 2013, *Theoretical Computer Science* ; repris dans les notebooks *Mechanism Design* de la série ICT) a proposé le **freebit** comme un bit de valeur que l'agent ne peut pas connaître *avant* l'acte de mesure — une incertitude *sur la valeur* dans un **espace déjà fixé**. La strate 7 d'ICT pose une question **strictement plus forte** : l'incertitude ne porte pas sur une valeur dans un espace fixé, mais sur **l'espace lui-même**.

Formellement, là où le freebit d'Aaronson est un point `x ∈ L` dans un espace `L` que l'agent ignore avant l'observation, le **freebit de second ordre** (notre objet) est :

> L'agent ne dispose pas encore des **concepts, actions et dimensions** du jeu qu'il joue — *c'est l'espace `L` lui-même qui est en cours de constitution*.

Cette formulation relève d'une **littérature *unawareness*** (modèles logiques où l'agent ignore jusqu'à *l'existence* de certaines variables, cf. Fagin-Halpern, *« Belief, Awareness, and Limited Reasoning »*, AIJ 1988 ; Heifetz-Morgenstern-Samuelson, *« Game Theory with Awareness of Assumptions »*, JET 2013). Le présent cadrage **ne réinvente pas** la littérature *unawareness* : il la **transpose** au formalisme 4-objets de la série ICT, et l'instancie dans la **grammaire extensionnelle** des catégories grothendieckiennes (cf. §1.2).

### 1.2 Le candidat formel : choix d'une extension

Le vrai candidat formel est **le choix d'une extension** :

```
ξ_t ∈ Ext(L_t, L_{t+1})
```

où `Ext(L_t, L_{t+1})` est l'**ensemble des extensions** d'un espace local `L_t` en un espace global `L_{t+1}` qui le contient. L'incertitude porte sur **le choix de l'extension** : l'agent, à l'instant `t`, doit choisir *comment* prolonger l'ancien espace — et ce choix est *non-canonique* (il y a, en général, plusieurs prolongements non équivalents).

Lien grothendieckien (cf. [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md)) : un objet local admet *plusieurs* extensions globales non équivalentes (cf. obstruction cohomologique `H¹ ≠ 0`, [`synthese-invariants-dissociations-obstructions.md`](synthese-invariants-dissociations-obstructions.md) §« Pourquoi cette grille »). Le choix d'extension est précisément **là où l'agent intervient comme décideur** : `H¹ ≠ 0` est la mesure *qu'il y a quelque chose à choisir* ; `|Ext(L_t, L_{t+1})|` est la mesure *combien* il y a à choisir ; et la **qualité du choix** (cf. §4) est ce qui distingue une extension utile d'une extension manipulatrice.

### 1.3 Barrière conservée : pas de bit physique ex nihilo

Le cadrage pose explicitement une **barrière conservée** :

> La strate 7 ne crée **pas** de bit physique *ex nihilo*. Ce qui est créé est un **degré de liberté causal** nouveau, qui n'était pas dans le bilan physique du système à l'instant `t-1`.

Cette barrière distingue la strate 7 du « surnuméraire métaphysique » : la **physique** du système (énergie, bits, lois) est conservée, et ce qui est ajouté est un **nouveau degré de liberté dans l'espace des représentations** que les agents (et l'observateur) peuvent utiliser. La « personne morale » en est l'exemple paradigmatique (cf. §1.4) : zéro bit physique ajouté au monde, une coordonnée efficace ajoutée au monde social — l'agent, à partir d'une telle coordonnée, peut agir sur le monde *comme si* elle existait physiquement, et les autres agents interagissent avec elle en conséquence.

### 1.4 Émergence historique : le cas « personne morale »

L'exemple historique canonique du free coordinate de second ordre est **l'institution de la personne morale** (l'entreprise, la cité, l'université, l'État). Aucune de ces entités n'a de « bit physique » qui la distingue du reste du monde : ce sont des **artefacts** *conventionnels* qui n'existent que parce que des agents les traitent comme existants. L'acte par lequel une société décide qu'une entreprise *existe* (registre du commerce, statuts, capital initial) est **un acte de free coordinate** : il ajoute un **degré de liberté causal** (l'entreprise peut signer des contrats, posséder, estorer en justice) sans ajouter un bit au monde physique.

Ce cas est paradigmatique pour la strate 7 parce qu'il exhibe **toutes les caractéristiques** de l'objet formel :

- **Non-canonique** : il y a plusieurs façons d'instituer une personne morale (SARL vs SA vs SCI vs association loi 1901), et la *façon* choisie engage des conséquences ;
- **Causal** : une fois instituée, la personne morale agit *sur* le monde (elle signe, elle possède, elle estorer en justice) — son existence conventionnelle est *performatrice* ;
- **Institutionnalisable** : la personne morale persiste *après* le retrait de ses instigateurs (le fondateur meurt, l'entreprise continue) ;
- **Irréversible** : dissoudre une personne morale est infiniment plus coûteux que la créer (asymétrie constitutive).

Les 6 proxys mesurables de la strate 7 (cf. §3) sont construits pour **capter** ces quatre caractéristiques en grandeur mesurable.

## 2. Le jeu évolutif G_t et le mécanisme M

### 2.1 La structure G_t = (N, L_t, S_t, A_t, U_t, P_t)

L'état de la strate 7 à l'instant `t` est un **jeu évolutif** `G_t` à 6 composantes :

| Composante | Symbole | Rôle | Exemple paradigmatique |
|---|---|---|---|
| **Agents** | `N` | L'ensemble des agents participant au jeu | Population, nation, écosystème d'agents LLM |
| **Langage** | `L_t` | L'espace des représentations partagées (mots, types, catégories) | Lexique, ontologie, vocabulaire mathématique |
| **Stratégies** | `S_t` | Les stratégies disponibles étant donné le langage | Stratégies économiques, modèles génératifs |
| **Actions** | `A_t` | Les actions que les agents peuvent entreprendre (au sein des stratégies disponibles) | Trade-offs, choix d'outils, do-calculus |
| **Utilités** | `U_t` | Les fonctions d'utilité des agents (étant donné le langage et les stratégies) | Récompenses, fonctions de perte |
| **Prédictions** | `P_t` | Les prédictions que les agents font sur les futurs possibles | Modèles génératifs, croyances, *priors* |

**L'état est un tuple**, pas un scalaire : la strate 7 ne **réduit pas** la situation à une grandeur unique. Le tuple est ce qui permet de capturer **simultanément** les aspects linguistiques, stratégiques, actantiels, évaluatifs et prédictifs d'un système qui peut *modifier son propre langage*.

### 2.2 Deux types de coups : internes et ontologiques

À chaque pas de temps, deux types de coups sont possibles :

- **Coups internes** : `a ∈ A_t` — un agent agit *au sein* de l'espace `L_t` (parle, échange, signe un contrat, joue un coup de poker). L'espace `L_t` n'est pas modifié par ces coups.
- **Coups ontologiques** : `η : G_t → G_{t+1}` — un agent (ou un mécanisme) *modifie* l'espace `L_t` en `L_{t+1}` : invente un nouveau mot, crée une nouvelle catégorie, définit un nouveau type d'agent, *redéfinit* ce qui était jouable. Ces coups sont **non-canoniques** (plusieurs `η` non équivalents possibles) et leur résultat est **un nouveau tuple** `G_{t+1}`.

La distinction entre coup interne et coup ontologique est **le cœur de la strate 7** : un agent qui n'a accès qu'aux coups internes est un agent *au sein d'un jeu fixé* (strate 6, cf. [`cadrage-trajectoires-representations.md`](cadrage-trajectoires-representations.md)) ; un agent qui a accès aux coups ontologiques est un agent *qui peut transformer le jeu lui-même* — c'est précisément la strate 7.

### 2.3 Le mécanisme M

À tout moment, **un mécanisme** `M` décide ce qui devient public :

```
M(η_1, η_2, ..., η_n) = G_{t+1}
```

où `η_1, ..., η_n` sont les coups ontologiques *proposés* par les agents, et `G_{t+1}` est l'état *résultant*. Le mécanisme `M` est l'**arbitre des visibilités** : il décide quels mots sont retenus, quelles catégories sont adoptées, quels types d'agents sont reconnus. C'est l'équivalent, pour la strate 7, du *mécanisme* en *mechanism design* (Hurwicz-Maskin-Myerson, Nobel 2007) — mais à un cran d'abstraction supérieur, puisque `M` opère sur **les règles elles-mêmes**, pas sur les coups au sein des règles.

L'analogie avec le *mechanism design* n'est **pas** fortuite : la strate 7 est précisément *ce qui se passe quand le mechanism design devient autoréférent* (le mécanisme doit choisir *quelles règles du mécanisme seront modifiables*). Cf. §3.4 (`P(R)` = pouvoir performatif) et §4 (la qualité du choix des variables libres comme composante de la performativité).

### 2.4 La question des institutions

La **question centrale** que la strate 7 pose est :

> *Quelles institutions (réalisations particulières de `M`) permettent l'apparition de vocabulaires utiles **sans capture immédiate** par les stratégies manipulatrices ?*

Cette question est explicitement un **point de rencontre** avec l'argumentation computationnelle (série Argumentum, cf. Argument_Analysis / SymbolicAI) : le *discours d'englobement* (cf. [#7742](https://github.com/jsboige/CoursIA/issues/7742) — jambe C3, **gelée** tant que corpus public non branché) est exactement un coup ontologique `η` dont l'enjeu est l'absorption d'un langage par un autre. La grammaire de propagation (cf. [#7743](https://github.com/jsboige/CoursIA/issues/7743) — jambe C4, jauge `π, W, causalité`) est la forme mesurable de la *qualité* d'un coup ontologique : un coup utile a une prégnance `π` suffisante, est rendu accessible par le workspace `W`, et a un pouvoir causal `P(R)` suffisant pour transformer le système qui l'a produit.

## 3. Les six proxys mesurables

La strate 7, comme toute strate qui se veut falsifiable, doit disposer de **grandeurs mesurables**. Les 6 proxys suivants sont construits pour rendre dicibles à la fois les **succès** (la strate 7 livre) et les **NON-résultats** (la strate 7 n'a pas livré) sans qu'on doive recourir à un scalaire global. Ce sont des **composantes**, pas un agrégat.

### 3.1 O_t — expansion ontologique

> **Définition.** `O_t = |L_{t+1} \ L_t|` — le nombre de concepts, catégories ou types d'agents ajoutés à `L_t` entre `t` et `t+1`.

Mesure l'**ouverture linguistique** du système : est-ce qu'il y a, entre `t` et `t+1`, des *nouveaux* concepts qui n'existaient pas avant ? Si `O_t = 0` toujours, le système est *linguistiquement fermé* (strate 6 plafonnée). Si `O_t` croît, le système est *linguistiquement ouvert* et les autres proxys deviennent dicibles.

### 3.2 ΔA_t — ouverture politique

> **Définition.** `ΔA_t = |A_{t+1} \ A_t|` — le nombre d'actions nouvelles rendues disponibles étant donné le langage étendu.

Mesure la **conséquence pratique** de l'expansion ontologique : l'ajout d'un mot dans le lexique ne compte comme extension *politique* que si ce mot *ouvre* des actions nouvelles. Un concept ornemental (qui ne change rien à ce que les agents peuvent faire) n'augmente pas `ΔA_t`. C'est un **garde-fou contre le verbiage** : l'expansion ontologique n'est mesurable qu'à travers sa *capacité à ouvrir des actions*.

### 3.3 C_t = |Ext(G_t)| — non-canonicité

> **Définition.** `C_t = |Ext(G_t)|` — le nombre d'extensions non équivalentes de `G_t` en `G_{t+1}`.

Mesure la **non-canonicité** du prolongement : y a-t-il *plus d'une* façon de prolonger l'espace ? Si `C_t = 1` (canonique), la strate 7 est *triviale* — il n'y a rien à choisir, le système se prolonge de lui-même. Si `C_t > 1`, il y a *quelque chose à choisir*, et l'agent (ou le mécanisme `M`) doit *trancher*. C'est le proxy le plus directement lié à la grammaire extensionnelle (cf. §1.2) : sans `C_t > 1`, la strate 7 n'a pas d'objet.

### 3.4 P(R) — pouvoir performatif (do-calculus)

> **Définition.** `P(R) = D(Pr(traj | do(R)) ‖ Pr(traj | do(¬R)))` — la divergence KL entre la distribution des trajectoires du système sous l'intervention `R` (réaliser le coup ontologique `η`) et sous la non-intervention `¬R`.

Mesure le **pouvoir causal** du coup ontologique. Formellement, c'est l'application du *do-calculus* de Pearl (cf. *« Causality »*, Cambridge UP, 2009 ; repris dans les notebooks ICT-14/14b Free Energy / Active Inference, cf. [`dissociations-matrix.md`](dissociations-matrix.md) strate 4) à la strate 7 : un coup ontologique a un pouvoir performatif élevé si les trajectoires du système *changent significativement* quand on l'interventionne. `P(R) ≈ 0` signifie que le coup ontologique n'a pas d'effet causal discernable — c'est un coup *décoratif* (un nouveau mot qui n'agit sur rien) ; `P(R) ≫ 0` signifie que le coup ontologique a transformé la dynamique du système.

### 3.5 Institutionnalisation — persistance après retrait de la cause

> **Définition.** Pour un coup ontologique `η` posé à l'instant `t`, l'institutionnalisation est la **probabilité** que `η` soit encore actif à l'instant `t + τ` *après* que l'agent instigateur a été retiré du jeu.

Mesure la **durabilité** d'un coup ontologique. Un coup *non-institutionnalisé* disparaît avec son instigateur (l'inventeur meurt, le mot tombe en désuétude) ; un coup *institutionnalisé* persiste (le mot reste dans le lexique, la catégorie reste disponible, l'artefact continue d'agir). L'institutionnalisation est **la signature temporelle de la strate 7** : sans institutionnalisation, la strate 7 se réduit à la strate 6 (des agents qui modifient leur langage sans que le langage modifié persiste).

### 3.6 I(R) — dette d'irréversibilité

> **Définition.** `I(R)` = le coût (en temps, énergie, attention, capital) de défaire un coup ontologique `η`, comparé au coût de le poser.

Mesure l'**asymétrie constitutive** entre création et dissolution. Une dette d'irréversibilité élevée (création ≪ dissolution) est la marque des *macro-faits* (cf. [#7746](https://github.com/jsboige/CoursIA/issues/7746) ancrage : *« une extension qui réussit devient un fait stable — le free coordinate disparaît au moment même où il réussit »*) : une fois le coup ontologique réussi et institutionnalisé, il *cesse d'être un free coordinate* (il devient partie du paysage) et défaire l'extension coûte infiniment plus que la créer.

### 3.7 Le 6-uplet (O_t, ΔA_t, C_t, P(R), institutionnalisation, I(R)) comme grille

Aucun des 6 proxys ne *suffit seul* à caractériser la strate 7 — et c'est précisément **le reframe épistémique** de §0 : le scalaire unique n'existe pas, et le 6-uplet est *la forme qui restait à nommer*. Les bancs ICT-26 → ICT-30 (D2, [#7746](https://github.com/jsboige/CoursIA/issues/7746) MERGED) sont des **instantiations particulières** où 1 à 3 de ces proxys sont mesurés sur des substrats précis :

- **ICT-26** (coordination à vocabulaire fixe) : ΔA_t = 0 par construction ; C_t = 1 ; O_t, P(R), institutionnalisation, I(R) à mesurer.
- **ICT-27** (invention de symboles) : O_t > 0 ; ΔA_t > 0 ; C_t > 1 ; P(R) à mesurer.
- **ICT-28** (adoption collective, seuil ρ_c) : P(R) à mesurer comme *fonction* de la fraction d'agents ; seuil critique où P(R) ≫ 0.
- **ICT-29** (inoculation d'un cadrage) : institutionnalisation du cadrage ; I(R) asymétrique.
- **ICT-30** (inhibition de l'innovation) : O_t = 0 par construction ; ΔA_t = 0 ; C_t = 1 forcé ; mesure des proxys comme *négatifs* (que se passe-t-il quand la strate 7 est interdite ?).

Le 6-uplet est *la forme de la strate 7*, et les bancs en sont des **coupes** sur cette forme.

## 4. Self-référence ≠ performativité

### 4.1 Le *cheap* de la self-référence

La strate 7 est souvent confondue avec une thèse sur la **self-référence** : un système qui se décrit lui-même, qui se représente en train de se représenter, etc. La self-référence est *cheap* : tout système Turing-complet peut s'auto-référencer (un interpréteur qui s'interprète, une fonction qui s'applique à elle-même, un document qui se cite). Le critère de Löb (les énoncés auto-référentiels sont *constructibles* en arithmétique) montre que la self-référence est *banale* du point de vue logique — c'est une curiosité formelle, pas une structure organisatrice.

L'erreur classique de la strate 7 (celle que la boussole D3 met en garde contre) est de prendre la self-référence *cheap* pour la performativité. Or la self-référence *seule* n'agit sur rien : un système qui se décrit lui-même, mais dont la description n'a aucun pouvoir causal sur le système, est *autiste*, pas *performant*.

### 4.2 La précision du choix

La performativité — ce que la strate 7 cherche réellement à capturer — n'est **pas la self-référence** ; c'est la **précision du choix de la coordonnée libre**. Un système qui se contente d'auto-référencer *sans choisir* est *cheap*. Un système qui, à chaque pas de temps, *choisit* parmi `C_t = |Ext(G_t)|` extensions non équivalentes, et dont le choix *agit causalement* sur le système (`P(R) > 0`) et *persiste* (institutionnalisation), est *performant*.

Le verbe lui-même est une **variable libre** : *se dévoiler* / *se résumer* / *exploser* (cf. D3, [`strate7-boussole-myth.md`](strate7-boussole-myth.md) §« Les trois verbes comme variables libres ») sont trois choix **non-canoniques** au sens où chacun engage une posture différente (réalisme caché, constructivisme de compression, générativité incontrôlée). *Choisir particulièrement bien* ses variables libres, c'est choisir le verbe qui **ouvre** la plus grande `ΔA_t` tout en gardant `P(R)` élevé — c'est une opération **d'équilibration** entre l'expansion et la causalité.

### 4.3 Notre propre autoperformance

La strate 7 a un statut **autoperformatif** dans la série ICT : nous *sommes* en train de poser un cadrage (le présent document) qui **étend** l'espace des représentations de la série (en posant le 6-uplet comme grille falsifiable) et qui **engage** la suite (les bancs D2 sont déjà construits, le présent D1 les *cadrent*). En ce sens, le cadrage D1 est lui-même une instance du phénomène qu'il décrit : nous avons posé un coup ontologique (le 6-uplet), et la qualité de ce coup se mesurera à la **précision avec laquelle il ouvre des actions nouvelles** (les bancs D2 le rendent-il dicible ?) tout en **gardant son pouvoir causal** (les non-résultats seront-ils dicibles aussi ?).

Cette autoperformance n'est **pas** une circulaire vicieuse ; c'est **une composante assumée** du cadrage. Si les proxys 3.1-3.6 sont *mal* choisis, ils ne serviront à rien — mais c'est *précisément* la leçon de la strate 7 : la qualité du choix des variables libres est composante de la performativité. Le présent cadrage est *à la merci* de cette critique, et c'est *honnête*.

## 5. Ancrage dans la série ICT

### 5.1 Lien D2 (bancs ICT-26 → ICT-30)

Le cadrage D1 est *la grille* ; les bancs D2 (cf. [#7746](https://github.com/jsboige/CoursIA/issues/7746) MERGED, ICT-26 → ICT-30) sont *les coupes sur la grille*. Les 5 bancs sont :

- **ICT-26 — Coordination à vocabulaire fixe.** Baseline sans coup ontologique : O_t = 0, ΔA_t = 0, C_t = 1.
- **ICT-27 — Invention de symboles.** O_t > 0, ΔA_t > 0, C_t > 1 : mesure de l'extension.
- **ICT-28 — Adoption collective.** Seuil ρ_c où P(R) ≫ 0 : la convention devient causative.
- **ICT-29 — Inoculation d'un cadrage.** Institutionnalisation d'un cadrage chez une minorité → transmission → survie post-instigateur → réinterprétation rétroactive.
- **ICT-30 — Inhibition de l'innovation.** O_t = 0 forcé : pont avec ICT-12d (jambe C2, *animat inhibé* de Laborit) — quand l'extension de vocabulaire est interdite, le système se rigidifie.

D1 *cadrent* D2 en explicitant le 6-uplet ; D2 *opérationnalise* D1 en mesurant le 6-uplet sur des substrats.

### 5.2 Lien D3 (boussole, PR #9579 MERGED c.1243)

Le cadrage D3 ([#7747](https://github.com/jsboige/CoursIA/issues/7747), [`strate7-boussole-myth.md`](strate7-boussole-myth.md)) pose la **boussole narrative** de la strate 7 : deux cascades d'investissement performatif (la mise-en-abyme descriptive vs la chaîne d'englobement performatif), le non-recollement entre elles, les trois verbes comme variables libres, le *caveat crackpot* auto-enregistré. D3 *raconte* la strate 7 ; D1 la *formalise*. Le présent document n'**entre pas en concurrence** avec D3 — les deux sont **complémentaires** : D3 fixe *où on refuse d'aller* (la cascade 2 n'est pas réductible à la cascade 1), D1 fixe *comment on y va* (le 6-uplet comme grille falsifiable).

### 5.3 Lien tresse (B4 non-recollement, PR #9551 MERGED c.1239)

Le cadrage D1 **hérite** du non-recollement de la tresse (cf. [`tresse-cartographie.md`](tresse-cartographie.md) §« B4 non-recollement »). La strate 7 a deux cascades non réconciliables (D3) et quatre opérations distinctes (Grothendieck, Schmidhuber, Thom, Friston) qui *ne se réduisent pas* les unes aux autres. Le 6-uplet de D1 est *la forme* qui assume ce non-recollement : aucun proxy n'agrège les 6, et aucun proxy n'est *réductible* à un autre.

## 6. Ce que ce document n'est pas

Pour éviter la confusion entre grille et verdict, ce document assume explicitement ce qu'il n'est **pas** :

- **Ce n'est pas un test de la strate 7.** Le 6-uplet est *une grille de falsifiabilité* ; les bancs (D2) sont *déjà construits* et *opérationnalisent* la grille. Le présent document ne propose pas de test direct, et n'ajoute aucun banc. Si les bancs D2 livrent des verdicts honnêtes par proxy, ils les livreront *en utilisant* le 6-uplet — sans que ce document *prétende* les avoir livrés lui-même.
- **Ce n'est pas une unification des strates 1 → 6.** Le reframe de §0 *construit* sur les strates précédentes, mais ne les réduit pas. La dissolution des scalaires ([`dissolution-scalaires.md`](dissolution-scalaires.md)) reste vraie ; le 6-uplet en *absorbe* la leçon (pas de scalaire unique) sans la *révoquer*.
- **Ce n'est pas une thèse sur la conscience.** Le 6-uplet est un *objet formel* (des grandeurs mesurables sur des systèmes en général) ; il n'est **pas** une thèse sur le sujet, l'esprit, ou la conscience. La posture est la même que dans D3 : on décrit la *forme*, pas le *contenu* subjectif.
- **Ce n'est pas une PR de code ou de notebook.** C'est un **cadrage formel** (mandat user explicite, [#7745](https://github.com/jsboige/CoursIA/issues/7745) : *« Document de cadrage — pas un notebook expérimental »*). Aucun notebook n'est créé ou modifié par ce document. Les bancs D2 sont déjà MERGED.
- **Ce n'est pas un matériau strate 6/7 sensible.** Cf. [#8182](https://github.com/jsboige/CoursIA/issues/8182) jalon 3 — la frontière privé → public est stricte. Ce cadrage reste au niveau de la *forme* (variables libres, 6 proxys, mécanisme M) ; il ne traite pas des *cas* (entreprises, nations, etc.) au-delà de l'exemple paradigmatique et pédagogique de la *personne morale* en §1.4.

## 7. Statut hiérarchique (mesuré / construit / nommé sans démonstration)

| Niveau | Élément |
|---|---|
| **Mesuré** (par les bancs D2, [#7746](https://github.com/jsboige/CoursIA/issues/7746) MERGED) | Émergence de conventions, croissance de vocabulaire (ICT-27), seuil d'adoption ρ_c (ICT-28), persistance post-instigateur (ICT-29), dette d'inhibition (ICT-30) — chaque proxy partiellement mesuré sur son banc dédié |
| **Construit** (formalisé dans le présent cadrage) | Le 6-uplet (O_t, ΔA_t, C_t, P(R), institutionnalisation, I(R)), le jeu évolutif G_t, le mécanisme M, la distinction coup interne / coup ontologique, l'ancrage *unawareness*, l'ancrage do-calculus, le reframe *le scalaire avait la mauvaise forme* |
| **Nommé sans démonstration** (grade C, posé pour cadrage) | L'idée que *la qualité du choix des variables libres est composante de la performativité* (§4), l'autoperformance du cadrage lui-même (§4.3), l'idée que la strate 7 admet une réponse catégorielle là où la réponse scalaire est falsifiée (§0) |

Le passage « nommé sans démonstration » au rang « construit » ou « mesuré » est un **livrable futur** (cadrage D3 + bancs D2 verdicts par proxy + ré-agrégation éventuelle du 6-uplet), pas un claim actuel. Si la strate 7 tient ce passage, ce sera une PR grade B à célébrer ; sinon, les éléments resteront au statut « nommé sans démonstration », et le cadrage restera cadrage.

## Voir aussi

- **Epic umbrella** : [#4588](https://github.com/jsboige/CoursIA/issues/4588) (ICT strate 5+) — toute la série ICT se rapporte à cet Epic.
- **Issue source** : [#7745](https://github.com/jsboige/CoursIA/issues/7745) — cadrage strate 7 (D1) — free coordinates de 2e ordre, jeu évolutif, 6 proxys. Le présent document en est la livraison.
- **Jambe D2 (bancs d'essai)** : [#7746](https://github.com/jsboige/CoursIA/issues/7746) — MERGED. 5 bancs ICT-26 → ICT-30, qui *opérationnalisent* le 6-uplet de D1.
- **Jambe D3 (boussole narrative)** : [#7747](https://github.com/jsboige/CoursIA/issues/7747), [`strate7-boussole-myth.md`](strate7-boussole-myth.md) — MERGED PR [#9579](https://github.com/jsboige/CoursIA/pull/9579) c.1243. Boussole et mythe fondateur, *complément narratif* de D1 (D3 raconte, D1 formalise).
- **Cadrage N2 (trajectoires de représentations)** : [#7396](https://github.com/jsboige/CoursIA/issues/7396), [`cadrage-trajectoires-representations.md`](cadrage-trajectoires-representations.md) — PR [#8541](https://github.com/jsboige/CoursIA/pull/8541) MERGED. Pivot états → représentations, antécédent direct de D1 (les *représentations* sont le terrain sur lequel les *free coordinates* opèrent).
- **Cartographie tresse (B4 non-recollement)** : [#7738](https://github.com/jsboige/CoursIA/issues/7738), [`tresse-cartographie.md`](tresse-cartographie.md) — PR [#9551](https://github.com/jsboige/CoursIA/pull/9551) MERGED c.1239. Le 6-uplet de D1 *hérite* du non-recollement entre les 4 opérations (Grothendieck / Schmidhuber / Thom / Friston).
- **Dissolution des scalaires (5e fil)** : [#7736](https://github.com/jsboige/CoursIA/issues/7736), [`dissolution-scalaires.md`](dissolution-scalaires.md) — PR [#9547](https://github.com/jsboige/CoursIA/pull/9547) MERGED c.1238. Le reframe de D1 §0 *construit* explicitement sur cette dissolution : *le scalaire avait la mauvaise forme*.
- **Problème de la représentation interne (4e fil)** : [#7735](https://github.com/jsboige/CoursIA/issues/7735), [`genealogy-representation-interne.md`](genealogy-representation-interne.md) — PR [#8061](https://github.com/jsboige/CoursIA/pull/8061) MERGED. La généalogie de `p̂` (ICT-10 → ICT-17) qui motive l'idée que la *représentation* est l'objet qu'il faut étendre, pas l'état.
- **Matrice de dissociations** : [#7734](https://github.com/jsboige/CoursIA/issues/7734), [`dissociations-matrix.md`](dissociations-matrix.md) — la matrice 4-objets `(s, q, π, W)` que le présent D1 *contourne* volontairement (les free coordinates opèrent *sur* `L`, pas dans l'espace `(s, q, π, W)`) — choix méthodologique explicite, pas un oubli.
- **Matrice inversée (chantier 3/3)** : [#9533](https://github.com/jsboige/CoursIA/issues/9533), PRs [#9546](https://github.com/jsboige/CoursIA/pull/9546) [#9572](https://github.com/jsboige/CoursIA/pull/9572) [#9588](https://github.com/jsboige/CoursIA/pull/9588) — la matrice inversée en *générateur d'expériences* (cadrage 4-cases, case 3 chiffrée, case 4 chiffrée) ; la strate 7 n'est **pas** dans la matrice inversée (la matrice 4-objets est strate ≤ 5), mais le geste de *générer des expériences* est commun à l'esprit de D1.
- **Jambe C3 (morphogenèse rhétorique)** : [#7742](https://github.com/jsboige/CoursIA/issues/7742) — *gelée* tant que corpus public non branché. Mentionnée en §2.4 comme point de rencontre.
- **Jambe C4 (grammaire de propagation)** : [#7743](https://github.com/jsboige/CoursIA/issues/7743) — la jauge `π, W, causalité` du seuil de bascule représentation → transformation du tout. Mentionnée en §2.4.
- **Veille TOE ↔ conscience (jalon 2/3)** : [#8182](https://github.com/jsboige/CoursIA/issues/8182) — l'iceberg de Jaimungal et le carrefour Schreiber ; la strate 7 ne s'y aventure pas publiquement.
- **Discipline grade C** : [`docs/grothendieckian-lens.md`](../grothendieckian-lens.md) — l'invariant d'ICT n'est pas dans le monde mais dans la *méthode*, et tout cadrage grade C est posé comme témoin de lecture, pas comme claim.

— *CoursIA-2 — c.1246 (po-2025) — 2026-08-06*
