# Pli 5, Grain C — la structure causale et le pont Gorard

Issue #23093 (EPIC Origami #19742). Organes : `causal_structure.py` (la mesure)
et `causal_structure_results.json` (la sortie intégrale, committée verbatim).
Ce document confronte la mesure aux articles de 2020 de Gorard, **sur leurs
copies archivées au gisement** — aucune affirmation n'est attribuée à un texte
non déposé (issue soeur #19741, règle bibliographie-hygiene).

## Sources archivées

| Texte | Copie archivée (gisement) |
|---|---|
| Gorard 2020, *Some Relativistic and Gravitational Properties of the Wolfram Model* (arXiv 2004.14810) | `G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\Wolfram Physics Project\2020 - Gorard - Some Relativistic and Gravitational Properties of the Wolfram Model (arXiv 2004.14810).pdf` |
| Gorard 2020, *Algorithmic Causal Sets and the Wolfram Model* (arXiv 2011.12174) | `G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\Wolfram Physics Project\2020 - Gorard - Algorithmic Causal Sets and the Wolfram Model (arXiv 2011.12174).pdf` |

Identités vérifiées sur les premières pages des copies (titre, auteur Jonathan
Gorard). Note honnête : les deux premières pages portent la date de révision
« October 19, 2021 » — les fichiers sont rangés au gisement sous l'année de
soumission 2020 (celle des identifiants arXiv) ; la révision est postérieure.

## Ce que dit la Définition 4, et ce que le grain lui confronte

Verbatim (2004.14810, section 2.1 « Basic Formalism and Causal Graphs », p. 6) :

> « A "causal graph", denoted G_causal, is a directed, acyclic graph in which
> every vertex corresponds to an application of an update rule (i.e. an
> "event"), and in which the edge A→B exists if and only if the update rule
> designated by event B was only applicable as a result of the outcome of the
> update rule designated by event A. Pragmatically speaking, this implies that
> the causal relation A→B exists if and only if the input for event B has a
> non-trivial overlap with the output of event A. »

Le témoin (règle de l'annonce `{{x,y},{x,z}} -> {{x,z},{x,w},{y,w},{z,w}}`,
état initial étoile, rejeu déterministe de 1500 événements, setreplace-py 0.2.0
— SOTA-OK au Grain A, PR #26671) confronte chaque élément :

| Élément de la définition | Contrôle (déclaré avant mesure) | Mesure |
|---|---|---|
| « directed, acyclic » | CC1 : toute arête va d'un événement antérieur vers un postérieur | **vrai** — 2602/2602 arètes `a < b`, numérotation 1-based mesurée |
| « every vertex corresponds to an application of an update rule » | CC2 : bijection sommets ↔ événements | **vrai** — 1500 sommets = 1500 événements, intervalle contigu |
| « edge A→B iff input of B overlaps output of A » | CC3a : la relation native = la relation jeton (créateur de chaque jeton d'entrée) | **vrai** — identité exacte 2602 = 2602 |
| (le même, lu depuis les états) | CC3b : reconstruire la relation depuis les seuls diffs d'états | **diverge** — et la cause est mesurée ci-dessous |

## La découverte du grain : le diff d'états ne détermine pas l'événement

La relation par contenus (suivre, pendant le rejeu, « createur le plus recent
du contenu consommé » — la lecture naturelle de la phrase pragmatique au
niveau des états) rend 2666 arètes : 291 arètes natives manquantes, 355
supplémentaires. La dissection (événements 9 à 13 du témoin, grand livre
`tokens()` du paquet) donne la cause exacte :

- l'événement 10 consomme réellement `[6,8]+[6,10]` (x=6) et re-crée `[6,10]` ;
- l'état précédent contient aussi `[6,8]+[8,10]` (x=8), qui re-crée `[8,10]` ;
- **les deux applications produisent le même état résultant** : le membre
  droit re-crée le membre gauche `{x,z}`, la destruction est invisible dans le
  diff, et le diff (1 arête consommée, 3 créées) ne tranche pas entre les deux
  liaisons.

Mesure (CC3b) :

- **459 événements ambigus sur 1500** (au moins deux liaisons valides
  produisent l'état observé) ;
- le rejeu par diff choisit la mauvaise liaison **223 fois** (il prend la
  première trouvée) ;
- l'erreur d'attribution **se propage en aval** : un événement non ambigu qui
  consomme un contenu mal attribué hérite de l'erreur — d'où les 291/355 ;
- **avec l'ambiguïté tranchée par le grand livre de jetons, la relation par
  contenus coïncide EXACTEMENT avec la relation native** (2602 = 2602).

Lecture pour le pli : la phrase pragmatique de la Définition 4 est vraie **au
niveau des objets** (les jetons, chacun créé une fois par un événement, détruit
une fois par un autre) ; les **états** en sont une projection qui perd
l'identité des objets quand la règle re-crée son membre gauche. Le contrôle C1
du Grain B (rejeu sémantique 1500/1500) reste vrai sous toute résolution —
les deux liaisons produisent le même état — c'est précisément pourquoi
l'ambiguïté est invisible au niveau des états.

## La structure causale émergente du témoin (descriptif)

Sur le DAG natif (1500 sommets, 2602 arètes, mur 7,8 s) :

- **signature de la règle** : degré entrant ≤ 2 (chaque événement consomme
  exactement 2 jetons à créateur), degré sortant ≤ 4 (chaque événement crée
  4 jetons), degré sortant moyen 1,735 ;
- **2 sources** (premiers événements sans ancêtre causal), **681 puits**
  (événements dont aucun des jetons créés n'est consommé dans l'horizon du
  run — degré sortant 0, mesuré sur les événements, pas sur les jetons) ;
- **profondeur maximale 11** (12 niveaux) ; largeurs par niveau :
  `2, 2, 4, 8, 14, 24, 48, 84, 162, 292, 532, 328` ;
- la largeur **double à peu près à chaque niveau de profondeur** (4→8→14~16→24~32→48~64→84~128→162~256→292~512) jusqu'au niveau 10, puis 328 au
  niveau 11 — la fin tronquée du run. C'est l'ombre singleway de la
  prolifération mesurée au Grain B (croissance NON_REDUCTIBLE, λ > 26) : même
  sur le chemin déterministe unique, la structure causale s'élargit
  géométriquement avec la profondeur.

## Le pont singleway / multiway, et ce qu'il ne faut pas conclure

Verbatim (2011.12174, p. 91, discussion des figures 71-72) :

> « [...] the multiway causal graph (i.e. the directed acyclic graph showing
> causal relationships between all events in the multiway system, including
> those on different branches of evolution history) into several "singleway"
> causal graphs (i.e. causal networks associated with single paths through the
> multiway system) »

Le graphe mesuré ici est **singleway** : le chemin déterministe de setreplace.
Le Grain B a mesuré la prolifération multiway. L'invariance causale, elle, est
définie sur la famille des graphes causaux d'un même système :

Verbatim (2004.14810, résumé, p. 1) :

> « causal invariance (namely, the requirement that all causal graphs be
> isomorphic, irrespective of the choice of hypergraph updating order) »

et sa condition nécessaire non suffisante (2011.12174, p. 22) :

> « global confluence is a necessary (though not sufficient) condition for
> causal invariance »

**Un seul chemin ne suffit pas à trancher l'invariance causale** : il faudrait
comparer les graphes causaux de chemins distincts. Le grain ne le claim pas.
Il apporte la brique en dessous : la relation causale d'un chemin est la
dérivativité par objets (mesuré ci-dessus), et la prolifération multiway du
Grain B montre que l'exploration ne s'effondre pas en un chemin unique —
condition préalable à toute discussion de confluence au sens de la citation.
À titre de contraste, la figure 20 de 2011.12174 (p. 25) montre le graphe
causal multiway d'une règle **confluente** `{{x,y},{z,y}} -> {{x,w},{y,w},{z,w}}`
— une autre règle que celle de l'annonce, choisie par Gorard précisément pour
son honorabilité ; la règle de l'annonce, elle, n'est pas celle-là, et le Grain
B mesure sa branching.

## Matrice du jalon 2 (#19766) utilisée par ce grain

- **[DISTILL-Pli5-C]** « le temps = application progressive d'une règle » —
  le graphe causal EST l'ordre de dérivation des applications successives ;
  sa profondeur (11 niveaux pour 1500 événements) est le temps causal du
  témoin, distinct du temps-calcul (mur 7,8 s).
- **[DISTILL-Pli5-A]** « l'espace = collection de relations abstraites » — les
  jetons sont les relations-objets : créées une fois, détruites une fois,
  jamais dupliquées (mesuré : 0 état avec contenu dupliqué) — et leur identité
  est exactement ce que les états seuls ne conservent pas.

## Non-livré ici (le pli continue)

- **Hôte du carnet** : argument au design-gate (Complexity 08 réservée par
  ai-01 — non prise) ; candidats à l'argument : branche Lean Conway ou
  sous-série neuve avec argument d'accrétion.
- **Invariance causale** : hors de portée d'un seul chemin (ci-dessus) ;
  aucun claim.

See #23093 · See #19741 · See #19742
