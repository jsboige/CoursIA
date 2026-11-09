## Note de conception — banc unique de la strate 7 ICT (capstone) — phase 1 (note avant tout carnet)

Lane `myia-po-2027:CoursIA-2` · dispatch ai-01 31/10 (`c2743-dispatch-23778`) · **exception nommée** au gel de création de carnets du 30/10 (accord du mainteneur 2026-10-31, couvrant ce banc + le capstone strate 6 #23777).

Cette note est la **phase 1** : elle fixe l'architecture du banc, avant tout carnet. Le carnet (phase 2) ne s'écrit **qu'après** lecture de cette note par le coordinateur, sur la note postée en commentaire de #23778.

### Plateau mesure (origin/main = `e89519fe26fd`)

- **ICT-46** — premier barreau de la strate 7 (#18052) : le banc exécutable `MyIA.AI.Notebooks/IIT/ICT-Series/ict/free_coordinates.py`, 9 sections + 3 exercices, tournant les **six proxys** sur un mini-jeu évolutif `G_t` à coups ontologiques. Sur `main`.
- **Six proxys** du banc (définis dans `free_coordinates.py`, testés dans `tests/test_free_coordinates.py`) : `O_t = |L_{t+1}\L_t|` (`expansion_ontology`), `ΔA_t = |A_{t+1}\A_t|` (`political_opening`), `C_t = |AdmExt(G_t)|` (`non_canonicity`), `P(R) = D(Pr(traj|do R)‖Pr(traj|do ¬R))` en bits (`performative_power`, marginalisation par équivalence optionnelle), **institutionnalisation** (`institutionalization`), `I(R) = undo_cost/pose_cost` (`irreversibility_debt`) — plus la jambe Aaronson `FixedSpacePredictor`.
- **Sondage firsthand des organes candidats** (lectures `file:line` ci-dessous) — **point structurel qui structure toute la note** : sur les six séries candidates, **seules trois** portent un **organe importable** dans leur série :

  | Série | Organe importable | Preuve |
  |---|---|---|
  | Probas / Causal-Bridges | `causal_organs.py`, `dowhy_organs.py` | `dowhy_organs.py:90` (`contrefactuel_individuel`), `:71` (`construire_scm`) ; `causal_organs.py:262` (`panel_did_two_by_two`) |
  | SymbolicAI / SmartContracts | `sc2b_experience.py` | `sc2b_experience.py:212` (`deployer`), `:181` (`envoyer`), `:523` (`mecanique`) |
  | Search | `search_helpers.py` | `search_helpers.py:46` (`draw_csp_graph`), `:19` (`SearchTreeNode`) |

  Les trois autres séries candidates (SemanticWeb SW-14/SW-15, GameTheory/SocialChoice 05/10) n'ont **aucun** organe importable : leurs fonctions vivent **inline dans les cellules de solution** (SW-14 : `rdflib.Graph.add` + `owlrl.DeductiveClosure` ; SW-15 : `ra`/`ca`/`grounded` ; SocialChoice 10 : `regle(R,k,m)` + `detecte_violation` — 14 defs, aucune exportée). C'est ce qui impose la forme à deux volets du § « mécanismes retenus » ci-dessous.
- Aucun claim d'autre lane ne bloque `docs/ict/` pour cette note (`check_lane_claim.py 23778 --lane myia-po-2027:CoursIA-2` : `blocking_lanes: []`, `my_active_claim: true`).

### Objet du banc et son rapport à ICT-46

**ICT-46 reste le premier barreau ; le banc unique en devient la tête.** Réponse au point de la phase 1 (« Le banc devient-il la tête du palier, ICT-46 en restant le premier barreau ? ») : **oui**.

- **ICT-46 (premier barreau)** = le banc **en isolement** : ses six proxys mesurés sur ses **propres** mécanismes jouets (quorum vs authority, la « personne morale », le « jargon privé »). Il pose l'organe et la grille, sans rien emprunter à d'autres séries.
- **Le banc unique (tête du palier)** = les **mêmes** six proxys employés comme **lentille** sur les mécanismes qui changent l'espace des actions **partout dans le dépôt** — chacun **appelé par son organe natif, dans sa série**. Le banc ne réimplémente rien : il passe chaque mécanisme à travers la grille d'ICT-46 et le **classe** (latent / nouveau / décoratif).

C'est l'escalier : le premier barreau établit la grille ; la tête (le capstone) est l'unification — la strate 7 lue **en travers** de tout le dépôt. Étendre `ict/free_coordinates.py` est dans le périmètre ; réimplémenter un mécanisme d'une autre série ne l'est pas (organe natif d'abord).

### Les mécanismes retenus — deux volets (c'est le point structurel du § plateau)

Le banc ne peut **invoquer l'organe natif** que si celui-ci est **importable dans sa série**. Le sondage montre que c'est vrai pour 3 séries seulement. Le banc a donc **deux volets**, et l'organisation en deux tableaux est la traduction directe de ce fait mesuré :

**Volet A — appelés par leur organe natif importable (3 mécanismes) :**

| Mécanisme | Série | Organe natif (importable) | Interface invoquée | Contrôle attendu* |
|---|---|---|---|---|
| Intervention contrefactuelle `do(X=v)` | Probas / Causal-Bridges | `dowhy_organs.py` | `construire_scm(generer_donnees(n))` puis `contrefactuel_individuel(scm, ligne, "T", v)` | **latent** |
| Mécanisme institutionnel persistant (on-chain) | SymbolicAI / SmartContracts | `sc2b_experience.py` | `deployer(w3, a)` → `envoyer(...)` (`soumettre`/`voter`/`cloturer` du contrat `Deliberation`) | **nouveau** |
| Espace de contraintes qui s'étend | Search | `search_helpers.py` | `draw_csp_graph(variables, domains, constraints)` / `SearchTreeNode` | **nouveau** |

**Volet B — copie pédagogique déclarée, l'organe natif étant inline-only (3 mécanismes) :**

| Mécanisme | Série | Organe natif (inline, non importable) | Copie minimale déclarée | Extraction à demander (Q3) | Contrôle attendu* |
|---|---|---|---|---|---|
| Coup ontologique (ajout d'axiome) | SemanticWeb / SW-14 | `rdflib.Graph.add` + `owlrl.DeductiveClosure(OWLRL_Semantics).expand` (cells `8c6563e4`, L512) | `g.add((s, RDFS.subClassOf, p))` + `owlrl` expand | oui — module `sw14` à exposer | **nouveau** |
| Coup argumentatif (argument + attaque) | SemanticWeb / SW-15 | `ra`/`ca`/`project_af`/`grounded` (L278–L765, cell-scoped) | RA/CA nodes + `grounded` AF de Dung | oui — module `sw15` à exposer | **latent** |
| Agrégation + manipulation stratégique | GameTheory / SocialChoice 10 | `regle(R,k,m)` + `detecte_violation` (L305, L527, inline) | `regle(R,k,m)` + `detecte_violation` | oui — module de choix social à exposer | **décoratif** |

\* « contrôle attendu » = l'hypothèse de classement que le banc va **mesurer** en phase 2. La note *construit* le protocole ; elle ne *prétend* pas les résultats (cadrage grade C de la strate 7 — voir `docs/ict/strate7-cadres-libres.md`).

Chaque ligne du **volet B** est une **copie pédagogique déclarée** au sens de la règle `organ-first-implementation` (section « Porte de sortie ») : une phrase dans le body de la PR le déclare, avec le motif (« l'organe natif est inline-only dans sa série »). Et — la conséquence directe de la règle — une copie déclarée qui **dure** (plusieurs carnets consommateurs) **devient une extraction à demander à la série source** (question 3). Le tableau ci-dessus pose donc les **trois extractions** (`sw14`, `sw15`, module de choix social) comme le **résiduel explicite** de ce capstone, à ouvrir en issues sur les séries concernées — pas à faire dans ce banc.

### Le protocole des trois contrôles

Pour chaque mécanisme `M` passé par le banc, on mesure les six proxys avant/après et on **classe** le coup :

- **nouveau** — l'espace change réellement : `O_t > 0` **et** `ΔA_t > 0` **et** `institutionalization > 0` (le coup ouvre de vraies actions et survit au retrait de son instigateur). C'est le coup ontologique au sens plein.
- **latent** — la coordonnée **existait déjà** dans l'espace : `O_t = 0`, `ΔA_t = 0`, `C_t` inchangé, mais `P(R) > 0` — le mécanisme ne fait que **révéler / activer** une coordonnée préexistante (ex. `do(T=v)` sur une variable `T` déjà dans le SCM : elle gagne de la saillance causale, rien n'est ajouté à l'espace).
- **décoratif** — un renommage / un habillage qui **ne change rien** aux proxys : sous la **marginalisation par équivalence** de `performative_power` (copie → original), `P(R) → 0`, et `C_t = 1` (canonique — toutes les extensions ouvrent les mêmes actions, il n'y a rien à choisir).

**Le témoin décoratif est le témoin négatif obligatoire, et il doit pouvoir rougir.** Le verdict « décoratif » est une assertion **falsifiable** :

```
P(R) marginalisée < ε   et   C_t == 1   et   O_t == 0   et   ΔA_t == 0
```

Le témoin **rougit** (le coup n'est **pas** décoratif) si **l'une** des quatre est violée :
- `P(R)` ne tombe **pas** à 0 sous l'équivalence → l'« habillage » change en réalité la trajectoire (c'est un coup qui agit, pas du vernis) ;
- `C_t > 1` → le « renommage » n'est pas un vrai renommage (les extensions ne sont pas équivalentes) ;
- `O_t > 0` ou `ΔA_t > 0` → il y a un ajout réel (ce n'est pas un habillage).

**SocialChoice 10 est le siège naturel de ce témoin** : on y distingue un *relabeling* des alternatives (décoratif — s'annule sous l'équivalence, `P(R)→0`, `C_t=1`) d'une *manipulation stratégique* réelle (`detecte_violation` ≠ None → `P(R)>0` → **le témoin rougit** et le « décoratif » est reclassé). C'est exactement le cas où le banc prouve qu'il sait dire « ce n'est pas décoratif ». C'est aussi le rôle du témoin négatif que `composition_report` joue déjà dans ICT-46 (des ouvertures disjointes doivent commuter sur les 4 axes — une non-commutativité mesurée là serait un **défaut de l'organe**, pas un résultat) ; le banc le généralise.

### Position dans la carte et le point à trancher (ordre des paliers 20-22)

La carte du 2026-10-11 place : **palier 20 = strate 7** (ce banc), **palier 21 = strate 6** (argumentation), **palier 22 = synthèse cross-substrat**. L'ordre numérique actuel met la strate 7 **avant** la strate 6.

**Position de cette note : l'ordre des paliers DOIT suivre celui des strates (6 puis 7), et la synthèse reste terminale.**

Raisonnement (règle `notebook-accretion-numbering` — un palier est l'étape suivante d'un **escalier pédagogique**) :
1. Un apprenant intègre d'abord l'agent **dans un jeu fixé** (strate 6 : argumenter / raisonner **à l'intérieur** d'un espace d'actions donné) **avant** l'agent **qui transforme le jeu** (strate 7 : les coups ontologiques qui changent l'espace). L'escalier impose donc 6 → 7.
2. La **synthèse cross-substrat** est l'étape qui **regarde en arrière** sur tous les substrats : elle doit rester **terminale** (en dernier).

⇒ On relit la carte en **inversant** le 20/21 : **palier 20 = strate 6 (argumentation)**, **palier 21 = strate 7 (banc)**, **palier 22 = synthèse** (terminale, inchangée).

**Distinction importante (pour ne pas contredire #20298)** : la règle « les **derniers numéros** d'ICT sont pour la strate 7 » (fixée le 31/10 sur #20298) porte sur la **numérotation de série** (quels carnets portent un numéro ICT élevé — ICT-46, et ce capstone), pas sur l'**ordre pédagogique des paliers**. Les deux axes sont orthogonaux : un carnet peut porter un numéro de série élevé tout en occupant, dans l'escalier, le palier qui correspond à sa **position pédagogique** (la strate 7, après la strate 6).

**Ce point est partagé avec la note sœur #23777 (strate 6, lane po-2028)** : les deux notes doivent trancher **de façon cohérente**. Cette note pose la position « 6 avant 7, synthèse terminale » ; si la note #23777 la confirme, l'inversion 20/21 est tranchée pour la série.

### Ré-exécution

Aucune. Cette note est **markdown seul** (un fichier `docs/ict/` neuf) : aucune cellule source de notebook n'est touchée, aucune ré-exécution n'est due (règle C.2).

### Mouvement (phase 2, différé)

Le carnet de phase 2, écrit **après** lecture de cette note :
1. **étend** `ict/free_coordinates.py` (dans le périmètre) d'un point d'entrée qui **invoque** un organe natif d'une autre série (volet A) ou sa copie minimale déclarée (volet B) et passe son effet aux six proxys ;
2. **n'en réimplémente aucun** — le body de la PR répond aux 5 questions d'`organ-first-implementation` (Q1-Q2 satisfaites par construction pour le volet A ; Q3 = les trois extractions posées en résiduel pour le volet B) ;
3. porte **3 exercices** et **aucune erreur volontaire** (C.1), est **exécuté de bout en bout** et committé **avec ses sorties** (C.2) ;
4. **classe** chaque mécanisme (latent / nouveau / décoratif) **en mesurant** les six proxys — le verdict par mécanisme est **mesuré en phase 2**, pas affirmé ici.

### Questions ouvertes

1. **Ordre des paliers 20/21** : position posée ci-dessus = **6 avant 7, synthèse terminale** (inversion du 20/21 de la carte). À **confirmer** par le coordinateur, de façon cohérente avec la note sœur #23777.
2. **Jeu final de mécanismes** : six retenus (3 volet A importable + 3 volet B copie déclarée). À confirmer, ou à restreindre (p. ex. 3+2) si l'on veut tenir le carnet court.
3. **Trois extractions** (`sw14`, `sw15`, module de choix social) : à ouvrir en **issues sur les séries sources** (pas dans ce banc) — à valider comme le résiduel naturel du capstone.
