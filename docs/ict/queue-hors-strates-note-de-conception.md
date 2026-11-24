> REFERENCE — vivante — dernière révision 2026-11-16

## Note de conception — queue « hors strates » de la série ICT (40a, 40b, 47, 47b, 48-Onset, 48-Wolfram, 49, 50) — phase 2

Lane `myia-po-2027:CoursIA-2` · dispatch ai-01 31/10 (`msg-20261031T172938`) · consigne du mainteneur 31/10.
Cette note donne à chacun des carnets « hors strates » une **destination**, et **clôt les trois options ouvertes** (47b, 40b, 48-Onset). C'est une **note de conception seule : aucun mouvement**. Les modules `ict/` consommés par ces carnets ne bougent pas. Le veto du 30/10 sur la création de carnets s'applique : on ne déplace que des carnets existants. Le mouvement (renommage de dossier / renumérotation) est **différé à la tranche suivante**, qui amendera cette note.

> **Amendement du 15/11/2026 — mouvement exécuté** ([#20298](https://github.com/jsboige/CoursIA/issues/20298), arbitrage ai-01 GO du 15/11, c.6889190719) : **ICT-49, ICT-50 et ICT-51 quittent la série ICT** et rejoignent la série **Complexity** sous les noms `Complexity-08c-MachinesDeGoedel` (ex-ICT-49), `Complexity-08-WolframRule30Aleatoire-Rule110Universelle` (ex-ICT-50) et `Complexity-08b-CombinateursSKI-TagDePost` (ex-ICT-51) — noms actuels conservés, seul le préfixe change ; ordre pédagogique 08 → 08b → 08c. **Sont supersédées par cet amendement** : la ligne « **48-Wolfram + 50 → palier 13** » (ICT-50 ne rejoint pas le palier 13 d'ICT — le fil Wolfram continue dans Complexity) et le « **maintien argumenté : ICT-49** » (il ne reste pas dans ICT comme distillation externe ; l'argument d'autonomie qui fondait le maintien vaut désormais rattachement Complexity). ICT-51, hors périmètre de cette note, part avec eux par la même décision. Le reste de la note (40a/40b → 04, 47/47b → 15, 48-Onset → 16, accrétions de famille 36/42 → 15) demeure la référence pour la queue restante.

### Plateau mesure (origin/main = `e89519fe26fd`)

- le nombre de carnets au premier niveau d'`ICT-Series/` est porté par le catalogue (`COURSE_CATALOG`) ; 99 en comptant les sous-séries.
- Le README (`MyIA.AI.Notebooks/IIT/ICT-Series/README.md`, section `### Distillation externe — hors strates`, l.248) range **sept** carnets vivants sous « Distillation externe — hors strates » : **40a, 40b, 47, 47b, 48-WolframClasses-ThermoSignature, 49, 50**. Trois « marchepieds » déjà descendus y figurent aussi (ex-41 → PT-15b, ex-41b → PT-15c, ex-44/22c → 2.9g) — ils ne sont plus dans la série et ne sont pas objets de cette note.
- **ICT-48-Onset9B-Aggregate** n'apparaît **pas** dans cette section du README (le seul `ICT-48-` de la section est `48-WolframClasses`, l.261) ; il n'entre dans le périmètre que par la table de la carte du 11/10. Il est donc traité ici comme 8ᵉ carnet de la queue.
- La carte du 11/10 (commentaire `#20298#issuecomment-6546758063`) couvre déjà et laisse ouvertes :

  | Carnet | Destination dans la carte | État |
  |---|---|---|
  | ICT-48-WolframClasses | 13 / automate et flèche du temps | **couvert** (R) |
  | ICT-47 | 15 / axe douleur | **couvert** (M) |
  | ICT-47b | 15 / instrument douleur, **ou** redescente vers le training | **option ouverte** |
  | ICT-40b | 04 / substrat analogique, **ou** palier distinct | **option ouverte** |
  | ICT-48-Onset9B | 16 / onset, **ou** organe training | **option ouverte** |
  | ICT-49 | — | absent (ajouté 10/24, #22081) |
  | ICT-50 | — | absent (ajouté 10/24, #22214) |
  | ICT-36b/c/d | — | absents (accrétions famille 36, palier 15 par construction) |
  | ICT-42c/d/e/f | — | absents (accrétions famille 42, palier 15 par construction) |

  ICT-40a n'apparaît **pas** dans cette table : sa destination est décidée par cette note (ci-dessous).

**Règle pour la suite** (carte du 11/10) : un carnet ICT nouveau ou déplacé ne prend pas le numéro qui suit le maximum ; il rejoint le palier qu'il sert — les derniers numéros sont réservés à la strate 7. Seul ICT-46 (coordonnées libres) relève de la strate 7.

### Argument pédagogique (règle notebook-accretion-numbering)

Le défaut que cette note corrige : la fin de série est devenue une **accumulation** de carnets ajoutés « à la suite », que le README classe lui-même « hors strates ». Un carnet rangé au palier qu'il **sert** (et non au numéro qui suit le maximum) restaure l'argument d'accrétion : chaque carnet est l'étape suivante d'un escalier pédagogique identifiable, pas un appendice.

**Principe directeur appliqué à toute la queue : chaque paire sibling s'accrète au palier de sa tête, selon la numérotation déjà posée par la carte du 11/10.** C'est le même geste que la carte a déjà fait pour les têtes (47 → 15, 48-Wolfram → 13) ; la note le prolonge aux membres de la paire, sans inventer de palier :

- **40a + 40b → palier 04** (« substrat & instruments ») : paire 40x. 40b y est déjà posé par la carte (« 04 / substrat analogique ») ; 40a (triangulation causale SAE × J-Lens × F-Lens) en est l'instrument frère — les séparer, c'est l'anti-pattern que la note refuse ailleurs.
- **47 + 47b → palier 15** (« axe douleur ») : 47 est tête (M) ; 47b est son contrôle d'instrument (même corpus, seul le nombre de bits change). Garder la paire ensemble.
- **48-Wolfram + 50 → palier 13** (« automate & flèche du temps ») : 50 déclare lui-même « Origami Wolfram pli 2 » — le même fil que 48-Wolfram (strate 4, parent ICT-18). C'est l'exemple que la carte elle-même propose (« ICT-50 près du palier 13 avec ICT-48-Wolfram »).

Les carnets **seuls** (sans frère dans la queue) s'accrètent au palier que la carte leur nomme : **48-Onset → palier 16** (« onset »).

Les **accrétions de famille** vont au palier de leur famille par construction : **36b/c/d → 15**, **42c/d/e/f → 15**.

Un seul **maintien argumenté** : **ICT-49** (Machines de Gödel, strand Schmidhuber). Il est une distillation externe autonome — machine-jouet honnête (comma-code, BIOPS, 9 331 techniques), claims G1–G4/OOPS confrontés à la mesure gate par gate, organe propre `ict.goedel_machine`. Il ne sert aucun palier ICT existant (aucun palier « méta-apprentissage / auto-modification »), et ce n'est pas un échafaudage pédagogique qui ait mûri vers une série (contrairement aux marchepieds ex-41/44). Il **reste donc dans ICT comme distillation externe, par décision** — c'est la destination 3 de la consigne, invoquée une fois, argumentée, pas par défaut.

### Table de destination

| Carnet | Destination | Type | Base de la décision |
|---|---|---|---|
| ICT-40a-TriangulationCausale | palier 04 (avec 40b, paire 40x) | accrétion | **note** (40a hors carte) |
| ICT-40b-AnalogCognitionWaves | palier 04 (substrat analogique) | accrétion | carte 11/10 — option close |
| ICT-47-PainAxisDistillation | palier 15 (axe douleur) | accrétion | carte 11/10 (M, couvert) |
| ICT-47b-PainAxisInstrument | palier 15 (avec 47, paire sibling) | accrétion | carte 11/10 — option close |
| ICT-48-Onset9B-Aggregate | palier 16 (onset) | accrétion | carte 11/10 — option close |
| ICT-48-WolframClasses-ThermoSignature | palier 13 (Origami Wolfram) | accrétion | carte 11/10 (R, couvert) |
| ICT-49-MachinesDeGoedel | **maintien en ICT** (distillation externe, strand Schmidhuber) | **maintien argumenté** | note |
| ICT-50-WolframRule30Aleatoire | palier 13 (avec 48-Wolfram) | accrétion | **note** (50 hors carte) |
| ICT-36b / 36c / 36d | palier 15 (par construction) | accrétion | carte 11/10 |
| ICT-42c / 42d / 42e / 42f | palier 15 (par construction) | accrétion | carte 11/10 |

Aucun palier n'est inventé : 04, 13, 15, 16 sont les numéros de la carte du 11/10. Les deux seules décisions de la note (40a → 04, 50 → 13) prolongent la numérotation de la carte aux membres de paire qu'elle n'avait pas nommés.

### Clôture des trois options ouvertes

- **47b** → **15 / instrument douleur** (rejet de « redescente vers le training ») : 47b est le contrôle d'instrument de 47 ; le descendre vers le training séparerait la paire 47/47b que la navigation croise déjà.
- **40b** → **04 / substrat analogique** (rejet de « palier distinct ») : la carte nomme déjà son palier ; ouvrir un palier distinct pour un seul carnet contredirait la règle « un carnet rejoint le palier qu'il sert ».
- **48-Onset** → **16 / onset** (rejet de « organe training ») : idem — la carte nomme le palier 16 ; l'organe d'onset reste où il est, seul le carnet rejoint le palier.

### Non-touché (délibéré)

- Les **modules `ict/`** (`ict.probes`, `ict.causal_engine`, `ict.wolfram_step`, `ict.time_arrow`, `ict.goedel_machine`, …) consommés par ces carnets **ne bougent pas** avec eux (section « redescente » de la carte).
- Les **marchepieds déjà descendus** (ex-41 → PT-15b, ex-41b → PT-15c, ex-44/22c → 2.9g) restent dans leurs séries cibles.
- Le **double numéro 48** (Onset9B vs WolframClasses) reste suivi par #20774 — cette note ne tranche pas le doublon de numéro, elle donne les deux leur palier (16 et 13).

### Mouvement (différé à la tranche suivante)

Cette note **ne déplace rien**. La tranche de mouvement qui suivra :
1. renommera les dossiers de sous-série par leur **sujet** (jamais un numéro nu — consigne user #20298) ;
2. regroupera les membres de paire dans le dossier de leur tête (04 : 40a+40b ; 15 : 47+47b+36b-d+42c-f ; 13 : 48-Wolfram+50 ; 16 : 48-Onset) ;
3. laissera ICT-49 en place (maintien) ;
4. amendera **cette note** pour pointer le mouvement exécuté.

*(Amendement du 15/11 : la tranche de mouvement exécutée a déplacé ICT-49/50/51 vers la série Complexity — voir le bloc d'amendement en tête de note, qui supersède les points 2 et 3 ci-dessus pour les carnets concernés ; le périmètre restant de cette liste est inchangé.)*

### Ré-exécution

Aucune. Ce grain est **markdown seul** (un fichier `docs/ict/` neuf) : aucune cellule source de notebook n'est touchée, aucune ré-exécution n'est due (règle C.2).

### Questions ouvertes : aucune
