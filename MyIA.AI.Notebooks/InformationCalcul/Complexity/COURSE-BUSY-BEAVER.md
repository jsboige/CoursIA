# La course Busy Beaver — document de course

**Document de course, pas un carnet.** Ce fichier ne présente aucun résultat nouveau et ne
revendique aucune position de numérotation dans la série. Il tient ce qui ne périme pas quand
un record tombe : **la généalogie datée**, les **auteurs et leurs programmes**, les **stratégies
d'exploration**, ce qui **évolue dans les moteurs de vérification**, et le **rapprochement borné**
avec l'échelle des témoins du Jeu de la Vie. À chaque nouveau bond, on **ajoute une ligne datée**
au journal de versions (§12) ; on ne réécrit pas l'historique.

Issue porteuse : [jsboige/CoursIA#28744](https://github.com/jsboige/CoursIA/issues/28744).
État au **2026-11-26**, lu sur `jamesyc/BusyBeaver` au commit
`88c1fdbbddb1f9759d9a12a6345acfecfbcdcbfc` (« Update docs », date d'auteur
`2026-11-24T01:25:59Z`).

**Hors périmètre, par construction** : le versant formel déjà livré
([`Complexity-08d`](Complexity-08d-IndependanceProuvee-BusyBeaver-Covering-Python.ipynb)), le
compte à rebours NF ([`Complexity-08e`](Complexity-08e-NF-MachinesCompteARebours-Python.ipynb)),
le tour descriptif des grands nombres
([`Complexity-07b`](Complexity-07b-LeTourDesGrandsNombres-Python.ipynb)), la preuve Lean
d'indépendance arithmétique (`Lean-42`), le dépouillement de `wlad-svennik/notes`
([#27537](https://github.com/jsboige/CoursIA/issues/27537)) et les jalons Lean de
`jamesyc/BusyBeaver` ([#27477](https://github.com/jsboige/CoursIA/issues/27477)). Ce document
**renvoie**, il ne recopie pas. La maison est l'EPIC
[#20607](https://github.com/jsboige/CoursIA/issues/20607).

## 1. Le cadre : une fonction non calculable, une borne qui descend

La fonction Busy Beaver **en temps d'exécution** assigne à `n` la plus longue course d'une
machine de Turing à `n` états qui s'arrête, lancée sur bande vierge. Le papier de 2016 la
définit ainsi et écarte l'autre variante — compter les 1 écrits —, qu'il juge moins solide :

> « because the number of 1's written is a somewhat arbitrary measure, it is not used in this
> work. »

(Yedidia-Aaronson, arXiv:1605.04343v1, §1.3, lu dans la copie archivée.)

La question qui structure le domaine est posée dès 2016 : « the smallest value of n for which
BB(n) is independent of ZFC set theory » — et la réponse y est une **borne supérieure**, pas une
valeur : il existe une machine de **7 910 états**, à une bande et deux symboles, dont on ne peut
prouver qu'elle ne s'arrête jamais dans ZFC, « assuming ZFC is consistent ». Dix ans plus tard,
la même question se pose pour **192 états**, mais sur **ZF** et non plus sur ZFC, avec un énoncé
à deux hypothèses (§5 et §8).

Le papier nomme aussi deux machines dérivées, qui ne sont pas des bornes d'indépendance mais des
bancs d'essai du langage : « We also use Laconic to design two Turing machines, G and R, that
halt if and only if there are counterexamples to Goldbach's Conjecture and the Riemann
Hypothesis, respectively. » Leur coût d'encodage est mesuré au §6.

## 2. Ce que « record » veut dire — et les deux échelles de temps

| Repère | Valeur | Théorie | Date |
|---|---|---|---|
| Machine `Z` de Yedidia-Aaronson | **7 910** états | ZFC | 13 mai 2016 (arXiv v1) |
| `PA196` | **196** états | PA (arithmétique du premier ordre) | 12 novembre 2026 |
| `ZF192` | **192** états | ZF du premier ordre | 22 novembre 2026 |

`7 910 / 192 = 41,2` : la borne a **baissé d'un facteur d'environ 41 en dix ans** — et non « en
moins d'un an » (correction datée du 26/11, erratum Hermes en commentaire de l'issue). Les deux
échelles de temps ne se confondent pas :

- **l'échelle longue** : 2016 → 2026, un facteur 41, qui mélange un changement de théorie
  (ZFC → ZF) et un changement de génération d'outils ;
- **l'échelle courte** : **une semaine de novembre 2026** pour la ligne ZF — `ZF209` le 15/11,
  `ZF207` le 19/11, `ZF192` le 22/11, soit **17 états en sept jours** — et six jours pour la
  ligne PA (`PA215` le 06/11 → `PA196` le 12/11, 19 états, dont un saut de 13 de `PA209` à
  `PA196`). C'est ce rythme-là qui a rendu ce document nécessaire : un carnet par descente de
  deux états serait périmé avant d'être relu.

**Avertissement de mesure.** Comparer 7 910 (ZFC) à 192 (ZF) demande de dire **ce qui est
comparé**. Ce qui est établi : les deux machines sont du même type (une bande, deux symboles,
bande vierge, état d'arrêt non compté dans `n`, fonction en temps d'exécution) et les deux
théorèmes visent la même moitié du problème — la **non-arrêt non prouvable**. Ce qui est
rapporté, non vérifié ici : le papier de 2016 affirme en note que « ZFC and ZF prove exactly the
same arithmetical statements », en citant Gödel 1940 et Schoenfield 1961 — deux références que
je n'ai pas ouvertes. Ce qui reste **non établi** : que les deux énoncés soient identiques, et
que le sens d'infinité de la bande soit le même (le 7-uplet de 2016 ne le fixe pas ; le README
de `ZF192` écrit « the tape is infinite in both directions »). La formulation retenue est donc
**« comparaison non établie »**, pas « machines incomparables ».

## 3. Les trois mouvements — et pourquoi les confondre est l'erreur

Le graphe de commits du dépôt (19 commits, linéaire, tous signés « James Chang ») donne la
trajectoire réelle. Dates **d'auteur** en UTC, relevées par l'API le 26/11 :

| Date (auteur) | Commit | Sujet | Mouvement |
|---|---|---|---|
| 2026-11-06T04:00:28Z | `eccd1b006e95` | Record full PA215 proof builds and final axiom audit | point de départ PA215 |
| 2026-11-08T04:25:55Z | `034d08df73b9` | Update machine and proof package to PA213 | **descente** |
| 2026-11-08T06:25:09Z | `51935df72b1f` | Prove two-sided PA213 independence in Lean | descente |
| 2026-11-08T06:52:18Z | `b42d9ffe1aee` | Add LaTeX exposition of PA213 independence and compiled PDF | descente |
| 2026-11-09T07:28:28Z | `1654314dd689` | Update machine and proof package to PA211 | descente |
| 2026-11-11T00:44:09Z | `9d5a76134790` | Publish the PA209 proof package | descente |
| 2026-11-11T05:58:59Z | `eaf1760795e0` | Prove PA209 reserve bounds before instantiating formula codes | descente |
| 2026-11-11T08:01:41Z | `69d98241a721` | Select the hosted runner for PA209 preflight | descente (instantané public PA209) |
| 2026-11-12T09:23:24Z | `64ff1b3047b9` | Replace PA209 with the PA196 proof package | **descente de 13 états** |
| 2026-11-12T12:27:45Z | `407cdc356f6b` | Polish the PA196 paper | descente |
| 2026-11-14T11:28:56Z | `74ca365bf41e` | Organize PA196 as a self-contained proof package | descente |
| 2026-11-15T09:13:13Z | `286324f9ad10` | Add the ZF209 proof package with a calibration-based proof | **changement de théorie (PA → ZF)** |
| 2026-11-19T03:19:35Z | `9437ef874e1c` | Add the ZF207 proof package | descente ZF |
| 2026-11-19T03:21:56Z | `8419afeb6513` | Let the Palomar preflight choose the project path | outillage |
| 2026-11-21T05:14:37Z | `5928cc3a0ca3` | Add the I3-380 proof package | **montée en théorie (ZFC + I₃)** |
| 2026-11-21T06:08:20Z | `66d069752138` | Add the I0-451 proof package | **montée en théorie (ZFC + I₀ + Berkeley)** |
| 2026-11-22T10:56:17Z | `bd3f7575b227` | Add the ZF192 proof and paper | **descente réelle ZF (209 → 192)** |
| 2026-11-23T11:38:50Z | `e71174d78877` | Add the standalone I3-334 proof package | descente en théorie montée (380 → 334) |
| 2026-11-24T01:25:59Z | `88c1fdbbddb1` | Update docs | documentation |

**Huit commits sur dix-neuf portent une date de committer postérieure à leur date d'auteur** — de
treize minutes (`e71174d78877`, 11:38:50Z → 11:52:13Z) à un peu plus de quarante-cinq heures
(`66d069752138`, 21/11 06:08:20Z → 23/11 03:19:06Z). Deux franchissent une frontière de jour
calendaire : `eccd1b006e95` (auteur le 06/11 à 04:00:28Z, committé le 07/11 à 01:39:14Z) et
`66d069752138`. Le document date par **auteur** — c'est la date à laquelle le travail a été
écrit —, et les deux listes sont dans `GRAPHE-COMMITS.txt` (§11) pour que le lecteur puisse
choisir l'autre convention.

**Les trois mouvements, et ils ne se comparent pas entre eux :**

1. **Descente d'états dans une théorie fixée.** PA215 → PA196 ; ZF209 → ZF207 → ZF192 ;
   I3-380 → I3-334. C'est le seul mouvement que le mot « course » suggère, et le seul où un
   écart d'états se lit directement.
2. **Changement de théorie.** PA → ZF (commit du 15/11), et ZF → NF chez l'autre programme
   (`wlad-svennik`, §5). Le prix en états n'est **pas** comparable tel quel : les deux calculs
   prouvent l'arrêt dans des systèmes différents, et c'est l'énoncé qu'il faut citer, pas le
   nombre.
3. **Montée en théorie.** ZFC + I₃ (`I3-380`, `I3-334`) puis ZFC + I₀ avec un cardinal de
   Berkeley (`I0-451`) : ici **on ne descend plus, on monte la force du système** pour obtenir
   l'indépendance. Ces résultats vont dans le sens **inverse** de l'intuition de record — et ils
   sont **conditionnels** (§8).

## 4. La généalogie — ce que le dépôt écrit lui-même

La généalogie n'est pas à deviner : elle est dans les `docs/provenance.md`, les
`formalization.yaml` et les bibliographies des sept papiers, tous archivés (§11). Ce que ces
fichiers disent, projet par projet :

- **Ligne PA** — `PA196` déclare deux antécédents : le développement Rocq **K230** d'Elliot
  Glazer et le dépôt **PA238** de Jeff Ketchersid, comme « background for the tape engine and
  proof calculus » (`PA196 - docs - reproduction.md`). `PA196` **remplace** `PA209` (commit
  `64ff1b3047b9`) et documente la réduction : « reducing the working-state count of the previous
  published construction by 13 ».
- **Ligne ZF** — `ZF209` ouvre un projet distinct de la ligne PA : son README écrit « This is a
  separate Lake project from PA196. », et son `provenance.md` nomme ses dettes techniques —
  moteur de bande d'après Elliott Glazer (`ProofSources/M6/Zip.lean`) et Jeff Ketchersid
  (`ProofSources/M6/Native.lean`). `ZF207` est **dérivé** de `ZF209` : « The machine runs the
  same proof search as ZF209 with a smaller decoder for the stored program »
  (`ZF207 - README.md`). `ZF192`, lui, **rompt** la dérivation : « A fresh search using Boolean
  satisfiability (SAT), starting from Glazer's 230-state K230 machine […] produced the ZF192
  table. The search was independent of the ZF207 and ZF209 transition tables »
  (`ZF192 - paper - zf192.tex`).
- **Ligne grands cardinaux** — `I3-334` adapte son support de `I3-380` : son `docs/provenance.md`
  écrit que le support local « adapts the arithmetic, … » puis renvoie à l'arbre `I3-380` épinglé
  sur `5928cc3a0ca3`, et le papier décrit « the binary tape semantics and proof transport adapted
  from the 380-state formalization, and a standalone Challenge ». Les bibliographies le
  confirment à la clé près : `I3-380` porte `corazza`, `meredith`, `robbins`, `goedel`,
  `foundation` ; `I3-334` en porte quatre (`corazza`, `robbins`, `goedel`, `foundation`) — la
  clé `meredith` disparaît avec la réécriture. `I0-451` porte sept clés (`bkw`, `zf207`,
  `foundation`, `goedel`, `goldberg`, `ketchersid`, `schlutzenberg`) : il cite donc `ZF207` en
  plus de ses références propres, et reprend trois fichiers patchés de `ZF207`
  (`provenance/FOUNDATION_PATCHES.json`).
- **2016** — le papier de `ZF192` cite Yedidia-Aaronson **une seule fois** (clé
  `yedidia-aaronson`, en introduction, pour situer la fonction BB en temps d'exécution ; ses
  autres clés sont `godel`, `zf207`, `zf209`, `k230`). Aucun autre des sept papiers ne les cite,
  et le mot **Laconic n'apparaît nulle part** dans les 83 fichiers archivés. La filiation
  Laconic → moteurs actuels est donc une **piste de lecture**, pas un fait documenté (§10).
  C'est une correction à l'issue, qui la présentait comme « l'ancêtre direct des moteurs
  actuels » : la formulation est plus forte que ce que les fichiers portent.

**Dates des ancêtres externes**, mesurées par l'API GitHub le 26/11 (elles ne figurent pas dans
les fichiers) : `elliotglazer/k230-rocq` créé le `2026-10-19T10:11:51Z` (12 étoiles ; description
de l'API : vérification Rocq sans axiome que K230 s'arrête si et seulement si ZFC est
incohérent) ; `jeff87654/busy-beaver` créé le `2026-10-04T21:09:48Z` (17 étoiles), révisions
épinglées par le dépôt `84049b5e7531` (`2026-10-27T01:37:52Z`) et `cde3649e0f1f`
(`2026-11-15T20:51:36Z`). L'API ne détecte **aucune licence** dans ces deux dépôts.

## 5. Les deux programmes — pas une même ligne de record

| | `jamesyc` (James Chang) | `wlad-svennik` |
|---|---|---|
| Théories | PA, ZF, ZFC + I₃, ZFC + I₀ (+ cardinal de Berkeley) | **NF**, NFU, C₀ ; plus deux notes archivées, une borne PA à 192 états « for non-regularity » et un Zermelo à 201 états |
| Livrable | sept projets Lean autonomes, un par machine, avec article, table de transitions et consignes de reproduction | articles et carnets ; dépouillé dans [#27537](https://github.com/jsboige/CoursIA/issues/27537) et distillé dans [`Complexity-08e`](Complexity-08e-NF-MachinesCompteARebours-Python.ipynb) |
| Rythme | 19 commits du 06/11 au 24/11 | selon [#27537](https://github.com/jsboige/CoursIA/issues/27537) |
| Stratégie | remplacer le paquet, réécrire la machine (§6) | **inverser** le problème : compte à rebours (§6) |
| Ce que la théorie impose | ZF et les grands cardinaux : résultats **conditionnels**, énoncés explicites (§8) | NF : compréhension **stratifiée** (Quine, 1937), ensemble universel, négation de l'axiome du choix démontrable — une théorie moins standard, dont la cohérence est ouverte depuis près de quatre-vingt-dix ans |

**Le piège du nombre.** Le nombre **192** circule des deux côtés. Chez `jamesyc`, `ZF192` est une
machine de 192 états dont le comportement est indépendant de **ZF**. Chez `wlad-svennik`,
`nf-bb192` est une **machine-compte à rebours de 192 états** — elle s'arrête si et seulement si
la NF du premier ordre prouve une contradiction —, et [`Complexity-08e`](Complexity-08e-NF-MachinesCompteARebours-Python.ipynb)
la classe comme « **théorème vérifié par Lean 4.35.0** sur la table littérale ». Deux
programmes distincts, deux théories distinctes, deux énoncés distincts : **aucun classement ne se
déduit de l'égalité des nombres**. Ce document ne compare que ce qui est comparable, et le dit
chaque fois.

## 6. Les stratégies d'exploration

**2016 — compiler un langage de haut niveau, contourner l'encodage des axiomes.** Yedidia et
Aaronson écrivent un langage, **Laconic**, « which is much more convenient than direct state
manipulation », qui compile vers **TMD** puis vers la machine finale. Le papier décrit TMD comme
« a multi-tape, 3-symbol Turing machine plus a function stack », et la chaîne exactement :
« Laconic compiles down to a TMD program, and TMD compiles down to a description of a
single-tape, 2-symbol Turing machine. »

Trois idées portent la parcimonie. Le papier les énumère lui-même : « Even to achieve a state
count of 7,910, we will need three nontrivial ideas: Harvey Friedman's order-theoretic
statements, on-tape processing, and introspective encoding. » Les deux dernières se laissent
citer, ce qui vaut mieux qu'un commentaire :

> « on-tape processing begins by writing the commands onto the tape, using as efficient an
> encoding as possible. Then, once the commands are on the tape, the commands are processed by a
> single group of states that understands how to interpret them. »

> « The third idea, introspective Turing machines, is a way to write long strings onto the tape
> using as few states as possible. The idea is to encode information one of each state's
> transitions, instead of encoding information in each state's write field. This is advantageous
> because there are many choices for which state to point a transition to, but only two choices
> for which bit to write. Therefore, more information can be encoded in each state using this
> method. »

Le gain du traitement sur bande est mesuré dans le papier, avec ses propres colonnes :

| Program | States (Naïve) | States (On-Tape Processing) |
|---|---:|---:|
| Goldbach | 7 902 | 4 888 |
| Riemann | 36 146 | 5 372 |
| ZFC | 340 943 | **7 910** |

et le commentaire qui l'accompagne : « As can be seen from this table, on-tape interpretation
results in huge gains, particularly in large and complex programs. » Les deux premières lignes
sont les machines `G` et `R` du §1 : elles ne bornent rien, elles paient le langage.

**2026 — réécrire la machine, pas la raffiner.** Le dépôt `jamesyc` **remplace** les paquets
(« Replace PA209 with the PA196 proof package », « Update machine and proof package to PA211 »)
au lieu de les empiler : chaque descente est une **nouvelle construction**, avec ses propres
preuves de démarrage et de simulation. Les deux exemples documentés :

- `ZF192` naît d'une **recherche SAT neuve** de table de transitions, lancée depuis K230 et
  explicitement **indépendante** des tables ZF207/ZF209 — donc pas un raffinement du 209 ;
- `PA196` réorganise le paquet (code du moteur de bande dans `ProofSources/PA196/Engine`,
  support arithmétique dans `ProofSources/PA196/ArithmeticSupport`) en conservant les
  déclarations et les crédits d'origine.

**Résonance à noter, sans filiation.** Le papier de 2016 s'interroge en note : chercher
directement des contradictions pourrait faire aussi bien ou mieux que passer par les énoncés de
Friedman, et « recent unpublished work by Stefan O'Rear has given some evidence for that ». La
voie de `ZF192` — une machine dont l'arrêt équivaut à une réfutation dans un calcul codé, table
trouvée par recherche — est proche de cette alternative. C'est une **lecture comparative**, pas
une dette documentée : aucun fichier archivé ne cite O'Rear.

**Inversion du problème (autre programme).** Chez `wlad-svennik`, la stratégie phare est le
**compte à rebours** — une machine qui s'arrête si et seulement si la théorie prouve une
contradiction —, ce qui retourne la question : au lieu de chercher une machine dont l'arrêt est
indépendant, on construit une machine dont l'arrêt *serait* une preuve d'incohérence. Traitement
complet dans [`Complexity-08e`](Complexity-08e-NF-MachinesCompteARebours-Python.ipynb) et
[#27537](https://github.com/jsboige/CoursIA/issues/27537).

## 7. Ce qui change dans les moteurs — anatomie et rôle du hachage

Chaque projet est un **lake Lean autonome**, avec la même anatomie. C'est cette anatomie qui est
le sujet, autant que les machines.

| Élément | Rôle | Où |
|---|---|---|
| `ProofSources/<Projet>/` | la preuve : machine, bande, simulation, théorème principal, `Solution.lean` | chaque projet |
| `Support/<Projet>Support/` | huit modules de support — Coding, Calculus, Execution, Machine, Logic, SetTheory, Independence, Palomar (liste du README de `ZF192`) | ZF192, I3-334 |
| `Vendor/` ou `vendor/` | sources *Foundation* embarquées (Apache-2.0) | tous |
| `VENDORED_FOUNDATION_HASHES.json` | **122 entrées** `chemin → sha256` (26 Vorspiel, 5 Logic, 84 FirstOrder, 3 Propositional, 4 Syntax) | ligne ZF |
| `provenance/FOUNDATION_FROM_PA196.json` | **39** fichiers repris de la copie PA196 (autre révision amont) | ligne ZF |
| `provenance/FOUNDATION_PATCHES.json` | fichiers patchés, avec `original_sha256`, `patched_sha256` et **raison** écrite | ligne ZF (1 fichier), I0-451 (3, hérités de ZF207) |
| `comparator.json` | modules défi/solution, noms de théorèmes, axiomes permis, `enable_nanoda` | tous |
| `check.py` | contrôle **source** (pas une preuve de compilation) : table exacte, données contextuelles, appendice du papier, défi autonome | ligne ZF |
| `Audit.lean` | `#print axioms` sur les déclarations clés — neuf dans `ZF207`, le compte varie par projet | tous |
| `formalization.yaml` | schéma v0.4 : sources, statut `sorry_count`/`axioms`, **statut de revue**, outils d'automatisation | tous |
| `lakefile.toml` + `lake-manifest.json` | épinglage de Mathlib (rev `56a005855ea1…`) et limites de compilation (§ ci-dessous) | tous |

Les limites de compilation ne sont pas uniformes, et ce détail dit quelque chose : `-j1 -M1536`
sur `I0-451`, `ZF192`, `ZF207`, `ZF209` ; `-j1 -M4096` sur `I3-334` et `I3-380` ; `-j1` seul sur
`PA196` (`weakLeanArgs` de chaque `lakefile.toml`, mesuré). La ligne « grands cardinaux » a
besoin de deux fois et demie plus de mémoire que la ligne ZF, et le projet PA d'aucune borne
explicite.

**Pourquoi on hache les fondations.** La preuve ne porte pas sur des mathématiques abstraites :
elle porte sur un **texte précis** de *Foundation*, à une révision donnée, éventuellement patché.
`check.py` (184 lignes, lu) rend ce texte **clos** :

- chaque fichier de `Vendor/Foundation` doit figurer dans **l'union** des deux manifestes —
  `present == listed`, à la ligne près : ni fichier non déclaré, ni fichier manquant ;
- un patch doit nommer un fichier **connu**, et son `original_sha256` doit égaler l'empreinte
  enregistrée, sinon « Patch changes the recorded upstream identity » ;
- un import PA196 ne peut pas dupliquer une entrée amont ;
- la table de transitions est hachée (`be1db915…`) et confrontée à la machine, aux données
  contextuelles, **et à l'appendice du papier** — un désaccord entre l'article et la machine
  rougit ;
- `check.py` s'arrête net en le disant : « Source checks do not establish compilation, axiom
  closure, Comparator, or NanoDa success. »

C'est la réponse enseignable à la question « pourquoi épingler un lac, et pourquoi hacher » : un
hachage transforme « la preuve suppose *Foundation* » en « la preuve suppose **ces 122 fichiers,
à ces empreintes** », et rend la dérive **visible** au lieu d'invisible.

**Ce que vérifier coûte — ce que les fichiers enregistrent, et ce qu'ils taisent.** Chaque ligne
ci-dessous paraphrase un `provenance.md`, un `reproduction.md` ou un `result.md` nommé ; là où
le fichier ne dit rien, la case le dit aussi.

| Projet | Enregistré dans les fichiers | Reste en attente, ou non enregistré |
|---|---|---|
| `PA196` | `reproduction.md` donne les commandes (audit racine, audits gardés) ; `result.md` décrit ce que `Solution` prouve | **aucun enregistrement d'exécution** dans les fichiers archivés ; comparaison en bac à sable à faire sous Linux avec Bubblewrap |
| `ZF209` | build local, audit, Comparator avec Lean **et** NanoDa ; le con-ron épinglé a **atteint sa limite locale de 30 minutes** sous émulation x86 sans verdict | vérification hébergée Palomar |
| `ZF207` | `check.sh --full` : preflight source, build de Solution et Challenge, audit des **neuf** déclarations ; Comparator accepté par NanoDa et le noyau Lean (`--inadvisably-no-sandbox`, Bubblewrap absent sur macOS) ; con-ron du toolchain : **34 414** déclarations en mode `--verified` | Comparator en bac à sable sous Linux ; Palomar, qui **épingle un autre build** de con-ron |
| `ZF192` | build décrit par `provenance.md` (le point de départ est lu depuis la table littérale) et `check.sh --full` | compilation, axiomes, Comparator et NanoDa **non enregistrés** ; Palomar annoncé comme « future submission » dans `reproduction.md` |
| `I3-380` | contrôles de table exacte, build de Challenge et Solution, audit d'axiomes sous Lean **4.37.0-rc1** sur macOS ; Comparator stock en mode local non bac-à-sable, acceptant `PalomarI3380.exactClaim` avec Lean et NanoDa | Palomar ; noter l'écart avec le `lean-toolchain` épinglé (`v4.35.0`) |
| `I3-334` | rien : son `docs/provenance.md` ne consigne que la dérivation depuis `I3-380` | toute vérification ; `formalization.yaml` porte `unchecked` |
| `I0-451` | **20 novembre 2026** : Lean 4.35.0 a bâti Solution et Challenge ; audit d'axiomes limité à `propext`, `Classical.choice`, `Quot.sound` ; Comparator accepté par le noyau Lean et NanoDa (macOS, sans Bubblewrap) ; con-ron fourni : **25 613** déclarations en mode vérifié | Palomar |

Trois enseignements pour nos carnets :

1. **le vérificateur n'est pas un oracle unique** : Lean (noyau), NanoDa, con-ron et le service
   hébergé Palomar sont quatre instruments distincts, et le dépôt trace lequel a dit quoi ;
2. **la même preuve peut être acceptée par trois instruments et rester « en attente »** du
   quatrième — `formalization.yaml` porte un `review.status` : `self-assessed` sur cinq projets
   (`I0-451`, `PA196`, `ZF192`, `ZF207`, `ZF209`), `unchecked` sur `I3-334` et `I3-380` ; la note
   « Hosted Palomar verification is pending. » n'apparaît que sur trois des cinq `self-assessed`
   (`PA196` porte une note différente, `I0-451` une troisième) ;
3. **l'outillage lui-même est daté** : une limite de 30 minutes sous émulation, un bac à sable
   indisponible sur macOS, un écart de toolchain, deux builds de con-ron différents selon le
   vérificateur — ce sont des faits de vérification, pas des anecdotes.

## 8. Le caractère conditionnel — écrit, cité, et scoped

Le README racine du dépôt le dit sans détour (verbatim) :

> « The ZF and large-cardinal results are conditional. The project statements spell out the
> consistency, soundness, and proof assumptions used in each result. »

Ce que cela donne concrètement :

- **`ZF192`** — deux hypothèses distinctes. Cohérence de ZF ⇒ la machine tourne indéfiniment et
  `ZF ⊬ ¬H` ; **Σ₁-solidité arithmétique** de ZF ⇒ ni `H` ni `¬H` ne sont prouvables. Limite
  déclarée par le projet : « The full reverse implication for nonstandard histories lies outside
  the scope of this development. »
- **`I3-334` et `I3-380`** — non-arrêt équivalent à la cohérence syntaxique de ZFC + I₃ ;
  l'indépendance exige la Σ₁-solidité. `I3-334` écrit lui-même les trois conséquences : le
  théorème clos représente l'arrêt sur bande vierge dans tout modèle de ZFC + I₃ ; la cohérence
  syntaxique donne le non-arrêt et l'improvabilité du non-arrêt ; la Σ₁-solidité donne que ni
  l'un ni l'autre n'est prouvable.
- **`I0-451`** — la prémisse est **troisième** : cohérence de B = ZF + cardinal de Berkeley,
  Σ₁-solidité de T = ZFC + I₀, et **une preuve dans B** de la cohérence de la présentation de
  Craig des conséquences arithmétiques de T. Le papier écrit lui-même ce qui reste ouvert :
  « Discharging it from the conventional set-theory consistency statement would require an
  implication provable in B between the two internal consistency sentences. […] That
  calculation leaves the internal implication open. »
- **`PA196`** — même structure de contrat côté PA, mais à deux côtés : le paquet expose
  `two_sided_independence` et `machine_nonhalting`, et l'audit ne laisse que `propext`,
  `Classical.choice`, `Quot.sound`.

Conséquence pédagogique : un « record d'états » n'est **jamais** une ligne de tableau sans sa
théorie, son énoncé et ses hypothèses. C'est la raison pour laquelle ce document écrit
« comparaison non établie » dès qu'on change de théorie.

## 9. Le rapprochement avec le Jeu de la Vie — et sa borne

L'intuition de départ : cette course ressemble à l'époque où de petits incréments mécaniques
grignotaient les limites de la logique dans le Jeu de la Vie, jusqu'à culminer avec le programme
**Gemini** (Wade, 2010). Le dépôt a ce récit, et le cite plutôt que de le paraphraser.

`GOL-04-Canons` ouvre sur une échelle de quatre barreaux — `| Barreau | Demande | État |`, où le
barreau 2 est « **ce notebook** » et les barreaux 3 et 4 « hors d'atteinte, nommé tel quel » — et
la referme sur un tableau de bilan, reproduit ici verbatim :

| Barreau | Vérifié ? | Construit ? | Témoignage |
|---|---|---|---|
| 1 — quasi-particule | **oui, par le lake** (`decide`, `Computation.lean:176`) | le planeur est une donnée, pas une construction | la translation périodique existe |
| 2 — source périodique | **oui, ici** : période 30 + cadence 30 mesurées, certificat `#eval` sur horizon 90 | **non, et mesuré** : 0/3 000 soupes, zéro calibré par contrôle positif | le canon de Gosper : croissance non bornée depuis 36 cellules |
| 3 — automate fini | non | non | nécessite une synthèse dirigée — hors d'atteinte, dit comme tel |
| 4 — machine de Turing | non | non | programme Gemini : des années de design |

La « demande » de chaque barreau est dans le premier tableau du carnet : une configuration à
translation périodique, une configuration bornée émettant périodiquement un vaisseau, une
configuration réalisant le graphe d'un automate fini, une configuration émulant une machine de
Turing. Le zéro du barreau 2 est **calibré**, et le carnet le dit dans ces termes : « Le zéro
mesure le budget, pas un aveuglement de l'instrument. »

Et la phrase que `GOL-04` formule pour lui-même, et qui vaut mot pour mot des deux côtés :

> « l'écart entre vérifier et construire n'est pas un manque d'ingéniosité, il est structurel » ;
> « Le barreau suivant ne se franchira pas en échantillonnant plus fort […] mais en assemblant des
> composants : c'est un changement de nature, pas de budget. »

**Le vocabulaire, pris aux fichiers.** Le terme « Spartan » est ancré dans
`conway_lean/Conway/Life/Computation_en.lean`, qui écrit au sujet de l'eater : « the first
building block of Spartan logic gates. », puis, en tête d'une liste : « In Spartan logic
(Rendell 2000, Goucher 2014), eaters serve as: » — suivie de « Signal sinks at gate outputs »,
« Boundary stabilisers in metapixel construction », « Absorbers at wire terminations ». Il l'est
aussi dans `GOL-01-Regles-Vie-Lean`, dont une annexe s'intitule « ### Annexe B — Spartan logic +
flux de gliders = logique constructive », et dans `scripts/hashlife/k_trajectory.py`, qui nomme
un « Spartan computronium » comme corpus d'une tranche suivante. En revanche, **`GOL-04` ne
prononce pas le mot** : le vocabulaire de l'échelle des témoins y est « quasi-particule »,
« faisceau », « source périodique ». Les deux vocabulaires ne se substituent pas l'un à l'autre.

**Un pont que le dépôt fournit déjà**, et qui vaut pour les deux côtés : `GOL-01` décrit Gemini
comme un « ribosome stationnaire [qui] interprete un flux de gliders qui construit une copie de
lui-même un peu plus loin » — une **machine fixe qui lit un flux d'instructions**. C'est
exactement l'architecture du **traitement sur bande** de 2016 (écrire les commandes sur la bande,
puis les interpréter par un seul groupe d'états) et du **scanner** de `ZF192` (« A scanner decodes
instructions from the tape, and seven states perform the register arithmetic »). Les deux
constructions séparent un **lecteur fixe** d'un **programme écrit sur le support** ; c'est une
parenté d'**architecture**, lisible dans les textes, et non une citation croisée.

**La borne, ferme.** Les deux courses ne se ressemblent pas : elles partagent une **structure de
coût**, et l'analogie est une **analogie de travail à éprouver**, pas un résultat. Ce qu'elle
affirme, et ce qu'elle n'affirme pas :

- **commun, et c'est une hypothèse de lecture** : le côté **construction** est le cher, et le
  progrès vient d'un changement de **représentation** (assembler des composants en GOL ;
  compresser un argument d'incomplétude en programme de registres en BB), pas d'un budget de
  calcul supplémentaire ;
- **non transféré** : « le vérificateur est bon marché ». C'est **mesuré en GOL** (polynôme en
  l'horizon) ; pour BB, ce document ne l'a **pas** mesuré, et les sources montrent plutôt
  l'inverse — build Lean, trois instruments indépendants, un service hébergé encore en attente
  (§7). La moitié « vérifier » de l'analogie doit donc être **retirée pour BB** tant qu'une
  mesure ne la rétablit pas ;
- **refusé** : toute assimilation des objets. GOL est un automate cellulaire, BB une machine de
  Turing ; le premier est un jeu de construction spatial, le second un codage arithmétique de la
  prouvabilité. L'analogie porte sur **l'épistémologie de la construction**, pas sur les objets.

## 10. Ce qui n'est pas établi, et le restera peut-être

| Question | État | Pourquoi |
|---|---|---|
| Laconic est-il l'ancêtre **direct** des moteurs actuels ? | **piste**, non établi | 0 occurrence de « Laconic » dans les 83 fichiers archivés ; Yedidia-Aaronson n'est cité qu'une fois, en introduction de `ZF192` |
| Un état PA et un état ZF mesurent-ils la même chose ? | **comparaison non établie** | théories différentes ; l'équivalence des énoncés arithmétiques est **rapportée** par la note de 2016, non vérifiée ici |
| La bande de 2016 est-elle infinie des deux côtés ? | non précisé là où j'ai lu | le 7-uplet ne fixe pas le sens ; `ZF192` écrit « in both directions » |
| Andrew James Wade (crédit du générateur) est-il l'auteur de Gemini ? | **homonymie non tranchée** | `ZF/generator/LICENSE.wade` ne dit que « MIT No Attribution / Copyright 2025 Andrew James Wade » |
| Le rythme actuel est-il tenable ? | non établi | six semaines d'historique (06/11 → 24/11) ne font pas une tendance |

## 11. Sources, et où elles sont archivées

**Dépôt** — `jamesyc/BusyBeaver`, commit épinglé `88c1fdbbddb1f9759d9a12a6345acfecfbcdcbfc`
(MIT, « Copyright (c) 2026 James Chang » ; sources *Foundation* Apache-2.0). Instantané de
**83 fichiers texte**, chacun vérifié byte-identique au commit par empreinte de blob git :

`G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\Complexity Theory and Hardness\2026 - Chang (depot jamesyc) - BusyBeaver, paquets de preuve PA, ZF et grands cardinaux (github, MIT)\`

Le dossier contient aussi `GRAPHE-COMMITS.txt` — les 19 commits avec **date d'auteur et date de
committer**, parents et sujet, produit depuis l'API — et `PROVENANCE.md` (table fichier par
fichier avec empreintes, ce qui n'est **pas** copié, et les mesures faites ici). Les preuves,
les PDF et les données machine restent au dépôt.

**Publication** — Yedidia & Aaronson, *A Relatively Small Turing Machine Whose Behavior Is
Independent of Set Theory*, arXiv:1605.04343v1 (13 mai 2016), lu dans la copie archivée :

`G:\Mon Drive\MyIA\IA\Bibliographie IA\Automata\Complexity Theory and Hardness\2016 - Yedidia Aaronson - A Relatively Small Turing Machine Whose Behavior Is Independent of Set Theory (arXiv 1605.04343v1, OA).pdf`
(SHA-256 `84f4075a00b838205e145c43d0ff12a811059530bc8be4020822a6af03b963b7`).

**Jeu de la Vie** — lus sur `origin/main` au commit de rédaction :
`MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/GOL-04-Canons.ipynb`,
`…/GOL-01-Regles-Vie-Lean.ipynb`, `…/conway_lean/Conway/Life/Computation_en.lean`,
`scripts/hashlife/k_trajectory.py`.

**Autre programme** — pièces du programme NF citées au §5 : voir
[#27537](https://github.com/jsboige/CoursIA/issues/27537) et
[`Complexity-08e`](Complexity-08e-NF-MachinesCompteARebours-Python.ipynb), qui épinglent les
révisions et listent les copies archivées au gisement. Ce document renvoie, il ne re-dépouille
pas.

**Ancêtres externes** — non archivés ici, datés par l'API le 26/11 :
`elliotglazer/k230-rocq` (commit `3142e4dd`), `jeff87654/busy-beaver` (commits `84049b5e`,
`cde3649e`). Le fil Reddit `r/mathematics` « BB(192) is independent of ZFC » est une **source de
veille** : il signale, il n'établit rien.

**Renvois internes** — [#27477](https://github.com/jsboige/CoursIA/issues/27477) (paquets Lean),
[#27537](https://github.com/jsboige/CoursIA/issues/27537) (programme NF),
[#20607](https://github.com/jsboige/CoursIA/issues/20607) (EPIC maison),
[`Complexity-08d`](Complexity-08d-IndependanceProuvee-BusyBeaver-Covering-Python.ipynb),
[`Complexity-08e`](Complexity-08e-NF-MachinesCompteARebours-Python.ipynb),
[`Complexity-07b`](Complexity-07b-LeTourDesGrandsNombres-Python.ipynb).

## 12. Journal des versions — on ajoute une ligne, on ne réécrit pas

| Date | Version | Événement | Ce qui change ici |
|---|---|---|---|
| 2026-11-26 | v1 | premier état, sur le cliché `88c1fdbbddb1` (7 projets, 19 commits) | création du document ; intègre l'erratum Hermes du 26/11 (échelle de temps longue, « comparaison non établie », vocabulaire de l'analogie ramené à une hypothèse de lecture) |

**Procédure de mise à jour.** Quand un bond survient : (1) ré-archiver le dépôt dans un **dossier
neuf** daté, jamais par écrasement ; (2) ajouter une ligne au tableau §3 si la trajectoire change,
une ligne au journal ci-dessus, et corriger la valeur de référence **en la datant** ; (3) si la
borne change de théorie, ajouter l'avertissement de §2 — un nombre sans théorie n'entre pas dans
ce document.

## Les neuf critères d'acceptation de l'issue, et où ils sont traités

| Critère | Où |
|---|---|
| Trois mouvements distingués et datés, aucune comparaison d'états entre théories sans le dire | §3, §2 |
| Généalogie avec sources ; Laconic, machines G et R nommés | §4, §6, §1 |
| Deux auteurs, deux programmes, séparés | §5 |
| Caractère conditionnel écrit, phrase du README citée | §8 |
| Anatomie des moteurs, rôle de `VENDORED_FOUNDATION_HASHES.json` et de `comparator.json` | §7 |
| Rapprochement GOL↔BB avec sa borne, vocabulaire « Spartan » sourcé | §9 |
| Rien de dupliqué avec #27477, #27537, #20607 — renvois, pas copies | en-tête, §11 |
| Aucun carnet de résultat, aucune numérotation consommée | en-tête |
| Document daté et versionné, ajout de ligne à chaque bond | §12 |

**Deux corrections apportées au texte de l'issue**, parce qu'un document de course ne peut pas
recopier une affirmation plus forte que sa source : « il s'est produit en moins d'un an » est
faux (7 910 en 2016 → 192 en 2026, soit dix ans), et « l'ancêtre direct des moteurs actuels »
pour Laconic est une piste de lecture, non un fait documenté. Les deux sont écrites comme telles
aux §2 et §4.
