# La mer qui monte — lire le dépôt CoursIA d'un seul geste







Grothendieck décrivait deux façons de venir à bout d'un problème dur, comme on ouvre une noix. On peut la frapper au marteau et au burin, jusqu'à ce que la coque cède sous les coups. Ou bien on peut la plonger dans l'eau et laisser la mer monter — lentement, sans bruit, sans qu'on sente jamais rien céder — jusqu'à ce qu'un jour la coque, ramollie, s'ouvre d'une pression de la main. Sa préférence allait à la seconde : non pas forcer le problème, mais faire monter autour de lui le cadre qui le rend soluble.







Ce dépôt contient une noix de cette espèce, et il vaut la peine de la poser sur la table avant toute théorie. Dans le Jeu de la Vie de Conway, un algorithme célèbre — HashLife — saute `2^k` générations d'un coup, là où la règle ne sait avancer que d'un pas. Encore faut-il qu'il aille juste : prouver que le bond calcule exactement ce que la règle, appliquée `2^k` fois, aurait calculé — voilà la noix. On peut la frapper : dérouler l'induction cellule par cellule, génération par génération. Chaque coup porte, aucun ne traverse ; l'obligation de preuve enfle avec le motif et le nombre de pas, et la coque ne cède pas. Gardez-la en vue. Elle va tremper dans tout ce qui suit, et — c'est la nouveauté de ces dernières semaines — l'eau vient de monter d'un cran qu'on n'avait pas prévu.







Car le dépôt CoursIA, parcouru d'une série à l'autre, ressemble d'abord à un catalogue : automates cellulaires, preuves formelles, programmation probabiliste, théorie des jeux, théorie des nœuds, planification, contrats intelligents, apprentissage par renforcement, trading, GenAI. Une vingtaine de sujets sans rapport évident. Mais lu avec une seule question en tête, il se met à raconter une histoire continue. La question n'est pas « comment résoudre ce problème ? » — elle est grothendieckienne : *dans quel cadre ce problème cesse-t-il d'être dur ?* Suivons-la, et laissons l'eau monter.







---







## Changer de représentation jusqu'à ce que la difficulté se dissolve







Le premier mouvement est partout le même : prendre un objet et le réécrire dans une autre langue, où il devient maniable.







Notre noix, d'abord. La règle de voisinage de Conway, posée cellule par cellule, n'apprend rien sur les motifs qui en émergent — c'est une myopie de principe : chaque cellule ne voit que ses huit voisines, et la question du bond de `2^k` générations ne peut même pas s'y formuler. Transformée en quadtree, puis en type inductif ([`conway_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/)), la même règle change de visage : un macro-carré se décrit par ses quatre quadrants, le saut de générations devient une équation entre constructeurs, et la question de la preuve, tout à l'heure informulable, devient un énoncé Lean qu'on peut écrire noir sur blanc — il s'appelle `hashlife_correct`. La noix n'est pas ouverte. Mais elle a cessé d'être une pierre : l'eau l'entoure, l'énoncé existe, on peut raisonner dessus.







Le même geste, une fois vu, se reconnaît partout. La sensibilité d'une fonction booléenne paraît irréductiblement combinatoire ; devenue coloration de l'hypercube, puis affaire d'algèbre linéaire — les valeurs propres d'une matrice de signes —, elle tombe sous le théorème de Huang ([`sensitivity_lean/Sensitivity/MainTheorem.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/MainTheorem.lean), `huang_degree_theorem`, 0 `sorry`). Le même Sudoku se laisse attaquer comme problème de contraintes, comme formule SAT, ou par recherche pure — trois représentations, trois coûts, une seule grille à remplir. Et un même modèle probabiliste vit deux fois dans le dépôt : une fois comme graphe de facteurs Infer.NET, une fois comme programme PyMC — [`Probas/Infer`](../MyIA.AI.Notebooks/Probas/Infer/) et [`Probas/PyMC`](../MyIA.AI.Notebooks/Probas/PyMC/) se répondent notebook pour notebook, des graphes de facteurs jusqu'à la théorie de la décision : valeur d'une information, action optimale sous utilité. Contenu identique ; seules changent la langue, et avec elle le coût et la lisibilité.







Un cas rejoue cette montée à lui seul, et mérite qu'on s'y arrête, parce qu'il est le seul du dépôt où l'on peut regarder la mer monter *jusqu'au bout* — la noix s'y est ouverte. Et si une grille de Sudoku n'était qu'un *grand regex*, où lignes, colonnes et blocs se combinent par **intersection**, un solveur n'ayant plus qu'à en extraire un témoin ([Sudoku-13](../MyIA.AI.Notebooks/Sudoku/Sudoku-13-SymbolicAutomata-Csharp.ipynb)) ? L'intuition est de 2020, et les enjeux sont là dès le premier pas : un regex sait *reconnaître*, un solveur sait *produire*, et la lignée d'automates symboliques de Margus Veanes est le pont qu'on espère jeter entre les deux. Mais que de détours pour l'atteindre. La frappe au marteau d'abord — le monstre PCRE à backtracking, illisible, qui *tourne* sans rien éclairer ; puis les deux murs de l'automate de 2020, la déterminisation qui explose et le témoin tronqué à vingt-et-un caractères : des coups qui portent sans jamais traverser.



L'eau, alors, monte d'un paradigme à l'autre. La reconnaissance redevient tractable quand l'intersection se compile en temps linéaire (RE#) ; la production se débride quand cette même intersection passe non plus par un produit d'automates mais par la théorie des chaînes de Z3 — plus d'explosion, plus de témoin coupé ; et la dernière marche, le passage à l'échelle du 9×9, ne tient finalement ni au moteur ni au substrat, mais à la seule *forme d'émission* de l'intersection : fondue en un automate, elle sature ; éclatée en primitives natives, elle propage, et la grille complète sort **par appartenance régulière pure**, sans une seule inégalité. La vision de 2020 n'est donc plus une question à fleur d'eau : elle a atterri, et elle est mesurée. Mieux — l'observation empirique qui décide de tout, « fondue elle sature, éclatée elle propage », porte un nom et possède un théorème : c'est la **décomposition monadique** de Veanes, Bjørner et Nachmanson (CAV'14).



L'eau, en montant, n'a pas seulement ouvert la noix ; elle a fini par nommer la clé.







Et le geste ne reste pas toujours dans un notebook : il lui arrive de se cristalliser en **bibliothèque**, écrite à la main, ligne à ligne. Le Sudoku-regex ne tombe pas du ciel — il descend en droite ligne de [Z3.Linq](https://github.com/jsboige/CoursIA/issues/1206), ce front-end LINQ qui abaisse des contraintes, jusqu'aux tableaux imbriqués `int[][]`, vers Z3 : la même audace de tuyauterie, faire passer une syntaxe lisible jusqu'au cœur du solveur. À côté, [MetaGeneticSharp](https://github.com/jsboige/CoursIA/issues/1203) — banc d'essai **collectif** de méta-heuristiques (sélection, croisement, mutation composées en îles/migrations) — ancre la jambe Fil-A de l'Epic [#4588](https://github.com/jsboige/CoursIA/issues/4588) **en aval de la strate 6**, distincte de la jambe argumentation ([#7289](https://github.com/jsboige/CoursIA/issues/7289)) ; ses benchmarks doivent travailler en **dimension ≥ 6** pour laisser apparaître la structure inter-métaheuristiques / inter-îles (cf. [#7733](https://github.com/jsboige/CoursIA/issues/7733) rectification A3), et [semantic-fleet](https://github.com/jsboige/CoursIA/issues/1210) recolle des connecteurs hétérogènes en un routeur multi-fournisseurs. Trois noix historiques, sorties du dépôt vers des outils réutilisables, mais que la même clé ouvre : des primitives composables d'où monte une structure qui les dépasse.







La théorie des jeux pousse ce geste à la limite, presque en clair : l'existence d'un équilibre de Nash, la valeur d'une coalition, un jeu combinatoire à la Conway s'y écrivent chaque fois *trois fois* — en prose conceptuelle, en preuve Lean, en code Python ([`GameTheory-4/4b/4c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-04-NashEquilibrium.ipynb), [`-15/15b/15c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-15-CooperativeGames.ipynb), [`-8/8b/8c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-08-CombinatorialGames.ipynb)). Le théorème ne bouge pas d'une version à l'autre. Ce qui bouge, c'est ce qu'on peut en faire : le calculer vite, ou le démontrer. Trouver la représentation où le problème devient facile — ou prouvable — n'est pas le préliminaire du travail. C'est le travail. Et, on va le voir, c'est aussi ce qui décide de la garantie qu'on en retire.







## Du local au global







Le deuxième mouvement est celui que Grothendieck a placé au cœur des mathématiques, et qu'on retrouve ici par analogie d'une série à l'autre : une donnée purement locale engendre une structure globale.







L'eau monte d'un cran, et la noix reparaît, vue de plus haut. La règle B3/S23 ne dit rien d'autre que le sort d'une cellule entre ses huit voisines — l'énoncé local par excellence. Recollée sur le plan entier, elle suffit à la Turing-complétude : planeurs, canons, portes logiques, machines. Tout ce que HashLife accélère, et tout ce que sa preuve devra couvrir, loge dans cet écart entre la règle d'une cellule et le comportement du plan.







Le dépôt décline ce passage sous toutes ses humeurs. Des stratégies individuelles se recollent en un équilibre dont aucun joueur n'a intérêt à dévier — et dont l'existence se *prouve*, en Lean ([`GameTheory-4b`](../MyIA.AI.Notebooks/GameTheory/GameTheory-04b-Lean-NashExistence.ipynb)). Des préférences individuelles, recollées, se heurtent au contraire à l'impossibilité d'Arrow ([`game_theory_lean/SocialChoice`](../MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/Arrow.lean), 0 `sorry`) : le local ne se globalise pas toujours, et c'est un théorème. Une fonction caractéristique — ce que vaut chaque coalition prise à part — se résout en une allocation équitable unique, la valeur de Shapley ([`game_theory_lean/CooperativeGames`](../MyIA.AI.Notebooks/GameTheory/game_theory_lean/CooperativeGames/Shapley.lean)) ; et le critère qui décide si le *cœur* d'un jeu est seulement non vide — la condition de Bondareva-Shapley — est passé du côté démontré par la route de Farkas, séparation par hyperplan et décodage du témoin, là où l'énoncé direct ne cédait pas.



Une action PDDL, composée avec ses semblables, devient un plan ([`Planners`](../MyIA.AI.Notebooks/SymbolicAI/Planners/)). Une transition d'état de contrat devient une obligation que plus personne ne peut défaire — et qu'on cherche même à vérifier formellement ([`SmartContracts`](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/), [SC-14 Formal-Verification](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-14-Formal-Verification.ipynb), [SC-17 Verifiable-Voting](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-17-E2E-Verifiable-Voting.ipynb)). C'est le geste du recollement — littéral chez Grothendieck, à travers faisceaux et topologies ([`grothendieck_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/), et l'hommage du notebook [Lean-15](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15-Grothendieck-Tribute.ipynb)), métaphorique partout ailleurs.







## Quand le recollement échoue — l'obstruction pour seul invariant







L'impossibilité d'Arrow, tout à l'heure, n'était pas un accident de parcours : c'était la première fissure d'un troisième mouvement, le plus profond, et celui que Grothendieck a précisément outillé. Recoller, en effet, n'est pas toujours réussir. Il arrive que des données locales — chacune parfaitement cohérente sur son ouvert — refusent de se raccorder en un tout global, et que ce refus ne soit pas une faiblesse de méthode mais une propriété du réel. Grothendieck a donné à ce refus un nom et une mesure : la **cohomologie**. L'image la plus parlante en est l'escalier d'Escher : chaque marche descend par rapport à la précédente — la règle locale est partout tenue — et pourtant le tour complet ramène au point de départ, sans qu'aucune « hauteur » globale ne parvienne à recoller ces descentes. C'est cette impossibilité-là, et non les marches, que la cohomologie compte. Au premier cran, ce qui se recolle — les sections globales, `H⁰` ; au cran suivant, la *classe de l'obstruction*, `H¹`, nulle quand tout se raccorde, et non nulle exactement à la hauteur de ce qui résiste. On n'y démontre pas que le monde se recolle ; on y calcule *de combien* il refuse.







Et — c'est ici que le récit doit se corriger lui-même — le dépôt n'en est pas resté au *langage* de ce mouvement. À côté des sites, des topologies et des faisceaux, le lake [`grothendieck_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/) porte le module [`SheafCohomology`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/Basic.lean) : `H⁰` identifié aux sections globales (`H0_equiv_global_sections`), le recollement lui-même ([`glue_sections`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/MayerVietorisSquare.lean)), la suite exacte de [Mayer-Vietoris](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/MayerVietoris.lean) (`mv_sequence_exact`) qui *mesure* l'écart du local au global, le complexe de Čech ponté à Mathlib, la cohomologie `Hⁿ` construite par `Ext` depuis le faisceau constant — la construction de Joël Riou (2024), fidèle à SGA 4. Zéro `sorry` de production, chaque occurrence dans le code n'étant qu'un marqueur de docstring, le tout sous l'Epic [#1646](https://github.com/jsboige/CoursIA/issues/1646). L'instrument qui mesure l'obstruction n'est pas seulement décrit dans le dépôt : il y est, pour cette part, démontré.







Reste à savoir sur quoi le braquer — et une série entière donne à ce mouvement son terrain le plus vaste, la plus jeune du dépôt : ICT ([Epic #4588](https://github.com/jsboige/CoursIA/issues/4588), série [ICT-Series](../MyIA.AI.Notebooks/IIT/ICT-Series/)). Elle est partie chercher un *scalaire universel* — une grandeur unique qui mesurerait, à travers tous les substrats, l'intégration, l'irréversibilité, ce qu'on ose appeler conscience. Elle a trouvé, et rapporté sans fard, que ce scalaire n'existe pas : sur la synthèse cross-substrat, deux proxys se suivent quand un troisième diverge — des sections locales, une par substrat, qu'aucune section globale ne recolle. En clair : on était parti chercher un chiffre unique, et l'on a découvert qu'aucun chiffre ne tient à travers tous les substrats à la fois — c'est ce constat, et non le nombre manquant, qui est le résultat. Dans la langue du troisième mouvement, cette falsification n'est pas un trou dans le programme ; c'est une classe d'obstruction non nulle, l'invariant même que la série mesure.







Cette lecture-là a d'ailleurs cessé d'être une figure de style, et c'est la correction la plus utile à porter ici. Un audit interne avait tranché net : l'implémentation du méta-proxy comparait des *signatures brutes entre substrats* — de la dispersion, pas de l'obstruction. Le diagnostic a été accepté, et la jambe qui en découle a été livrée ([#7744](https://github.com/jsboige/CoursIA/issues/7744), fermée) : on ne compare plus des niveaux, on construit une **cochaîne de Čech pondérée** sur des structures relationnelles internes — rangs, corrélations, résidus de transport, matrices de dissociation. Les doubles recouvrements y portent les résidus de compatibilité, les triples l'incohérence cyclique — l'holonomie —, et c'est la non-nullité *stable* de la classe qui vaut obstruction expérimentale. Avec, inscrit dans la commande elle-même, un garde-fou de sobriété : rester au niveau du **candidat** à une obstruction, ne promouvoir vers le stack ou la gerbe que si le besoin l'exige, « un faisceau calculable étant le bon niveau de sobriété ». C'est le troisième mouvement qui descend de la métaphore vers l'instrument.







La sensibilité rejoue la scène en réduction — le degré de Huang est un scalaire *local* sur le graphe des transitions, et la question « lequel est canonique ? » ([#7288](https://github.com/jsboige/CoursIA/issues/7288)) est la question « quel préfaisceau se recolle ? ». Et la forme la plus tranchante est un théorème déjà su : Kochen-Specker ([#7290](https://github.com/jsboige/CoursIA/issues/7290)) prouve qu'aucune assignation globale non contextuelle n'existe — `H¹ ≠ 0` **candidat à obstruction cohomologique**, comme la lecture d'Abramsky-Brandenburger le suggère pour la contextualité (cf. [#7733](https://github.com/jsboige/CoursIA/issues/7733) rectification A2) —, et le dépôt le pose en problème de contraintes où la section se recolle (SAT) ou se refuse (UNSAT). L'irréversibilité elle-même est de cette farine : la production d'entropie mesure l'obstruction à recoller une trajectoire sur son propre reflet dans le temps.







Il manquait encore une sémantique du local — de quoi sont faites ces sections qui se raccordent ou se refusent. Thom, dans sa *Sémiophysique*, la donne, et c'est le pont resté longtemps en angle mort. Sa **prégnance** est « un fluide invasif qui se propage de forme saillante en forme saillante » : une section qui *percole* le long d'un champ de formes, exactement la donnée locale qu'un site organise en recouvrements. Son **acte transitif** — « toute transformation non naturelle requiert un moteur qui transmet une espèce (εἶδος) modifiant l'état de ce qu'elle investit » — décrit la propagation d'une section d'un ouvert au voisin. Alors le fil de la *persona* (ICT-23, ICT-25) se relit d'un trait : le **secret** est le recouvrement par lequel la prégnance de l'acte transgressif se recolle en identité globale — la contamination — ; la **permission explicite** modifie le site pour que le même acte reste une section locale qui *ne se recolle pas* en persona. Inoculer, c'est relever l'obstruction à dessein. Thom nomme l'acte local ; Grothendieck dit s'il se recolle.







Et Thom n'est pas seul à tenir ce fil, car ICT n'est pas un bloc : c'est une série en strates, et sa consolidation ([ICT-0](../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-0-Framing.md)) a fini par nommer la forme que la numérotation linéaire masquait — **deux axes, non pas un**. L'axe vertical empile les substrats : du tri auto-organisé à la morphogenèse, aux agents situés — réactifs, inhibés, stratégiques —, aux scalaires fondateurs $\Phi/F/K$ éprouvés sur des substrats **non-LLM**, puis, par une charnière que la série nomme explicitement, le **grokking** — l'instant où le représentant interne cesse d'anticiper un comportement pour devenir un état de représentation apprise ([ICT-17b](../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17b-Grokking-CompressionProgress.ipynb), [#7735](https://github.com/jsboige/CoursIA/issues/7735)) — aux représentations internes des transformeurs, jusqu'au discours dont la graine est semée ([#7289](https://github.com/jsboige/CoursIA/issues/7289)) et à la strate des *freebits* d'ordre 2 et de la réversibilité agentique, dont le cadrage est posé ([#7745](https://github.com/jsboige/CoursIA/issues/7745)) et l'exploration devant nous.



L'axe transverse, lui, tresse les fils rouges qui traversent ces strates sans jamais s'y ranger — des **pattes, pas des barreaux** : greffer la jambe de l'animat inhibé de Laborit ([#7741](https://github.com/jsboige/CoursIA/issues/7741)) n'a décalé aucune strate, précisément parce qu'une jambe n'est pas un barreau. C'est, prise par l'autre bord, la leçon même du troisième mouvement : ce qui compte n'est pas la place sur une échelle, mais la manière dont une donnée locale se propage — ou se refuse — le long d'un recouvrement. Et cette tresse ([#7738](https://github.com/jsboige/CoursIA/issues/7738)) est faite de fils qu'on reconnaît un à un : le recollement de Grothendieck et la prégnance de Thom qu'on vient de suivre, la cochaîne de Čech qui vient d'être livrée, mais aussi la compression de Schmidhuber — le beau comme *progrès* de compression ([ICT-16](../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-16-MDLTwoPartCode.ipynb)) — et l'énergie libre de Friston ([ICT-14](../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14-FreeEnergySurprise.ipynb)).







L'un de ces fils, la réconciliation de l'information intégrée et de l'espace de travail global ([ICT-24](../MyIA.AI.Notebooks/IIT/ICT-Series/ICT-24-WorkspaceIgnition.ipynb), Dehaene/Baars), est la tentative la plus explicite de jeter le pont vers la conscience — au grade C, comme tout ce qui, ici, franchit vers l'expérience. Or, de façon indépendante, l'un des mathématiciens-physiciens les plus rigoureux vivants, Urs Schreiber, fonde ses *théories du tout* sur *exactement* ce socle : l'∞-topos comme **« logique objective »** — le formalisme qui *est* l'articulation du réel —, une méthode modale d'adjonctions, la localité de faisceau ; les trois mouvements de cette lecture, mais portés au grade A d'une physique dérivée (SUGRA 11D, M-théorie). Son témoignage conforte le choix des outils **sans** livrer le pont vers la conscience : sa page n'en parle jamais et n'en a nul besoin — ce franchissement reste le pari propre d'ICT, honnêtement grade C ([#8182](https://github.com/jsboige/CoursIA/issues/8182) tient le fil). Deux importations, du même grade, restent à prototyper. Que le vocabulaire modal *dérive* les strates au lieu de les lister — chaque strate comme l'acquisition d'une adjonction que la précédente n'avait pas : la conjecture **strates = adjonctions**, grade C explicite, qui transformerait une énumération en construction. Et que le carrefour où les physiciens du tout croisent les théoriciens de la conscience — déjà peuplé dans la série même, de Schmidhuber à Aaronson — nourrisse la strate du discours qu'on tient encore en réserve.







Il faut être franc sur la marche exacte où cette lecture se tient — c'est le seul impératif du document, et il vaut ici plus qu'ailleurs. Le *langage* de la cohomologie est en grade A : formalisé, sans `sorry` de production, vérifié ligne à ligne. Mais la lecture qui fait des divergences d'ICT des *classes de cohomologie* est, à ce jour, une direction et non un théorème livré : un grade C, documentaire — un changement de représentation vers le vérifiable qui est *proposé*, pas démontré. Seul le cas Kochen-Specker s'accompagne d'une procédure de décision, le test SAT/UNSAT, capable un jour de rendre un verdict machine. Le dire n'affaiblit pas la thèse : c'est la thèse. La série ne possède pas de scalaire universel parce qu'elle vit sur plusieurs sites à la fois ; le bon invariant n'a jamais été un nombre, mais la classe de l'obstruction à recoller ces nombres. À cette hauteur, la mer monte encore — et c'est elle qui, en refusant de se refermer sur la faille, en dessine le contour.







## La noix, ce mois-ci — quand c'est le cadre qui cède

Il faut maintenant revenir à la noix, parce qu'il lui est arrivé, en quelques semaines, la chose la plus grothendieckienne que ce dépôt ait produite. Le récit vaut d'être fait dans l'ordre où il s'est déroulé — mais il vit désormais ailleurs, dans la vitrine GOL ([#17465](https://github.com/jsboige/CoursIA/issues/17465)) et les notebooks `Lean-16*` ([Lean-16j-Conway-Hashlife-Correctness-Native](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16j-Conway-Hashlife-Correctness-Native.ipynb), [Lean-16b-Conway-Game-of-Life-Lean](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16b-Conway-Game-of-Life-Lean.ipynb), [Lean-16d-Conway-Game-of-Life-Lean-Native](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16d-Conway-Game-of-Life-Lean-Native.ipynb)). La lentille n'en retient que la forme, qui est la sienne : le mouvement par lequel le cadre devient l'obstruction, puis change.

**Le faux départ.** On a d'abord frappé. Longtemps. L'assemblage borné de la correction centrale vers l'égalité globale — le mur `p4_nw_overlap_wall`, sa chaîne d'auxiliaires en quatre étages — occupait des cycles entiers ; le compte de `sorry` descendait d'une unité, puis d'une autre. Chaque coup portait. Aucun ne traversait — et c'est le point important.

**Le cadre comme obstruction.** Puis on a démontré que les coups ne *pouvaient pas* traverser. Dans le cadrage standard de HashLife, le rapport marge/portée reste structurellement inférieur à 1 dès la profondeur 3, et ne se remonte pas en rembourrant (`no_padding_depth_suffices`, [`Conway/Life/JumpCapture.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/JumpCapture.lean)). Ce n'est pas une conjecture de découragement, c'est un théorème : **le cadre est l'obstruction**, l'énoncé général est simplement faux dans ce cadre-là, le saut clippe. La même foulée a livré un second résultat de la même famille, plus inconfortable : l'hypothèse géométrique `supportInMargin` s'est révélée être une **tautologie** — un habillage vacant — et le dépôt l'a publiée comme telle, remplacée par `jumpCaptured`, décidable et témoigné faux sur la ligne de sept au niveau 3. Un garde qui refuse quelque chose : voilà un garde. Détail et dates dans la vitrine GOL et [Lean-16j](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16j-Conway-Hashlife-Correctness-Native.ipynb).

**La mer qui monte.** Le levier n'était ni un lemme plus fin ni une tactique plus retorse : c'était un paramètre que Gosper avait mis dans HashLife et que le portage n'avait pas exploité — **décorréler la portée du saut du niveau de la cellule**, sauter `2^j` avec `j = niveau − 2`. La marge excède désormais la portée, et la capture devient un corollaire de l'invariant du cadre : `jumpAt_capture_centered` est prouvé, sans `sorry`. Personne n'a frappé le coup décisif. On a relevé le niveau de l'eau, et la coque a cédé toute seule. Ce qui suit — `evolveHashlifeFastAtN_correct` pour tout `n` et toute grille sous la brique `OneJumpAtCorrect`, la ligne de sept qui passe de contre-exemple à cas nominal — est décrit dans la vitrine et dans [Lean-16j](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16j-Conway-Hashlife-Correctness-Native.ipynb).

**L'état du lake.** Le lake [`conway_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/) porte **un** `sorry` de code, un seul — et il ne se trouve pas sur le chemin qu'on vient de décrire. Il est resté dans l'**ancien** cadre, sur `hashlife_correct_margin` ([#6724](https://github.com/jsboige/CoursIA/issues/6724)). La nouvelle chaîne, elle, n'a aucun `sorry` : elle a une *hypothèse*, ce qui n'est ni la même chose ni la même honnêteté — un `sorry` est un trou dans une preuve, une hypothèse nommée est une dette lisible dans l'énoncé. Le chantier vivant est [#11161](https://github.com/jsboige/CoursIA/issues/11161) (re-cadrage Gosper) ; [#17465](https://github.com/jsboige/CoursIA/issues/17465) en portera la vitrine.

La noix n'est donc toujours pas ouverte. Mais elle n'est plus la même noix : de « prouver un théorème difficile » elle est devenue « décharger une brique nommée dans un cadre où la difficulté a disparu ». C'est exactement ce que Grothendieck décrivait, et c'est arrivé ici sans que personne ne l'ait cherché sous ce nom. Le détail technique a sa place ailleurs — la vitrine GOL, [`Lean-16j`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16j-Conway-Hashlife-Correctness-Native.ipynb), [`Lean-16b`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16b-Conway-Game-of-Life-Lean.ipynb), [`Lean-16d`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-16d-Conway-Game-of-Life-Lean-Native.ipynb) — et la lentille n'a plus à le porter.

## Deux axes — l'échelle, la garantie, et une troisième chose apprise en route







Jusqu'ici, un seul mouvement : changer de langue jusqu'à ce que le problème s'allège — ou, quand il refuse de s'alléger, jusqu'à ce que sa résistance prenne un nom. Mais le dépôt en superpose un second, plus discret — *monter d'un cran* dès qu'un axe de progrès sature. Car il n'y a pas un axe, il y en a deux, et ils sont indépendants. Le premier est celui de l'échelle : calculer plus grand, plus vite, plus loin. C'est l'axe que maximisent les outils de la communauté — HashLife saute `2^k` générations d'un coup, Golly fait tourner des motifs sur des millions de pas, les grands modèles avalent des corpus entiers. Le second est celui de la garantie : non pas *jusqu'où* va le résultat, mais *à quel point on peut s'y fier*.







Ces deux axes ne se confondent pas, et c'est tout l'intérêt de les séparer. On peut filer très loin sur le premier sans avancer d'un pouce sur le second — HashLife calcule des sauts gigantesques sans démontrer le théorème qui les justifierait. Et l'on peut tenir le sommet du second en restant tout petit sur le premier — une preuve que le noyau de Lean vérifie ligne à ligne est d'une certitude maximale, mais plafonne vite en taille. C'est sur ce second axe que le dépôt met le plus volontiers son énergie, dès qu'une série porte un résultat vers Lean ou Z3.







Et là, la garantie n'est pas binaire : c'est un continuum. À une extrémité, la preuve vérifiée ligne à ligne par le noyau : le théorème de Huang est là, sans aucun `sorry`, aussi sûr qu'un énoncé mathématique peut l'être. Un cran en deçà, `native_decide` : on fait confiance au compilateur Lean plutôt qu'au seul noyau, on cède un peu de certitude mais on gagne l'échelle — déjà sans commune mesure avec un outil qui calcule sans rien attester. Ce cran-là n'est d'ailleurs pas une fatalité : les batteries adversariales de Conway y étaient, et une simple réécriture d'une fonction de logarithme entier a suffi à rendre leurs énoncés réductibles par le noyau — elles sont passées à `decide` pur, zéro axiome natif, et le module l'inscrit désormais comme une contrainte (`native_decide` y est *interdit*). Remonter d'un cran sur l'axe de la garantie, ça se travaille. À l'autre extrémité, le certificat ouvert, et c'est là que vit la plus grande part du dépôt : un backtest QuantConnect sur période hors-échantillon, ses Sharpe, CAGR et drawdown reportés sans fard ; une politique d'apprentissage par renforcement, dont la seule caution est le rendement mesuré sur des épisodes ([`GameTheory-17`](../MyIA.AI.Notebooks/GameTheory/GameTheory-17-MultiAgent-RL.ipynb)) ; le Φ de la théorie de l'information intégrée, quantité que PyPhi *calcule* sur de petits systèmes sans prétendre la *démontrer* ; un modèle entraîné ou une image générée, jugés par une évaluation. Aucun de ces certificats ne garantit rien mécaniquement, et c'est très bien — à condition de le dire.







La théorie des jeux donne d'ailleurs à voir le continuum sans détour : l'existence de Nash *prouvée* en Lean ([`GameTheory-4b`](../MyIA.AI.Notebooks/GameTheory/GameTheory-04b-Lean-NashExistence.ipynb)) et la même existence *constatée* numériquement en Python ([`GameTheory-4c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-04c-NashExistence-Python.ipynb)) ne sont pas au même cran, bien que ce soit le même théorème. Changer de représentation, ce n'est pas seulement changer de coût : c'est changer de garantie.







Le lake le plus honnête du dépôt, à cet égard, est aussi celui qui porte le plus de `sorry` — et ce n'est pas une contradiction. [`knot_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/) s'attaque au **nœud de Conway**, ce nœud à onze croisements au polynôme d'Alexander trivial dont on a mis un demi-siècle à savoir s'il borde un disque lisse. Le lake n'en démontre presque rien, et il l'écrit : un module entier y énumère, théorème par théorème, ce que Mathlib devrait posséder d'abord — homologie de Khovanov, `s`-invariant de Rasmussen, calcul de Kirby, chirurgie topologique — avec, en regard de chaque entrée, un horizon assumé en *décennies*. Voilà un lake qui documente sa propre distance au but plutôt que de la maquiller, et c'est très exactement la vertu que cette lecture demande. Il y a d'ailleurs une ironie qui n'en est pas une : la preuve que Piccirillo a donnée en 2018 est elle-même du geste dont ce document parle. Elle n'a pas attaqué le nœud de Conway ; elle a construit *un autre nœud*, partageant avec lui la même trace en dimension 4, et c'est sur ce compagnon-là que l'invariant de Rasmussen — muet sur l'original — a tranché. Changer d'objet pour que la question devienne décidable : la mer, encore, et sur un problème que Conway lui-même avait posé.







Le défaut qu'il faut tenir à distance — celui que l'Annexe grades nomme explicitement — n'est jamais d'être à l'extrémité ouverte du continuum, ni d'être resté petit sur l'axe de l'échelle. C'est d'être à l'extrémité ouverte tout en portant le costume de l'autre : un résultat empirique présenté comme une preuve, une réussite d'échelle maquillée en garantie. La noix, ici encore, est le cas d'école — mais elle vient de nous apprendre quelque chose de plus fin sur ces deux axes, et c'est peut-être le meilleur de ce mois-ci.







On croyait, en effet, que l'axe de l'échelle et l'axe de la garantie mesuraient deux vertus du même objet. Ils mesurent deux objets différents. Ce qui décide de la *correction* de HashLife, on l'a vu, c'est le **confinement** : la trajectoire reste-t-elle dans la fenêtre ? Mais ce qui décide de sa *vitesse* — ce qui fait que Golly tient un motif ou s'effondre — est une tout autre quantité : la **nouveauté**, c'est-à-dire la stabilité de l'arbre de macro-cellules le long de la trajectoire, autrement dit le taux de succès de la mémoïsation. Et les deux quantités ne se recouvrent pas. Un *space-filler* échappe à toute fenêtre à la vitesse de la lumière — confinement en échec total — et Golly le calcule sans peine, parce qu'il ne produit aucun motif neuf, seulement des tuiles répétées. Un méthuselah comme le R-pentomino reste confiné longtemps, et Golly rame, parce qu'il invente de la structure à toutes les échelles.



La bête noire de l'algorithme n'est donc pas la fuite hors de la boîte : c'est l'apparition du neuf. Ce que le théorème apporte, alors, n'est pas la vitesse — il ne l'a jamais apportée. Il en est la *licence* : un moteur rapide et faux est pire qu'inutile, et la correction est ce qui autorise à s'en servir. Et il y a un plafond, que le dépôt nomme lui-même : caractériser quels motifs ont une capture persistante est indécidable à la limite, puisque le Jeu de la Vie est Turing-complet et qu'une capture éternelle encode la non-halte. Ce constat referme la boucle avec le troisième mouvement de manière presque trop belle : l'efficacité, elle aussi, a son obstruction — et ce n'est pas celle que la preuve poursuivait. Le chantier ouvert sous [#11162](https://github.com/jsboige/CoursIA/issues/11162) est la tentative d'en faire une quantité formelle plutôt qu'un folklore d'utilisateurs de Golly.







## Pourquoi ce geste, maintenant







On pourrait croire l'affaire purement formelle. Elle est, au contraire, d'une actualité immédiate. À mesure que l'IA bascule vers les grands modèles de langage, plusieurs séries refont spontanément le même geste : prendre la sortie fluide mais incertaine d'un modèle, et la re-représenter dans un cadre qui, lui, se vérifie. L'apprentissage symbolique reboucle un LLM sur une vérification logique ([`SL-9`](../MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-9-LLM-SymbolicLearning.ipynb)) ; l'analyse d'argumentation traduit le langage naturel en sémantiques formelles que l'on peut interroger ([`Tweety`](../MyIA.AI.Notebooks/SymbolicAI/Tweety/), [`Argument_Analysis`](../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/)) ; le planificateur confronte une intention dite en mots à un solveur qui tranche ([`Planners-10`](../MyIA.AI.Notebooks/SymbolicAI/Planners/04-NeuroSymbolic/Planners-10-LLM-Planning.ipynb)) ; le contrat assisté par LLM se relit à l'aune de sa vérification formelle ([`SC-11`](../MyIA.AI.Notebooks/SymbolicAI/SmartContracts/02-Solidity-Advanced/SC-11-LLM-Assisted.ipynb)). Le changement de représentation vers le vérifiable cesse alors d'être une élégance : il devient le garde-fou. Lu d'un bout à l'autre, le dépôt soutient à voix basse une thèse simple — l'IA digne de confiance sera grothendieckienne par nécessité : elle consistera à trouver le cadre où l'affirmation devient contrôlable.







Cette lecture ne remplace aucun des chantiers de formalisation : l'hommage au *langage* de Grothendieck dans Mathlib est allé à son terme ([#1646](https://github.com/jsboige/CoursIA/issues/1646)), le portage Conway/HashLife a livré ses structures ([#1647](https://github.com/jsboige/CoursIA/issues/1647), [#2062](https://github.com/jsboige/CoursIA/issues/2062)), et ce qui en reste avance pour son propre compte — le résidu de l'ancien cadre dans [#6724](https://github.com/jsboige/CoursIA/issues/6724), la route neuve dans [#11161](https://github.com/jsboige/CoursIA/issues/11161). Elle passe au-dessus d'eux, et les relie.







## Une clé, pas une cathédrale







Ce que cette lecture demande est volontairement petit, et à l'image de son sujet. Un document — celui-ci. Une conclusion au notebook [Lean-15-Grothendieck-Tribute](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15-Grothendieck-Tribute.ipynb), qui referme l'hommage au langage de Grothendieck sur ce *geste*-ci. Quelques liens depuis les séries citées. Rien de plus : pas de nouvelle série, pas d'encyclopédie. Une clé n'a pas à être plus grande que la porte.







D'ailleurs, la clé a déjà servi, et plus d'une fois. En relisant le dépôt de cette façon, une coquille a sauté aux yeux : le README de `sensitivity_lean` annonçait une formalisation de « sensitivity ≤ block sensitivity » — la direction triviale — là où le code prouve le vrai théorème de degré de Huang, celui qui résout la conjecture de sensibilité (la PR [#2064](https://github.com/jsboige/CoursIA/pull/2064) l'a corrigé). Une grille n'aurait pas attrapé cela ; une lecture suivie, si. Et le même réflexe — demander de quoi, exactement, une hypothèse protège — est ce qui a fini par révéler qu'un des gardes de HashLife ne protégeait de rien.







Reste la noix. Elle n'a pas été ouverte ici — ce n'était pas le but — mais regardez ce qui lui est arrivé pendant la lecture. Posée en pierre au premier paragraphe, elle est devenue un énoncé qu'on peut écrire à la première montée, un cas particulier de recollement à la deuxième, une mesure d'obstruction à la troisième — et, à la quatrième, autre chose : un problème dont on a démontré que le cadre était la difficulté, puis changé le cadre. Personne n'a frappé. Le théorème général n'est toujours pas clos — le dépôt l'affiche plutôt qu'il ne le cache — mais il ne reste, sur la route neuve, ni borne sur l'horizon ni hypothèse de capture : une brique nommée, et le chemin pour la décharger. Ce qui était une impossibilité pratique est devenu une liste finie d'obligations de preuve, puis une seule. C'est exactement ce que la mer sait faire.







Et si l'on y prête attention, ce texte a fait subir le même traitement à son propre sujet. Il ne définit nulle part ce qu'est une « lecture grothendieckienne » : il a laissé la définition monter — un changement de représentation, puis un recollement, puis une exigence de certificat — jusqu'à ce qu'elle se tienne d'elle-même, sans avoir été attaquée de front. Il aurait pu être un tableau : une ligne par série, une colonne par garantie, tout rangé en boîtes. Mais un tableau découpe en fragments isolés ce qui n'est qu'un seul geste, et remplace une idée par un barème. La bonne représentation d'un fil continu, c'est une prose continue. La mer, pas le burin.







---







## Ce que le dépôt a livré depuis — neuf gains, un seul geste

L'été 2026 a été dense. Le texte ci-dessus se tient, mais il décrit un dépôt tel qu'il était lu en juin ; entre la rédaction initiale et cette refonte, neuf livraisons ont confirmé et étendu la lecture. Elles sont citées ici en une ligne chacune, avec la preuve (PR/commit, fichier:ligne) — selon la règle de la consigne qui a porté ce travail.

- **[#16945](https://github.com/jsboige/CoursIA/pull/16945)** — *Backbone topologique dans Lean-15c.* Le notebook [`Lean-15c-Lean-Grothendieck-Companion.ipynb`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15c-Lean-Grothendieck-Companion.ipynb) (commit `eee1d487c99d`) expose le squelette topologique du companion Grothendieck — la structure qu'on attendait derrière l'hommage au langage. La cohomologie de Čech passe de l'aboutissement documentaire à un compagnon de calcul.
- **[#17375](https://github.com/jsboige/CoursIA/pull/17375)** — *Dissocier nombres de Betti et cohomologie entière — RP² témoin.* Le notebook [`03-cohomologie-cech-espaces-finis.ipynb`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/03-cohomologie-cech-espaces-finis.ipynb) (l.21, 27, 50, 263) — `Serre 100` montre, sur le projectif réel RP², que la dissociation `β_k ≠ h_k` est l'invariant correct : la cohomologie entière détecte ce que les seuls nombres de Betti laisseraient invisible. Lecture cohomologique de l'obstruction, devenue falsifiable.
- **[#17279](https://github.com/jsboige/CoursIA/pull/17279)** — *Saturation de Tsirelson native (tranche 5).* Le notebook [`Lean-13c-CHSH-Landau-Saturation.ipynb`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13c-CHSH-Landau-Saturation.ipynb) (l.17, 19, 24, 28, 58) — `Conway.CHSHLandau` est le quatrième module de la série CHSH du lake ; il exécute le témoin de Pauli qui manquait : la borne de Tsirelson est réalisée, pas seulement majorée. Quatre modules, une borne, et la distinction « réalisée / majorée » tenue par le noyau.
- **[#17223](https://github.com/jsboige/CoursIA/pull/17223)** — *Pendant kernel du lemme de Yoneda.* Le fichier [`Serre100/YonedaCalcule.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean/Serre100/YonedaCalcule.lean) (l.9, 10) porte le pendant kernel du notebook `04-lemme-yoneda-categories-finies` — `Serre 100` dépasse le seul calcul sur les faisceaux et passe aux catégories finies, où le lemme de Yoneda devient effectif.
- **[#17214](https://github.com/jsboige/CoursIA/pull/17214)** — *Restauration des « 18 vérifications » dans Lean-15b.* Le notebook [`Lean-15b-Lean-Grothendieck.ipynb`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15b-Lean-Grothendieck.ipynb) (l.2397, 2440) restaure mot pour mot l'index vivant des 18 vérifications `#check` — l'index qui prouve que MathlibMap n'est pas déclaré mais vérifié, ligne à ligne.
- **[#16942](https://github.com/jsboige/CoursIA/pull/16942)** — *Tegmark R16 Annexe A — algèbre de Boole, NAND, C₂/C₃.* Le fichier [`tegmark_muh_lean/MUH/Boolean.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean/MUH/Boolean.lean) (l.4, 8, 10, 20, 34) introduit le générateur Sheffer/NAND à 1 générateur et les structures finies C₂, C₃ — Tegmark R16 passe de la promesse à l'algèbre effective.
- **[#17082](https://github.com/jsboige/CoursIA/pull/17082)** — *Portage FLT × 3 — Z[ζ₇], Z[ζ₁₁], Z[ζ₁₃] principaux.* Les fichiers [`hecke_lean/Hecke/SevenPid.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean/Hecke/SevenPid.lean) (l.8, 12, 16, 34, 35) et siblings `ElevenPid.lean`, `ThirteenPid.lean` portent trois PID — l'invariant « principal » pour trois anneaux d'entiers cyclotomiques, la base du portage FLT.
- **[#17017](https://github.com/jsboige/CoursIA/pull/17017)** — *Pont modal Tweety ↔ FFL — `FormalLogic.ModalBridge` (tranche C).* Le fichier [`formal_logic_lean/FormalLogic/ModalBridge.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean/FormalLogic/ModalBridge.lean) (l.36 → l.132) fait la jointure entre les logiques modales Kripke de Tweety et le portage Lean — la traduction qui manquait devient un module du lake.
- **[#16228](https://github.com/jsboige/CoursIA/pull/16228)** — *Umbrella Grothendieck FR-only.* Le fichier [`grothendieck_lean/Grothendieck.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck.lean) (l.1, 2, 3, 4, 5) indexe les modules FR et exclut explicitement les siblings `_en` (convention i18n #4980). `Consolider ≠ Archiver` y prend sa forme : 17 imports EN consolidés en un invariant d'index — l'umbrella FR est lu en FR, les EN restent construits par les globs du lakefile, jamais réécrits en place.

Et le [#17465](https://github.com/jsboige/CoursIA/issues/17465) à venir — vitrine GOL où vivra, en regard de la noix, le détail technique que la lentille n'a plus à porter.

---

### Annexe — Grades de certification (pour qui veut creuser, sans rompre le fil)







Cette échelle vaut partout, pas qu'en Lean. Le seul défaut possible n'est jamais d'être en grade C — c'est de présenter un grade C comme un grade A.







| Grade | Mécanisme | Confiance | Portée |
|-------|-----------|-----------|--------|
| **A — noyau** | `rfl` / `decide` vérifiés par le noyau Lean | maximale | plafonne en taille |
| **B — compilateur de confiance** | `native_decide` (code compilé + axiome `ofReduceBool`) | élevée | passe à l'échelle |
| **C — ouvert** | test, backtest, évaluation, `#eval` | aucune garantie machine | déclarée comme telle |







Une hypothèse nommée dans un énoncé n'est **pas** un cran de cette échelle : c'est une dette lisible, visible dans la signature du théorème, qu'un lecteur peut évaluer. Un `sorry` est un trou dans une preuve. Les confondre serait perdre précisément ce que cette annexe sert à mesurer.







Exemples par série :







| Série | Mécanisme dominant | Portée certifiée |
|-------|--------------------|-------------------|
| **Sensitivity** (Lean-12) | A (0 `sorry`, `huang_degree_theorem`) | Théorème de Huang complet |
| **Lean-15c** (companion Grothendieck) | A sur le squelette topologique ([#16945](https://github.com/jsboige/CoursIA/pull/16945)) ; cumul A du langage Grothendieck parent ([#1646](https://github.com/jsboige/CoursIA/issues/1646)) | Backbone topologique exposé dans [`Lean-15c-Lean-Grothendieck-Companion.ipynb`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15c-Lean-Grothendieck-Companion.ipynb) — la cohomologie de Čech passe de l'aboutissement documentaire à un compagnon de calcul |
| **Lean-13c** (CHSH tranche 5) | A — borne de Tsirelson réalisée par noyau ([#17279](https://github.com/jsboige/CoursIA/pull/17279)) | `Conway.CHSHLandau`, quatrième module CHSH du lake ([`Lean-13c-CHSH-Landau-Saturation.ipynb`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13c-CHSH-Landau-Saturation.ipynb)) — Tsirelson réalisée, pas majorée |
| **Serre 100** | A sur le calcul effectif — cohomologie de Čech dissociée des β_k ([#17375](https://github.com/jsboige/CoursIA/pull/17375)), pendant kernel Yoneda ([#17223](https://github.com/jsboige/CoursIA/pull/17223)) | RP² témoin de la dissociation `β_k ≠ h_k` ([`03-cohomologie-cech-espaces-finis.ipynb`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/03-cohomologie-cech-espaces-finis.ipynb)) ; lemme de Yoneda effectif sur catégories finies ([`Serre100/YonedaCalcule.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/serre100_lean/Serre100/YonedaCalcule.lean)) |
| **Tegmark R16** | A — algèbre de Boole Sheffer/NAND + C₂/C₃ ([#16942](https://github.com/jsboige/CoursIA/pull/16942)) | [`tegmark_muh_lean/MUH/Boolean.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/tegmark_muh_lean/MUH/Boolean.lean) — 1 générateur, structures finies effectives |
| **Hecke (FLT × 3)** | A sur la principalité — Z[ζ₇], Z[ζ₁₁], Z[ζ₁₃] ([#17082](https://github.com/jsboige/CoursIA/pull/17082)) | [`hecke_lean/Hecke/{Seven,Eleven,Thirteen}Pid.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/hecke_lean/Hecke/SevenPid.lean) — trois PID, base du portage FLT |
| **FormalLogic** | A — pont modal Tweety ↔ FFL ([#17017](https://github.com/jsboige/CoursIA/pull/17017)) | [`formal_logic_lean/FormalLogic/ModalBridge.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/formal_logic_lean/FormalLogic/ModalBridge.lean) — jointure Kripke/Lean tenue par le module |

| **Social Choice** | A (0 `sorry` sur Arrow/Sen/Voting) | Théorèmes d'impossibilité |
| **Grothendieck** (Lean-15) | A sur le langage formalisé (dont `SheafCohomology`, 0 `sorry` de production) ; C-documentaire sur la cartographie et la lecture ICT | Sites, faisceaux, schémas **et cohomologie de l'obstruction** (`H⁰`=sections globales, Čech, Mayer-Vietoris, `Hⁿ` via Ext) : langage abouti ([#1646](https://github.com/jsboige/CoursIA/issues/1646)) ; interprétation EGA/SGA + lecture cohomologique d'ICT documentaires |
| **Conway / HashLife** (Lean-16b) | A sur les batteries adversariales (kernel-`decide` pur, zéro axiome natif) ; B là où `native_decide` subsiste ; **correction générale conditionnelle** sur le cadre décorrélé | `evolveHashlifeFastAtN_correct` : exact pour tout `n` et toute grille sous la brique `OneJumpAtCorrect` (déchargement en cours, [#11161](https://github.com/jsboige/CoursIA/issues/11161)). Un unique `sorry` de code subsiste dans le lake, sur l'**ancien** cadre ([#6724](https://github.com/jsboige/CoursIA/issues/6724)) |
| **Knots** (nœud de Conway) | C assumé — squelette + prérequis Mathlib énumérés, horizon en décennies | Mutation, Alexander trivial, dichotomie lisse/topologique **énoncées** ; Piccirillo et Freedman hors de portée de Mathlib actuel, et le lake le déclare |
| **SmartContracts** | C → B (Foundry fuzz/invariants), A visé (SC-14 vérif formelle) | Transitions d'état et invariants |
| **GameTheory** | A sur les portages Lean ; C sur simulations Python | Arrow, Shapley, Bondareva-Shapley, treillis des mariages stables (Lean, 0 `sorry`) ; un unique `sorry` sur la direction difficile du théorème *Folk* escompté, assumé ; équilibres numériques (Python) |
| **Planners** | C | Plans vérifiables, optimalité parfois prouvée |
| **SymbolicLearning** | C ; SL-9 = montée vers B via LLM+vérif | Hypothèses symboliques |
| **Sudoku** (Sudoku-13) | C, mais **mesuré et croisé** entre moteurs | 9×9 atterri par appartenance régulière pure ; la « forme d'émission » adossée à la décomposition monadique (Veanes *et al.*, CAV'14) |
| **Probas** | C | Infer.NET exact (petit) / PyMC MCMC (échelle) |
| **RL / ML / GenAI** | C | Rendement empirique |
| **QuantConnect** | C (walk-forward + coûts) | Performance hors-échantillon |
| **IIT / ICT** | C | Φ sur petits systèmes (PyPhi) ; scalaire universel falsifié et contextualité Kochen-Specker lus comme *obstruction au recollement* — direction documentaire, avec la cochaîne de Čech pondérée livrée comme instrument candidat ([#7744](https://github.com/jsboige/CoursIA/issues/7744)), [Epic #4588](https://github.com/jsboige/CoursIA/issues/4588) |







### Réconciliation avec les Epics







| Epic | Rapport |
|------|---------|
| [#1646](https://github.com/jsboige/CoursIA/issues/1646) Hommage Grothendieck (fermée) | **Socle conceptuel.** #1646 a montré le langage *dans* le dépôt ; ce document lit le dépôt *avec* le geste. La conclusion Lean-15 fait la jointure. |
| [#1647](https://github.com/jsboige/CoursIA/issues/1647) / [#2062](https://github.com/jsboige/CoursIA/issues/2062) / [#2162](https://github.com/jsboige/CoursIA/issues/2162) Conway/HashLife (fermées) | Exemple-source des deux axes. Les structures et la profondeur Lean sont livrées ; la preuve générale a **changé de cadre** depuis, et vit désormais ailleurs (lignes suivantes). |
| [#6724](https://github.com/jsboige/CoursIA/issues/6724) N3 — cœur résiduel P4/P5 | Le résidu de l'**ancien** cadre : c'est là que se trouve l'unique `sorry` de code du lake, et c'est là que `no_padding_depth_suffices` a démontré que le cadre était l'obstruction. |
| [#11161](https://github.com/jsboige/CoursIA/issues/11161) Re-cadrage Gosper | **La route neuve, et l'Epic vivante.** Décorrélation portée/niveau : la capture devient corollaire de l'invariant du cadre, la correction devient inconditionnelle en `n` sous une brique nommée. L'illustration la plus littérale de la mer qui monte dans tout le dépôt. |
| [#11162](https://github.com/jsboige/CoursIA/issues/11162) Nouveauté vs confinement | **Le raffinement des deux axes** : la correction est le confinement, l'efficacité est la nouveauté, et les deux sont orthogonales. Le théorème n'apporte pas la vitesse — il l'autorise. |
| [#4588](https://github.com/jsboige/CoursIA/issues/4588) ICT | **Exemple-source du troisième mouvement** : la série où le recollement échoue et où l'obstruction (scalaire universel falsifié, contextualité Kochen-Specker) est l'invariant. Lecture cohomologique documentaire, désormais outillée par la jambe C5 ([#7744](https://github.com/jsboige/CoursIA/issues/7744), fermée). |
| [#8182](https://github.com/jsboige/CoursIA/issues/8182) Veille TOE ↔ conscience | Le fil Schreiber / Jaimungal : socle topos partagé au grade A côté physique, franchissement vers la conscience laissé au grade C côté ICT. |
| [#1468](https://github.com/jsboige/CoursIA/issues/1468) SOTA Lean (fermée) | La grille des 3 grades en a hérité un vocabulaire commun ; le chantier lui-même est distinct (concret vs. méta). |
| [#1203](https://github.com/jsboige/CoursIA/issues/1203) / [#1206](https://github.com/jsboige/CoursIA/issues/1206) / [#1210](https://github.com/jsboige/CoursIA/issues/1210) | Les trois bibliothèques externalisées, lues par la clé, mentionnées seulement. |
| [#11703](https://github.com/jsboige/CoursIA/issues/11703) Lean-15c companion topologique | [#16945](https://github.com/jsboige/CoursIA/pull/16945) : squelette topologique exposé dans le notebook — le backbone que l'hommage au langage attendait |
| [#16920](https://github.com/jsboige/CoursIA/issues/16920) Serre100 dissociation Betti/cohomologie | [#17375](https://github.com/jsboige/CoursIA/pull/17375) : sur RP², `β_k ≠ h_k` devient l'invariant falsifiable — la lecture cohomologique de l'obstruction quitte le documentaire |
| [#13106](https://github.com/jsboige/CoursIA/issues/13106) Lean-13c CHSH tranche 5 | [#17279](https://github.com/jsboige/CoursIA/pull/17279) : `Conway.CHSHLandau` réalise la borne de Tsirelson — la distinction « réalisée / majorée » est tenue par le noyau |
| [#16334](https://github.com/jsboige/CoursIA/issues/16334) Serre100 pendant kernel Yoneda | [#17223](https://github.com/jsboige/CoursIA/pull/17223) : le pendant kernel du notebook Yoneda ouvre la voie des catégories finies effectives |
| [#17066](https://github.com/jsboige/CoursIA/issues/17066) Lean-15b 18 vérifications | [#17214](https://github.com/jsboige/CoursIA/pull/17214) : restauration mot pour mot de l'index vivant `#check` — MathlibMap est vérifié, pas déclaré |
| [#16753](https://github.com/jsboige/CoursIA/issues/16753) Tegmark R16 algèbre effective | [#16942](https://github.com/jsboige/CoursIA/pull/16942) : Sheffer/NAND à 1 générateur, C₂/C₃ et structures finies — la promesse passe à l'algèbre |
| [#16557](https://github.com/jsboige/CoursIA/issues/16557) Portage FLT × 3 | [#17082](https://github.com/jsboige/CoursIA/pull/17082) : Z[ζ₇], Z[ζ₁₁], Z[ζ₁₃] principaux — trois PID, base du portage |
| [#15066](https://github.com/jsboige/CoursIA/issues/15066) Pont modal Tweety ↔ FFL | [#17017](https://github.com/jsboige/CoursIA/pull/17017) : `FormalLogic.ModalBridge` fait la jointure entre les logiques modales Kripke de Tweety et le portage Lean |
| [#16154](https://github.com/jsboige/CoursIA/issues/16154) Umbrella Grothendieck FR-only | [#16228](https://github.com/jsboige/CoursIA/pull/16228) : 17 imports EN consolidés en invariant d'index — `Consolider ≠ Archiver` : FR-only par construction, EN par lakefile |
| [#17465](https://github.com/jsboige/CoursIA/issues/17465) Vitrine GOL | À venir : le détail technique que la lentille n'a plus à porter — `Lean-16*` notebooks + `conway_lean/**`, point de rendez-vous de la noix |
| [#2137](https://github.com/jsboige/CoursIA/issues/2137) Argumentum (fermée) | Une ligne de la table ; pipeline LLM + Tweety = changement de représentation vers le vérifiable. |







---







*Repères vérifiables : [`conway_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/) — `Conway/Life/Hashlife.lean` (`jumpAt_capture_centered`, `evolveHashlifeFastAtN`), `Conway/Life/HashlifeCorrectness.lean` (`OneJumpAtCorrect`, `evolveHashlifeFastAtN_correct`), `Conway/Life/JumpCapture.lean` (`no_padding_depth_suffices`, `jumpCaptured_not_trivial`), `Conway/Life/HashlifeMarginFragment.lean` (l'unique `sorry` du lake) ; [`sensitivity_lean/Sensitivity/MainTheorem.lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/sensitivity_lean/Sensitivity/MainTheorem.lean) (`huang_degree_theorem`, 0 `sorry`) ; [`game_theory_lean/SocialChoice`](../MyIA.AI.Notebooks/GameTheory/game_theory_lean/SocialChoice/Arrow.lean) (Arrow, 0 `sorry`) ; [`game_theory_lean/CooperativeGames`](../MyIA.AI.Notebooks/GameTheory/game_theory_lean/CooperativeGames/Shapley.lean) + [`GameTheory-15b`](../MyIA.AI.Notebooks/GameTheory/GameTheory-15b-Lean-CooperativeGames.ipynb) (Shapley) ; [`GameTheory-4/4b/4c`](../MyIA.AI.Notebooks/GameTheory/GameTheory-04-NashEquilibrium.ipynb) (Nash : concept/Lean/Python) ; [`knot_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/knot_lean/) — `Knots/Conway.lean` et `Knots/MathlibPrerequisites.lean` (prérequis énumérés, horizons assumés) ; [`grothendieck_lean`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/) + notebook [Lean-15](../MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15-Grothendieck-Tribute.ipynb) ([#1646](https://github.com/jsboige/CoursIA/issues/1646)), dont le module [`SheafCohomology`](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/Basic.lean) (`H0_equiv_global_sections`, Čech, [Mayer-Vietoris](../MyIA.AI.Notebooks/SymbolicAI/Lean/grothendieck_lean/Grothendieck/SheafCohomology/MayerVietoris.lean), `glue_sections`, 0 `sorry` de production) ; [`Sudoku-13`](../MyIA.AI.Notebooks/Sudoku/Sudoku-13-SymbolicAutomata-Csharp.ipynb) ; `Probas/Infer` ↔ `Probas/PyMC` (miroir 1-à-1) ; `SymbolicAI/{SmartContracts, Planners, SymbolicLearning, Argument_Analysis, Tweety}` ; `IIT` + [`IIT/ICT-Series`](../MyIA.AI.Notebooks/IIT/ICT-Series/) ([Epic #4588](https://github.com/jsboige/CoursIA/issues/4588)) ; `QuantConnect`. Comptes de `sorry` mesurés avec `python scripts/lean/count_code_sorry.py --json` (champ `distinct_code_sorry`), jamais par `grep`.*



