# Note — IA et preuves mathématiques en 2026

> Sous-issue de [#19729](https://github.com/jsboige/CoursIA/issues/19729) (grain 3 / 3).
> Référence : `MyIA.AI.Notebooks/SymbolicAI/Lean/Note-IA-et-preuves-2026.md` (note transverse, ce fichier).
> Série parente : [`MyIA.AI.Notebooks/SymbolicAI/Lean/ANALYSE/`](./ANALYSE/) (fil vivant #18408, distillation de résultats majeurs récents en Lean + Python).
> Sources archivées sur GDrive : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Probabilistic\2026 - …` (cf. corps de l'issue #19729).

Cette note compare les **trois AI-disclosures** publiées à l'occasion de la résolution de la conjecture KLS (Kannan–Lovász–Simonovits, ouverte 1995, tranchée 3× début octobre 2026). Elle ne porte pas sur la mathématique des preuves (cf. le carnet Lean `ANALYSE-05`, livré, pour ça), mais sur **ce que la collaboration humain–IA révèle des modes de production et de vérification**, en regard des règles d'or du dépôt (B.0, G-VAR, MEMORY le tells cross-cycle).

L'enjeu pédagogique, dans un dépôt d'enseignement de l'IA, est double : (1) faire voir aux étudiants ce qu'a été cette collaboration **sur un problème réel et difficile**, avec ses réussites et ses angles morts ; (2) armer la discussion sur le statut du peer-review quand une preuve vient en partie d'un LLM. Les trois déclarations sont publiées, donc comparables — et leurs **différences** sont aussi instructives que leurs ressemblances.

## 1. Le triplet 2026

| Papier | Auteurs (affiliation) | Date | Stratégie en une ligne | AI-disclosure |
|---|---|---|---|---|
| [arXiv:2610.01447v2](https://arxiv.org/abs/2610.01447) | Zhao Song (indépendant), Xinzhi Zhang (Microsoft Research) | 2→4 oct. 2026 | Variance des polynômes d'Appell sans dépendance en la dimension → double itération imbriquée (log puis log-star) → O(1) | « GPT-6 Astra, GPT-5.6 Sol, Claude Fable 5, Fable 5.1 » ; > 100 approches explorées depuis le 28 juillet |
| [arXiv:2610.05474](https://arxiv.org/abs/2610.05474) | Pierre Bizeul, Boaz Klartag, Joseph Lehec (Weizmann, TAU, Sorbonne) | 4 oct. 2026 | Borne du 3ᵉ moment → cumulants de tous ordres via localisation stochastique → moyennes basculées + construction de suspension | « Most proofs and mathematical ideas in this paper were found by ChatGPT; a notable exception is the idea to use suspension which was suggested by the authors. The role of the authors has been mostly to understand these proofs and improve their exposition. » |
| Préprint GitHub | Krishnakumar Balasubramanian (UC Davis/Amazon), Shiva Kasiviswanathan (Amazon) | oct. 2026 | Opérateurs d'intégration + courbure de Hodge uniforme en rang tensoriel → lemme d'opérateur → localisation stochastique + transfert inverse | « We developed this proof with substantial assistance from several frontier AI models » — l'IA créditée nommément de deux ingrédients |

Les trois sont des **préprints non relus** à ce jour. La vérification communautaire suit — et c'est précisément sur ce point que la suite de cette note insiste.

## 2. Trois modes de collaboration

Ce qui frappe à la lecture en parallèle, c'est la **variété** des positionnements.

**Song–Zhang : l'IA comme multiplicateur d'effort.** L'effort court depuis juillet (3 mois), 100+ approches explorées, plusieurs modèles sollicités. La disclosure est en mode **annuaire de ressources** : c'est une équipe de chercheurs, dont l'IA est l'un des outils. La responsabilité (« authors take full responsibility for the correctness ») est formulée à l'ancienne — l'humain garantit. Le tout **avant** la résolution, comme un sous-traitant qu'on présente.

**Bizeul–Klartag–Lehec : l'IA comme producteur principal.** La disclosure est sans ambiguïté : ChatGPT a trouvé *la plupart* des preuves et des idées. Les auteurs déclarent leur apport — l'idée de suspension —, puis tout le reste : comprendre, reformuler, rendre lisible. L'introduction elle-même annonce « The KLS conjecture poses little challenge for contemporary AI tools ». C'est une **inversion de la charge** : l'IA propose, l'humain valide et expose. Le peer-review se fait en deux temps : sur la *correction* (les auteurs) et sur *l'attribution* (la communauté, à venir).

**Balasubramanian–Kasiviswanathan : l'IA comme ingrédient nommé.** La disclosure cite *quel ingrédient* a été trouvé par IA (comparaison de Hodge pondérée, normes de coefficients d'Appell), avec une constante explicite et un blog compagnon qui travaille un exemple. C'est la position la plus proche d'une *pratique de laboratoire* : on note au passage, dans la recette, quelle étape a été suggérée par la machine.

**L'enseignement** : la transparence des trois est à saluer — mais elle n'est pas homogène. Song–Zhang parle d'« outils », Bizeul–Klartag–Lehec parle d'un *co-auteur de fait*, Balasubramanian–Kasiviswanathan parlent d'*ingrédients identifiés*. Le peer-review, qui doit aujourd'hui statuer sur la *correction* de la preuve (tâche classique) et sur l'*attribution* (tâche nouvelle), n'a pas encore de convention pour cette deuxième dimension.

## 3. Trois angles morts partagés

Les trois déclarations, lues ensemble, révèlent trois angles morts — et c'est sur ces angles morts qu'un dépôt d'enseignement doit insister.

**(a) Vérification automatisée, qui l'a faite ?** Song–Zhang écrivent « All of the proofs have been carefully verified by the authors and several AI tools ». Mais *par quel mécanisme* ? Les autres papiers ne le précisent pas. La question est ouverte : un LLM qui vérifie un autre LLM est-ce une vraie vérification, ou une *résonance* stylistique ? Le présent dépôt a tranché (MEMORY, tells c.18529, c.18590) : un notebook sans `execution_count` réel, ou un diff `json.dump(separators=(',',':'))` qui altère la sortie, c'est une **falsification** — la preuve d'exécution compte, pas la cohérence apparente. Le KLS n'est pas au-dessus de cette discipline.

**(b) Responsabilité en cas d'erreur cachée.** Si un peer-reviewer trouve dans six mois une faille dans la preuve co-écrite, qui corrige ? L'IA, qui ne signe pas ? L'auteur, qui n'a peut-être pas la capacité de suivre chaque lemme en détail ? Les trois déclarations évacuent la question (« authors take full responsibility »). Le dépôt a une position explicite, héritée de Stop & Repair ([secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md), règle 6) : **on ne maquille jamais une sortie**, on corrige la cause et on re-exécute. C'est une discipline de *process*, pas de résultat.

**(c) Reproductibilité.** Aucune des trois déclarations ne donne de commande pour rejouer la preuve. Song–Zhang écrivent que « les preuves ont été vérifiées », Balasubramanian–Kasiviswanathan donnent un blog compagnon, Bizeul–Klartag–Lehec n'indiquent pas de référence pour la « construction de suspension » au-delà de leur Lemme 4.2. La reproductibilité d'une preuve IA-assistée est un sujet ouvert : le dépôt l'a réglé pour les notebooks (papermill, commit AVEC outputs, C.2 — cf. [notebook-conventions.md](../../.claude/rules/notebook-conventions.md)) et pour Lean (`lake build SUCCESS` sur la même cible, B.3, [pr-review-discipline.md](../../.claude/rules/pr-review-discipline.md)). Le standard existe, il n'est pas encore appliqué aux preuves IA.

## 4. Trois leçons pour le dépôt

Laissant la mathématique au carnet `ANALYSE-05` (livré), on tire trois leçons directement applicables à la production d'un dépôt d'enseignement IA.

**L1 — Documenter l'IA comme un auteur de fait, mais tenir la discipline de sortie.** Bizeul–Klartag–Lehec le font. Quand une cellule de notebook vient d'un LLM (ce qui est notre cas quotidien), la note doit l'écrire — mais l'output doit toujours porter `execution_count != null`, sinon c'est un mensonge de timeline, pas une économie. La discipline B.0 / C.2 / Stop & Repair tient, et elle devient **davantage** visible quand l'IA est dans la boucle, pas moins.

**L2 — Les angles morts sont les nôtres, pas ceux de l'IA.** « Le LLM ne peut pas X » est un claim souvent faux (cf. [verify-before-claiming.md](../../.claude/rules/verify-before-claiming.md), règle 1) — il faut tester avant d'écrire. Le triplet 2026 montre qu'on a aussi des angles morts en propre : la vérification automatisée, la responsabilité en cas d'erreur, la reproductibilité. L'IA n'est pas l'obstacle à ces trois ; l'absence de standard partagé l'est. Notre travail de dépôt est de **poser ces standards** là où ils manquent — carnet par carnet, B.0 par B.0.

**L3 — Le peer-review est en avance sur le code, et inversement.** Le peer-review mathématique traite depuis longtemps la question « qui a trouvé quoi » (Poincaré, Perelman, etc.) et la confiance probabiliste dans une preuve encore incomplète. L'ingénierie logicielle a depuis longtemps les tests, CI, pre-commit. Le **trou** est dans la *vérification automatisée d'une preuve IA-assistée* : ce qui se passe entre l'AI-disclosure et l'acceptation par les pairs. C'est là que ce dépôt a le plus à dire — par les `lake build SUCCESS` réels, par les 484/484 tests verts, par les cellules de notebook qui s'exécutent vraiment. C'est aussi là qu'il a le plus à faire : inventer les *garde-fous* d'un tel pipeline, mesure par mesure, et ne pas laisser l'enthousiasme de l'IA-outil dispenser de la rigueur de la preuve.

### Ré-évaluation à la lumière d'ANALYSE-05 (2026-10-28)

> Mesures à l'appui : audit de pin, `#check` et `#print axioms` dans [`ANALYSE-05-KLS-Lean-Python` §3 et §3.2](./ANALYSE/ANALYSE-05-KLS-Lean-Python.ipynb) — carnet committé sur `main`, outputs inclus.

[`ANALYSE-05-KLS-Lean-Python`](./ANALYSE/ANALYSE-05-KLS-Lean-Python.ipynb) est livrée — grains 1 et 2 par #19830 et #19834, grain 4 (Song–Zhang O(1), `ANALYSE-05b`) par #22275. Le pied de page de cette note demandait de confronter L1–L3 à ce que l'expérience concrète aurait montré ; c'est fait ci-dessous, mesures sur `main` à l'appui.

**L1 — tenue, et doublée d'un pendant formel.** Le carnet s'exécute de bout en bout : zéro `execution_count` nul, zéro erreur, aucune sortie de repli. Ce que l'expérience ajoute : la discipline de sortie a son exact homologue du côté formel — **l'axiome déclaré**. `#print axioms` rend `[propext, Classical.choice, Quot.sound]` : aucun `sorryAx`, aucun `native_decide`, et les cinq preuves du lac sont complètes au sens du noyau. La « documentation de l'IA comme auteur de fait » devient, côté preuve, une **dette de formalisation écrite** : le `README` du lac `kls_lean` énumère les énoncés exclus (Théorème 1.1, thin-shell, germe quadratique) et la condition de leur entrée, plutôt que de poser des `sorry` d'énoncé. L'honnêteté sur ce qui n'est pas prouvé est la même vertu que L1 exige sur ce qui n'est pas exécuté.

**L2 — confirmée par sa propre méthode.** La première friction consignée du carnet est L2 en acte : l'instinct « Mathlib doit bien avoir la log-concavité » est faux au pin `v4.32.1` — l'audit (§3 du carnet) rend **zéro fichier** pour `IsLogConcave`, la constante de Poincaré d'une mesure, celle de Cheeger, le thin-shell et l'isotropie. Sans cet audit, le lac aurait redéfini à l'aveugle. La leçon s'étend au-delà du claim de capacité (« le LLM ne peut pas X ») au **claim de couverture** (« Mathlib a déjà Y ») : même organe, grep sur les sources réelles au pin avant d'écrire la première définition. (Audit #19765 du 07/10, pin `v4.32.1` inchangé depuis : à tout futur bump Mathlib, ce constat se **re-mesure**, il ne se re-copie pas.)

**L3 — précisée : le « trou » commence une étape plus tôt que prévu.** La note plaçait le manque dans la vérification automatisée d'une preuve IA-assistée. L'expérience montre que, sur un résultat de 2026, même les **définitions** manquent : le pipeline ne démarre pas à « vérifier la preuve » mais à « poser les objets ». Sur ce qui existe, le standard revendiqué par L3 est tenu localement — `lake build` réel, `#check` élaborés par le compilateur (pas recopiés), axiomes imprimés, zéro `sorry` — et le Théorème 1.1 reste hors du lac volontairement, sa preuve n'étant formalisée dans aucun lac public. C'est la frontière honnête entre **digérer** et **déclarer prouvé** — exactement la frontière que L3 demandait d'instrumenter.

**Bilan.** Les trois leçons sortent consolidées de l'épreuve du concret, aucune inversée : L1 gagne son pendant formel (l'axiome déclaré, la dette écrite), L2 gagne un organe (l'audit de pin), L3 gagne une étape (les définitions avant les preuves).

## 5. Pour aller plus loin (à c.98+)

Trois grains documentés à [#19729](https://github.com/jsboige/CoursIA/issues/19729) :

- **Grain 1 (à ouvrir en sous-issue)** : `ANALYSE-05-KLS-Lean-Python` — théorème 1.1 de Bizeul–Klartag–Lehec (la plus courte des trois preuves, 32 p.) — récit de la preuve + expériences Python (constante de Cheeger par Monte-Carlo, variance thin-shell Var|X|², gap spectral). Énoncé Lean en fonction de la couverture Mathlib (`Measure.IsLogConcave`, `Poincaré`, inégalité de Cheeger). Le grain suppose un archétypal `Lean-04` (tactiques Mathlib) + `Lean-20` (capstone). PR attendue à partir de c.98.
- **Grain 2 (à ouvrir en sous-issue)** : `Probas-KLS-Concentration` — carnet Probas sur la concentration des mesures log-concaves : estimation Monte-Carlo du gap spectral / de la constante de Cheeger sur cube, simplexe et gaussienne en dimension croissante ; marche hit-and-run et temps de mélange ; variance thin-shell. Pas de verdict SOTA (CPU-borné). PR attendue à partir de c.99+.
- **Grain 3 (cette note)** : la présente note transverse. PR à ouvrir en c.97.

Statut : note rédigée en c.97 par `myia-po-2024:CoursIA-2`. Référencée par le README de la série `ANALYSE/`. Relue en regard de la sortie d'ANALYSE-05 (livrée) : leçons L1–L3 ré-évaluées au §4 — consolidées, aucune inversée (critère 4 de #19762).

## Sources

- `G:\Mon Drive\MyIA\IA\Bibliographie IA\Probabilistic\2026 - Bizeul Klartag Lehec - Presenting a proof of the Kannan-Lovasz-Simonovits conjecture (arXiv 2610.05474).pdf` (archive au commit de cette note, cf. issue #19729).
- `G:\Mon Drive\MyIA\IA\Bibliographie IA\Probabilistic\2026 - Song Zhang - An O(1) Bound for the KLS Constant (arXiv 2610.01447v2).pdf`.
- `G:\Mon Drive\MyIA\IA\Bibliographie IA\Probabilistic\2026 - Balasubramanian Kasiviswanathan - A Dimension-Free Bound on the Poincare Constant of Isotropic Log-Concave Measures.pdf`.

Prérequis de la chaîne non archivés ici : Chen–Klartag arXiv:2607.23307 (thin-shell), Letwin arXiv:2607.24164 (inégalité quadratique) — à archiver si un grain les consomme.
