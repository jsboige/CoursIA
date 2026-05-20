# Cours EPITA SymbolicAI — 2026-05-18 — Recap pedagogique

> Recap des etapes du cours, prepare la veille pendant la nuit. Le coordinateur (ai-01) a ete brefe pour collaborer sur la finalisation deck 03-logique.

## Etat du materiel (debut de journee)

| Element | Etat | Reference |
|---------|------|-----------|
| Deck 03-logique slides | Phase 1 fix (slides 1+2 frontmatter + bullets), repair-PR ouverte pour 23 regressions images | `slides/03-logique/slides.md` + PR liee |
| Deck S1-argumentation | Slides Argumentum + QR code prets | `slides/S1-argumentation/slides.md` |
| PowerPoint backup user | Propre mais incomplet (mention user 2026-05-18 nuit) | local user |
| Notebooks SymbolicAI/Tweety | Serie 1-9 complete | `MyIA.AI.Notebooks/SymbolicAI/Tweety/` |
| Issue GitHub tracking | A creer (deck 03-logique problemes) | a ouvrir |

## Phase 1 — Walkthrough deck 03-logique (logique propositionnelle et FOL)

**Duree estimee**: ~90 min

**Slides cles**:
- Slide 1 cover : "Bases de connaissances et Logique" + grille 4 modules (Logique propositionnelle gras, FOL, Planification, Representation)
- Slide 2 section : Plan du cours 7 chapitres, "III. Bases de connaissances et logique" en focus
- Slide 3 sommaire : ouverture du chapitre
- Slides 4-22 : Logique propositionnelle (KB-agent, inference, Modus Ponens, resolution, forward/backward chaining)
- Slides 23-34 : FOL (syntaxe, semantique, unification, FOL inference)
- Slides 29-44 : Planification (PDDL, GraphPlan, POP, hierarchique)
- Slides 45-50 : Representation des connaissances (Ontologies, Semantic web, TMS)
- Slides 51-93 : TP propositionnel + FOL + projets trimestriels

**Backup**: PowerPoint user (propre, incomplet — completer oral sur les sections manquantes).

**Notes pedago**:
- Insister sur le pont conceptuel KB-agent -> inference -> resolution -> planification
- Slide 65 (projets trimestriels) : mettre a jour si la liste a evolue depuis le dernier semestre

## Phase 2 — Jeu de cartes Argumentum

**Duree estimee**: ~45 min

**Setup**:
- Site Argumentum : QR code present dans `slides/S1-argumentation/images/argumentum_qrcode.png`
- Acces direct : ouvrir le deck `slides/S1-argumentation/slides.md` slide d'introduction Argumentum
- Cartes physiques : verifier qu'il y a un jeu disponible en salle (sinon mode digital uniquement)

**Deroulement type** (deja teste en sessions precedentes):
1. Brief 10 min : presentation des 64 cartes (arguments + sophismes)
2. Distribution 5 cartes / etudiant
3. Tour de table : chaque etudiant joue une carte sur un theme donne ("L'IA est-elle dangereuse ?", "Le nucleaire ?", etc.)
4. Vote du plus convaincant + debrief sophismes detectes
5. Pont avec la theorie : argumentation abstraite de Dung, frameworks AF + bipolaires (Tweety-5 + Tweety-7a)

**Materiel slides**:
- Deck S1-argumentation slides 14-25 (histoire + theorie) prepares
- Demo Tweety-5-Abstract-Argumentation.ipynb si temps

## Phase 3 — Presentation du depot etudiants

**Duree estimee**: ~30 min

**Depot** : voir CLAUDE.md section ECE (cf `docs/ece-grading.md` pour les patterns de notation).

**Points a couvrir**:
1. Structure du depot type (README + notebooks par theme + tests)
2. Workflow git (fork, branche, PR, review)
3. Conventional commits + revues automatisees
4. Outils mis a disposition :
   - `scripts/notebook_tools/notebook_tools.py` (validate, execute, skeleton, analyze)
   - GradeBookApp pour notation
   - GitHub Actions CI (validation notebooks)
5. Calendrier rendus + jalons trimestriels
6. Demos cliquables : un exemple de notebook bien rendu vs un exemple de soumission invalide (papermill error)

## Phase 4 — Presentation series notebooks SymbolicAI

**Duree estimee**: ~45 min

**Series Tweety** (`MyIA.AI.Notebooks/SymbolicAI/Tweety/`) :
| Notebook | Theme | Statut |
|----------|-------|--------|
| Tweety-1-Setup | Installation, JVM, Tweety package | OK |
| Tweety-2-Basic-Logics | Logique propositionnelle, modus ponens | OK |
| Tweety-3-Advanced-Logics | FOL, semantique, models | OK |
| Tweety-4-Belief-Revision | AGM, contraction, expansion | OK |
| Tweety-5-Abstract-Argumentation | Dung AFs, semantique grounded/preferred | OK |
| Tweety-6-Structured-Argumentation | ASPIC+, rules-based | OK |
| Tweety-7a-Extended-Frameworks | Bipolaires, value-based | OK |
| Tweety-7b-Ranking-Probabilistic | Ranking-based, probabiliste | OK |
| Tweety-8-Agent-Dialogues | Dialogues argumentatifs | OK |
| Tweety-9-Preferences | Preferences orderings | OK |

**Series Lean** (`MyIA.AI.Notebooks/SymbolicAI/Lean/`) :
- `stable_marriage_lean/` : port Gale-Shapley, 2 sorry residuels (Knuth lattice DEMO 16/17)
- `social_choice_lean/` : port Arrow/Sen/Voting
- Cross-refs : `GameTheory/`, `Tweety-9-Preferences`

**Autres series**:
- `Argument_Analysis/`, `Planners/`, `RDF.Net/`, `SemanticWeb/`, `SmartContract/`

**Demos cliquables a preparer** :
1. Tweety-2 cellule Modus Ponens en live (illustre theorie slide 13)
2. Tweety-5 cellule grounded semantics sur AF jouet (pont Argumentum -> Tweety)
3. Stable Marriage Lean : `lake build` + extension a "voter" pour Phase 4 Social Choice

## Outils ai-01 / coordinateur

Pendant le cours, le coordinateur peut etre sollicite via :
- Dashboard RooSync workspace CoursIA : `roosync_dashboard(action: "append", type: "workspace", tags: ["ASK"], content: "...")`
- Direct message si urgence : `roosync_messages(action: "send", to: "ai-01", ...)`

Voir issue GitHub liee a ce cours pour le tracking des problemes deck 03-logique.

## Checklist a faire ce matin AVANT le cours

- [ ] Verifier que la PR de fix deck 03-logique est merged par ai-01
- [ ] Verifier qu'aucun fix slide-improver n'a casse une autre slide (sweep `?clicks=99` rapide sur les 93 slides)
- [ ] Imprimer ou afficher le PowerPoint backup en parallele de Slidev (au cas ou)
- [ ] Verifier le QR code Argumentum a l'ecran (`?` page 14 ou 16 du deck S1)
- [ ] Demarrer un kernel .NET Interactive + un kernel Python pour la phase 4 demo
- [ ] Tester un notebook Tweety-2 cellule par cellule (warmup kernel)

---

*Recap genere automatiquement la nuit 2026-05-17 -> 2026-05-18 par Claude Code (Opus 4.7), conformement a la demande user "fais-moi un .md recap avec les etapes du cours demain".*
