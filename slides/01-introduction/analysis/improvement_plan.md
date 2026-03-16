# Deck 01 - Introduction : Analyse Visuelle et Plan d'Amelioration

**Date d'analyse** : 2026-02-13
**Fichier source** : Intelligence Artificielle - 1 - Introduction.pptx
**Statistiques** : 43 slides, 40 images, 1790 mots, 1.63 MB
**Theme PowerPoint** : Gris-bleu clair, titre saumon/rouge, separateur pointille, badge numero

---

## 1. Diagnostic global

### Points forts
- **Theme coherent** : palette sobre gris-bleu + accents rouge/saumon, lisible en projection
- **Slides 25-29** (taxonomie "Intelligences") : excellent mapping conceptuel Type/Inference/Modeles/Apprentissage/Agents, recurrent pour chaque branche (Exploratoire, Symbolique, Probabiliste). Design original et pedagogiquement fort.
- **Slides 35-39** (types d'agents) : bons diagrammes AIMA (boucle agent-environnement) avec images d'illustration
- **Slide 14** (Qui fait de l'IA) : bonne variete visuelle avec logos universites/entreprises
- **Slide 10** (matrice 2x2 des approches) : bon schema avec code couleur

### Problemes majeurs
1. **Slides textuelles austeres** : slides 5, 11, 15, 17-19, 23-24, 30, 32, 41 = murs de texte sans aucun visuel
2. **Slides dupliquees** : slide 23 et 24 sont identiques (agents rationnels)
3. **Slides "Questions?" vides** : slides 7 et 20 sont des placeholders sans valeur ajoutee
4. **Historique date** : slide 13 s'arrete a 2019 (manque GPT-3/4/5, ChatGPT, Midjourney, DALL-E, Claude, etc.)
5. **Tables illisibles** : slides 31 et 33 ont des tableaux trop petits pour la projection
6. **Animations plates** : slides 25-26 sont deux etats de la meme animation (cercles imbriques) qui ne fonctionnent pas en statique
7. **Trop de slides de navigation** : slides 4, 8, 21 repetent le meme sommaire avec l'element courant en gras
8. **Absence de cross-references notebooks** : aucun lien vers les TPs/notebooks du workspace

### Metriques visuelles
- Slides sans aucune image : **22/43 (51%)**
- Slides avec diagrammes AIMA : 8 (slides 22, 35-40)
- Slides purement textuelles a ameliorer en priorite : 12
- Slides dupliquees/placeholder a supprimer : 3

---

## 2. Analyse slide par slide

### Section 1 : Presentation du cursus (slides 1-7)

| Slide | Titre | Note | Verdict |
|-------|-------|------|---------|
| 1 | Intelligence artificielle (titre) | Propre mais minimaliste. Manque un visuel marquant | Ameliorer |
| 2 | IA 101 (infos cursus) | Fonctionnel. Reference AIMA 3e edition (la 4e existe) | Mettre a jour |
| 3 | Sommaire visuel | Bonne idee d'image laterale, trop petit | Ameliorer |
| 4 | Sommaire navigation | Utile en animation, redondant en statique | Conserver |
| 5 | Objectifs du cours | **Trop de texte** (89 mots). Viole la regle 1-6-6. | Restructurer |
| 6 | Plan du cours | OK, sobre et clair | Conserver |
| 7 | Questions? | Placeholder vide | Supprimer ou enrichir |

### Section 2 : Introduction a l'IA (slides 8-20)

| Slide | Titre | Note | Verdict |
|-------|-------|------|---------|
| 8 | Navigation | Sommaire avec section courante en gras | Conserver |
| 9 | Qu'est-ce que l'IA? (definitions) | Tableau AIMA trop petit/flou. Texte OK | Ameliorer visuel |
| 10 | 4 approches (matrice 2x2) | **Bon** schema couleur. Garder. | Conserver |
| 11 | Fondements de l'IA | Dense mais structuree. Manque icones/visuels | Ameliorer |
| 12 | Histoire succincte | Tres dense (128 mots). Image Turing trop petite. | Eclater en 2-3 slides |
| 13 | Etat de l'art | **Critique** : 157 mots, s'arrete a 2019. Date. | Refaire + update 2020-2026 |
| 14 | Qui fait de l'IA | Logos varies, bonne slide | Mettre a jour logos |
| 15 | Applications quotidiennes | Texte seul, aucun visuel | Ajouter icones/images |
| 16 | Test de Turing | Diagramme correct, mise en page OK | Conserver |
| 17 | Sciences cognitives | Texte seul | Ajouter visuel cerveau/cognition |
| 18 | Lois de la raison | Texte seul | Ajouter visuel logique/Aristote |
| 19 | L'agent rationnel | Texte seul | Ajouter schema decision |
| 20 | Questions? | Placeholder vide | Supprimer |

### Section 3 : Systemes d'agents (slides 21-43)

| Slide | Titre | Note | Verdict |
|-------|-------|------|---------|
| 21 | Navigation | Section agents en gras | Conserver |
| 22 | Les agents (definition) | Bon diagramme agent-env, taille OK | Conserver |
| 23 | Agents rationnels | Dense, texte seul | Ameliorer |
| 24 | Agents rationnels (DOUBLON) | **Identique a 23** | Supprimer |
| 25 | Intelligences (cercles) | Excellent concept, etat 1 de l'animation | Fusionner 25+26 |
| 26 | Intelligences (cercles v2) | Meme concept, etat 2 | Fusionner avec 25 |
| 27 | Intelligence de la recherche | **Excellent** tableau taxonomique | Conserver |
| 28 | Intelligence logique | Meme structure, tres bien | Conserver |
| 29 | Intelligence probabiliste | Meme structure, tres bien | Conserver |
| 30 | Environnement PEAS | Texte seul, pas de schema | Ajouter diagramme PEAS |
| 31 | PEAS exemples (table) | Table trop petite | Agrandir ou eclater |
| 32 | Types d'environnement | Dense (77 mots), texte seul | Ajouter visuels/icones |
| 33 | Types d'env exemples (table) | Table trop petite | Agrandir |
| 34 | Types d'agents | Pseudo-code + liste. Encombre | Restructurer |
| 35 | Agent reflexe | **Bon** : diagramme AIMA + Wolfram | Conserver |
| 36 | Agent reflexe modele | Bon : diagramme + photos Brooks | Conserver, nettoyer |
| 37 | Agent fonde sur buts | Diagramme AIMA, texte sparse | Ameliorer texte |
| 38 | Agent fonde sur utilite | Diagramme AIMA, texte sparse | Ameliorer texte |
| 39 | Agent apprenant | Diagramme AIMA correct | Conserver |
| 40 | Fonctionnement interne | Diagrams atomique/factorise/structure, petits | Agrandir |
| 41 | Resume | Texte seul mais OK pour un resume | Conserver |
| 42 | Plan du cours (closing) | Navigation, coherent | Conserver |
| 43 | Merci | Clean | Conserver |

---

## 3. Cross-references avec les notebooks

Le deck Introduction est transversal : il presente les concepts que les notebooks approfondissent dans chaque domaine. Voici les liens a materialiser :

### Liens directs slide -> notebook

| Slide(s) | Concept | Notebooks pertinents |
|-----------|---------|---------------------|
| 27 | Intelligence exploratoire | `Search/Exploration_non_informee_et_informee_intro.ipynb`, `Search/CSPs_Intro.ipynb` |
| 27 | Satisfaction de contraintes | `Sudoku/Sudoku-1-Backtracking.ipynb` a `Sudoku-6-Infer.ipynb` |
| 27 | Algorithmes genetiques | `Search/Portfolio_Optimization_GeneticSharp.ipynb`, `Sudoku/Sudoku-2-Genetic.ipynb` |
| 28 | Intelligence symbolique | `SymbolicAI/Lean/Lean-1-Setup.ipynb` a `Lean-10-LeanDojo.ipynb` |
| 28 | Solveurs SMT | `Sudoku/Sudoku-4-Z3.ipynb` |
| 28 | Argumentation | `SymbolicAI/Argument_Analysis/` (5 notebooks) |
| 29 | Inference bayesienne | `Probas/Infer-101.ipynb`, `Probas/Infer/Infer-3-Factor-Graphs.ipynb` a `Infer-14` |
| 29 | Reseaux de decision | `Probas/Infer/Infer-14-Decision-Utility-Foundations.ipynb` |
| 29 | Theorie des jeux | `GameTheory/GameTheory-2b-Lean-Definitions.ipynb` a `GameTheory-16b` |
| 13 | Deep learning / GenAI | `GenAI/Image/` (15+ notebooks), `ML/ML.Net/` (5 notebooks) |
| 13 | Trading algorithmique | `QuantConnect/` (27 notebooks - a verifier) |
| 39 | Agent apprenant | `RL/stable_baseline_1_intro_cartpole.ipynb` a `stable_baseline_3` |

### Slide "Pour aller plus loin" a ajouter

Apres le resume (slide 41), ajouter une slide de cross-references :
```
Pour aller plus loin : les notebooks du cours
- Exploration : Search/, Sudoku/ (15 notebooks)
- Logique : SymbolicAI/, Lean/ (35 notebooks)
- Probabilites : Probas/Infer/ (22 notebooks)
- Jeux : GameTheory/ (26 notebooks)
- Apprentissage : ML/, RL/ (8 notebooks)
- IA Generative : GenAI/ (58 notebooks)
```

---

## 4. References AIMA a mettre a jour

| Slide | Reference actuelle | Mise a jour |
|-------|-------------------|-------------|
| 2 | "3e edition" | Ajouter mention 4e edition (2020) + PDF en ligne |
| 9 | Matrice 4 approches | OK (identique AIMA 3e et 4e) |
| 13 | Historique -> 2019 | Completer 2020-2026 (GPT-3/4/5, ChatGPT, Claude, diffusion models, Gemini, DeepSeek) |
| 16 | Test de Turing | Mentionner debat post-ChatGPT sur la pertinence du test |
| 22-24 | Definition agent | OK (AIMA ch. 2, inchange) |
| 35-39 | Types d'agents | OK (AIMA ch. 2, inchange). Ajouter "Agent LLM" comme nouveau type ? |

---

## 5. Plan d'amelioration prioritaire

### Priorite 1 : Corrections immediates (impact fort, effort faible)

1. **Supprimer slide 24** (doublon exact de 23)
2. ~~Supprimer slide 20~~ **GARDER** : les slides "Questions?" servent de respiration entre sections
3. **Fusionner slides 25-26** (deux etats de la meme animation)
4. **Mettre a jour slide 2** : reference AIMA 4e edition
5. **Mettre a jour slide 13** : ajouter historique 2020-2026

### Priorite 2 : Ameliorations visuelles (impact fort, effort moyen)

6. **Slide 1** (titre) : ajouter un visuel marquant (reseau de neurones, robot, cerveau + circuit)
7. **Slide 5** (objectifs) : restructurer en 3-4 blocs visuels au lieu d'un mur de texte
8. **Slide 11** (fondements) : ajouter icones pour chaque discipline
9. **Slide 12** (histoire) : eclater en 2 slides (pre-2000 / post-2000) avec frise visuelle
10. **Slide 13** (etat de l'art) : refaire completement, timeline moderne avec images
11. **Slide 15** (applications) : ajouter icones/photos pour chaque domaine
12. **Slide 30** (PEAS) : ajouter diagramme visuel du framework PEAS
13. **Slides 31, 33** (tables) : agrandir les tableaux ou les repartir sur 2 slides

### Priorite 3 : Enrichissement pedagogique (impact moyen, effort plus eleve)

14. **Slides 17-19** (cognitif/raison/agent) : ajouter un visuel pertinent a chaque
15. **Slide 23** (agents rationnels) : ajouter schema recapitulatif
16. **Slide 32** (types d'environnement) : ajouter exemples visuels (echecs, poker, voiture)
17. **Slide 34** (types d'agents) : separer pseudo-code et liste
18. **Ajouter slide cross-ref notebooks** : apres slide 41
19. **Slide 40** (representation etats) : agrandir les 3 schemas

### Priorite 4 : Modernisation du contenu

20. **Slide 13** : mentionner GPT-3 (2020), DALL-E (2021), ChatGPT (2022), GPT-4 (2023), Claude (2024), GPT-5 (2025), agents LLM
21. **Slide 14** : ajouter OpenAI, Anthropic, Mistral, DeepSeek aux logos
22. **Slide 15** : ajouter assistants IA (ChatGPT, Copilot), generation d'images, voitures autonomes Level 4
23. **Slide 35** : moderniser l'exemple agent reflexe (thermostat intelligent, automate de jeu)
24. **Ajouter slide "Agent LLM"** : nouveau type d'agent post-2023 (RAG, tool use, agentic workflows)

---

## 6. Estimation de l'effort

| Priorite | Slides touchees | Effort estime |
|----------|----------------|---------------|
| P1 : Corrections | 5 slides | 15 min |
| P2 : Visuels | 8 slides | 1-2h |
| P3 : Pedagogie | 6 slides | 1h |
| P4 : Modernisation | 5 slides | 1h |
| **Total** | **~20 slides** | **~3-4h** |

Resultat attendu : ameliorer significativement la lisibilite en projection et l'equilibre texte/visuels. Le deck passerait de 43 slides a ~42-44 slides.

---

## 7. Revue visuelle qualitative (slide par slide)

Observations issues de l'examen visuel de chaque rendu PNG 1920x1080, jugees selon :
- **Test des 3 secondes** : le message principal est-il compris immediatement ?
- **Regle 1-6-6** : 1 idee, max 6 points, max 6 mots par point
- **Lisibilite en projection** : taille de police, contraste, depuis le fond de salle
- **Equilibre texte/visuel** : pas de murs de texte, visuels pertinents
- **Hierarchie visuelle** : l'oeil est-il guide logiquement ?

### Slides 1-8 (Presentation du cursus)

**Slide 1 (Titre)** : Titre "Intelligence artificielle" en rouge-brique, bonne taille et lisibilite. Mais la moitie basse est froide et vide - juste 3 bullets de credentials textuels (MRes CSAI, Aricie-DNN-PKP, My Intelligence Agency). En projection, ca ne capte pas l'attention. **Manque un visuel d'accroche** (reseau neuronal, robot, cerveau+circuit). Le separateur pointille avec cercle numerote est un bon element de design du theme.

**Slide 2 (IA 101)** : Slide organisationnelle propre, 3 blocs bien espaces (Livres, Classe, Projets). 100% texte mais acceptable pour ce type de slide. Lien cliquable en cyan. **"3e edition" a mettre a jour** vers 3e/4e. Pourrait ajouter la couverture du livre AIMA, une photo de classe, des icones.

**Slide 3 (Sommaire global)** : La couverture AIMA a droite est un bon reflexe visuel. Mais le **texte est trop petit** : les sous-points gris clair (descriptions de chaque section) seront illisibles depuis le fond de la salle en projection. Le contraste gris/fond gris-bleu est insuffisant.

**Slide 4 (Sommaire detaille)** : Navigation avec sections en gras noir (actives) vs gris (a venir). Propre, mais texte pur sans aucun element graphique. Acceptable en tant que slide de navigation.

**Slide 5 (Objectifs)** : **MUR DE TEXTE** typique. Liste imbriquee sur 4 niveaux de profondeur. En projection, les sous-sous-points sont certainement illisibles (taille estimee <18pt). Viole la regle 1-6-6 : trop d'idees, trop de mots par point. **A eclater en 3-4 slides** : une par grand objectif (modeles informatiques / programmes / systemes intelligents) avec un visuel illustrant chaque objectif.

**Slide 6 (Plan du cours)** : Liste numerotee I-VIII en chiffres romains rouges. Bon espacement, texte lisible, bonne hierarchie visuelle. Propre et aere. Pourrait etre plus attractif visuellement (icones par section ?) mais correct tel quel.

**Slide 7 (Questions?)** : Slide de respiration entre sections. Remplit son role.

**Slide 8 (Sommaire nav)** : "Introduction" en gras, section active. Ajout "TP" et "Projets de groupe" en grise. Bonne utilisation du gris pour les sections futures.

### Slides 9-16 (Introduction a l'IA)

**Slide 9 (Definitions IA)** : Le tableau 2x2 au centre est une **capture d'ecran du livre AIMA en basse resolution**, texte minuscule completement illisible en projection. C'est la pire slide du deck visuellement. La progression "Automates -> Calculateur -> ... -> Generatif ?" en bas est bonne mais perdue dans le bruit. **A refaire** : reconstruire le tableau en PowerPoint natif avec texte lisible, ou utiliser la slide 10 comme remplacement.

**Slide 10 (4 approches)** : **Excellente slide**. Matrice 2x2 coloree (brun fonce/orange) avec "Penser comme l'homme / de facon rationnelle" et "Agir comme l'homme / de facon rationnelle". Texte grand, bien contraste, message clair en 3 secondes. "Notre angle principal: Agir de facon rationnelle -> Conception d'agents". Seul bemol : les couleurs brun/orange ne sont pas dans la palette du theme (gris-bleu, rouge-brique) - ca cree une rupture de ton.

**Slide 11 (Fondements de l'IA)** : 9 disciplines listees en deux colonnes (discipline | description). Le texte est **trop petit pour la projection** - les descriptions a droite sont en corps ~16-18pt estime. Aucun visuel pour un sujet qui s'y prete naturellement. **A transformer** en diagramme en roue (IA au centre, 9 branches) ou eclater en 2-3 slides avec icones par discipline.

**Slide 12 (Histoire succincte)** : Timeline textuelle de 1943 a 2010s. Schema du test de Turing en haut a droite - utile mais **petit et chevauche par le texte**. Texte TRES dense, surtout les sous-points des annees recentes. En projection, les lignes post-2010 sont illisibles. **A eclater** en 2 slides (avant 2000 / apres 2000) avec une frise chronologique visuelle au lieu d'une liste de bullets.

**Slide 13 (Etat de l'art)** : Meme probleme que slide 12 - mur de texte chronologique hyper-dense. Logos DARPA et ImageNet en haut a droite = bon reflexe. Les dates en rouge clair creent de la hierarchie. **Contenu s'arrete a 2019** (Starcraft 2, Pluribus). Manque TOUTE la revolution 2020-2026 : GPT-3, AlphaFold 2, DALL-E 2, ChatGPT, GPT-4, Claude, Gemini, Stable Diffusion, agents LLM, Claude Code, Copilot. **A refaire completement** sur 2-3 slides thematiques avec images/logos modernes.

**Slide 14 (Qui fait de l'IA)** : 3 categories avec bons logos (Carnegie Mellon, MIT, Berkeley, IDSIA en haut ; Google, Facebook, Amazon, Microsoft, etc. en bas). Apporte du visuel bienvenu. **Probleme : tres date**. "Facebook" est devenu Meta (2021), BodyMedia est rachete, manquent les acteurs majeurs post-2020 : OpenAI, Anthropic, DeepMind (Google), Mistral, DeepSeek, Hugging Face.

**Slide 15 (Vie quotidienne)** : 6 domaines d'application en liste (Poste, Banque, Service client, Internet, Securite, Jeux). **100% texte**, pas un seul visuel pour un sujet qui s'illustre parfaitement (photos, icones, captures d'ecran). Les applications citees sont datees : "Lecture de cheques et verification de signatures" (les cheques disparaissent). **Manque** : conduite autonome, assistants vocaux (Siri/Alexa), recommandation (Netflix/Spotify), generation d'images, traduction automatique.

**Slide 16 (Test de Turing)** : **Bon equilibre** texte/schema. Dessin du test de Turing a droite (interrogateur humain, systeme IA), clair et pertinent. Liste des competences a gauche (Langage, Representation, Raisonnement, Apprentissage). "Total Turing" avec Vision + Robotique. Mention "Dnn + Portal Keeper: plateforme web d'agents" un peu cryptique pour les etudiants.

### Slides 17-24 (Fin introduction + debut agents)

**Slide 17 (Sciences cognitives)** : Texte seul pour un sujet sur le cerveau humain et les sciences cognitives. C'est une occasion manquee : un schema cerveau vs ordinateur, ou un diagramme top-down (psychologie) vs bottom-up (neurosciences) serait naturel et eclairant. Le contenu est bon (revolution cognitive, 3 raisons de la separation IA/cognitif) mais la forme est austere.

**Slide 18 (Lois de la raison)** : Mur de texte classique avec 3 blocs (Aristote, lien maths/philo, problemes). Aucun visuel. Un diagramme de syllogisme, ou une illustration du passage "logique formelle -> IA" ferait la difference. Le texte est dense mais structure.

**Slide 19 (L'agent rationnel)** : 3 blocs textuels (comportement rationnel, theorie de la decision, utilite). Bon usage du gras sur les mots-cles (maximisera, objectif, information disponible). Mais aucun schema alors que le concept d'agent rationnel (perception -> decision -> action) s'illustre naturellement avec un diagramme simple.

**Slide 20 (Questions?)** : Respiration entre "Introduction" et "Systemes d'agents". Marque bien la transition.

**Slide 21 (Sommaire nav - Agents)** : "Systemes d'agents" en gras, le reste en gris. **Footer "Intelligence(s)"** au lieu de "IA 101" - **inconsistance** a corriger.

**Slide 22 (Les agents)** : **Bonne slide** avec le schema agent-environnement AIMA a droite (cycle perceptions/actions). Definition formelle [f: P* -> A] a gauche. Le bonhomme bleu/violet est un clip-art un peu date mais le diagramme est clair et pertinent. **Footer "Intelligence(s)"** - inconsistance.

**Slide 23 (Agents rationnels)** : Texte dense, 3 blocs sur 3 niveaux d'indentation (bonne action, rationnel != omniscient, environnement limite). Pas de visuel. Le contenu est bon mais la forme est un mur de texte. Footer "Intelligence(s)".

**Slide 24 (Agents rationnels - DOUBLON)** : **Identique a la slide 23** - meme titre, meme contenu, meme mise en forme, seul le numero change (24 vs 23). **A supprimer.**

### Slides 25-32 (Taxonomie + Environnements)

**Slide 25 (Intelligences - cercles v1)** : **Concept excellent et original** : diagramme en cercles concentriques emboites (Procedurale > Exploratoire > Symbolique > Probabiliste) avec des images en haut a droite (carte, molecules, taquin). Categories en bas (Automates, Algorithmes). Les textes dans les cercles sont petits mais le schema est pedagogiquement fort. C'est un **etat d'animation** - sans animation, c'est un instantane incomplet.

**Slide 26 (Intelligences - cercles v2)** : Meme structure que 25 mais sans le cercle numerote et avec un zoom leger. C'est le **second etat de la meme animation**. En PDF/statique, ces deux slides se ressemblent trop. **A fusionner en une seule slide** qui montre l'etat final.

**Slide 27 (Intelligence de la recherche)** : **Excellente slide**. Tableau taxonomique complet : Type (Exploratoire) -> Inference (Recherche de chemin, Exploration locale, Satisfaction de contraintes) -> Modeles -> Apprentissage -> Agents. Les boites rouge-brique sur fond rose clair sont lisibles et esthetiquement coherentes avec le theme. Bonne hierarchie visuelle. Footer "Intelligences" - inconsistance mais coherent avec la sous-section.

**Slide 28 (Intelligence logique)** : Meme structure taxonomique pour l'intelligence Symbolique. Aussi bien que 27. Raisonnement -> Bases de connaissances / Plans / Smart-contracts -> Apprentissage inductif/deductif / Solveurs SMTs -> Agents. Coherent et lisible.

**Slide 29 (Intelligence probabiliste)** : Meme structure pour l'intelligence Probabiliste. Inference Bayesienne, Recherche de politique, Analyse strategique -> Modeles graphiques, Reseaux de decision, Processus de Markov -> Apprentissage Bayesien, Systeme expert, RL, Minimisation de regret -> Agents. Complet et bien structure.

**Slide 30 (Environnement de tache PEAS)** : Description textuelle du framework PEAS (Performance, Environnement, Effecteurs, Capteurs) avec l'exemple du taxi. **Pas de schema** alors que PEAS se represente naturellement en diagramme (agent au centre, 4 composantes autour). Le texte est lisible mais austere. Footer "Intelligence(s)".

**Slide 31 (PEAS exemples - tableau)** : Tableau 5 colonnes x 5 lignes avec des exemples d'agents (diagnostic medical, satellites, robot de pieces, controleur de raffinerie, repetiteur d'anglais). Le texte est **trop petit** pour la projection - les cellules sont surchargees de mots. A eclater en 2 slides ou agrandir significativement.

**Slide 32 (Types d'environnement)** : 8 paires de proprietes listees en bullets (Observable, Deterministe, Episodique, Statique, Discret, Mono/multiagent, Connu). Dense (77 mots) mais structure. **Aucun visuel** - on pourrait illustrer chaque paire avec un exemple visuel (echecs = deterministe/connu, poker = stochastique/partiellement observable). Footer "IA 101" - retour a la coherence.

**Slide 33 (Types d'environnement exemples - tableau)** : Tableau complexe 8 colonnes x 6 lignes (Environnement / Observable / Agents / Deterministe / Episodique / Statique / Discret). Les cellules sont **minuscules et surchargees de texte** - completement illisible en projection, meme depuis la premiere rangee. Police estimee <14pt. Chaque cellule a des mots comme "Entierement", "Mono", "Semi", "Sequentiel", "Dynamique", "Continu". **Critique : a agrandir sur 2 slides** ou refaire sous forme de diagramme comparatif.

**Slide 34 (Types d'agents)** : **Tres chargee**. Bloc pseudo-code f(agent) en haut a gauche ("Architecture physique + Programme") avec detail table-driven, puis 4 bullets "Taille? Duree? Autonomie?". Puis liste "Types dans l'ordre de generalite" (4 lignes). Police petite et mise en page desequilibree - le pseudo-code prend trop d'espace pour peu de valeur. **A restructurer** : separer le concept de fonction d'agent de la liste des types.

**Slide 35 (Agent reflexe)** : **Bonne slide**. Diagramme agent-environnement AIMA avec boucle perception-decision-action a droite. Definition "Pas de memoire" et regles condition/action a gauche. En dessous, 5 blocs textuels sur l'intelligence animale (Behaviourism, Artificial Life, Cellular Automata) avec une couverture du livre "A New Kind of Science" (Wolfram). Le diagramme est clair et pertinent. La partie Wolfram est tangente mais enrichissante. Footer "IA 101".

**Slide 36 (Agent reflexe fonde sur un modele)** : Meme structure que 35 - diagramme agent-environnement a droite avec boite supplementaire "Etat" (historique + memoire). A gauche : definition "Etat du monde" avec 4 sous-bullets. En bas, exemple Subsomption (Brooks) avec 3 photos couleur d'un petit robot hexapode. Le diagramme est correct. Les photos de robot ajoutent de la credibilite concrete mais sont petites. **Nettoyage mineur** : uniformiser la taille des photos.

**Slide 37 (Agent fonde sur des buts)** : Diagramme agent-environnement avec boite "Buts" ajoutee, fleches "Comment le monde evolue-t-il ?" et "Quelle actions je dois faire ?". Definition a gauche "Reactif -> Deliberatif" avec 2 bullets (Consideration du futur, Exploration/planification). Texte sparse - **l'idee est presente mais peu developpee**. Le diagramme est pedagogiquement coherent. **Amelioration possible** : ajouter un exemple concret d'agent a buts (GPS, robot menager, agent joueur).

**Slide 38 (Agent fonde sur l'utilite)** : Meme structure que 37, avec boite "Utilite" ajoutee. Definition a gauche "Alternatives ? Niveau de succes ..." et "Fonction U : Compromise entre ..." puis "Arbitrages : Chance de succes, Importance, Urgent". Texte sparse, diagramme correct. **Meme commentaire que 37** : manque un exemple concret (trading automatique, allocation de ressources, planification sous contrainte).

**Slide 39 (Agent capable d'apprentissage)** : Diagramme agent-environnement AIME avec module "Apprentissage" central relie a "Performance", "Critique", "Generateur de probleme". A gauche : 4 bullets "Modules : Performance / Apprentissage / Critique / Generateur de probleme" puis "Plusieurs formes : Direct, Non supervise, Recompense". **Diagramme dense mais pedagogiquement important**. Les fleches sont nombreuses mais le concept d'agent apprenant est complexe par nature. Footer "IA 101".

**Slide 40 (Fonctionnement interne des agents)** : Titre + 3 concepts en bullets : "Representation de la connaissance importante", "Niveau de representation des Etats" (4 sous-items : Atomique, Indivisible, Factorise, Proprietes, Structuree, Modele/DB), "Compromis : Flexibilite vs complexite". A droite, 4 diagrammes en noir/blanc illustrant Atomique (boites simples), Factorise (variables), Structuree (arbre), (autre). Les **diagrammes sont trop petits** - texte <12pt estime, illisible en projection. **A agrandir significativement** ou eclater en 2 slides (une par niveau de representation).

**Slide 41 (Resume)** : Slide textuelle pure : 2 blocs "Intelligence artificielle" (5 bullets) et "Agents" (6 bullets). Dense (111 mots) mais **acceptable pour une slide de resume** - son role est de recapituler, pas d'illustrer. Les bullets sont courts et hierarchises. Police standard, contraste bon. Footer "IA 101". **Conserver tel quel**, eventuellement ajouter une slide "Pour aller plus loin" apres avec liens vers notebooks.

**Slide 42 (Plan du cours - closing)** : Reprise du sommaire I-VII avec "Introduction" en gris clair (fait) et le reste en noir (a venir). Coherent avec les slides de navigation du debut. Propre, sans surcharge. **Conserver**.

**Slide 43 (Merci)** : Slide finale minimaliste : "Merci" en rouge-brique, nom + email en bleu en dessous (JEAN-SYLVAIN BOIGE, jsboige@myia.org). Tres epuree, fond gris-bleu avec separateur pointille. **Parfait tel quel** - la sobriete est appropriee pour une slide de cloture.

---

## 8. Matching avec ressources etudiantes

Les presentations etudiantes les plus prometteuses pour ameliorer ce deck :

| Slide(s) a ameliorer | Ressource etudiante | Interet |
|----------------------|--------------------|---------|
| 1 (titre) | JSBoige - Intelligence Artificielle - 3h.pptx (113 slides, misc) | Visuel de titre de reference |
| 1 (titre) | Rentree ecole IA MS P2.pptx (84 slides, 17.82 MB, misc) | Probablement riche en visuels d'accroche IA |
| 13 (etat de l'art) | IA-et-Bot.pptx (13 slides, 19.73 MB, misc) | Fichier tres lourd = visuels HD |
| 15 (applications) | AI-Presentation-Chatbots.pptx (47 slides, nlp) | Applications IA modernes |
| 14 (qui fait) | Logos a chercher en ligne | OpenAI, Anthropic, Meta, DeepMind, Mistral |

### Ressources bibliographiques

| Slide(s) | Ressource | Usage |
|----------|-----------|-------|
| 2, 9 | AIMA 4th edition (2020) | Mettre a jour references |
| 13 | Timeline IA post-2020 | Recherche web pour dates/evenements |
| 35-39 | AIMA ch. 2 (Agent architectures) | Diagrammes de reference |
| 15 | conseils-slides.md (regle 1-6-6) | Restructurer les murs de texte |
