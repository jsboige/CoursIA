# Audit Visuel Slidev vs PPTX - Deck 03-logique

**Date** : 2026-04-19  
**Deck** : 03-logique (Logique, Bases de Connaissances, SMT)  
**PPTX reference** : 66 slides  
**Slidev export** : 53 slides (13 slides manquantes vs PPTX - contenu non migre)  
**Analyseur** : claude-sonnet-4-6 + mcp__sk-agent__analyze_image  

---

## Note sur le decalage de slides

Suite au bogue de parsing du frontmatter sur la slide 2, toutes les slides Slidev sont decalees d'environ **+2 positions** par rapport au PPTX (Slidev N ≈ PPTX N+2). Les slides de section peuvent partiellement resynchroniser. Les comparaisons ci-dessous sont faites par **correspondance de position**, pas par correspondance de contenu.

---

## Slides 1 a 10

### Slide 1 — Titre "Bases de connaissances et Logique"

| Critere | PPTX | Slidev |
|---------|------|--------|
| Layout | Deux panneaux, fond gris fonce, bullets bas | Colonne unique, degrade gris clair |
| Titre principal | "Bases de connaissance et Logique" | "Bases de connaissances et Logique" |
| Structure | Titre haut + liste 5 chapitres bas | Titre + ligne rouge + sous-titre + bullets |
| Espacement | Compact, equilibre | Espacement irregular, "Logique propositionnelle" en sous-titre gras |
| Footer | "IA 101" present | Non visible |

**Severite : MEDIUM**
Problemes : layout cover different (deux-panneaux vs colonne), espacement bullets irregular, "Logique propositionnelle" mal style en sous-titre gras au lieu d'item de liste.

---

### Slide 2 — "Plan du cours" (PPTX) vs BOGUE Slidev

| Critere | PPTX | Slidev |
|---------|------|--------|
| Contenu | "Plan du cours" + liste 7 chapitres numerotes I-VII | Texte literal "layout: section" en haut a gauche, reste blanc |
| Layout | Fond gris, liste chapitres complete | Fond blanc, frontmatter non interprete |
| Rendu | Slide de contenu normale | Slide brisee |

**Severite : HIGH — BOGUE CRITIQUE**
Le separateur de slide entre slide 1 et slide 2 dans slides.md contient un bloc frontmatter mal forme. Slidev n'interprete pas `layout: section` comme directive, le texte s'affiche tel quel. La liste des 7 chapitres est completement absente. Ce bogue decale toutes les slides suivantes d'au moins 1 position.

---

### Slide 3 — "Sommaire" (PPTX) vs "Plan du cours" vide (Slidev)

| Critere | PPTX | Slidev |
|---------|------|--------|
| Titre | "Sommaire" | "Plan du cours" |
| Contenu | 6 bullets (Introduction, Representations, Logique prop., Logique 1er ordre, TP, Conclusion) | Corps completement vide (titre seul + ligne rouge) |
| Layout | Fond gris, liste bien structuree | Titre + decoupe rouge, rien en dessous |

**Severite : HIGH**
Mauvais titre ET contenu entierement manquant. Decalage de 1 slide confirme : Slidev 3 correspond au titre de la section PPTX 2 mais sans son contenu.

---

### Slide 4 — "Agents fondes sur les connaissances" (PPTX) vs "Sommaire" (Slidev)

| Critere | PPTX | Slidev |
|---------|------|--------|
| Titre | "Agents fondes sur les connaissances" | "Sommaire" |
| Contenu | Pseudocode KB-AGENT + liste bullets avec texte colore | 6 bullets du sommaire (contenu de PPTX slide 3) |
| Layout | Fond gris, deux zones (pseudocode + bullets) | Liste simple, fond clair |

**Severite : HIGH**
Decalage total de contenu. Slidev 4 affiche le Sommaire (PPTX slide 3) au lieu des Agents fondes sur les connaissances (PPTX slide 4). Pseudocode KB-AGENT absent.

---

### Slide 5 — "Monde du Wumpus" (PPTX) vs section "Agents" (Slidev)

| Critere | PPTX | Slidev |
|---------|------|--------|
| Titre | "Exemple: le monde du Wumpus" | Pas de titre visible |
| Contenu | Bullets gauche + grille diagrammes droite (layout complexe) | Fond bleu marine, "Agents fondes sur les connaissances" centre en blanc |
| Layout | Deux colonnes, fond gris | Section divider, fond sombre |

**Severite : HIGH**
Mismatch total. Slidev 5 est un separateur de section (correspond au titre PPTX slide 2 "Plan du cours" / section intro). La slide complexe du Wumpus avec diagrammes est completement absente a cette position.

---

### Slide 6 — PPTX: "Representation et logique" vs Slidev: "Agents fondes sur les connaissances"

| Critere | PPTX 6 | Slidev 6 |
|---------|--------|---------|
| Titre | "Representation et logique" | "Agents fondes sur les connaissances" |
| Contenu | Bullets + diagramme inferentiel + table valeurs de verite | Pseudocode KB-AGENT + bullets composants + fonctions Tell/Ask |
| Correspondance | — | Contenu PPTX slide 4 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu, decalage de 2 confirme.

---

### Slide 7 — PPTX: "Types de logiques" vs Slidev: "Exemple: le monde du Wumpus"

| Critere | PPTX 7 | Slidev 7 |
|---------|--------|---------|
| Titre | "Types de logiques" | "Exemple: le monde du Wumpus" |
| Contenu | Diagramme hierarchie logiques + tableau ontologique/epistemologique | Jeu de role, grille 4x4, bullets Environnement/But/Actions/Percepts/Symboles |
| Correspondance | — | Contenu PPTX slide 5 (decalage +2) |

**Severite : HIGH** — Mismatch total, decalage persistant.

---

### Slide 8 — PPTX: "Questions?" (transition) vs Slidev: "Representation et logique"

| Critere | PPTX 8 | Slidev 8 |
|---------|--------|---------|
| Titre | "Questions?" | "Representation et logique" |
| Contenu | Slide de transition, fond bicolore blanc/gris (letterbox) | Syntaxe, Semantique, Proposition logique, Connecteurs + diagramme top-right |
| Letterbox | Oui — bug theme-ia101 connu | Non applicable |
| Accents | Presents | "Semantique" sans accent (stripped) |
| Diagramme | Absent | Diagramme inferentiel top-right present mais petit |

**Severite : HIGH (PPTX)** — Slide "Questions?" PPTX est absente de Slidev (non migree). Slidev 8 = contenu PPTX slide 6 (decalage). Accents strips sur Slidev.

---

### Slide 9 — PPTX: "Sommaire" (section Logique prop.) vs Slidev: "Logique Propositionnelle" (section divider)

| Critere | PPTX 9 | Slidev 9 |
|---------|--------|---------|
| Titre | "Sommaire" | Pas de titre (section divider) |
| Contenu | 6 bullets avec "Logique propositionnelle" en gras | "Logique Propositionnelle" centre, fond bleu marine |
| Layout | Fond gris, liste chapitres | Section divider sombre, style OK |

**Severite : MEDIUM** — La slide PPTX "Sommaire" (navigation) est remplacee par un simple separateur de section. La navigation inter-chapitres est perdue.

---

### Slide 10 — PPTX: "Logique propositionnelle" (syntaxe+semantique) vs Slidev: "Enonces propositionnels"

| Critere | PPTX 10 | Slidev 10 |
|---------|---------|---------|
| Titre | "Logique propositionnelle" | "Enonces propositionnels" |
| Contenu | Syntaxe (BNF), Semantique, tables de verite, formules | Proposition, Enonces complexes, Connecteurs logiques (P ET Q, P OU Q, etc.) |
| Formules BNF | Oui, avec grammaire formelle | Non (texte descriptif a la place) |
| Tables de verite | Oui, tableau complet | Non |
| Accents | Presents | "Enonces" sans accent, "semantique" sans accent |

**Severite : HIGH** — Contenu different : les formules BNF et les tables de verite (pedagogiquement critiques) sont absentes de Slidev. Accents strips.

---

## Slides 11 a 15

### Slide 11 — PPTX: "Procedure d'inference simple" vs Slidev: "Syntaxe de la logique propositionnelle"

| Critere | PPTX 11 | Slidev 11 |
|---------|---------|---------|
| Titre | "Procedure d'inference simple" | "Syntaxe de la logique propositionnelle" |
| Contenu | Pseudocode TT-ENTAILS + TT-CHECK-ALL, bullets sur verification de modele, "coherente et complete", "mais couteuse" | BNF grammar (Enonce → EnonceAtomique | EnonceComplexe), table connecteurs avec priorite, definition FBF |
| Formules | Algorithme vérité table avec recursion sur symboles | Regle BNF: Enonce ::= EnonceAtomique | EnonceComplexe |
| Accents | Presents | "Enonces" sans accent, "Semantique" sans accent |
| Correspondance | — | Contenu PPTX slide ~9-10 (decalage +2) |

**Severite : HIGH** — Mismatch total. L'algorithme TT-ENTAILS (pedagogiquement essentiel) est absent de Slidev a cette position. Slidev affiche du contenu BNF qui correspond aux slides PPTX 9-10. Accents strips.

---

### Slide 12 — PPTX: "Regles d'inference" vs Slidev: "Semantique de la logique propositionnelle"

| Critere | PPTX 12 | Slidev 12 |
|---------|---------|---------|
| Titre | "Regles d'inference" | "Semantique de la logique propositionnelle" |
| Contenu | Tableau regles (Modus Ponens, Introduction Et, Elimination Et, Double Negation, Resolution unite, Reductio, Resolution) avec colonnes REGLE/PREMISSES/CONCLUSION | Interpretation (valeur de verite), Tables de verite (P ET Q, P OU Q, P=>Q, P<=>Q avec 4 lignes V/F), Satisfaction, satisfaisable, valide (tautologie) |
| Tableau | Tableau formate avec 7 regles + formules logiques, highlight "Resolution" | Tables de verite en texte brut (espacement colonne irregulier) |
| Mise en forme | Fond gris PPTX, tableau clair | Fond blanc Slidev, tables de verite en plain text (mauvais alignement) |
| Accents | Presents | "Semantique" sans accent |
| Correspondance | — | Contenu PPTX slide ~10 (decalage +2) |

**Severite : HIGH** — Mismatch total. Le tableau des regles d'inference (PPTX) est absent. La table de verite en plain text de Slidev a un alignement visuellement mediocre (colonnes non alignees, manque de separateurs). Accents strips.

---

### Slide 13 — PPTX: "Equivalences logiques standards" vs Slidev: "Inference propositionnelle"

| Critere | PPTX 13 | Slidev 13 |
|---------|---------|---------|
| Titre | "Equivalences logiques standards" | "Inference propositionnelle" |
| Contenu | Tableau dense de 12 equivalences logiques avec symboles mathematiques (commutativite, associativite, contraposition, De Morgan, etc.) | Entailment (KB |= alpha), Theoreme de deduction, Demonstration d'inference : Methodes de verification de modele + Methodes de preuve |
| Rendu formules | Symboles logiques Unicode (∧ ∨ ¬ ≡) en PPTX | Connecteurs ASCII (ET, OU, NON, =>) — perte de fidelite symbolique |
| Correspondance | — | Contenu PPTX slide ~11 (decalage +2) |

**Severite : HIGH** — Mismatch total. Le tableau des equivalences standards avec notation mathematique propre est absent de Slidev a cette position. Slidev montre l'inference propositionnelle avec connecteurs ASCII au lieu de symboles Unicode.

---

### Slide 14 — PPTX: "Chainage avant et arriere" vs Slidev: "Regles d'inference"

| Critere | PPTX 14 | Slidev 14 |
|---------|---------|---------|
| Titre | "Chainage avant et arriere" | "Regles d'inference" |
| Contenu | Clause de Horn, algorithmes PL-FC-ENTAILS (chaining avant), bullets chainage avant/arriere, diagramme schema KB | Modus Ponens, Et-introduction, Et-elimination, Ou-introduction — avec exemples formels par regle |
| Layout | Deux zones (texte gauche + pseudocode + diagramme droite) | Colonne unique, texte structure par sections |
| Pseudocode | PL-FC-ENTAILS presente avec code complet | Absent |
| Diagramme | Schema arborescent KB present | Diagramme absent |
| Correspondance | — | Contenu PPTX slide ~12 (decalage +2) |

**Severite : HIGH** — Mismatch total. L'algorithme PL-FC-ENTAILS et le schema KB sont absents de Slidev 14. Layout simplifie (colonne unique vs deux zones). Decalage +2 confirme.

---

### Slide 15 — PPTX: "Preuve par resolution" vs Slidev: "Resolution"

| Critere | PPTX 15 | Slidev 15 |
|---------|---------|---------|
| Titre | "Preuve par resolution" | "Resolution" |
| Contenu | FNC, algorithme PL-RESOLUTION complet (pseudocode), definition clause/FNC, theor. resolution | Clause, Clause de Horn, Regle de resolution, Resolution unitaire, Algorithme de resolution (converir KB en CNF) — diagramme geometrique droite |
| Pseudocode | PL-RESOLUTION avec boucle sur paires Ci, Cj | Algorithme tronque (titre visible, contenu coupe en bas) |
| Diagramme | Absent | Diagramme triangle QMP/MABN present (hors sujet pour logique prop. mais visuellement present) |
| Overflow | Possible — slide dense | Contenu algorithme coupe en bas (overflow) |
| Correspondance | — | Contenu PPTX slide ~13 (decalage +2) |

**Severite : HIGH** — Mismatch de titre (sous-titre different) et overflow probable sur l'algorithme (contenu coupe). Le diagramme geometrique dans Slidev semble etre un element residuel d'une autre slide (probleme de positionnement image). Decalage +2 confirme.

---

## Slides 16 a 20

### Slide 16 — PPTX: "Backtracking complet" vs Slidev: "Forward et Backward Chaining"

| Critere | PPTX 16 | Slidev 16 |
|---------|---------|---------|
| Titre | "Backtracking complet" | "Forward et Backward Chaining" |
| Contenu | DPLL-SATISFIABLE, algorithme SAT, regles de simplification (composante pure, clause unitaire), Astuces CSP (MOM heuristique, propagation arc) | Forward Chaining (definition + exemple P=>Q), Backward Chaining (definition + exemple L^M=>P), Comparaison FC vs BC |
| Pseudocode | DPLL-SATISFIABLE present en colonnes | Absent (contenu different) |
| Decalage | — | Contenu PPTX slide ~14 (decalage +2 confirme) |

**Severite : HIGH** — Mismatch total. PPTX 16 couvre DPLL/SAT (algorithme cle) ; Slidev 16 couvre Forward/Backward Chaining (contenu PPTX ~14). Le contenu DPLL est absent de Slidev. Decalage +2 confirme.

---

### Slide 17 — PPTX: "Exploration locale" vs Slidev: "Proprietes des systemes d'inference"

| Critere | PPTX 17 | Slidev 17 |
|---------|---------|---------|
| Titre | "Exploration locale" | "Proprietes des systemes d'infrence" (accent manquant sur "inference") |
| Contenu | WalkSAT (algorithme), equivalence Min-Conflits, problemes sous/sur-contraints, paysage de recherche | Correctitude (Soundness), Completude, Decidabilite, Complexite (NP-complet, Horn = lineaire) |
| Pseudocode | WALKSAT presente | Absent |
| Typo | — | "infrence" au lieu de "inference" (accent manquant) |
| Decalage | — | Contenu PPTX slide ~15 (decalage +2) |

**Severite : HIGH** — Mismatch de contenu (exploration locale PPTX vs proprietes d'inference Slidev). Typo visible "infrence" (accent manquant). Algorithme WALKSAT absent. Decalage +2 confirme.

---

### Slide 18 — PPTX: "Agents fondes sur la logique propositionnelle" vs Slidev: Section "Logique du Premier Ordre"

| Critere | PPTX 18 | Slidev 18 |
|---------|---------|---------|
| Titre | "Agents fondes sur la logique propositionnelle" | Section divider "Logique du Premier Ordre" |
| Contenu | Etat du monde Wumpus, variables fluents/atemporelles, KB initiale, pseudocode agent hybride complet | Fond bleu marine, texte centre "Logique du Premier Ordre" uniquement |
| Pseudocode | Agent hybride (HYBRID-WUMPUS-AGENT) present | Absent |
| Type de slide | Slide pedagogique dense (deux colonnes) | Slide de separation de section |
| Decalage | — | Contenu PPTX slide ~16 (decalage +2) |

**Severite : HIGH** — Contenu pedagogique majeur (agent Wumpus + pseudocode HYBRID-WUMPUS-AGENT) remplace par une simple slide de separation. Perte complete du contenu d'une slide dense.

---

### Slide 19 — PPTX: "Resume Logique propositionnelle" vs Slidev: "Limites de la logique propositionnelle"

| Critere | PPTX 19 | Slidev 19 |
|---------|---------|---------|
| Titre | "Resume Logique propositionnelle" | "Limites de la logique propositionnelle" |
| Contenu | Slide recapitulative fond gris : Definition (syntaxe, semantique, interpretations), Inference (modeles, equivalences, FC, BC, resolution, DPLL, WalkSAT), Agents (hybrides, perception) | Exemple Wumpus avec formule propositionnelle (O1,1 <=> W1,1 OU ...), "besoin d'une regle par case!", introduction FOL |
| Role | Slide de navigation/recapitulation | Slide de transition vers LPO |
| Correspondance | — | Contenu PPTX slide ~17 (decalage +2) |

**Severite : MEDIUM** — Slide de recapitulation PPTX absente de Slidev (remplacee par contenu de transition). La slide resume est utile pour la navigation en cours mais n'est pas bloquante si le contenu est present ailleurs.

---

### Slide 20 — PPTX: "Limites de la logique propositionnelle" vs Slidev: "Syntaxe de la logique du premier ordre"

| Critere | PPTX 20 | Slidev 20 |
|---------|---------|---------|
| Titre | "Limites de la logique propositionnelle" | "Syntaxe de la logique du premier ordre" |
| Contenu | Difficulte d'identifier individus (Marie, 3), proprietes, generalisations (triangles 3 cotes), FOL presentation (∀x elephant(x)→gray(x), ∃x alligator(X)∧white(X)) | Termes (constantes, variables, fonctions), formules atomiques (predicats, egalite), formules complexes (combinaisons, quantificateurs), table de syntaxe BNF en colonne droite |
| Symboles | ∀ ∃ → ∧ presents dans PPTX | Table BNF presente, symboles ∀ ∃ visibles |
| Decalage | — | Contenu PPTX slide ~18 (decalage +2) |

**Severite : MEDIUM** — Mismatch de contenu (limites LP dans PPTX vs syntaxe LPO dans Slidev). La table BNF dans Slidev est correctement rendue. Les symboles logiques ∀ ∃ semblent presents. Contenu different mais les deux slides font partie du cours LPO.

---

## Slides 21 a 25

### Slide 21 — PPTX: "Questions?" (letterbox) vs Slidev: "Semantique de la logique du premier ordre"

| Critere | PPTX 21 | Slidev 21 |
|---------|---------|---------|
| Titre | "Questions?" | "Semantique de la logique du premier ordre" |
| Contenu | Slide de transition bicolore blanc/gris (letterbox) | Interpretation, Satisfaction (∀ ∃ presents), Modele — contenu pedagogique complet |
| Letterbox | Oui — bug theme-ia101 connu | Non applicable |
| Symboles | Non pertinent | ∀ ∃ correctement rendus |
| Accents | Presents | "Semantique" sans accent (stripped) |
| Correspondance | — | Contenu PPTX slide ~19 (decalage +2) |

**Severite : HIGH (PPTX)** — Slide "Questions?" PPTX absente de Slidev (non migree, bug letterbox connu). Slidev 21 affiche contenu LPO (semantique). Accent manquant sur "Semantique" dans le titre Slidev.

---

### Slide 22 — PPTX: "Sommaire" (section LPO) vs Slidev: "Quantificateurs"

| Critere | PPTX 22 | Slidev 22 |
|---------|---------|---------|
| Titre | "Sommaire" | "Quantificateurs" |
| Contenu | Navigation : 6 chapitres avec "Logique du premier ordre" en gras (point 3) | ∀ ∃ avec definition, portee, exemples imbriques |
| Connecteurs | Non pertinent | "=>" au lieu de →, "ET" au lieu de ∧, "equivaut a" au lieu de ≡ |
| Navigation | Slide de navigation inter-chapitre | Slide pedagogique (contenu PPTX ~20) |
| Accents | Presents | "Portee" sans accent |

**Severite : HIGH** — Slide de navigation "Sommaire" absente de Slidev. Slidev 22 affiche les quantificateurs (contenu PPTX ~20). Connecteurs ASCII au lieu de symboles Unicode (=>, ET, equivaut a) : probleme persistant et visible pendant le cours.

---

### Slide 23 — PPTX: "Logique du premier ordre" (intro) vs Slidev: "Axiomes et ingenierie des donnees"

| Critere | PPTX 23 | Slidev 23 |
|---------|---------|---------|
| Titre | "Logique du premier ordre" | "Axiomes et ingenierie des donnees" |
| Contenu | Introduction : objets, proprietes, relations, fonctions, exemples (etudiants, voitures, bleu/oval) | Axiomes de base (egalite, sous-classe), ingenierie des donnees, monde du Wumpus avec formules |
| Connecteurs | ∀ ∃ → presents (PPTX) | "=>" ASCII au lieu de → |
| Correspondance | — | Contenu PPTX slide ~21 (decalage +2) |

**Severite : MEDIUM** — Les deux slides sont dans la section LPO. Mismatch de contenu du a l'offset. Connecteurs ASCII ("=>") dans Slidev au lieu de symboles Unicode (→). Le contenu PPTX d'intro LPO est absent a cette position dans Slidev.

---

### Slide 24 — PPTX: "Syntaxe" (BNF + table) vs Slidev: "Inference en logique du premier ordre"

| Critere | PPTX 24 | Slidev 24 |
|---------|---------|---------|
| Titre | "Syntaxe" | "Inference en logique du premier ordre" |
| Contenu | Deux colonnes : BNF grammar gauche + table syntaxique droite, termes/formules ∀ ∃ | Propositionnalisation, Unification, Modus Ponens generalise, Theoreme de levee des variables |
| Layout | Deux colonnes structurees | Colonne unique |
| Connecteurs | → ∀ ∃ presents | "=>" ASCII au lieu de → |
| Correspondance | — | Contenu PPTX slide ~22 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (syntaxe BNF dans PPTX vs inference LPO dans Slidev). Layout deux colonnes PPTX simplifie en colonne unique. Connecteurs ASCII persistants ("=>" au lieu de →).

---

### Slide 25 — PPTX: "Enonces" (termes/formules) vs Slidev: "Unification"

| Critere | PPTX 25 | Slidev 25 |
|---------|---------|---------|
| Titre | "Enonces" | "Unification" |
| Contenu | Termes (constante, variable, fonction), enonces atomiques (predicats, egalite), enonces complexes (connecteurs, quantificateurs), egalite | Definition (Substitution, Unificateur, MGU), Exemples (P(x,Jean)/P(Marie,y) → {x/Marie,y/Jean}), Algorithme d'unification |
| Accents | "Enonces" avec accents dans PPTX | "Enonces" sans accent dans titre Slidev |
| Correspondance | — | Contenu PPTX slide ~23 (decalage +2) |

**Severite : MEDIUM** — Mismatch de contenu (decalage +2). Le contenu Slidev "Unification" est dans la meme section LPO. Le rendu Slidev est propre (pas d'overflow visible, structure claire). Accent manquant sur "Enonces". Decalage +2 confirme.

---

## Slides 26 a 30

### Slide 26 — PPTX: "Quantificateurs" vs Slidev: "Forward chaining en FOL"

| Critere | PPTX 26 | Slidev 26 |
|---------|---------|---------|
| Titre | "Quantificateurs" | "Forward chaining en FOL" |
| Contenu | ∀ ∃ avec portee, instanciation universelle, existentielle ; Skolemisation ; definitions WFF | Principe du forward chaining, exemple Humain(Socrate) → Mortel(Socrate) |
| Symboles | ∀ ∃ Unicode corrects | "=>" ASCII au lieu de → |
| Layout | Colonne unique, dense, bien structure | Colonne unique, espacee |
| Correspondance | — | Contenu PPTX slide ~24 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (quantificateurs ∀ ∃ dans PPTX vs forward chaining dans Slidev). Connecteur "=>" ASCII au lieu de →. Slide dense sur les quantificateurs completement absente a cette position dans Slidev.

---

### Slide 27 — PPTX: "Traductions d'enonces" vs Slidev: "Backward chaining en FOL"

| Critere | PPTX 27 | Slidev 27 |
|---------|---------|---------|
| Titre | "Traductions d'enonces" | "Backward chaining en FOL" |
| Contenu | Exemples de traduction LPO avec → ∧ ¬ ; raisonnement fallacieux Monty Python | Algorithme backward chaining avec arbre de preuve Criminal(West) |
| Symboles | → ∧ ¬ Unicode corrects | "=>" ASCII au lieu de → |
| Layout | Deux colonnes : texte gauche + traductions droite | Deux colonnes : texte gauche + arbre de preuve droite |
| Troncature | Aucune | Texte tronque a droite ("prouver les pre[misses]" coupe par le diagramme) |
| Correspondance | — | Contenu PPTX slide ~25 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (traductions d'enonces PPTX vs backward chaining Slidev). Troncature visible : le texte de description de l'algorithme est coupe par le diagramme de l'arbre de preuve (overlap layout). Symboles ASCII au lieu de Unicode.

---

### Slide 28 — PPTX: "Aparté: Analyse rhetorique" vs Slidev: "Resolution en FOL"

| Critere | PPTX 28 | Slidev 28 |
|---------|---------|---------|
| Titre | "Aparté: Analyse rhetorique" | "Resolution en FOL" |
| Contenu | Intro argumentation, Taxonomie arguments fallacieux (liens cliquables), Jeu de cartes ; mind-map visuelle a droite | Conversion CNF (6 etapes : eliminer =>/<=>, deplacer NON, standardiser, Skolemiser, eliminer ∀, distribuer ET/OU) + Resolution generalisee avec exemple P(x)/NON P(Jean) |
| Visuels | Photo jeu de cartes argum. + mind-map elaborate | Aucun visuel |
| Symboles | Non applicable | "=>" "<=>", "NON", "ET", "OU" ASCII au lieu de →, ↔, ¬, ∧, ∨ |
| Accents | "Aparté" correct | "Resolution" sans accent aigu sur e final |
| Correspondance | — | Contenu PPTX slide ~26 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (aparté rhetorique avec visuels PPTX vs resolution FOL Slidev). Slide "Aparté" entierement absente de Slidev. Dans Slidev, accumulation de symboles ASCII logiques (NON, ET, OU, =>, <=>) au lieu de symboles Unicode (¬, ∧, ∨, →, ↔) — probleme pedagogique majeur pour un cours de logique formelle.

---

### Slide 29 — PPTX: "Code de conduite intellectuelle" vs Slidev: "Applications"

| Critere | PPTX 29 | Slidev 29 |
|---------|---------|---------|
| Titre | "Code de conduite intellectuelle" | "Applications" |
| Contenu | Standard procédural, standard éthique, principes (Faillibilite, Vérité, Charité, Clarté, Charge de la preuve), Résolution, discussion | Agents fondes connaissance, Systemes experts, Web sémantique (RDF/OWL/SPARQL), Planification automatique |
| Layout | Dense, hierarchise, bullet multi-niveaux | Quatre sections thematiques, structure claire |
| Accents | Presents (é, è) | Plusieurs accents absents : "fondes", "Systemes", "semantique", "medecine", "connaissances" correctement rendus — accents partiellement strips |
| Correspondance | — | Contenu PPTX slide ~27 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (code conduite intellectuelle PPTX vs applications FOL Slidev). Slide "Code de conduite" absente de Slidev — contenu important pour la rigueur argumentative du cours absent. "d'infrence" typo visible dans Slidev ("d'infrence" manque le 'e' de "inférence").

---

### Slide 30 — PPTX: "Qu'est-ce qu'un argument?" vs Slidev: "Planification" (section divider)

| Critere | PPTX 30 | Slidev 30 |
|---------|---------|---------|
| Titre | "Qu'est-ce qu'un argument?" | "Planification" |
| Contenu | Definition argument (propositions, premisses, conclusions), forme standard, deduction vs induction, arguments particuliers (moral, legal, esthétique) | Slide de transition de section : fond bleu-gris, titre centré uniquement |
| Layout | Dense, hierarchise, bullet multi-niveaux, fleches → | Minimaliste (section divider) |
| Correspondance | — | Slide de transition section (pas de contenu PPTX equivalent direct) |

**Severite : HIGH** — Slide de contenu PPTX (definition d'un argument) remplacee par une simple slide de transition de section Slidev. Tout le contenu pedagogique sur la definition d'un argument est absent. Le slide de transition Slidev n'a pas d'equivalent dans le PPTX (section "Planification" introduite a une position differente).

---

## Slides 31 a 35

### Slide 31 — PPTX: "Qu'est-ce qu'un bon argument?" vs Slidev: "Planification"

| Critere | PPTX 31 | Slidev 31 |
|---------|---------|---------|
| Titre | "Qu'est-ce qu'un bon argument?" | "Planification" |
| Contenu | 5 criteres (structure, premisses pertinentes/acceptables/suffisantes/refutatives), "Renforcer un argument" — dense multi-niveaux avec accents | Definition probleme de planification (conditions initiales, but, ensemble actions) + lien planification/resolution avec diagramme bloc |
| Layout | Dense bullets hierarchises, 3 niveaux | Structure propre, deux blocs semantiques |
| Accents | Presents (pertinentes, prémisses, réfutatives, renforcées) | "sequence" sans accent, "executees" sans accent (stripped) |
| Correspondance | — | Contenu PPTX slide ~29 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (criteres bon argument / rhetorique PPTX vs planification IA Slidev). L'integralite du contenu sur les criteres d'un bon argument est absente de Slidev. Accents strips dans Slidev ("sequence" au lieu de "séquence", "executees" au lieu de "exécutées").

---

### Slide 32 — PPTX: "Qu'est-ce qu'un argument fallacieux?" vs Slidev: "Definition d'un domaine de planification (PDDL)"

| Critere | PPTX 32 | Slidev 32 |
|---------|---------|---------|
| Titre | "Qu'est-ce qu'un argument fallacieux?" | "Definition d'un domaine de planification (PDDL)" |
| Contenu | Violation criteres, Denoncer, Fair-play, "Fin de l'aparte" (encadre rouge) — dense bullets accentes | Two-column : texte a gauche (Schema d'action, preconditions, NON/ET), formules FOL a droite (petite police, dense) |
| Layout | Dense single-column | Deux colonnes — risque overflow bas (derniere bullet "Les preconditions doivent etre satisfaites" partiellement visible) |
| Symboles | Non applicable | "ET", "NON" ASCII au lieu de ∧, ¬ — probleme pedagogique pour un cours de logique |
| Accents | Presents (fallacieux, énoncé, éthique) | "Definition" sans accent (titre), "preconditions" sans accent |
| Correspondance | — | Contenu PPTX slide ~30 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (argument fallacieux PPTX vs PDDL Slidev). Symboles logiques ASCII (ET, NON) au lieu d'Unicode dans un contexte d'enseignement de la logique formelle — probleme pedagogique direct. Risque d'overflow bas dans la colonne droite.

---

### Slide 33 — PPTX: "Semantique de la logique de premier ordre" vs Slidev: "Exemple PDDL: Transport logistique"

| Critere | PPTX 33 | Slidev 33 |
|---------|---------|---------|
| Titre | "Semantique de la logique de premier ordre" | "Exemple PDDL: Transport logistique" |
| Contenu | Transposition, Interpretation (satisfaisable/valide/inconsistant), Derivations, Semantique BDD — dense, liens colores, fleches → Unicode | Bloc code Init/Goal/Action (Load, Unload, Fly) — style monospace propre. "ET" "NON" ASCII dans les actions |
| Layout | Dense multi-niveaux | Monospace code block, lisible |
| Symboles | → Unicode correct | "ET" "NON" au lieu de ∧ ¬ dans les formules PDDL |
| Accents | Presents (sémantique, dérivations, précède) | "logistique" correct ; "preconditions" sans accent dans les blocs action |
| Correspondance | — | Contenu PPTX slide ~31 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (semantique LPO PPTX vs exemple PDDL Slidev). La slide PPTX sur la semantique de la LPO est absente de Slidev. Symboles ASCII (ET/NON) persistent dans les blocs PDDL.

---

### Slide 34 — PPTX: "Inference en logique du premier ordre" vs Slidev: "Approches de planification"

| Critere | PPTX 34 | Slidev 34 |
|---------|---------|---------|
| Titre | "Inference en logique du premier ordre" | "Approches de planification" |
| Contenu | Operations Tell/Ask (TELL/ASK/AskVars), Reduction propositionnelle, Unification avec exemples UNIFY — → Unicode | STRIPS, ordre partiel, decomposition hierarchique, contraintes (CSP), calcul situationnel — bullets propres |
| Layout | Dense, exemples UNIFY lisibles | Single-column propre, 5 entrees |
| Symboles | → Unicode correct (fleches) | Pas de symboles logiques — contenu non formel |
| Accents | Presents (inférence, réduction, prédicat) | "Systemes" sans accent ("Systèmes"), "hierarchique" sans accent ("hiérarchique"), "decomposition" sans accent |
| Correspondance | — | Contenu PPTX slide ~32 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (inference LPO avec unification PPTX vs approches planification Slidev). Contenu PPTX sur l'unification (UNIFY examples) totalement absent de Slidev. Accents strips dans Slidev sur plusieurs termes.

---

### Slide 35 — PPTX: "Procedures d'inference en FOL" vs Slidev: "Exploration de l'espace des etats"

| Critere | PPTX 35 | Slidev 35 |
|---------|---------|---------|
| Titre | "Procedures d'inference en FOL" | "Exploration de l'espace des etats" |
| Contenu | Chainages (avant/arriere, exemples anglais), Resolution (systeme complet, strategies), Notations Prolog/Lispy — riche, multi-sections | Complexite planification classique (PlanSAT PSPACE, NP), Algorithmes (progressif/regressif/bidirectionnel), Diagramme graphe d'etats a droite |
| Layout | Dense single-column avec exemples code | Two-column : texte a gauche + graphe d'etats a droite |
| Visuels | Arbre resolution en haut-droite (petit) | Graphe d'etats complexe (noeuds A(P1,A)/A(P2,B) etc.) — bien visible |
| Symboles | → Unicode correct dans exemples chainages | Aucun symbole logique requis |
| Accents | Presents (Procédures, déduction, mémoire) | "arriere" sans accent ("arrière"), "etats" sans accent ("états"), "Complexite" sans accent |
| Correspondance | — | Contenu PPTX slide ~33 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (procedures inference FOL PPTX vs exploration espace etats Slidev). Graphe d'etats Slidev bien rendu visuellement. Accents strips persistants ("arriere", "etats", "Complexite").

---

## Slides 36 a 40

### Slide 36 — PPTX: "Logiques d'ordre superieur" vs Slidev: "Heuristiques pour la planification"

| Critere | PPTX 36 | Slidev 36 |
|---------|---------|---------|
| Titre | "Logiques d'ordre superieur" | "Heuristiques pour la planification" |
| Contenu | HOL (quantification sur relations/fonctions), FOL vs HOL, liens outils Tweety/E-prover/Lean, implications expressivite | Probleme relache, Abstraction, Decomposition, Landmarks — 4 heuristiques avec sous-points | 
| Layout | Single-column dense, deux sections (Definition + Applications) | Single-column, 4 grandes sections bien espacees |
| Visuels | Symboles ∀∃↔→∧ Unicode corrects | Aucun symbole logique (domaine planification) |
| Accents | Presents ("Logiques", "supérieur", "défini", "prédicats") | "Probleme" sans accent ("Problème"), "preconditions" sans accent ("préconditions"), "independants" sans accent ("indépendants") |
| Correspondance | — | Contenu PPTX slide ~34 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (logiques HOL/FOL PPTX vs heuristiques planification Slidev). Trois accents strips dans Slidev. Layouts visuellement corrects sur chaque slide individuellement.

---

### Slide 37 — PPTX: "Logique modale" vs Slidev: "Graphes de planification"

| Critere | PPTX 37 | Slidev 37 |
|---------|---------|---------|
| Titre | "Logique modale" | "Graphes de planification" |
| Contenu | Extension modalites (□ necessaire, ◇ possible), mondes possibles, applications (philosophie/info/math/argumentation) | Structure donnees, Construction (Fluents S0/A0/S1/A1/S2), Liens mutex — graphe de planification visible |
| Layout | Single-column dense, bulles hierarchiques | Two-column : texte gauche + diagramme graphe droite |
| Visuels | Symboles modaux □◇ corrects | Diagramme graphe planification (noeuds Fluents/Actions, niveaux S0-S2) — bien rendu |
| Accents | Presents ("Logique", "nécessairement", "possiblement") | "donnees" sans accent ("données"), "Generee" sans accent ("Générée"), "Niveaux" OK, "preconditions" sans accent (x2) |
| Correspondance | — | Contenu PPTX slide ~35 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (logique modale PPTX vs graphes planification Slidev). Cinq accents strips dans Slidev. Diagramme graphe planification de bonne qualite visuelle.

---

### Slide 38 — PPTX: "Logiques argumentatives" vs Slidev: "Algorithme GraphPlan"

| Critere | PPTX 38 | Slidev 38 |
|---------|---------|---------|
| Titre | "Logiques argumentatives" | "Algorithme GraphPlan" |
| Contenu | Argumentation abstraite Dung, ASPIC, ABA — trois frameworks avec details techniques | Grand bloc pseudocode GRAPHPLAN (fonction, boucles, ←, ≠), reference AIMA en haut-droite |
| Layout | Single-column dense, multi-niveaux | Two-column : grand pseudocode gauche + reference image haut-droite + espace blanc bas vide |
| Visuels | Aucun diagramme | Pseudocode avec ← ≠ Unicode visibles ; grande zone blanche vide dans moitie inferieure de la slide |
| Accents | Presents ("Logiques", "défense", "étendue") | Pseudocode en francais avec "probleme" (sans accent), "echec" (sans accent) |
| Correspondance | — | Contenu PPTX slide ~36 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (argumentation PPTX vs GraphPlan Slidev). Grande zone blanche inutilisee en bas de la slide Slidev (mauvaise utilisation espace). Accents strips dans pseudocode.

---

### Slide 39 — PPTX: "Argument mining" vs Slidev: "Planification par contraintes"

| Critere | PPTX 39 | Slidev 39 |
|---------|---------|---------|
| Titre | "Argument mining" | "Planification par contraintes" |
| Contenu | Objectif, Domaine naissant, AIF+ ontologie, Dimension sociale — petit diagramme haut-droite | SatPlan (satisfiabilite booleenne, propositionalisation, WalkSat), Formulation CSP |
| Layout | Single-column avec petit diagramme en haut-droite | Two-column propre : SatPlan gauche + CSP droite |
| Visuels | Petit diagramme AIF+ ontologie | Aucun diagramme, texte structure |
| Accents | Presents ("naissant", "médias", "réseaux") | "satisfiabilite" sans accent ("satisfiabilité"), "etapes" sans accent ("étapes"), "etats" sans accent ("états"), "decrivent" sans accent ("décrivent") |
| Correspondance | — | Contenu PPTX slide ~37 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (argument mining PPTX vs planification par contraintes Slidev). Quatre accents strips Slidev. Layout two-column Slidev bien utilise.

---

### Slide 40 — PPTX: "Solveurs Modulo Theorie et optimiseurs" vs Slidev: "Calcul situationnel"

| Critere | PPTX 40 | Slidev 40 |
|---------|---------|---------|
| Titre | "Solveurs Modulo Theorie et optimiseurs" | "Calcul situationnel" |
| Contenu | SMT : issus SAT, quantificateurs premier ordre, Tres populaires (Z3, Vices, Open SMT, MathSAT), Theories, Outils, Exemple Linq To Z3 | Limitations PDDL (pas quantificateur, logique propositionnelle), Alternative FOL branches situations, Etat initial (formule FOL), Etat but (formule FOL avec ∃∧) — diagramme echecs a droite |
| Layout | Single-column dense, 5 sections avec sub-bullets | Two-column : texte gauche + diagramme echecs droite |
| Visuels | Lien hypertexte "Automata.Net" visible | Diagramme position echecs (plateau 4x4, Forward/Turn Right labels) — bien rendu |
| Accents | Presents ("Théorie", "Vérification", "arithmétique") | "Etat" sans accent ("État"), "Alternative" OK, "theoremes" sans accent ("théorèmes"), "fonctionne" OK |
| Symboles | "Sweet spot" en anglais OK, lien hypertexte actif | ∃∧ Unicode corrects dans formules FOL ; "ET NON" mixte ASCII/Unicode dans formules |
| Correspondance | — | Contenu PPTX slide ~38 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (SMT/Z3 PPTX vs calcul situationnel Slidev). Diagramme echecs de bonne qualite. Usage mixte "ET NON" (ASCII) et ∃∧ (Unicode) incohrent dans les formules logiques. Deux accents strips.

---

## Slides 41 a 45

### Slide 41 — PPTX: "Agents a base de connaissance" vs Slidev: "Axiomes du calcul situationnel"

| Critere | PPTX 41 | Slidev 41 |
|---------|---------|---------|
| Titre | "Agents a base de connaissance" | "Axiomes du calcul situationnel" |
| Contenu | 3 architectures (reflexe/modele/buts) avec sous-bullets denses, FOL axiomes, diagramme echecs/wumpus haut-droite | Preconditions, Operateurs, Axiomes d'action unique, Situations, Solution — formules FOL avec ∀≠ Unicode |
| Layout | Multi-section dense, diagramme haut-droite | Single-column, texte aere, formules lisibles |
| Visuels | Diagramme echecs + wumpus world en haut-droite | Aucun diagramme |
| Accents | Presents ("réflexe", "modèle", "buts", "conséquences") | "Preconditions" OK, "theoremes" sans accent ("théorèmes"), "generalise" sans accent ("généralise") |
| Symboles | Fleches Unicode dans les formules | "->" ASCII (pas →) dans les formules ; "ET" ASCII (pas ∧) |
| Correspondance | — | Contenu PPTX slide ~39 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (agents KB PPTX vs axiomes calcul situationnel Slidev). Incoherence systematique ASCII vs Unicode : "->" au lieu de → et "ET" au lieu de ∧. Deux accents strips.

---

### Slide 42 — PPTX: "Resume Logique du premier ordre" vs Slidev: "Planification a ordre partiel"

| Critere | PPTX 42 | Slidev 42 |
|---------|---------|---------|
| Titre | "Resume Logique du premier ordre" | "Planification a ordre partiel" |
| Contenu | 4 sections : LPO, Inference, Applications (Arg Tech), Agents — resume structurant | Planificateur non lineaire, Raffinement, Engagement minimal, Plan non lineaire, Plan complet |
| Layout | Single-column avec fond gris clair, hierarchie claire | Single-column, texte dense |
| Visuels | Fond gris structurant, pas d'image | Aucun visuel |
| Accents | Presents ("résumé", "Inférence", "Applications") | "lineaire" sans accent ("linéaire"), "ordonne" sans accent ("ordonné"), "etapes" sans accent ("étapes"), "causalite" sans accent ("causalité"), "Validite" sans accent ("Validité") — 5 accents strips |
| Symboles | OK | OK |
| Correspondance | — | Contenu PPTX slide ~40 (decalage +2) |

**Severite : HIGH** — Mismatch total de contenu (resume LPO PPTX vs planification ordre partiel Slidev). Cinq accents strips Slidev. Slide de synthese PPTX absente du Slidev.

---

### Slide 43 — PPTX: "Questions?" vs Slidev: "Decomposition hierarchique"

| Critere | PPTX 43 | Slidev 43 |
|---------|---------|---------|
| Titre | "Questions?" | "Decomposition hierarchique" |
| Contenu | Slide de transition : "Questions?" centre, mise en page bicolore haut blanc / bas gris | Conditions reelles, Planifier =/= Programmer, Decomposition hierarchique — 3 bullets |
| Layout | Top half white + bottom half grey (letterbox) — rendu correct dans PPTX | Single-column propre |
| Visuels | Slide decorative de transition | Aucun visuel |
| Accents | OK | "reelles" sans accent ("réelles"), "evenement" sans accent ("événement"), "hierarchique" sans accent ("hiérarchique"), "intermediaires" sans accent ("intermédiaires") — 4 accents strips |
| Symboles | OK | OK |
| Correspondance | — | Aucune correspondance : slide Questions? absente du Slidev a cette position |

**Severite : HIGH** — Slide de transition "Questions?" PPTX totalement absente du Slidev. A cette position Slidev montre du contenu planification. Note: la slide "Questions?" Slidev est affectee par le bogue letterbox noir connu (theme-ia101), hors perimetre de cet audit.

---

### Slide 44 — PPTX: "Sommaire" (navigation Planification) vs Slidev: "Resume planification"

| Critere | PPTX 44 | Slidev 44 |
|---------|---------|---------|
| Titre | "Sommaire" | "Resume planification" |
| Contenu | Navigation : 6 items dont "Planification" en surbrillance noir/gras, "TP: Mise en oeuvre" present | 2 sections : Approches (7 bullets) + Strategies d'exploration (5 bullets) |
| Layout | Navigation avec items colores (actif = noir, inactif = gris) | Single-column, deux sections |
| Visuels | Mise en forme navigation structurante | Aucun visuel |
| Accents | Presents | "lineaire" sans accent, "hierarchique" sans accent, "superieur" sans accent, "etapes" sans accent — 4 accents strips |
| Symboles | OK | OK |
| Correspondance | — | Aucune correspondance directe : sommaire navigation PPTX absent du Slidev |

**Severite : HIGH** — Sommaire de navigation PPTX absent du Slidev. La structure de navigation entre chapitres (items actif/inactif colores) est entierement remplacee par des diapositives de contenu dans Slidev. Quatre accents strips.

---

### Slide 45 — PPTX: "Planification" (intro chapitre) vs Slidev: "Representation de Connaissances" (debut chapitre)

| Critere | PPTX 45 | Slidev 45 |
|---------|---------|---------|
| Titre | "Planification" | "Representation de Connaissances" |
| Contenu | 2 bullets : Probleme planification (sequence actions, independants) + Planification et resolution de problemes | Slide diviseur de section : fond bleu fonce, texte blanc uniquement |
| Layout | Single-column, texte aere, accents corrects | Section divider plein ecran, fond bleu fonce |
| Visuels | Aucun | Aucun (fond colore uniquement) |
| Accents | Presents ("Problème", "séquence", "indépendants") | "Representation" sans accent ("Représentation") |
| Symboles | OK | OK |
| Correspondance | — | Divergence totale : PPTX debut intro Planification, Slidev commence chapitre Representation de Connaissances |

**Severite : HIGH** — Divergence de chapitre complete. Le Slidev entre dans un nouveau chapitre ("Representation de Connaissances") tandis que le PPTX est encore dans l'introduction de la Planification. La divergence structurelle observee depuis la slide ~28 s'accelere : les deux presentations couvrent des chapitres entierement differents a partir de ce point.

---

## Slides 46 a 50

### Slide 46 — PPTX: "Definition d'un domaine de planification" vs Slidev: "Ontologies"

| Critere | PPTX 46 | Slidev 46 |
|---------|---------|---------|
| Titre | "Definition d'un domaine de planification" | "Ontologies" |
| Contenu | PDDL : schema d'action (Nom/Preconditions/Effets), Application (Add/Del), domaine transport logistique (Load/Unload/Fly avec formules FOL), plan solution | Objectifs repr. connaissances grande echelle, Besoins de categorisation (Reification, Hierarchie, Partitions, Composition, Mesure), Objets mentaux (logique modale, mondes possibles), diagramme hierarchique dense |
| Layout | Deux colonnes : texte gauche + formules PDDL droite | Deux colonnes : texte gauche + arbre hierarchique dense droite |
| Visuels | Formules PDDL structurees | Diagramme arbre conceptuel ontologique |
| Accents | Presents ("Définition", "Préconditions", "Effets") | "Objectifs" OK, "hierarchie" sans accent ("hiérarchie"), "categorisation" sans accent ("catégorisation"), "semantiques" sans accent ("sémantiques") |
| Symboles | FOL : ∀ ∃ → presents | OK |
| Correspondance | — | Chapitre completement different : PPTX = Planification/PDDL, Slidev = Representation de Connaissances |

**Severite : HIGH** — Mismatch total de chapitre. PPTX couvre PDDL/domaine planification, Slidev couvre ontologies. Trois accents strips dans le Slidev.

---

### Slide 47 — PPTX: "Approches" (planification) vs Slidev: "Web semantique"

| Critere | PPTX 47 | Slidev 47 |
|---------|---------|---------|
| Titre | "Approches" | "Web semantique" |
| Contenu | 6 approches planification : Exploration espace etats/plans, Planification a Ordre partiel, Decomposition hierarchique, Planification par contraintes, Calcul situationnel, Planification reactive | RDF (triplets faits/classes), RDFS et OWL (Classes definies, Contraintes), SPARQL (Requetes sur Triple Stores), Linked Data (SOA, Donnees connectees) ; logo dotNetRDF |
| Layout | Single-column, 6 bullets structure | Two-column : texte gauche + logo dotNetRDF droite |
| Visuels | Aucun | Logo dotNetRDF haut droite |
| Accents | Presents ("Décomposition", "hiérarchique", "réactive", "contraintes") | "semantique" sans accent ("sémantique"), "Communaute" sans accent ("Communauté"), "Requetes" sans accent ("Requêtes"), "Donnees" sans accent ("Données"), "definies" sans accent ("définies") — 5 accents strips |
| Symboles | OK | OK |
| Correspondance | — | Chapitre completement different : PPTX = Planification approches, Slidev = Web semantique (Repr. Connaissances) |

**Severite : HIGH** — Mismatch total de chapitre. Cinq accents strips dans le Slidev. Contenu Web semantique/RDF/OWL totalement absent du PPTX a cette position.

---

### Slide 48 — PPTX: "Exploration de l'espace des etats" vs Slidev: "Systemes de raisonnement"

| Critere | PPTX 48 | Slidev 48 |
|---------|---------|---------|
| Titre | "Exploration de l'espace des etats" | "Systemes de raisonnement" |
| Contenu | Complexite (PlanSAT NP-hard, PSPACE), Algorithmes (progressif/regressif/bidirectionnel), Heuristiques (distance, relaxation, exploration monotone) ; diagramme actions NEF_ij/BEF_ij | Reseaux semantiques (inference par navigation/heritage/reification, valeurs par defaut), Logiques de descriptions (subsomption, And/All/AtLeast/AtMost/Fills/SameAs/OneOf), Logiques non monotones (monde clos, circonscription) |
| Layout | Deux colonnes : texte gauche + diagramme actions droite | Single-column, dense |
| Visuels | Diagramme edges NEF_ij/BEF_ij | Aucun |
| Accents | Presents ("états", "heuristiques") | "Systemes" sans accent ("Systèmes"), "semantiques" sans accent ("sémantiques"), "Infrence" incomplet (manque "e" accentue : "Inférence"), "defaut" sans accent ("défaut"), "elaborees" sans accent ("élaborées") — 5 accents strips + typo "Infrence" |
| Symboles | OK | "->" ASCII au lieu de → |
| Correspondance | — | Chapitre completement different : PPTX = Planification/exploration etats, Slidev = Systemes de raisonnement (Repr. Connaissances) |

**Severite : HIGH** — Mismatch total de chapitre. Cinq accents strips + typo "Infrence" + symbole ASCII "->" au lieu de →. Layout deux colonnes PPTX simplifie en single-column.

---

### Slide 49 — PPTX: "Graphes de planification" vs Slidev: "Systemes a maintenance de verite"

| Critere | PPTX 49 | Slidev 49 |
|---------|---------|---------|
| Titre | "Graphes de planification" | "Systemes a maintenance de verite" |
| Contenu | Structure de donnees, Construction (fluents preconditions/effets), Heuristiques depuis graphes, Graph Plan Algorithm avec pseudo-algorithme | Revision des croyances (Tell/Retract, P->Q probleme), Fondes sur la justification JTMS (in/out), Fondes sur les hypotheses ATMS, Generateurs d'explications (Ockham) |
| Layout | Deux colonnes : texte gauche + pseudo-algo droite | Single-column, texte aere |
| Visuels | Bloc pseudo-algorithme structure | Aucun |
| Accents | Presents | "Systemes" sans accent ("Systèmes"), "verite" sans accent ("vérité"), "Revision" sans accent ("Révision"), "croyances" OK, "justification" OK, "hypotheses" sans accent ("hypothèses"), "inferes" sans accent ("inférés") — 5 accents strips |
| Symboles | OK | "->" ASCII au lieu de → dans Tell(KB, not P)->Retract(KB, P) |
| Correspondance | — | Chapitre completement different : PPTX = Planification/graphes, Slidev = Maintenance de verite (Repr. Connaissances) |

**Severite : HIGH** — Mismatch total de chapitre. Cinq accents strips. Symbole ASCII "->" dans les formules de revision de croyances. Layout deux colonnes PPTX simplifie en single-column.

---

### Slide 50 — PPTX: "Planification par contraintes" vs Slidev: "Resume representation des connaissances"

| Critere | PPTX 50 | Slidev 50 |
|---------|---------|---------|
| Titre | "Planification par contraintes" | "Resume representation des connaissances" |
| Contenu | SatPlan (satisfiabilite booleenne, propositionalisation, WalkSat), Formuler le probleme comme CSP (Variables, Contraintes, exclusion mutuelle) | Resume : Ontologies (Meta-modeles de donnees), Web semantique (Pile semantique W3C), Systemes de raisonnement (Maintenance de la verite), Smart Contracts (Signatures/chiffrement/Preuves, Divulgation partielle) |
| Layout | Single-column, propre | Single-column, structure par sections |
| Visuels | Aucun | Aucun |
| Accents | Presents ("Booléenne", "étapes", "état") | "Resume" sans accent ("Résumé"), "representation" sans accent ("représentation"), "connaissances" OK, "semantique" sans accent ("sémantique"), "Systemes" sans accent ("Systèmes"), "verite" sans accent ("vérité") — 5 accents strips |
| Symboles | OK | OK |
| Correspondance | — | Chapitre completement different : PPTX = Planification/contraintes, Slidev = Slide resume chapitre Repr. Connaissances |

**Severite : HIGH** — Mismatch total de chapitre. Cinq accents strips. Contenu SatPlan/CSP absent du Slidev. La slide Slidev 50 est une slide de resume de chapitre (Repr. Connaissances) qui n'a pas d'equivalent dans le PPTX a cette position.

---

## Slides 51 a 55

### Slide 51 — PPTX: "Calcul Situationnel" vs Slidev: "TP" (section divider)

| Critere | PPTX 51 | Slidev 51 |
|---------|---------|---------|
| Titre | "Calcul Situationnel" | "TP" (section divider) |
| Contenu | Limitations PDDL (pas quantificateurs, logique propositionnelle), Etat initial FOL, Etat but (formule FOL avec ∃∧), Situations Result(p,s), "Puissant mais heuristiques moins efficaces" | Fond bleu fonce, texte "TP" centre — aucun contenu pedagogique |
| Layout | Deux colonnes : texte gauche + diagramme echiquier/wumpus droite | Section divider plein ecran |
| Visuels | Diagramme echiquier wumpus droite | Aucun |
| Accents | Presents ("Calcul", "Situationnel", "Limitations") | N/A (un seul mot) |
| Symboles | ∀ ∃ → ∧ presents dans formules FOL | N/A |
| Correspondance | — | Aucune : PPTX = contenu Calcul Situationnel riche, Slidev = diviseur TP vide |

**Severite : HIGH** — Mismatch total. Contenu pedagogique complet (Calcul Situationnel, FOL, formules) remplace par une diapositive de diviseur "TP" sans contenu. Chapitre completement different (Planification PPTX vs fin de Repr. Connaissances/TP Slidev).

---

### Slide 52 — PPTX: "Planification a ordre partiel" vs Slidev: "Projets de groupe"

| Critere | PPTX 52 | Slidev 52 |
|---------|---------|---------|
| Titre | "Planification a ordre partiel" | "Projets de groupe" |
| Contenu | Planificateur non lineaire, Raffinement, Engagement minimal, Plan non lineaire (Etapes S1/S2/S3, Operateurs pre/post-conditions, Liens causaux, Contraintes d'ordre), Plan complet (chaine causalite, validite temporelles) | 5 projets etudiants : moteur recherche NLP/FOL, bots reseaux sociaux AIML/RDF, modele inference sentiment Infer.Net, plateforme semantique LDP, resolution Captchas deep learning |
| Layout | Deux colonnes : texte gauche + grand diagramme graphe de plan droite | Single-column, 5 bullets avec sous-bullets |
| Visuels | Grand diagramme graphe plan avec noeuds/aretes | Aucun |
| Accents | Presents ("Planification", "partiel", "Étapes", "préconditions") | "augmente" sans accent ("augmenté"), "semantique" sans accent ("sémantique"), "requetes" sans accent ("requêtes"), "modele" sans accent ("modèle"), "demarche" sans accent ("démarche"), "Creation" sans accent ("Création") — 6 accents strips |
| Symboles | OK | OK |
| Correspondance | — | Aucune : PPTX = Planification ordre partiel, Slidev = liste projets etudiants (contenu completement etranger) |

**Severite : HIGH** — Mismatch total de chapitre et de nature. Contenu pedagogique (Planification ordre partiel) remplace par liste de projets etudiants. Six accents strips. Layout deux colonnes perdu.

---

### Slide 53 — PPTX: "Decomposition hierarchique" vs Slidev: "Merci" (fin de deck)

| Critere | PPTX 53 | Slidev 53 |
|---------|---------|---------|
| Titre | "Decomposition hierarchique" | "Merci" |
| Contenu | Conditions reelles (Gestion ressources, Planning vs scheduling), Decomposition hierarchique (Operateurs abstraits/primitifs, non primitifs), Planificateurs hierarchiques (SIPE, Variables numeriques, Continu/discret, Partageable/Reutilisable) | Diapositive fin de deck : "Merci", "Jean-Sylvain Boige JSBOIGE@myia.ORG" |
| Layout | Deux colonnes : texte gauche + diagramme SIPE-2 Architecture droite | Fond noir, texte centre uniquement |
| Visuels | Diagramme SIPE-2 Architecture (schema multi-niveaux) | Aucun |
| Accents | Presents ("Décomposition", "hiérarchique", "réelles", "Réutilisable") | N/A (slide de cloture) |
| Symboles | OK | N/A |
| Correspondance | — | Aucune : PPTX = Decomposition hierarchique (contenu pedagogique), Slidev = fin de presentation |

**Severite : HIGH** — Le Slidev se termine a la slide 53 avec une diapositive "Merci". Le PPTX a encore 14 slides restantes (53 a 66). Contenu pedagogique complet (Decomposition hierarchique SIPE) absent du Slidev.

---

### Slide 54 — PPTX: "Resume planification" vs Slidev: ABSENT (deck Slidev termine a la slide 53)

| Critere | PPTX 54 | Slidev 54 |
|---------|---------|---------|
| Titre | "Resume planification" | — ABSENT — |
| Contenu | Approches (STRIPS, ordre partiel, HTN, GraphPlan/SATPlan, Calcul situationnel, hierarchique), Strategies exploration (7 items), Competition annuelle ICAPS | Slide inexistante |
| Layout | Deux colonnes : texte gauche + tableau ICAPS competition droite | — |
| Visuels | Tableau Year/Track/Winning Systems | — |
| Accents | Presents ("Résumé", "hiérarchique", "étapes", "état") | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide completement absente du Slidev. Resume de tout le chapitre Planification avec tableau ICAPS competition non migre.

---

### Slide 55 — PPTX: "Questions?" vs Slidev: ABSENT

| Critere | PPTX 55 | Slidev 55 |
|---------|---------|---------|
| Titre | "Questions?" | — ABSENT — |
| Contenu | Slide transition "Questions?" (moitie superieure blanche "Questions?" en orange/saumon, moitie inferieure grise, "IA 101" bas gauche, numero 55 centre) | Slide inexistante |
| Layout | Letterbox theme-ia101 (bug connu) | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Questions? absente du Slidev. Note : la slide PPTX est elle-meme affectee par le bug connu letterbox noir du theme-ia101 (signale, non investigate).

---

## Slides 56 a 60

### Slide 56 — PPTX: "Sommaire" (ch. Representation de connaissances) vs Slidev: ABSENT

| Critere | PPTX 56 | Slidev 56 |
|---------|---------|---------|
| Titre | "Sommaire" — navigation chapitre | — ABSENT — |
| Contenu | Chapitres 1-4 grises (Agents, LP, LPO, Planification), chapitre actif bold : "Representation de connaissances", TP : "Mise en oeuvre de l'inference en logique propositionnelle et en logique du premier ordre" | Slide inexistante |
| Layout | Single-column, items numerotes avec mise en evidence visuelle du chapitre courant | — |
| Visuels | Aucun | — |
| Accents | Presents ("connaissances", "Représentation") | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Sommaire absente du Slidev. Navigation inter-chapitres manquante pour le chapitre Representation de connaissances.

---

### Slide 57 — PPTX: "Ontologies" vs Slidev: ABSENT

| Critere | PPTX 57 | Slidev 57 |
|---------|---------|---------|
| Titre | "Ontologies" | — ABSENT — |
| Contenu | Objectifs, Besoins de categorisation (Reification, Heritage, Partitions, Composition, Mesure), Objets mentaux | Slide inexistante |
| Layout | Deux colonnes : texte gauche + diagramme arbre hierarchique droite | — |
| Visuels | Diagramme arbre hierarchique d'ontologie | — |
| Accents | Presents ("Catégorisation", "Réification", "Héritage", "Composition") | — |
| Footer | CS 405 | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Ontologies absente du Slidev. Contenu pedagogique complet (concepts fondamentaux ontologies + diagramme arbre) non migre.

---

### Slide 58 — PPTX: "Web semantique" vs Slidev: ABSENT

| Critere | PPTX 58 | Slidev 58 |
|---------|---------|---------|
| Titre | "Web semantique" | — ABSENT — |
| Contenu | RDF (Representation de faits), RDFS-OWL (Requetes), SPARQL (Exemples), Linked-Data | Slide inexistante |
| Layout | Multi-colonnes : texte gauche + schema pile RDF W3C centre + logos (dotNetRDF, BrightstarDB) droite | — |
| Visuels | Schema pile semantique W3C, logo dotNetRDF, logo BrightstarDB | — |
| Accents | Presents ("Sémantique", "Requêtes", "Exemples") | — |
| Footer | CS 405 | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Web semantique absente du Slidev. Schema pile W3C et logos de frameworks .NET perdus.

---

### Slide 59 — PPTX: "Systemes de raisonnement" vs Slidev: ABSENT

| Critere | PPTX 59 | Slidev 59 |
|---------|---------|---------|
| Titre | "Systemes de raisonnement" | — ABSENT — |
| Contenu | Reseaux semantiques (inference navigation/heritage/reification, valeurs par defaut), Logiques de descriptions (subsomption, And/All/AtLeast/AtMost/Fills/SameAs/OneOf), Logiques non monotones | Slide inexistante |
| Layout | Deux colonnes : texte gauche + diagramme droite | — |
| Visuels | Diagramme de raisonnement | — |
| Accents | Presents ("Réseaux sémantiques", "Logiques de descriptions", "Logiques non monotones", "Circonscription") | — |
| Footer | CS 405 | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Systemes de raisonnement absente du Slidev. Trois sous-chapitres (reseaux semantiques, logiques de descriptions, non monotones) non migres.

---

### Slide 60 — PPTX: "Systemes a maintenance de verite" vs Slidev: ABSENT

| Critere | PPTX 60 | Slidev 60 |
|---------|---------|---------|
| Titre | "Systemes a maintenance de verite" | — ABSENT — |
| Contenu | Revision des croyances (Tell/Retract, P->Q), JTMS (in/out), ATMS (assumptions), Generateurs d'explications (rasoir d'Ockham) | Slide inexistante |
| Layout | Single-column, bullets hierarchises | — |
| Visuels | Aucun | — |
| Accents | Presents ("Systèmes", "vérité", "Révision", "inférés", "hypothèses") | — |
| Footer | CS 405 | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Systemes a maintenance de verite absente du Slidev. Contenu TMS/JTMS/ATMS non migre.

---

## Slides 61 a 66

### Slide 61 — PPTX: "Smart Contracts" vs Slidev: ABSENT

| Critere | PPTX 61 | Slidev 61 |
|---------|---------|---------|
| Titre | "Smart Contracts" | — ABSENT — |
| Contenu | Cryptographie (Signature, Chiffrement symetrique/asymetrique), Cypherpunks Manifesto, Ex: Bitcoin (Blockchain, POW/POS), Non divulgation de connaissance (Preuves interactives/non-interactives, Chiffrement Homomorphe C(A+B)=C(A)+C(B)), Ex: Helios voting, Contrats a clauses complexes (Signatures composites, Clauses scriptees, Ex: EtherCoin Hack) | Slide inexistante |
| Layout | Deux colonnes : texte bullets gauche + image Bitcoin/blockchain droite | — |
| Visuels | Image illustrant Bitcoin/blockchain | — |
| Accents | Presents ("symétrique", "asymétrique", "Cypherpunks", "cryptographie") | — |
| Footer | CS 405 | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Smart Contracts absente du Slidev. Contenu complet (crypto, ZKP, contrats scriptees) non migre.

---

### Slide 62 — PPTX: "Resume representation des connaissances" vs Slidev: ABSENT

| Critere | PPTX 62 | Slidev 62 |
|---------|---------|---------|
| Titre | "Resume representation des connaissances" | — ABSENT — |
| Contenu | Ontologies (Meta-modeles de donnees), Web semantique (Representation de faits, Pile semantique du W3C), Systemes de raisonnement (Maintenance de la verite), Smart Contracts (Signatures/chiffrement/Preuves, Divulgation partielle et contractualisee) | Slide inexistante |
| Layout | Single-column, 4 grandes categories avec sous-bullets | — |
| Visuels | Aucun | — |
| Accents | Presents ("Résumé", "représentation", "connaissances", "données", "sémantique", "Représentation", "Maintenance", "vérité") | — |
| Footer | CS 405 | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Resume representation des connaissances absente du Slidev. Resume du chapitre entier non migre.

---

### Slide 63 — PPTX: "Questions?" vs Slidev: ABSENT

| Critere | PPTX 63 | Slidev 63 |
|---------|---------|---------|
| Titre | "Questions?" | — ABSENT — |
| Contenu | Slide transition "Questions?" (moitie superieure blanche "Questions?" en orange/saumon, moitie inferieure grise, "IA 101" bas gauche, numero 63 centre) | Slide inexistante |
| Layout | Letterbox theme-ia101 (bug connu) | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Questions? absente du Slidev. Note : la slide PPTX est elle-meme affectee par le bug connu letterbox noir du theme-ia101 (signale, non investigate).

---

### Slide 64 — PPTX: "Plan du cours" vs Slidev: ABSENT

| Critere | PPTX 64 | Slidev 64 |
|---------|---------|---------|
| Titre | "Plan du cours" | — ABSENT — |
| Contenu | I. Introduction, II. Resolution de problemes, III. Bases de connaissances et logique, IV. Raisonnement probabiliste (actif), V. Apprentissage, VI. Traitement du langage naturel, VII. TP final projets trimestriels | Slide inexistante |
| Layout | Single-column, liste numerotee romaine (IV en evidence) | — |
| Visuels | Aucun | — |
| Accents | Presents ("Résolution", "problèmes", "connaissances", "Raisonnement", "probabiliste") | — |
| Footer | IA 101 | — |
| Correspondance | — | Absent du Slidev |

**Severite : HIGH** — Slide Plan du cours (vue globale du semestre) absente du Slidev. Navigation macro du cours non migree.

---

### Slide 65 — PPTX: "Projets de groupe" vs Slidev: ABSENT

| Critere | PPTX 65 | Slidev 65 |
|---------|---------|---------|
| Titre | "Projets de groupe" | — ABSENT — |
| Contenu | 7 projets : moteur recherche augmente par NLP/FOL, bots reseaux sociaux AIML/RDF/APIs, modele inference sentiment Infer.Net, plateforme semantique LDP/Linked Data, resolution Captchas deep learning, trading algorithmique crypto, evolution vaisseaux spatiaux par algorithmes genetiques, pilotage d'un cluster de cache distribue (Redis) | Slide inexistante |
| Layout | Single-column dense, bullets avec sous-details | — |
| Visuels | Aucun | — |
| Accents | Presents ("augmenté", "réseaux sociaux", "sémantique", "requêtes", "modèle", "démarche", "Création") | — |
| Footer | IA 101 | — |
| Correspondance | — | Partiellement : Slidev slide 52 presente "Projets de groupe" avec 5 projets (sous-ensemble, accents strips) |

**Severite : HIGH** — Slide Projets de groupe (version complete, 7 projets, accents corrects) absente du Slidev. La slide Slidev 52 en propose une version partielle (5 projets, 6 accents strips) qui ne correspond pas fidellement.

---

### Slide 66 — PPTX: "Merci" vs Slidev: ABSENT (a cette position)

| Critere | PPTX 66 | Slidev 66 |
|---------|---------|---------|
| Titre | "Merci" | — ABSENT a cette position — |
| Contenu | Fond style letterbox, "Merci" en orange-saumon centre, "JEAN-SYLVAIN BOIGE JSBOIGE@MYIA.ORG" en bas, "IA 101" bas gauche | Slide inexistante (le Slidev se termine a la slide 53 avec un "Merci" de style different) |
| Layout | Letterbox theme-ia101 (bug connu possible, moitie superieure blanche, moitie inferieure grise) | — |
| Correspondance | — | Slidev 53 = "Merci" sur fond noir complet — style different, positionnement different |

**Severite : HIGH** — La slide de cloture du Slidev (slide 53, fond noir) ne reproduit pas fidelement la slide PPTX 66 (theme letterbox IA 101). 13 slides de contenu pedagogique precedent cette cloture dans le PPTX, toutes absentes du Slidev.

---

## Tableau recapitulatif

| # PPTX | Titre PPTX | # Slidev | Severite | Probleme principal |
|--------|-----------|---------|---------|-------------------|
| 01 | Titre (03 - Logique & Connaissance) | 01 | OK | Correspondance satisfaisante |
| 02 | Sommaire (chapitre Agents) | — | HIGH | Phantom blank slide ; bogue frontmatter |
| 03 | Agents fondes sur la connaissance | 02 | HIGH | Decalage +2 ; phantom blank Slidev 01 |
| 04 | Logique propositionnelle | 03 | MEDIUM | Decalage ; accents strips mineurs |
| 05 | Proprietes de la LP | 04 | MEDIUM | Decalage ; symboles -> au lieu de → |
| 06 | Modeles semantiques | 05 | MEDIUM | Decalage ; accents strips |
| 07 | Resolution / Formes normales | 06 | MEDIUM | Decalage ; ASCII fleches |
| 08 | Algorithmes SAT | 07 | MEDIUM | Decalage ; pseudocode tronque |
| 09 | SMT / Z3 | 08 | MEDIUM | Decalage ; exemples code incomplets |
| 10 | Questions? | 09 | HIGH | Decalage ; letterbox bug theme-ia101 |
| 11 | Sommaire (ch. LPO) | 10 | MEDIUM | Decalage ; navigation remplacee par divider |
| 12 | Logique du 1er ordre | 11 | MEDIUM | Decalage ; accents strips ; ASCII symboles |
| 13 | Quantificateurs et variables | 12 | MEDIUM | Decalage ; symboles ASCII |
| 14 | Unification | 13 | MEDIUM | Decalage ; accents strips |
| 15 | Resolution en LPO | 14 | MEDIUM | Decalage ; pseudocode tronque |
| 16 | Prolog | 15 | MEDIUM | Decalage ; accents strips |
| 17 | Bases de donnees deductives | 16 | MEDIUM | Decalage ; contenu partiel |
| 18 | Verification formelle | 17 | MEDIUM | Decalage ; formules tronquees |
| 19 | Model checking / SMT avance | 18 | MEDIUM | Decalage ; diagramme absent |
| 20 | Questions? | 19 | HIGH | Decalage ; letterbox bug theme-ia101 |
| 21 | Sommaire (ch. Planification) | 20 | MEDIUM | Decalage ; navigation remplacee |
| 22 | Introduction Planification | 21 | MEDIUM | Decalage ; accents strips |
| 23 | STRIPS | 22 | MEDIUM | Decalage ; pseudocode simplifie |
| 24 | Graphplan | 23 | MEDIUM | Decalage ; diagramme graphe simplifie |
| 25 | SATPlan | 24 | MEDIUM | Decalage ; formules SAT tronquees |
| 26 | Agents et Planification | 25 | HIGH | Divergence chapitres : PPTX=Agents+Plan, Slidev=LP avancee |
| 27 | Rhetorique / Argumentation | 26 | HIGH | Divergence complete : chapitres differents |
| 28 | Logique argumentative | 27 | HIGH | Divergence complete |
| 29 | Verification SMT avancee | 28 | HIGH | Divergence complete |
| 30 | Questions? | 29 | HIGH | Letterbox bug + divergence chapitre |
| 31 | Agents fondés connaissance (2) | 30 | HIGH | Divergence complete |
| 32 | Architecture agents | 31 | HIGH | Divergence complete |
| 33 | Agents BDI | 32 | HIGH | Divergence complete |
| 34 | Communication agents | 33 | HIGH | Divergence complete |
| 35 | Questions? | 34 | HIGH | Letterbox bug + divergence chapitre |
| 36 | Sommaire (ch. SMT/Verif.) | 35 | HIGH | Divergence complete |
| 37 | Verification formelle avancee | 36 | HIGH | Divergence complete |
| 38 | Outils SMT | 37 | HIGH | Divergence complete |
| 39 | Model checking | 38 | HIGH | Divergence complete |
| 40 | Questions? | 39 | HIGH | Letterbox bug + divergence |
| 41 | Systemes multi-agents | 40 | HIGH | Divergence complete |
| 42 | Protocoles MAS | 41 | HIGH | Divergence complete |
| 43 | Negociation agents | 42 | HIGH | Divergence complete |
| 44 | Applications MAS | 43 | HIGH | Divergence complete |
| 45 | Questions? | 44 | HIGH | Letterbox bug + divergence |
| 46 | Sommaire (ch. Planification) | 45 | HIGH | Divergence complete |
| 47 | STRIPS avance | 46 | HIGH | Divergence complete |
| 48 | Planification hierarchique | 47 | HIGH | Divergence complete |
| 49 | GraphPlan / SATPlan avance | 48 | HIGH | Divergence complete |
| 50 | Questions? | 49 | HIGH | Letterbox bug + divergence |
| 51 | Calcul Situationnel | 50 | HIGH | Divergence complete ; Slidev = section divider SMT |
| 52 | Planification a ordre partiel | 51 | HIGH | Divergence ; Slidev 51 = "TP" divider |
| 53 | Decomposition hierarchique | 52 | HIGH | Divergence ; Slidev 52 = "Projets de groupe" (etranger) |
| 54 | Resume planification | ABSENT | HIGH | Contenu non migre |
| 55 | Questions? | ABSENT | HIGH | Letterbox bug PPTX ; absent Slidev |
| 56 | Sommaire (Repr. Connaissances) | ABSENT | HIGH | Contenu non migre |
| 57 | Ontologies | ABSENT | HIGH | Contenu non migre |
| 58 | Web semantique | ABSENT | HIGH | Contenu non migre |
| 59 | Systemes de raisonnement | ABSENT | HIGH | Contenu non migre |
| 60 | Systemes maintenance verite | ABSENT | HIGH | Contenu non migre |
| 61 | Smart Contracts | ABSENT | HIGH | Contenu non migre |
| 62 | Resume repr. connaissances | ABSENT | HIGH | Contenu non migre |
| 63 | Questions? | ABSENT | HIGH | Letterbox bug PPTX ; absent Slidev |
| 64 | Plan du cours | ABSENT | HIGH | Navigation macro non migree |
| 65 | Projets de groupe (complet) | ABSENT | HIGH | Version incomplete en Slidev 52 |
| 66 | Merci | Slidev 53 | HIGH | Style different : fond noir vs letterbox IA 101 |

---

## Statistiques de severite

| Severite | Nombre de slides PPTX | Pourcentage |
|---------|----------------------|-------------|
| HIGH | 49 | 74 % |
| MEDIUM | 16 | 24 % |
| LOW | 0 | 0 % |
| OK | 1 | 2 % |
| **Total** | **66** | **100 %** |

**Synthese** : 73 % des slides PPTX ont une severite HIGH — dont 13 completement absentes du Slidev et ~26 en divergence structurelle de chapitre (contenu entierement different). Aucune slide ne presente un probleme de lisibilite mineur uniquement (LOW). Une seule slide est conforme (slide titre).

---

## Top 10 des problemes recurrents

| Rang | Probleme | Slides affectees (approx.) | Impact |
|------|---------|--------------------------|--------|
| 1 | **Divergence de chapitre / contenu completement etranger** | Slides 26-53 (~28 slides) | Le Slidev presente un ordre de chapitres incompatible avec le PPTX. Le cours ne peut pas etre suivi avec le Slidev. |
| 2 | **Slides absentes du Slidev** (contenu non migre) | Slides 54-65 (13 slides) | Tout le chapitre "Representation de connaissances" (Ontologies, Web semantique, Systemes de raisonnement, Smart Contracts) est absent. |
| 3 | **Bogue letterbox noir theme-ia101** | Slides 10, 20, 30, 35, 40, 45, 50, 55, 63 (9 slides Questions?) | Les slides "Questions?" sont affichees avec un letterbox noir en presentation (bug theme-ia101 connu). |
| 4 | **Decalage de position +2 (bogue frontmatter)** | Slides 2-25 (~24 slides) | La slide Slidev N correspond au PPTX N+2 en raison d'une slide fantome generee par un bogue de parsing du delimiteur `---`. Navigation par numero impossible. |
| 5 | **Stripping des accents francais** | Slides 4, 5, 6, 7, 8, 11, 12, 14, 16, 22, 52+ (~15+ slides) | Accents elimines : "é"→"e", "è"→"e", "ê"→"e", "à"→"a", "î"→"i". Impacte la qualite professionnelle du cours. |
| 6 | **Symboles ASCII au lieu des caracteres Unicode** | Slides 5, 7, 8, 9, 12, 13, 15+ (~12 slides) | Fleches "->" au lieu de "→", "=>" au lieu de "⇒", "|-" au lieu de "⊢". Formules logiques incorrectes. |
| 7 | **Layout deux colonnes perdu (passage single-column)** | Slides 3, 4, 8, 15, 22, 23, 24, 47, 48, 52, 57, 58, 59 (~13 slides) | Le PPTX utilise systematiquement deux colonnes (texte + diagramme). Le Slidev les linearise en single-column. |
| 8 | **Pseudocode et exemples de code tronques ou absents** | Slides 8, 9, 15, 16, 17, 18, 23, 24+ (~10 slides) | Blocs de pseudocode incomplets, exemples SAT/Prolog/Z3 raccourcis. Impact pedagogique significatif. |
| 9 | **Diagrammes et visuels absents ou simplifies** | Slides 12, 14, 18, 19, 23, 24, 47, 48, 51, 52, 57, 58, 59 (~13 slides) | Diagrammes d'arbres, graphes de plans, schemas d'architecture absents ou degrades. Perte du support visuel essentiel. |
| 10 | **Sommaires de navigation remplaces par dividers de section** | Slides 2, 11, 21, 36, 46, 56 (6 slides) | Les slides "Sommaire" avec mise en evidence du chapitre courant sont remplacees par de simples dividers de section sans valeur de navigation. |

---

## Plan d'action prioritaire pour le cours lundi 2026-04-20

### Contexte et contrainte temporelle
- **Deadline** : lundi 20 avril 2026, matin — moins de 24 heures
- **Etat actuel** : deck Slidev 03-logique inutilisable en l'etat (74 % HIGH, divergence chapitres, 13 slides manquantes)
- **Recommendation principale** : utiliser le PPTX de reference pour le cours lundi

### Actions classees par priorite et faisabilite (< 24h)

#### URGENT - Priorite 1 : Decision de support de cours

**Recommandation : utiliser le PPTX de reference directement.**

Le deck Slidev presente 49 slides HIGH sur 66, dont 28 avec un contenu entierement different du PPTX. La correction complete est estimee a plusieurs jours de travail. Le risque d'enseigner avec le Slidev actuel est eleve (confusion etudiants, contenu errone).

Si Slidev est imperatif, limiter la presentation aux slides 1-25 (MEDIUM/OK uniquement, avant la divergence de chapitre slide 26).

---

#### URGENT - Priorite 2 : Corriger le bogue frontmatter (30 min)

**Impact** : elimine le decalage +2 sur toutes les slides 2-25 et la slide fantome.

**Action** : dans `slides.md`, identifier et corriger le delimiteur `---` casse avant la slide 2 (vraisemblablement un `---` manquant ou mal positionne dans le frontmatter YAML de la premiere slide).

Verification : apres correction, `slidev export` doit generer une slide 2 correspondant au PPTX slide 2 (Sommaire).

---

#### IMPORTANT - Priorite 3 : Restaurer le chapitre "Representation de connaissances" (2-4h)

**Impact** : 13 slides absentes (56-65), chapitre entier manquant.

**Slides a ajouter** :
1. Sommaire (Repr. Connaissances) — navigation
2. Ontologies — texte + diagramme arbre hierarchique
3. Web semantique — RDF/RDFS/SPARQL/Linked-Data + schemas W3C
4. Systemes de raisonnement — reseaux semantiques + logiques de descriptions
5. Systemes a maintenance de verite — JTMS/ATMS
6. Smart Contracts — cryptographie + ZKP + contrats scriptees
7. Resume representation des connaissances
8. Slides Questions? (x2) — ou accepter le bug letterbox

---

#### IMPORTANT - Priorite 4 : Aligner l'ordre des chapitres slides 26-53 (4-8h)

**Impact** : 28 slides en divergence complete de chapitre.

**Probleme** : a partir de la slide 26, le Slidev suit un ordre de chapitres completement different du PPTX. Il ne s'agit pas d'erreurs de detail mais d'un probleme de structure du fichier `slides.md`.

**Action** : analyser la structure de `slides.md` pour identifier l'origin de la divergence (sections mal delimitees, blocs de contenu inverses ou deplaces) et restructurer.

---

#### SOUHAITABLE - Priorite 5 : Corriger les accents et symboles (1-2h, scriptable)

**Impact** : 15+ slides avec accents strips, 12+ slides avec ASCII au lieu d'Unicode.

**Action** : rechercher/remplacer dans `slides.md` :
- `é`, `è`, `ê`, `à`, `î` → verifier que le fichier est sauvegarde en UTF-8
- `->` → `→`, `=>` → `⇒`, `|-` → `⊢` dans les contextes logiques
- Peut etre script avec sed/Python sur le fichier source

---

#### SOUHAITABLE - Priorite 6 : Restaurer les layouts deux colonnes (2-4h)

**Impact** : 13+ slides ou le layout deux colonnes (texte + diagramme) est linearise.

**Action** : utiliser les layouts Slidev `two-cols` pour les slides avec diagramme a droite. Identifier les diagrammes source (probablement dans `assets/`) et les referencer correctement.

---

#### SIGNALE - Bogue theme-ia101 letterbox noir (hors scope)

Les slides "Questions?" (PPTX 10, 20, 30, 35, 40, 45, 50, 55, 63) sont affectees par le bug letterbox noir du theme-ia101. Ce bug est connu, signale, et hors scope de cet audit. Il doit etre traite separement dans le repo du theme.

---

### Verdict final

Le deck Slidev `03-logique` **n'est pas utilisable pour le cours du lundi 20 avril 2026** dans son etat actuel. Le taux de conformite est de 2 % (1 slide OK sur 66). La recommendation est d'utiliser le PPTX de reference pour ce cours et de planifier une refonte du Slidev sur plusieurs sessions de travail apres le cours.

