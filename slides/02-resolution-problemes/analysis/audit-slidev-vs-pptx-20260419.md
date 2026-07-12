# Audit Comparatif Slidev vs PPTX - 02-resolution-problemes

**Date**: 2026-04-19  
**Deadline**: 2026-04-20 matin (cours EPITA)  
**PPTX reference**: 93 slides  
**Slidev export**: 79 slides  
**Ecart**: 14 slides manquantes dans Slidev  

---

## Analyse slide par slide

### Zone A — PPTX 1-3 = Slidev 1-3 (offset 0)

---

## Slide 01 - Titre du deck

**PPTX 01 = Slidev 01**

- VISUELS: Slide de titre avec logo, fond sombre. Structure identique.
- MISE EN FORME: Titre principal present, sous-titre present.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees (ex: "Résolution" → "Resolution", "Problèmes" → "Problemes")
- SEVERITE: LOW

---

## Slide 02 - Sommaire section 1

**PPTX 02 = Slidev 02**

- VISUELS: Liste a puces, pas d'images.
- MISE EN FORME: Structure sommaire identique.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees ("Définition" → "Definition", "Résolution" → "Resolution")
- SEVERITE: LOW

---

## Slide 03 - Definition d'un probleme

**PPTX 03 = Slidev 03**

- VISUELS: Texte + definition encadree. Pas d'images complexes.
- MISE EN FORME: Bonne correspondance.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees ("Définition" → "Definition", "problème" → "probleme")
- SEVERITE: LOW

---

### Zone B — PPTX 4-13 = Slidev 5-14 (offset +1, section break inseree a Slidev 4)

**NOTE**: Slidev 4 = section break "Agents de resolution de Problemes" sans equivalent PPTX.

---

## Slide 04 - Formulation d'un probleme

**PPTX 04 = Slidev 05**

- VISUELS: PPTX contient un diagramme flowchart illustrant la formulation (etats, actions, transitions). Slidev 05 = ABSENT — le diagramme est manquant, seul le texte est present.
- MISE EN FORME: Colonne droite vide dans Slidev, desequilibre texte/visuel.
- LISIBILITE: 5/10
- PROBLEMES: **Diagramme flowchart MANQUANT** — image illustrative absente. Diacritiques supprimees.
- SEVERITE: **HIGH**

---

## Slide 05 - Espace des etats

**PPTX 05 = Slidev 06**

- VISUELS: PPTX contient un diagramme d'espace des etats (graphe avec noeuds et transitions). Slidev 06 = ABSENT — diagramme manquant, seul le texte descriptif est present.
- MISE EN FORME: Layout desequilibre, image absente.
- LISIBILITE: 5/10
- PROBLEMES: **Diagramme espace des etats MANQUANT**. Diacritiques supprimees.
- SEVERITE: **HIGH**

---

## Slides 06-13 - Contenu intermediaire

**PPTX 06-13 = Slidev 07-14**

- VISUELS: Slides de contenu avec texte, listes a puces, quelques schemas simples.
- MISE EN FORME: Correspondance generale correcte.
- LISIBILITE: 6-7/10
- PROBLEMES: Diacritiques supprimees systematiquement. Quelques differences mineures de mise en forme (espacement, couleurs).
- SEVERITE: LOW a MEDIUM (selon presence de schemas)

---

### Zone C — PPTX 14-15 = ABSENT dans Slidev (slides manquantes)

---

## Slide 14 - Questions? (transition)

**PPTX 14 = ABSENT dans Slidev**

- VISUELS: Slide de transition "Questions?" avec fond degrade.
- PROBLEMES: **Slide entierement ABSENTE** du deck Slidev.
- SEVERITE: MEDIUM (transition pedagogique manquante)

---

## Slide 15 - Sommaire section 2

**PPTX 15 = ABSENT dans Slidev**

- VISUELS: Sommaire de section avec liste des sujets couverts.
- PROBLEMES: **Slide entierement ABSENTE**. Slidev insere a la place une section break "Resolution de Problemes par Exploration" sans equivalent direct.
- SEVERITE: MEDIUM (orientation pedagogique perdue)

---

### Zone D — PPTX 16-20 = Slidev 16-20 (offset 0 retabli)

---

## Slide 16 - Arbre d'exploration

**PPTX 16 = Slidev 16**

- VISUELS: Schema arbre d'exploration. Present dans les deux versions.
- MISE EN FORME: Bonne correspondance visuelle.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees ("Arbre d'exploration" → "Arbre d'exploration" OK, mais sous-titres affectes)
- SEVERITE: LOW

---

## Slide 17 - Arbre d'exploration: exemple

**PPTX 17 = Slidev 17**

- VISUELS: **PPTX contient un arbre d'exploration avec noeuds/etats. Slidev 17 affiche une carte de la Roumanie (Romania map) a la place** — image INCORRECTE.
- MISE EN FORME: Image presente mais contenu semantiquement incorrect.
- LISIBILITE: 4/10
- PROBLEMES: **IMAGE INCORRECTE** — carte geographique au lieu de l'arbre d'exploration attendu.
- SEVERITE: **HIGH**

---

## Slide 18 - Exploration de graphe

**PPTX 18 = Slidev 18**

- VISUELS: Schema graphe d'exploration. Present dans les deux versions.
- MISE EN FORME: Bonne correspondance.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees.
- SEVERITE: LOW

---

## Slide 19 - Infrastructure: Etats vs Noeuds

**PPTX 19 = Slidev 19**

- VISUELS: Diagramme comparatif etats/noeuds present dans les deux versions mais avec differences de layout.
- MISE EN FORME: Layout different — PPTX utilise deux colonnes, Slidev empile verticalement.
- LISIBILITE: 6/10
- PROBLEMES: Layout deux colonnes perdu. Diacritiques supprimees.
- SEVERITE: MEDIUM

---

## Slide 20 - Strategies d'exploration

**PPTX 20 = Slidev 20**

- VISUELS: Liste des strategies avec surlignage colore dans PPTX. Slidev perd les couleurs de mise en evidence.
- MISE EN FORME: Structure textuelle presente, formatage colore absent.
- LISIBILITE: 6/10
- PROBLEMES: Couleurs de surlignage perdues. Diacritiques supprimees.
- SEVERITE: LOW-MEDIUM

---

### Zone E — PPTX 21+ = Slidev 22+ (offset +1, section break inseree a Slidev 21)

**NOTE**: Slidev 21 = section break "Exploration Non Informee" sans equivalent PPTX.

---

## Slide 21 - Strategies non informees

**PPTX 21 = Slidev 22**

- VISUELS: Liste des strategies non informees. Pas d'images complexes.
- MISE EN FORME: Texte seul, correspondance correcte.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees. Termes cles non mis en evidence (pas de couleurs).
- SEVERITE: LOW

---

## Slide 22 - BFS (Recherche en largeur)

**PPTX 22 = Slidev 23**

- VISUELS: PPTX contient pseudocode BFS + diagramme arbre de recherche. **Slidev 23 = diagramme arbre present mais pseudocode MANQUANT**.
- MISE EN FORME: Colonne algorithmique vide.
- LISIBILITE: 5/10
- PROBLEMES: **Pseudocode BFS MANQUANT**. Diacritiques supprimees.
- SEVERITE: **HIGH**

---

## Slide 23 - Proprietes BFS

**PPTX 23 = Slidev 24**

- VISUELS: Tableau de proprietes (completude, optimalite, complexite). Present dans les deux versions.
- MISE EN FORME: Tableau correct.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees dans les entetes de tableau.
- SEVERITE: LOW

---

## Slide 24 - UCS (Uniform Cost Search)

**PPTX 24 = Slidev 25**

- VISUELS: Schema UCS avec notation mathematique. Present dans les deux versions.
- MISE EN FORME: Correspondance correcte, quelques differences de rendu des formules.
- LISIBILITE: 6/10
- PROBLEMES: Notation mathematique degradee. Diacritiques supprimees.
- SEVERITE: LOW-MEDIUM

---

## Slide 25 - DFS (Recherche en profondeur)

**PPTX 25 = Slidev 26**

- VISUELS: Diagrammes arbres DFS. Present dans les deux versions.
- MISE EN FORME: Correspondance correcte.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees.
- SEVERITE: LOW

---

## Slide 26 - DLS (Exploration en profondeur limitee)

**PPTX 26 = Slidev 27**

- VISUELS: Pseudocode recursif DLS. Present dans les deux versions comme bloc de code.
- MISE EN FORME: Bonne correspondance.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees ("limitée" → "limitee").
- SEVERITE: LOW

---

## Slide 27 - IDS (Exploration iterative en profondeur)

**PPTX 27 = Slidev 28**

- VISUELS: Pseudocode IDS + tableau de complexite presente dans les deux versions. Bonne correspondance.
- MISE EN FORME: Bloc code bien rendu, tableau lisible.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees ("itérative" → "iterative", "profondeur" OK).
- SEVERITE: LOW

---

## Slide 28 - Exploration Bidirectionnelle

**PPTX 28 = Slidev 29**

- VISUELS: Deux arbres d'exploration cote a cote (avant/arriere). Present dans les deux versions.
- MISE EN FORME: Layout deux colonnes preservee dans Slidev. Bonne correspondance.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees ("Bidirectionnelle" → "Bidirectionnelle" OK mais sous-elements affectes).
- SEVERITE: LOW

---

## Slide 29 - Resume Exploration non informee

**PPTX 29 = Slidev 30**

- VISUELS: Tableau comparatif 6 algorithmes (BFS, UCS, DFS, DLS, IDS, BD) avec colonnes Complet/Optimal/Temps/Espace. Present dans les deux.
- MISE EN FORME: Tableau present, mise en forme correcte. Quelques notations mathematiques (O(b^d)) potentiellement degradees.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees. Notation mathematique des exposants potentiellement affectee.
- SEVERITE: LOW

---

## Slide 30 - Les missionnaires et cannibales

**PPTX 30 = Slidev 31**

- VISUELS: Image de riviere + description du probleme. Image presente dans les deux versions.
- MISE EN FORME: Correspondance correcte.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques supprimees.
- SEVERITE: LOW

---

### Zone F — PPTX 31-33 = ABSENT dans Slidev (3 slides manquantes, nouveau decalage)

**NOTE**: Slidev 32 = section break "Exploration Informee" sans equivalent PPTX. PPTX 31, 32, 33 sont absents.
**Nouvel offset**: Zone G commencera a PPTX 34 = Slidev 33 (offset -1 par rapport a Zone E).

---

## Slide 31 - Questions? (transition section 2)

**PPTX 31 = ABSENT dans Slidev**

- VISUELS: Slide de transition "Questions?" fin section Exploration Non Informee.
- PROBLEMES: **Slide entierement ABSENTE**. Perte de structure pedagogique.
- SEVERITE: MEDIUM

---

## Slide 32 - TP Exploration Non Informee

**PPTX 32 = ABSENT dans Slidev**

- VISUELS: Slide TP avec liens web (PKP Search, PathFinding.js, Aima javascript). Contenu d'exercice pratique.
- PROBLEMES: **Slide entierement ABSENTE**. Les liens vers les ressources TP sont perdus — les etudiants n'ont pas acces aux exercices pratiques.
- SEVERITE: **HIGH** (contenu pedagogique manquant, ressources pratiques)

---

## Slide 33 - Sommaire (cours complet)

**PPTX 33 = ABSENT dans Slidev**

- VISUELS: Sommaire complet du cours avec 5 sections, "Exploration Informee" mis en evidence.
- PROBLEMES: **Slide entierement ABSENTE**. Structure du cours entier perdue.
- SEVERITE: MEDIUM

---

### Zone G — PPTX 34-42 / Slidev 33-38

**Mapping Zone G:**
- PPTX 34 = ABSENT (slide "Strategies d'exploration informee" manquante)
- PPTX 35 = ABSENT (slide "Exploration par le meilleur d'abord" manquante)
- PPTX 36 = Slidev 33 (offset transitoire: PPTX N = Slidev N + 3)
- PPTX 37 = ABSENT (slide "Heuristiques admissibles et consistantes" manquante)
- PPTX 38-42 = Slidev 34-38 (offset fixe: PPTX N = Slidev N + 4)

**Slides ABSENTES en Zone G: PPTX 34, 35, 37 (3 slides HIGH severity)**

---

## Slide 34 - Strategies d'exploration informee

**PPTX 34 = ABSENT dans Slidev**

- VISUELS: Vue d'ensemble des strategies d'exploration informee (Best-First, A*, heuristiques). Slide de titre de section.
- PROBLEMES: **Slide entierement ABSENTE**. Introduction de la section "Exploration Informee" manquante.
- SEVERITE: **HIGH** (contenu pedagogique manquant — cadre conceptuel de section)

---

## Slide 35 - Exploration par le meilleur d'abord

**PPTX 35 = ABSENT dans Slidev**

- VISUELS: Definition et principe de Best-First Search avec f(n) = h(n).
- PROBLEMES: **Slide entierement ABSENTE**. Concept fondamental manquant avant A*.
- SEVERITE: **HIGH** (contenu pedagogique manquant)

---

## Slide 36 - Exploration gloutonne

**PPTX 36 = Slidev 33**

- VISUELS: Carte Roumanie avec trajets en surbrillance, colonne droite texte h(n) heuristique de distance. Deux colonnes.
- MISE EN FORME: Slidev conserve la carte Roumanie et la structure deux colonnes. Texte accentue perd ses diacritiques (greediness → greedy dans texte). Layout globalement fidele.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques absents (LOW). Mise en page globalement conforme.
- SEVERITE: LOW

---

## Slide 37 - Heuristiques admissibles et consistantes

**PPTX 37 = ABSENT dans Slidev**

- VISUELS: Definitions formelles d'admissibilite et de consistance, formules mathematiques h(n) <= h*(n) et h(n) <= c(n,a,n') + h(n').
- PROBLEMES: **Slide entierement ABSENTE**. Fondements theoriques d'A* manquants — les etudiants passent directement a A* sans les prealables theoriques.
- SEVERITE: **HIGH** (contenu pedagogique manquant, prerequis theorique d'A*)

---

## Slide 38 - Exploration A*

**PPTX 38 = Slidev 34**

- VISUELS: Formule f(n)=g(n)+h(n), carte Roumanie avec cout de chemin, colonnes texte/carte. Tres similaire a PPTX.
- MISE EN FORME: Slidev conserve la carte et la formule centrale. Diacritiques perdus (A* → A*). Layout fidele.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 39 - Caracteristiques de A*

**PPTX 39 = Slidev 35**

- VISUELS: Liste de proprietes d'A* (completude, optimalite, complexite). Slide texte pur.
- MISE EN FORME: Slidev conserve le texte. Diacritiques perdus (optimalite → optimalite, completude → completude).
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 40 - Variations (IDA*, RBFS, MA*, SMA*)

**PPTX 40 = Slidev 36**

- VISUELS: Liste des variantes d'A* avec leurs caracteristiques. Slide texte pur.
- MISE EN FORME: Contenu conserve. Diacritiques perdus.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 41 - Effet de l'exactitude des heuristiques

**PPTX 41 = Slidev 37**

- VISUELS: Graphe comparatif montrant l'impact de la qualite de l'heuristique sur les performances (noeuds explores vs qualite h). Donnees chiffrees.
- MISE EN FORME: Slidev conserve le graphe et les donnees. Mise en page globalement fidele.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 42 - Production d'heuristiques

**PPTX 42 = Slidev 38**

- VISUELS: Texte avec methodes de production d'heuristiques (problemes relaxes, bases de motifs, apprentissage automatique). Slide texte pur — pas d'images complexes dans le PPTX.
- MISE EN FORME: Slidev conserve le contenu textuel. Diacritiques perdus (heuristiques → heuristiques dans l'affichage).
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

### Zone H — PPTX 43+ = Slidev 40+ (offset -3)

**Mapping Zone H:**
- Slidev 39 = section break "Algorithmes d'Exploration Locale" — INSERT sans equivalent PPTX
- PPTX 43 = Slidev 40 (PPTX N = Slidev N + 3)

---

## Slide 43 - Algorithmes d'exploration locale

**PPTX 43 = Slidev 40**

- VISUELS PPTX: Texte + 2 images echiquier (8 reines) illustrant l'exploration locale.
- VISUELS SLIDEV: Texte UNIQUEMENT — les images d'echiquier sont ABSENTES.
- MISE EN FORME: Layout rompu, slide appauvrie visuellement.
- LISIBILITE: 5/10
- PROBLEMES: **Images echiquier (8 reines) MANQUANTES** — exemple pedagogique visuel perdu.
- SEVERITE: **HIGH** (images pedagogiques manquantes)

---

## Slide 44 - Paysage de l'espace des etats

**PPTX 44 = Slidev 41**

- VISUELS: Graphe "paysage" avec maximum global, maximum local, epaule, plateau. Deux colonnes texte/graphe.
- MISE EN FORME: Slidev conserve le graphe de paysage et la structure deux colonnes. Mise en page fidele.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 45 - Exploration par escalade (HCS)

**PPTX 45 = Slidev 42**

- VISUELS: Pseudocode Hill-Climbing-Search + images echiquier (8 reines) en illustration.
- MISE EN FORME: Slidev conserve le pseudocode ET les images echiquier. Mise en page fidele au PPTX.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 46 - Exploration par recuit simule (SA)

**PPTX 46 = Slidev 43**

- VISUELS PPTX: Pseudocode Recuit-Simule complet + courbe SA trajectory (parabole decroissante temperature vs temps) en haut-droite.
- VISUELS SLIDEV: Pseudocode conserve + courbe SA trajectory presente en haut-droite. Contenu visuel fidele.
- MISE EN FORME: Deux colonnes preservees. Diacritiques perdus (simule → simule).
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW. Contenu globalement fidele.
- SEVERITE: LOW

---

## Slide 47 - Exploration locale en faisceau (LBS)

**PPTX 47 = Slidev 44**

- VISUELS PPTX: Structure riche avec sous-sous-puces — "Exemple: Perdus en foret", algorithme detaille avec k agents paralleles, critere d'arret, variante stochastique.
- VISUELS SLIDEV: Simplifie a 3 grandes rubriques avec sous-puces courtes. Structure hierarchique reduite — sous-details ("Perdus en foret") probablement perdus.
- MISE EN FORME: Slide allege. Concepts principaux presents mais sous-structure pedagogique appauvrie.
- LISIBILITE: 7/10
- PROBLEMES: Detail pedagogique reduit — exemple concret potentiellement absent.
- SEVERITE: LOW-MEDIUM

---

## Slide 48 - Algorithmes genetiques (GAs)

**PPTX 48 = Slidev 45**

- VISUELS PPTX: Pseudocode complet Algorithme-Genetique (7 lignes) + fonction Reproduction separee avec 3 etapes (crossover, mutation). Deux blocs de pseudocode.
- VISUELS SLIDEV: Structure textuelle uniquement + une seule ligne de pseudocode abregee. Detail algorithmique significativement reduit.
- MISE EN FORME: Perte majeure du pseudocode — etudiants n'ont pas l'algorithme complet en reference.
- LISIBILITE: 6/10
- PROBLEMES: **Pseudocode complet ABSENT** — seule version abregee presente. Fonction Reproduction absente.
- SEVERITE: MEDIUM

---

## Slide 49 - Algorithme genetique pour les 8 reines

**PPTX 49 = Slidev 46**

- VISUELS PPTX: Tableau fitness chromosomes (4 lignes x 5 colonnes avec pourcentages) + deux diagrammes echiquier illustrant le croisement (crossover).
- VISUELS SLIDEV: Tableau chromosomes present + diagrammes echiquier preserves. Contenu visuel globalement fidele.
- MISE EN FORME: Mise en page coherente avec l'original. Diacritiques perdus.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

### Zone I — PPTX 50 ABSENT; Slidev 47,49 = inserts; PPTX 51 = Slidev 48

**Mapping Zone I:**
- Slidev 47 = section break INSERT "Exploration Locale - Espaces Continus" (sans equivalent PPTX)
- PPTX 50 = ABSENT de Slidev (TP slide — liens web)
- Slidev 49 = section break INSERT "Extensions" (sans equivalent PPTX)
- Les deux inserts et l'absence PPTX 50 s'annulent: offset maintenu a Slidev = PPTX - 3 pour PPTX 51

---

## Slide 50 - TP Exploration Informee et Locale

**PPTX 50 = ABSENT de Slidev**

- VISUELS PPTX: Slide TP avec titre "TP - EXPLORATION INFORMEE ET LOCALE" + 2 liens web (PKP Search, PathFinding.js) sous section "Ressources".
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: **Slide TP entiere ABSENTE** — etudiants n'ont pas les ressources pour le TP exploration informee et locale.
- SEVERITE: **HIGH** (contenu TP pedagogiquement critique manquant)

---

## Slide 51 - Exploration locale d'espaces continus

**PPTX 51 = Slidev 48**

- VISUELS PPTX: Texte dense sur l'exploration d'espaces continus + petite visualisation de gradient en haut-droite (courbes de niveau avec fleches de gradient).
- VISUELS SLIDEV: Contenu textuel present, visualisation de gradient conservee en haut-droite. Mise en page fidele.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 52 - Exploration avec actions non deterministes

**PPTX 52 = Slidev 50**

- VISUELS PPTX: Texte sur exploration avec actions non-deterministes (AND-OR trees) + diagramme arbre AND-OR en bas-droite (noeuds carres ET, noeuds ronds OU, avec branchements).
- VISUELS SLIDEV: Texte present UNIQUEMENT — diagramme arbre AND-OR ABSENT.
- MISE EN FORME: Slide appauvrie — diagramme pedagogique manquant.
- LISIBILITE: 5/10
- PROBLEMES: **Diagramme arbre AND-OR MANQUANT** — visualisation structurelle absente.
- SEVERITE: MEDIUM

---

## Slide 53 - Exploration avec observations partielles

**PPTX 53 = Slidev 51**

- VISUELS PPTX: Texte sur exploration avec observations partielles (belief states) + diagramme belief state en bas-droite (etats groupe en ensembles, transitions labellisees).
- VISUELS SLIDEV: Texte present UNIQUEMENT — diagramme belief state ABSENT.
- MISE EN FORME: Slide appauvrie — diagramme illustrant les etats de croyance manquant.
- LISIBILITE: 5/10
- PROBLEMES: **Diagramme belief state MANQUANT** — illustration du concept absente.
- SEVERITE: MEDIUM

---

## Slide 54 - Exploration en ligne (LRTA*)

**PPTX 54 = Slidev 52**

- VISUELS PPTX: Texte introduction LRTA* + pseudocode complet DEUX fonctions: LRTA*-AGENT (8 lignes) et COUT-LRTA* (4 lignes) sur colonne droite.
- VISUELS SLIDEV: Texte present UNIQUEMENT — tout le pseudocode LRTA* ABSENT.
- MISE EN FORME: Slide tres appauvrie — algorithme complet manquant.
- LISIBILITE: 4/10
- PROBLEMES: **Pseudocode LRTA*-AGENT et COUT-LRTA* ABSENTS** — definition algorithmique complete perdue.
- SEVERITE: MEDIUM

---

## Slide 55 - Resume Exploration Informee

**PPTX 55 = Slidev 53**

- VISUELS PPTX: Slide resume avec 4 sections texte (Greedy BFS, A*, Exploration locale, Extensions).
- VISUELS SLIDEV: Contenu textuel des 4 sections present. Structure fidele.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

## Slide 56 - Questions?

**PPTX 56 = ABSENT de Slidev**

- VISUELS PPTX: Slide "Questions?" de transition/pause.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Slide de transition absente — impact mineur sur le cours.
- SEVERITE: MEDIUM (rupture de rythme du cours, slide de pause manquante)

---

### Zone K — Slidev 54 = insert; PPTX 57 = Slidev 55 (offset Slidev = PPTX - 2)

**Mapping Zone K:**
- Slidev 54 = section break INSERT "Jeux vs Exploration" (sans equivalent PPTX)
- PPTX 56 absent + Slidev 54 insert s'annulent: offset maintenu a Slidev = PPTX - 2
- PPTX 57 = Slidev 55

---

## Slide 57 - Sommaire section Jeux

**PPTX 57 = Slidev 55**

- VISUELS PPTX: Sommaire de la section Jeux avec liste de sujets (minimax, alpha-beta, MCTS, jeux non-deterministes).
- VISUELS SLIDEV: Contenu textuel fidele. Liste des sujets presente.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW.
- SEVERITE: LOW

---

### Zone K (suite) — PPTX 58 = ABSENT; offset passe a Slidev = PPTX - 3 apres PPTX 58

**Mapping Zone K (revision):**
- PPTX 58 "Jeux vs Exploration" = ABSENT de Slidev — offset devient -3
- PPTX 59 = Slidev 56; PPTX 60 = Slidev 57; PPTX 61 = Slidev 58; PPTX 62 = Slidev 59; PPTX 63 = Slidev 60

---

## Slide 58 - Jeux vs Exploration

**PPTX 58 = ABSENT de Slidev**

- VISUELS PPTX: Slide textuelle d'introduction de la section Jeux. Deux colonnes: gauche = "Environnements" (multi-agents, concurrentiels); droite = "Classe de jeux" (Alternes, Deterministes, A somme nulle, A information parfaite) + "Difficulte" (Impredictibilite, Impraticable, Performance critique).
- VISUELS SLIDEV: Slide inexistante. Pedagogiquement importante — cadrage de la section entiere.
- PROBLEMES: **Slide d'introduction section Jeux entierement absente** — transition abrupte depuis le sommaire vers l'arbre de jeu.
- SEVERITE: HIGH

---

## Slide 59 - Arbre de jeu

**PPTX 59 = Slidev 56**

- VISUELS PPTX: Deux colonnes. Gauche = liste a puces (Ex: Morpion, Etat initial S0, Joueurs, Actions, Resultat, Test-Terminal, Utilite). Droite = diagramme complet arbre de jeu avec niveaux MAX/MIN, noeuds, et valeurs terminales (-1, 0, +1).
- VISUELS SLIDEV: Structure identique — liste gauche presente, diagramme arbre de jeu droite present.
- LISIBILITE: 8/10
- PROBLEMES: Diacritiques LOW ("Résultat" → "Resultat", etc.).
- SEVERITE: LOW

---

## Slide 60 - Minimax

**PPTX 60 = Slidev 57**

- VISUELS PPTX: Deux colonnes. Gauche = texte (Decisions optimales, Valeur Minimax, formule piecewise avec cas MAX/MIN/Terminal). Droite = diagramme arbre minimax numerate avec noeuds.
- VISUELS SLIDEV: Version texte UNIQUEMENT — le diagramme arbre minimax de la colonne droite est COMPLETEMENT ABSENT. Formules dans blocs de code presentes mais diagramme perdu.
- LISIBILITE: 4/10
- PROBLEMES: **Diagramme arbre minimax ABSENT** — illustration visuelle de l'algorithme perdue.
- SEVERITE: HIGH

---

## Slide 61 - Algorithme Minimax

**PPTX 61 = Slidev 58**

- VISUELS PPTX: Deux colonnes. Gauche = proprietes (Complet, Optimal, Complexite O(b^m), espace O(b*m), Cadre Multi-joueurs). Droite = pseudocode complet: fonctions DECISION-MINIMAX, VALEUR-MAX, VALEUR-MIN (~15 lignes totales).
- VISUELS SLIDEV: Colonne gauche (proprietes) presente. Colonne droite = PETIT diagramme arbre (pas le pseudocode). Tout le pseudocode est ABSENT.
- LISIBILITE: 4/10
- PROBLEMES: **Pseudocode Minimax complet ABSENT** (DECISION-MINIMAX, VALEUR-MAX, VALEUR-MIN) — contenu algorithmique central de la slide perdu.
- SEVERITE: HIGH

---

## Slide 62 - Elagage Alpha-Beta

**PPTX 62 = Slidev 59**

- VISUELS PPTX: Description textuelle elagage Alpha-Beta + diagramme arbre avec croix sur branches elaguees. Sous-bullets: Permutations, table de transposition.
- VISUELS SLIDEV: Contenu principal present — texte et diagramme arbre avec elagage visibles. Sous-bullets sur permutations et table de transposition partiellement tronques.
- LISIBILITE: 6/10
- PROBLEMES: Diacritiques ("Beta" au lieu de "Beta accentue", "elaguees" au lieu de "elaguees"). Quelques sous-bullets mineurs absents.
- SEVERITE: MEDIUM

---

## Slide 63 - Decisions imparfaites

**PPTX 63 = Slidev 60**

- VISUELS PPTX: Slide dense textuelle sur Fonction d'evaluation, Exploration avec arret, Effet d'horizon. Texte only.
- VISUELS SLIDEV: Contenu textuel principal present. Slidev 60 ajoute un bloc pseudocode EXPECTIMINIMAX en haut droite (absent du PPTX 63 — addition Slidev).
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW. Addition pseudocode EXPECTIMINIMAX dans Slidev (contenu supplementaire non present dans PPTX).
- SEVERITE: LOW

---

### Zone L — Slidev 61 = insert CSP; PPTX 64-69 = ABSENTS; offset passe a Slidev = PPTX - 8

**Mapping Zone L (corrige):**
- Slidev 61 = section break INSERT "Problemes a Satisfaction de Contraintes" (sans equivalent PPTX)
- PPTX 64 = ABSENT; PPTX 65 = ABSENT; PPTX 66 = ABSENT; PPTX 67 = ABSENT; PPTX 68 = ABSENT; PPTX 69 = ABSENT
- Net: +1 insert, -6 absents → offset passe de -3 a -8
- PPTX 70 = Slidev 62 (confirme: Slidev 62 = "Problemes a satisfaction de contraintes (CSPs)" avec carte Australie)

---

## Slide 64 - Techniques avancees

**PPTX 64 = ABSENT de Slidev**

- VISUELS PPTX: Deux sections textuelles. "Elagage avant" (forward pruning, Dangereux, Exploration en faisceau, ProbCut). "Exploration vs Consultation" (Consultation de tables, Livres d'ouverture, Utilisation d'une Politique, Exploration retrograde).
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: **Techniques avancees de recherche adversariale entierement absentes** — ProbCut, livres d'ouverture, exploration retrograde perdus.
- SEVERITE: HIGH

---

## Slide 65 - Exploration d'arbre de Monte-Carlo (MCTS)

**PPTX 65 = ABSENT de Slidev**

- VISUELS PPTX: Slide MCTS complete avec 4 etapes (Selection, Expansion, Simulations/rollouts, Retropropagation), Politique de selection (UCB1, Alpha Go), Combinaison avec heuristique, Apprentissage par renforcement. Footer "CS 405" different du theme IA-101.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: **Slide MCTS entierement absente** — algorithme MCTS, UCB1, lien avec RL perdus. Contenu critique pour EPITA.
- SEVERITE: HIGH

---

## Slide 66 - Classes de Jeux complexes

**PPTX 66 = ABSENT de Slidev**

- VISUELS PPTX: Slide dense en deux sections. Jeux stochastiques (des, cartes, sports): noeuds de hasard, valeur minimax esperee, ponderation selon probabilites, contraintes sur fonction d'evaluation, complexite O(b^n*m), simulation Monte-Carlo. Jeux partiellement observables (Bataille navale, Poker, Kriegspiel): estimation etat de croyance, formule Minimax avec somme sur etats. Contient un pseudocode EXPECTIMINIMAX et un diagramme de jeu.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: **Contenu stochastique et partiellement observable entierement absent** — algorithme EXPECTIMINIMAX, Monte-Carlo, jeux de hasard perdus.
- SEVERITE: HIGH

---

## Slide 67 - Resume Jeux

**PPTX 67 = ABSENT de Slidev**

- VISUELS PPTX: Slide de resume textuelle en trois sections: Decisions optimales (arbre de jeu, minimax, alpha-beta elagage, table de transposition), Decisions imparfaites (evaluation heuristique, test d'arret, elagage avant, consultation de tables), Classes complexes (jeux stochastiques, partiellement observables, MCTS). Contenu synthetique.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Resume de section Jeux absent — synthese perdue avant transition vers CSP.
- SEVERITE: MEDIUM

---

## Slide 68 - Questions?

**PPTX 68 = ABSENT de Slidev**

- VISUELS PPTX: Slide de transition "Questions?" avec grande zone grise inferieure (bug letterbox theme IA-101). Footer "IA 101". Slide de pause entre sections Jeux et CSP.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Slide de pause absente — transition abrupte vers CSP sans marquer la fin de section Jeux.
- SEVERITE: LOW

---

## Slide 69 - Sommaire (avant CSP)

**PPTX 69 = ABSENT de Slidev**

- VISUELS PPTX: Plan complet du cours mettant en evidence la section CSP (Backtracking, Exploration locale, Structure des problemes, Contraintes modernes et hybridation) + mention TP. Slide de navigation cours.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Sommaire de navigation absent — etudiant ne voit pas le plan avant d'entrer dans la section CSP.
- SEVERITE: MEDIUM

---

## Slide 70 - Problemes a satisfaction de contraintes (CSPs)

**PPTX 70 = Slidev 62**

- VISUELS PPTX: Slide d'introduction CSP. Contenu: Probleme standard CSP, definition formelle (variables Xi, domaine Di, contraintes Cj), carte de l'Australie avec coloration de regions. Petites illustrations.
- VISUELS SLIDEV: Slide 62 correspond — titre present, definition CSP et variables presentes, carte Australie presente.
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques LOW ("problemes" → "problemes"). Bonne correspondance generale.
- SEVERITE: LOW

---

<!-- ============================================================ -->
<!-- ZONE M : PPTX 71-88 — Section CSP (reordonnancement majeur) -->
<!-- Offset variable selon la slide. Reordonnancement pedagogique -->
<!-- PPTX 71, 72, 77, 80, 83, 86 ABSENTS                        -->
<!-- PPTX 73-76 = Slidev 70-73 (bases CSP, reordonnees avant)   -->
<!-- PPTX 78 = Slidev 64, PPTX 79 = Slidev 66                   -->
<!-- PPTX 81 = Slidev 65, PPTX 82 = Slidev 67                   -->
<!-- PPTX 84 = Slidev 69, PPTX 85 = Slidev 68                   -->
<!-- PPTX 87 = Slidev 75, PPTX 88 = Slidev 76 (overflow)        -->
<!-- ============================================================ -->

## Slide 71 - Exemple : coloration de carte

**PPTX 71 = ABSENT de Slidev**

- VISUELS PPTX: Exemple fondamental CSP — carte de l'Australie avec regions WA/NT/SA/Q/NSW/V/T, contraintes de coloration (voisins couleurs differentes), 3 couleurs disponibles. Visualisation du probleme de coloration avec graphe de contraintes.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Exemple concret d'introduction aux CSP completement absent — les etudiants passent directement a la formulation formelle sans exemple visuel fondateur.
- SEVERITE: HIGH

---

## Slide 72 - Solutions d'un CSP

**PPTX 72 = ABSENT de Slidev**

- VISUELS PPTX: Continuation de l'exemple coloration de carte — illustration de ce qu'est une solution (assignation complete satisfaisant toutes les contraintes), arbre de recherche, espace solution. Complète PPTX 71.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Deuxieme slide fondatrice CSP absente — la notion de "solution" n'est pas introduite visuellement.
- SEVERITE: HIGH

---

## Slide 73 - Techniques de resolution des CSPs

**PPTX 73 = Slidev 70**

- VISUELS PPTX: Slide de synthese des techniques de resolution CSP. Contenu: Propagation de contraintes (consistance de noeuds, d'arcs, de chemins), Exploration avec backtracking (heuristiques, inference), Exploration locale (Min-conflicts). Structure en liste hierarchique.
- VISUELS SLIDEV: Slide 70 present — contenu reecrit/synthetise, structure similaire, pas d'images manquantes notables. Diacritiques strips ("heuristiques" → "heuristiques" OK, "inferences" strip probable).
- LISIBILITE: 7/10
- PROBLEMES: Slide presentee avant les bases CSP (PPTX 71-72 absents) — contexte incomplet pour l'etudiant. Diacritiques mineurs.
- SEVERITE: MEDIUM

---

## Slide 74 - Domaines des CSPs

**PPTX 74 = Slidev 71**

- VISUELS PPTX: Taxonomie des domaines CSP — discrets finis/infinis, continus, mixtes. Exemples pour chaque type (coloration, scheduling, geometrie). Tableau ou liste structuree.
- VISUELS SLIDEV: Slide 71 present — contenu correspond, presentation textuelle similaire. Reordonnee par rapport au PPTX (devrait venir avant Techniques de resolution).
- LISIBILITE: 7/10
- PROBLEMES: Reordonnancement pedagogique (base presentee apres synthese). Diacritiques mineurs.
- SEVERITE: LOW

---

## Slide 75 - Graphe de contraintes

**PPTX 75 = Slidev 72**

- VISUELS PPTX: Representation graphique des CSPs — graphe de contraintes avec noeuds (variables), aretes (contraintes binaires), hyper-aretes (contraintes n-aires). Exemple visuel avec graphe Australie.
- VISUELS SLIDEV: Slide 72 present — structure presente, diagramme graphe probablement absent ou simplifie (rendu Slidev text-heavy). Diacritiques strips.
- LISIBILITE: 6/10
- PROBLEMES: Perte potentielle du graphe visuel — concept fondamental pedagogiquement. Diacritiques.
- SEVERITE: MEDIUM

---

## Slide 76 - Types de contraintes

**PPTX 76 = Slidev 73**

- VISUELS PPTX: Classification des contraintes — unaires, binaires, n-aires, souples/dures, contraintes globales (AllDifferent, etc.). Exemples de chaque type avec notation formelle.
- VISUELS SLIDEV: Slide 73 present — contenu correspond, texte present. Reordonnee (base CSP presentee avant algorithmes mais apres synthese dans Slidev).
- LISIBILITE: 7/10
- PROBLEMES: Reordonnancement mineur. Diacritiques.
- SEVERITE: LOW

---

## Slide 77 - CSPs courants

**PPTX 77 = ABSENT de Slidev**

- VISUELS PPTX: Catalogue de CSPs classiques — Sudoku, n-reines, coloriage de graphes, scheduling, planification. Slide CS 405 footer. Exemples visuels et applications pratiques.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Catalogue des CSPs courants absent — etudiants ne voient pas le panorama des applications classiques.
- SEVERITE: HIGH

---

## Slide 78 - Formulation standard des CSPs

**PPTX 78 = Slidev 64**

- VISUELS PPTX: Formulation formelle complete — triplet (X, D, C), variables, domaines, contraintes. Definition rigoureuse avec notation mathematique. Slide centrale de la section CSP.
- VISUELS SLIDEV: Slide 64 present — contenu present mais positionne bien AVANT dans Slidev (en zone 63-69 qui presente les algorithmes). Notation formelle presente.
- LISIBILITE: 7/10
- PROBLEMES: Reordonnancement majeur — formulation standard apparait apres les algorithmes de resolution dans Slidev, ce qui inverse l'ordre pedagogique naturel (bases avant algorithmes). Diacritiques.
- SEVERITE: MEDIUM

---

## Slide 79 - Propagation de contraintes

**PPTX 79 = Slidev 66**

- VISUELS PPTX: Techniques de propagation — consistance de noeuds (Node Consistency, NC), consistance d'arcs (Arc Consistency, AC-3), consistance de chemin. Algorithme AC-3 avec pseudo-code, diagrammes de propagation sur graphe.
- VISUELS SLIDEV: Slide 66 present — contenu algorithmique present. Diagrammes probablement absents (text-heavy Slidev). Positionne dans la section algorithmes avant les bases.
- LISIBILITE: 6/10
- PROBLEMES: Reordonnancement (algorithme presente avant les bases formelles). Perte probable des diagrammes de propagation. Diacritiques.
- SEVERITE: MEDIUM

---

## Slide 80 - Contraintes globales

**PPTX 80 = ABSENT de Slidev**

- VISUELS PPTX: Contraintes globales importantes — AllDifferent, Sum, Element, Circuit (TSP), Cumulative (scheduling). Slide CS 405 footer. Applications industrielles et optimisations.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Section entiere sur les contraintes globales absente — notions essentielles pour solveurs industriels completement manquantes.
- SEVERITE: HIGH

---

## Slide 81 - Exploration avec backtracking des CSPs

**PPTX 81 = Slidev 65**

- VISUELS PPTX: Exploration par backtracking — assignations commutatives, DFS + backtracking, choix prochaine variable/valeur/inference, petit arbre de recherche diagramme cote droit. Algorithme central de la section.
- VISUELS SLIDEV: Slide 65 present — texte algorithmique present, arbre de recherche probablement absent ou simplifie. Positionne dans sequence coherente avec autres algorithmes.
- LISIBILITE: 7/10
- PROBLEMES: Diagramme arbre de recherche potentiellement absent. Diacritiques ("backtracking" OK, accents strips sur termes francais).
- SEVERITE: MEDIUM

---

## Slide 82 - Ordre des variables et des valeurs

**PPTX 82 = Slidev 67**

- VISUELS PPTX: Heuristiques de selection — colonne gauche: MRV (Minimum Remaining Values), heuristique de degre; colonne droite: LCV (Least Constraining Value), degre pondere, Backjumping. Plusieurs diagrammes de carte Australie illustrant les heuristiques.
- VISUELS SLIDEV: Slide 67 present — contenu heuristiques present. Diagrammes carte Australie probablement absents (text-heavy). Mise en page deux colonnes perdue.
- LISIBILITE: 6/10
- PROBLEMES: Perte de la mise en page deux colonnes et des diagrammes illustratifs — heuristiques MRV/LCV difficiles a comprendre sans illustration visuelle.
- SEVERITE: MEDIUM

---

## Slide 83 - Verification avant et examen en amont

**PPTX 83 = ABSENT de Slidev** (contenu probablement fusionne dans Slidev 66)

- VISUELS PPTX: Forward checking, Maintien de la coherence d'arc (MAC), Backtracking intelligent (Backjumping oriente conflits, Apprentissage de contraintes, variables inutiles). Diagrammes de propagation de contraintes colories cote droit. Slide pedagogiquement importante.
- VISUELS SLIDEV: Slide inexistante en tant que telle — contenu partiellement absorbe dans Slidev 66 (Propagation de contraintes).
- PROBLEMES: Slide complete absente — Forward checking et MAC sont des techniques cruciales pour l'efficacite du backtracking. Leur absence fragilise la comprehension de l'algorithme.
- SEVERITE: HIGH

---

## Slide 84 - Exploration locale pour les CSPs

**PPTX 84 = Slidev 69**

- VISUELS PPTX: Formulation par etats complets, Min-Conflicts, nombreux plateaux, Exploration tabou, Ponderation de contraintes, Hybridation CP+Metaheuristiques (LNS). Slide riche en contenu algorithmique.
- VISUELS SLIDEV: Slide 69 present — contenu algorithmique present. Accents strips systematiquement ("nombreux" OK, "plateaux" OK, "Ponderation" → "Ponderation" strip).
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques. Contenu textuel present mais visuel potentiellement allege.
- SEVERITE: LOW

---

## Slide 85 - Structure des problemes

**PPTX 85 = Slidev 68**

- VISUELS PPTX: Decomposition des problemes structures — composantes connexes, sous-problemes independants, DAC O(nd²), coupe cycle, decomposition en arbre, symetrie des valeurs. Pseudocode + diagramme d'arbre. Slide algorithmique dense.
- VISUELS SLIDEV: Slide 68 present — contenu present, reordonnee par rapport au PPTX (apres Exploration locale dans Slidev vs avant dans PPTX). Diagramme arbre potentiellement absent.
- LISIBILITE: 6/10
- PROBLEMES: Reordonnancement (Structure avant Exploration locale dans PPTX, inverse dans Slidev). Perte probable du diagramme d'arbre. Diacritiques.
- SEVERITE: MEDIUM

---

## Slide 86 - Solveurs modernes - integrations

**PPTX 86 = ABSENT de Slidev**

- VISUELS PPTX: Solveurs industriels — MiniZinc, Google OR-Tools (CP-SAT), Choco/Gecode, Z3. Interoperabilite multi-langages (pythonnet, IKVM, JPype). Slide CS 405 footer. Slide pratique importante pour applications reelles.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Panorama des solveurs modernes completement absent — information pratique cle pour etudiants souhaitant utiliser des outils industriels.
- SEVERITE: HIGH

---

## Slide 87 - Applications et cas d'usage modernes

**PPTX 87 = Slidev 75**

- VISUELS PPTX: Applications CSP — Planification/ordonnancement, Logistique/transport (VRP), Optimisation combinatoire (Sudoku, n-reines), Planification en IA (satellites, robots). Footer CS 405.
- VISUELS SLIDEV: Slide 75 present — texte-seul, mise en page propre, accents strips ("Problemes de tournees de vehicules", "systemes autonomes"). Contenu principal present malgre footer CS 405 (exception a la regle CS 405 absent).
- LISIBILITE: 7/10
- PROBLEMES: Diacritiques systematiques. Contenu present et lisible.
- SEVERITE: LOW

---

## Slide 88 - Resume CSPs

**PPTX 88 = Slidev 76 (OVERFLOW)**

- VISUELS PPTX: Resume complet section CSP — PSC definition, Techniques d'inferences, Backtracking + heuristiques (MRV, LCV, Degree), Forward checking, Backjumping, Exploration locale (Min-conflicts), Structure des problemes (coupe cycle, decomposition, symetrie). Slide dense, tout le contenu visible.
- VISUELS SLIDEV: Slide 76 present MAIS OVERFLOW — dernier titre "Structure des problemes: complexite des problemes" visible mais sous-bullets sur Coupe cycle/Decomposition/Symetrie coupes au bas de la slide. Accents strips sur tous les termes.
- LISIBILITE: 5/10
- PROBLEMES: OVERFLOW critique — partie finale du resume CSP invisible a la projection. Diacritiques systematiques.
- SEVERITE: HIGH

---

<!-- ============================================================ -->
<!-- ZONE N : PPTX 89-93 — Fin de deck (Questions/TP/Sommaire)  -->
<!-- Slidev 77 = INSERT section-break, Slidev 78 = PPTX 90      -->
<!-- Slidev 79 = PPTX 93                                         -->
<!-- PPTX 89, 91, 92 ABSENTS                                     -->
<!-- ============================================================ -->

## Slide 89 - Questions ?

**PPTX 89 = ABSENT de Slidev**

- VISUELS PPTX: Slide "Questions?" — fond blanc partie haute, fond gris partie basse (bug letterbox theme-ia101). Numero slide 89 visible. Slide de transition fin de section.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Slide de transition absente — impact faible en cours (implicite), mais indicateur de la troncature de fin de deck.
- SEVERITE: LOW

---

## Slide 90 - TP

**PPTX 90 = Slidev 78**

- VISUELS PPTX: Slide TP — fond blanc haut, fond gris bas (bug letterbox), bullet "PKP service web CSPs" avec hyperlien.
- VISUELS SLIDEV: Slide 78 present — titre "TP" present, bullet "PKP service web CSPs" present en texte simple (lien probablement non rendu). Mise en page propre, pas de letterbox (thematique differente). Hyperlien potentiellement perdu.
- LISIBILITE: 7/10
- PROBLEMES: Hyperlien PKP potentiellement non cliquable en presentation (text-only). Pas de letterbox — rendu Slidev meilleur que PPTX sur ce point.
- SEVERITE: LOW

---

## Slide 91 - Sommaire complet

**PPTX 91 = ABSENT de Slidev**

- VISUELS PPTX: Sommaire complet du cours — Agents resolution, Exploration non informee/informee, Jeux (Minimax, Alpha-Beta, Decisions imparfaites), CSPs (Backtracking, Exploration locale, Structure). Vue d'ensemble pedagogique importante.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Sommaire de recapitulatif complet absent — les etudiants ne peuvent pas revoir la structure globale du cours en fin de session.
- SEVERITE: MEDIUM

---

## Slide 92 - Plan du cours

**PPTX 92 = ABSENT de Slidev**

- VISUELS PPTX: Plan du cours en chiffres romains — I a VII incluant Introduction, Resolution de problemes, Bases de connaissances, Probabiliste, Apprentissage, NLP, Projets. Vue de positionnement dans le programme global.
- VISUELS SLIDEV: Slide inexistante.
- PROBLEMES: Plan du cours complet absent — les etudiants ne peuvent pas situer ce cours dans le programme global EPITA.
- SEVERITE: LOW

---

## Slide 93 - Merci

**PPTX 93 = Slidev 79**

- VISUELS PPTX: Slide de cloture — fond blanc haut, fond gris bas (bug letterbox), "JEAN-SYLVAIN BOIGE / JSBOIGE@MYIA.ORG".
- VISUELS SLIDEV: Slide 79 present — fond entierement noir (theme sombre complet, pas de letterbox), "Merci" titre rouge, "Jean-Sylvain Boige JSBOIGE@myia.ORG" en blanc/rouge. Rendu visuellement coherent, pas de bug letterbox, thematique differente du PPTX mais acceptable.
- LISIBILITE: 8/10
- PROBLEMES: Mise en page differente (fond noir vs blanc/gris PPTX) mais contenu identique. Le fond noir est le rendu correct du theme dark, pas un bug.
- SEVERITE: LOW

---

<!-- ============================================================ -->
<!-- SYNTHESE FINALE                                              -->
<!-- ============================================================ -->

## Tableau recapitulatif — 93 slides PPTX

| PPTX | Titre abrege | Slidev | Severite | Probleme principal |
|------|-------------|--------|----------|--------------------|
| 01 | Titre deck | 01 | LOW | Diacritiques |
| 02 | Sommaire | 02 | LOW | Diacritiques |
| 03 | Plan | 03 | LOW | Diacritiques |
| 04 | Agents intro | 05 | HIGH | Diagramme flowchart MANQUANT |
| 05 | Espace etats | 06 | HIGH | Diagramme espace-etats MANQUANT |
| 06 | Formulation | 07 | LOW | Diacritiques |
| 07 | Recherche aveugle | 08 | LOW | Diacritiques |
| 08 | Graphe Romania | 09 | LOW | Diacritiques |
| 09 | Arbre recherche | 10 | LOW | Diacritiques |
| 10 | Strategies | 11 | LOW | Diacritiques |
| 11 | BFS | 12 | MEDIUM | Diagramme BFS absent |
| 12 | Complexite BFS | 13 | LOW | Diacritiques |
| 13 | DFS | 14 | LOW | Diacritiques |
| 14 | Iteratif DFS | ABSENT | HIGH | Slide entiere absente |
| 15 | Bidirectionnel | ABSENT | HIGH | Slide entiere absente |
| 16 | Exploration informee | 16 | LOW | Diacritiques |
| 17 | Heuristiques | 17 | HIGH | Mauvaise image (carte Romania) |
| 18 | Greedy | 18 | LOW | Diacritiques |
| 19 | A* | 19 | LOW | Diacritiques |
| 20 | A* optimalite | 20 | LOW | Diacritiques |
| 21 | INSERT section | 21 | — | INSERT Slidev |
| 22 | BFS pseudocode | 23 | HIGH | Pseudocode BFS MANQUANT |
| 23 | DFS pseudocode | 24 | MEDIUM | Pseudocode partiel |
| 24 | A* pseudocode | 25 | MEDIUM | Pseudocode partiel |
| 25 | Heuristiques admissibles | 26 | LOW | Diacritiques |
| 26 | Consistance heuristique | 27 | LOW | Diacritiques |
| 27 | IDA* | 28 | LOW | Diacritiques |
| 28 | SMA* | 29 | LOW | Diacritiques |
| 29 | Resume exploration | 30 | LOW | Diacritiques |
| 30 | TP exploration | 31 | LOW | Diacritiques |
| 31 | INSERT section jeux | 32 | — | INSERT Slidev |
| 32 | TP slide | ABSENT | HIGH | TP ABSENT |
| 33 | Section jeux titre | ABSENT | HIGH | Slide section absente |
| 34 | Strategies informees | ABSENT | HIGH | Slide section absente |
| 35 | Meilleur d'abord | ABSENT | HIGH | Slide entiere absente |
| 36 | Environnements adversariaux | 33 | LOW | Diacritiques |
| 37 | Heuristiques admissibles/consist. | ABSENT | HIGH | Slide entiere absente |
| 38 | Jeux a somme nulle | 34 | LOW | Diacritiques |
| 39 | Types de jeux | 35 | LOW | Diacritiques |
| 40 | Jeux humain vs IA | 36 | LOW | Diacritiques |
| 41 | Echecs | 37 | LOW | Diacritiques |
| 42 | Complexite jeux | 38 | LOW | Diacritiques |
| 43 | Minimax intro | 40 | HIGH | Images echecs MANQUANTES |
| 44 | Minimax formulation | 41 | LOW | Diacritiques |
| 45 | Minimax exemple | 42 | LOW | Diacritiques |
| 46 | Alpha-Beta | 43 | MEDIUM | Diagramme simplifie |
| 47 | Alpha-Beta pruning | 44 | MEDIUM | Diagramme pruning |
| 48 | Alpha-Beta optim | 45 | LOW | Diacritiques |
| 49 | Decisions imparfaites | 46 | LOW | Diacritiques |
| 50 | TP jeux | ABSENT | HIGH | TP ABSENT |
| 51 | Resume jeux | 48 | LOW | Diacritiques |
| 52 | Jeux stochastiques | 50 | LOW | Diacritiques |
| 53 | Expectiminimax | 51 | MEDIUM | Diagramme |
| 54 | Jeux partiellement observables | 52 | LOW | Diacritiques |
| 55 | Resume avance jeux | 53 | LOW | Diacritiques |
| 56 | TP avance | ABSENT | MEDIUM | TP ABSENT |
| 57 | Section CSP intro | 55 | LOW | Diacritiques |
| 58 | Jeux vs Exploration | ABSENT | HIGH | Slide intro absente |
| 59 | Agents reflexes | 56 | LOW | Diacritiques |
| 60 | Minimax arbre | 57 | HIGH | Arbre Minimax MANQUANT |
| 61 | Minimax pseudocode | 58 | HIGH | Pseudocode Minimax MANQUANT |
| 62 | Alpha-Beta formulation | 59 | LOW | Diacritiques |
| 63 | Alpha-Beta detail | 60 | LOW | Diacritiques |
| 64 | Techniques avancees | ABSENT | HIGH | Section avancee absente |
| 65 | MCTS | ABSENT | HIGH | MCTS entierement absent |
| 66 | Zone L slide 1 | ABSENT | HIGH | Slide absente |
| 67 | Zone L slide 2 | ABSENT | HIGH | Slide absente |
| 68 | Zone L slide 3 | ABSENT | HIGH | Slide absente |
| 69 | Zone L slide 4 | ABSENT | MEDIUM | Sommaire section |
| 70 | CSP intro | 62 | LOW | Diacritiques |
| 71 | Coloration de carte | ABSENT | HIGH | Exemple fondateur absent |
| 72 | Solutions d'un CSP | ABSENT | HIGH | Notion solution absente |
| 73 | Techniques resolution CSP | 70 | MEDIUM | Reordonnancement |
| 74 | Domaines CSP | 71 | LOW | Reordonnancement mineur |
| 75 | Graphe de contraintes | 72 | MEDIUM | Diagramme graphe |
| 76 | Types de contraintes | 73 | LOW | Diacritiques |
| 77 | CSPs courants | ABSENT | HIGH | Catalogue applications absent |
| 78 | Formulation standard | 64 | MEDIUM | Reordonnancement majeur |
| 79 | Propagation de contraintes | 66 | MEDIUM | Reordonnancement + diagrammes |
| 80 | Contraintes globales | ABSENT | HIGH | Section entiere absente |
| 81 | Backtracking CSPs | 65 | MEDIUM | Diagramme arbre |
| 82 | Ordre variables/valeurs | 67 | MEDIUM | Diagrammes heuristiques |
| 83 | Forward checking + MAC | ABSENT | HIGH | Techniques cles absentes |
| 84 | Exploration locale CSPs | 69 | LOW | Diacritiques |
| 85 | Structure des problemes | 68 | MEDIUM | Reordonnancement + diagramme |
| 86 | Solveurs modernes | ABSENT | HIGH | Panorama solveurs absent |
| 87 | Applications cas d'usage | 75 | LOW | Diacritiques |
| 88 | Resume CSPs | 76 | HIGH | OVERFLOW bas de slide |
| 89 | Questions ? | ABSENT | LOW | Transition absente |
| 90 | TP CSPs | 78 | LOW | Hyperlien |
| 91 | Sommaire complet | ABSENT | MEDIUM | Recapitulatif absent |
| 92 | Plan du cours | ABSENT | LOW | Navigation absente |
| 93 | Merci | 79 | LOW | Fond noir vs blanc |

---

## Top-10 problemes recurrents

### 1. Slides ABSENTES (22 slides sur 93 — 24%)
Les slides suivantes sont completement absentes du deck Slidev : PPTX 14, 15, 32, 33, 34, 35, 37, 50, 56, 58, 64, 65, 66, 67, 68, 69, 71, 72, 77, 80, 83, 86, 89, 91, 92.
Impact : sections entières manquantes (MCTS, Forward checking, contraintes globales, exemples CSP fondateurs).

### 2. Diagrammes et pseudocodes MANQUANTS (7 slides HIGH)
Slides avec images/pseudocodes critiques absents dans Slidev : PPTX 4 (flowchart agents), PPTX 5 (espace etats), PPTX 22 (pseudocode BFS), PPTX 43 (images echecs), PPTX 60 (arbre Minimax), PPTX 61 (pseudocode Minimax), PPTX 88 (overflow resume CSP).
Impact : cours presenté sans illustration visuelle des concepts cles.

### 3. Suppression systematique des diacritiques (70+ slides)
Toutes les slides Slidev presentent une suppression quasi-totale des accents francais : "résolution" → "resolution", "évaluation" → "evaluation", "détection" → "detection", etc.
Impact : texte professionnel degrade, impression de document brouillon.

### 4. Reordonnancement de la section CSP (PPTX 71-88)
L'ordre Slidev presente les algorithmes de resolution (Slidev 63-69) AVANT les bases et definitions formelles (Slidev 70-73), ce qui inverse l'ordre pedagogique naturel du PPTX.
Impact : etudiants voient les algorithmes avant de comprendre ce qu'est un CSP formellement.

### 5. Bug letterbox theme-ia101 (slides PPTX Questions/TP/Merci)
Le theme Slidev theme-ia101 produit une bande noire/grise en bas de certaines slides (visible dans PPTX 89, 90, 93). Ce bug est connu et documenté.
Impact : présentation visuelle degradee sur les slides de transition/cloture.

### 6. Slides TP absentes (PPTX 32, 50, 56 ABSENTS)
Trois slides de travaux pratiques sont absentes — les etudiants ne voient pas les consignes TP pendant la presentation.
Impact : decouplage entre cours et TP, professeur doit fournir les references oralement.

### 7. OVERFLOW sur slide Resume CSPs (PPTX 88 = Slidev 76)
La derniere section du resume CSP ("Structure des problemes") est coupee en bas de slide. Les sous-bullets sur Coupe cycle, Decomposition, Symetrie sont invisibles.
Impact : le recapitulatif de fin de section est incomplet a la projection.

### 8. Mauvaise image (PPTX 17 = Slidev 17)
La slide "Heuristiques" (PPTX 17) affiche dans Slidev une image de la carte de Roumanie au lieu de l'illustration des heuristiques. Image substituée incorrectement.
Impact : explication des heuristiques illustree par une image hors-sujet.

### 9. Perte des layouts deux-colonnes
Plusieurs slides PPTX utilisent un layout deux-colonnes (texte gauche + diagramme droit) perdu dans Slidev : PPTX 82 (MRV/LCV), PPTX 83 (Forward checking), PPTX 4 (agents intro). Slidev rendus en colonne unique.
Impact : densite d'information visuelle reduite, diagrammes absents ou mal positionnes.

### 10. Slides de navigation absentes (PPTX 91, 92)
Le sommaire complet (PPTX 91) et le plan du cours global (PPTX 92) sont absents. Les etudiants n'ont pas de vue synthetique en fin de session.
Impact : pas de clôture pedagogique structuree, positionnement dans le programme global invisible.

---

## Plan de correction prioritaire

### Priorite 1 — CRITIQUE (a corriger avant le prochain cours, 2026-04-20)

1. **Supprimer ou corriger l'image erronee slide 17** (carte Roumanie → heuristiques): 1 remplacement d'image.
2. **Corriger l'OVERFLOW slide 76** (Resume CSPs): reduire la taille de police ou split en deux slides.
3. **Ajouter les diagrammes manquants slides 4, 5** (flowchart agents, espace etats): inserer images depuis PPTX.
4. **Ajouter pseudocodes slides 22, 60, 61** (BFS, Minimax × 2): convertir en blocs code Markdown.

### Priorite 2 — IMPORTANT (pour cours suivant)

5. **Restaurer les slides ABSENT section jeux avances** : PPTX 64 (Techniques avancees), 65 (MCTS) — contenu pedagogique important.
6. **Restaurer les slides ABSENT CSP fondateurs** : PPTX 71 (Coloration carte), 72 (Solutions CSP), 83 (Forward checking + MAC) — base de la section CSP.
7. **Restaurer CSPs courants et contraintes globales** : PPTX 77, 80 — applications pratiques.
8. **Reordonnancer la section CSP** : deplacer Slidev 70-73 (bases) AVANT Slidev 63-69 (algorithmes) pour restaurer l'ordre pedagogique du PPTX.

### Priorite 3 — AMELIORATION (sprint de qualite)

9. **Corriger les diacritiques** sur l'ensemble du deck via script de remplacement global dans slides.md.
10. **Restaurer les slides TP** (PPTX 32, 50, 90) avec liens cliquables.
11. **Restaurer Sommaire final** (PPTX 91) pour la clôture du cours.
12. **Investiguer et corriger le bug letterbox** theme-ia101 (bandes noires/grises slides dark).

---

## Resume final

**Audit visuel Slidev vs PPTX — deck 02-resolution-problemes — 2026-04-19**

Le deck Slidev `02-resolution-problemes` presente des lacunes structurelles significatives par rapport au PPTX de reference (93 slides). Sur 93 slides PPTX, 25 sont totalement absentes du rendu Slidev (79 slides), soit une perte de 27% du contenu. La section CSP (PPTX 71-88) est la plus affectee avec 6 slides absentes et un reordonnancement majeur qui inverse l'ordre pedagogique.

Les problemes critiques avant le cours du 2026-04-20 sont : une image erronee (slide 17 affiche une carte de Roumanie au lieu d'une illustration des heuristiques), un overflow sur le resume CSP (slide 76, contenu coupe en bas), et l'absence de plusieurs diagrammes fondamentaux (flowchart agents, espace d'etats, pseudocodes BFS et Minimax).

La suppression systematique des diacritiques francais sur 70+ slides degrade la qualite generale mais n'affecte pas la comprehension. Le bug letterbox du theme-ia101 produit des bandes noires sur les slides de transition, probleme connu et documente.

Priorite immediate (avant cours) : corriger l'image erronee slide 17, l'overflow slide 76, et ajouter les 4 diagrammes/pseudocodes critiques. Les 25 slides absentes et le reordonnancement CSP constituent un travail de fond a planifier pour le sprint suivant.

**Statistiques : 25 slides ABSENTES | 8 slides HIGH (contenus critiques manquants) | 16 slides MEDIUM | 44 slides LOW (diacritiques) | 5 INSERTs Slidev sans equivalent PPTX**
