# Deck S1 - Argumentation : Analyse Visuelle et Plan d'Amelioration

## Statistiques

- **Slides**: 30
- **Images**: 9 (ratio faible: 0.3 image/slide)
- **Mots**: 2477
- **Taille**: 0.52 MB
- **Derniere MAJ**: Jun 2023 (le plus ancien)
- **Footer**: "Argumentum" (branding unique)
- **Sections**: Histoire et theories, Principes, Bons/mauvais arguments, Fondements logiques, References

## 1. Diagnostic global

### Forces
- **Branding distinctif**: Footer "Argumentum" donne identite unique au deck
- **Slide 15 remarquable**: Table coloree des regles d'inference (Modus Ponens, Resolution, etc.)
- **Structure pedagogique**: Progression logique de l'histoire aux fondements formels
- **Cross-ref SymbolicAI**: 5 notebooks Argument_Analysis (Tweety, schemes)
- **Chevauchement utile**: Overlap avec deck 03-Logique slides 28-32 (aparte argumentation)

### Faiblesses
- **Ratio images faible**: 0.3 image/slide (en-dessous du seuil de 0.5)
- **Anciennete**: Jun 2023, peut manquer developpements recents (argument mining, LLMs pour argumentation)
- **Nature textuelle**: Sujet naturellement text-heavy (philosophie, logique formelle)
- **Manque de schemas**: Arbres d'arguments, graphes de debat absents visuellement
- **Redondance potentielle**: Overlap avec deck 03 a clarifier/exploiter

### Opportunites
- **Argument mining**: NLP pour extraction d'arguments (notebooks SymbolicAI/Argument_Analysis)
- **Visualisation graphes**: Argument maps, attack/support relations
- **Exemples actuels**: Debats politiques, fact-checking, AI safety arguments
- **Integration Tweety**: Demos interactives de frameworks d'argumentation abstraite
- **LLMs et argumentation**: Claude/GPT pour generation/evaluation d'arguments

## 2. Recommandations par section

### Section 1: Histoire et theories
**Slides estimees**: 1-8
**Themes**: Aristote, rhetorique, dialectique, sophismes historiques

**Ameliorations suggerees**:
- **Timeline visuelle**: Aristote → Moyen Age → Logique moderne → Argumentation computationnelle
- **Portraits**: Aristote, Toulmin, Perelman (avec citations cls)
- **Schema rhetorique**: Ethos, Pathos, Logos avec exemples visuels
- **Cartes conceptuelles**: Relations entre rhetorique, dialectique, logique formelle
- **Exemples historiques**: Reproductions de debats celebres (Platon, sophistes)

### Section 2: Principes de l'argumentation
**Slides estimees**: 9-15
**Themes**: Structure d'arguments, schemes, Toulmin model

**Ameliorations suggerees**:
- **Modele de Toulmin**: Schema visuel (Claim, Data, Warrant, Backing, Qualifier, Rebuttal)
- **Schemes d'argumentation**: Galerie visuelle des schemes courants (analogie, autorite, cause-effet)
- **Arbres d'arguments**: Exemples d'arguments complexes structures en arbre
- **Flowcharts**: Construction d'argument etape par etape
- **Exemples annotes**: Arguments reels deconstruits visuellement

### Section 3: Bons et mauvais arguments
**Slides estimees**: 16-22
**Themes**: Sophismes, fallacies, criteres de qualite

**Ameliorations suggerees**:
- **Taxonomie visuelle**: Arbre des fallacies (formelles vs informelles)
- **Exemples illustres**: Chaque sophisme avec cartoon/illustration pedagogique
  - Ad hominem: Caricature attaquant personne vs idee
  - Strawman: Bonhomme de paille visuel
  - False dilemma: Bifurcation fausse illustree
  - Slippery slope: Dominos qui tombent
  - Appeal to authority: Figure d'autorite avec asterisque
- **Avant/apres**: Mauvais argument → version corrigee
- **Detection guide**: Checklist visuelle pour identifier fallacies
- **Exemples actuels**: Fact-checking de debats politiques recents (anonymises si necessaire)

### Section 4: Fondements logiques du raisonnement
**Slides estimees**: 23-29
**Slide cle identifiee**: Slide 15 "Regles d'inference"
**Themes**: Logique propositionnelle, regles d'inference, validite

**Slide 15 (Regles d'inference)** - DEJA BONNE:
- **Conserver**: Table coloree avec Modus Ponens, Modus Tollens, Resolution, etc.
- **Enrichir**: Ajouter exemples concrets pour chaque regle
  - Modus Ponens: "Si pluie → parapluie. Il pleut. Donc: parapluie."
  - Resolution: Exemple de refutation avec clauses
- **Visualiser**: Arbres de preuve pour chaque regle (notation naturelle)

**Autres slides de cette section**:
- **Logique propositionnelle**: Tables de verite avec code couleur (vrai=vert, faux=rouge)
- **Arbres de preuve**: Exemples de deduction naturelle avec branches
- **Graphes de resolution**: Refutation visuelle etape par etape
- **Validite vs solidite**: Diagramme de Venn (validite ⊃ solidite)
- **Ponts avec IA**: Comment les LLMs "raisonnent" (spoiler: pas vraiment de logique formelle)

### Section 5: References bibliographiques
**Slide estimee**: 30
**Ameliorations suggerees**:
- **Categorisation visuelle**: Ouvrages classiques vs modernes, papiers cls
- **QR codes**: Liens vers ressources en ligne (Stanford Encyclopedia, Tweety docs)
- **Icones**: Livre/papier/web pour type de ressource
- **Recommandations niveaux**: Debutant/intermediaire/avance avec code couleur

### Slides "Questions?"
**Recommandation**: **CONSERVER ABSOLUMENT**
Dans un deck dense et abstrait, ces pauses sont critiques pour digestion du contenu.

## 3. Cross-references notebooks

### SymbolicAI/Argument_Analysis/ (5 notebooks - RESSOURCE CLE)

**Notebooks identifies**:
- Tweety framework (argumentation abstraite)
- Argument schemes extraction
- Argument mining (NLP)
- Dung semantics (grounded, preferred, stable)
- Argumentation graphs visualization

**Integration slides**:

**Section Histoire**:
- Ajouter slide "Argumentation computationnelle" avec timeline:
  - 1995: Dung abstract argumentation frameworks
  - 2000s: Argument mining, NLP applications
  - 2010s: Tweety, ASPIC+, ABA frameworks
  - 2020s: LLMs et argumentation, AI safety debates

**Section Principes**:
- **Dung frameworks**: Schema AF = (Arguments, Attacks) avec graphe exemple
- **Semantics**: Comparaison grounded vs preferred vs stable avec exemples visuels
- **Tweety demo**: Screenshot de notebook avec code + graphe genere

**Section Bons/mauvais arguments**:
- **Argument mining**: Pipeline NLP (text → argument detection → scheme classification)
- **Evaluation automatique**: Metriques de qualite d'arguments (strength, acceptability)
- **Fact-checking**: Architecture de systeme avec argument analysis

**Section Fondements logiques**:
- **Logique argumentative**: Ponts entre logique formelle et argumentation
- **ASPIC+**: Framework combinant regles strictes et defeasibles
- **Proof standards**: Visualisation de dialectical proof trees

**Liens pratiques**:
- QR codes vers notebooks Tweety (execution locale ou Binder)
- References aux papers implementes dans notebooks
- Exercices interactifs: "Construisez votre AF avec Tweety"

### Chevauchement avec Deck 03-Logique (slides 28-32)

**Strategie de coherence**:
1. **Deck 03 (aparte argumentation)**: Vue d'ensemble rapide, teaser
   - Slide 28-32 restent light, pointent vers Deck S1 pour details
   - Ajouter callout: "Voir deck Argumentum pour approfondissement"

2. **Deck S1 (specialise)**: Traitement complet et detaille
   - Assume que etudiants ont vu aparte du Deck 03
   - Peut faire rappels brefs des concepts de base
   - Focus sur profondeur et applications

3. **Navigation cross-deck**:
   - Deck 03 slide 28: "Approfondissement disponible dans deck Argumentum"
   - Deck S1 slide 1: "Complement du cours de Logique (section argumentation)"
   - Coherence footer: "CS 405" sur Deck 03, "Argumentum" sur S1 (identites distinctes OK)

### SymbolicAI/RDF/ (pour representation d'arguments)
**Pertinence**: Ontologies d'argumentation, AIF (Argument Interchange Format)
**Integration**: Section fondements logiques, representation formelle

### ML/ ou GenAI/LLM/ (pour LLMs et argumentation)
**Pertinence**: Generation/evaluation d'arguments par LLMs
**Integration**: Nouvelle section "IA et argumentation moderne"

## 4. Plan d'amelioration prioritaire

### Phase 1: Rehabilitation visuelle (9 → 20+ images)
**Objectif**: Passer au-dessus du seuil de 0.5 image/slide (minimum 15 images)

**Actions immediates**:

1. **Section Histoire** (+3 images):
   - Timeline illustree de l'argumentation
   - Portraits Aristote, Toulmin, Perelman
   - Schema rhetorique (Ethos, Pathos, Logos)

2. **Section Principes** (+4 images):
   - Modele de Toulmin (schema complet)
   - 3 schemes d'argumentation illustres (analogie, autorite, cause-effet)

3. **Section Bons/mauvais arguments** (+6 images):
   - Arbre taxonomique des fallacies
   - 5 sophismes illustres (ad hominem, strawman, false dilemma, slippery slope, appeal to authority)

4. **Section Fondements logiques** (+4 images):
   - Slide 15 enrichie avec exemples (deja bonne, ameliorer)
   - 2 arbres de preuve
   - Graphe de resolution

5. **References** (+1 image):
   - Infographie de ressources avec QR codes

**Resultats attendus**: 9 + 18 = 27 images, ratio monte a 0.9 image/slide

### Phase 2: Integration notebooks Tweety
**Objectif**: Lier theorie formelle a implementation pratique

**Actions**:

1. **Nouvelle section "Argumentation computationnelle"** (+5 slides):
   - Slide "Histoire de l'argumentation computationnelle"
   - Slide "Dung abstract argumentation" avec graphe exemple
   - Slide "Semantics" (grounded, preferred, stable) avec comparaisons visuelles
   - Slide "Tweety framework" avec screenshot notebook + code snippet
   - Slide "Applications" (fact-checking, AI safety, debat automatise)

2. **QR codes systematiques**:
   - Section principes: QR vers notebook schemes extraction
   - Section fondements: QR vers notebook Dung semantics
   - Section mauvais arguments: QR vers notebook argument mining (detection fallacies)

3. **Exercices interactifs**:
   - "Construisez votre AF": Instructions + QR code vers notebook Tweety
   - "Evaluez cet argument": Exemples avec solutions dans notebook
   - "Detectez les sophismes": Pipeline NLP avec notebook argument mining

**Resultats attendus**: 30 + 5 = 35 slides, pont solide theorie-pratique

### Phase 3: Actualisation et modernisation
**Objectif**: Passer de Jun 2023 a etat de l'art 2025

**Contenus a ajouter**:

1. **LLMs et argumentation** (+3 slides):
   - Slide "LLMs comme debaters" (GPT-4, Claude 3.5 capabilities)
   - Slide "Evaluation d'arguments par LLMs" (metrics, benchmarks)
   - Slide "Limites" (hallucinations, biais, manque de logique formelle)

2. **Applications modernes** (+2 slides):
   - Slide "Fact-checking automatise" (ClaimBuster, FactCheck.org pipelines)
   - Slide "AI safety debates" (constitutional AI, debate training, scalable oversight)

3. **Nouveaux developpements** (+2 slides):
   - Slide "Argument mining 2024-2025" (BERT, transformers pour AM)
   - Slide "Hybrid approaches" (neuro-symbolic, LLM + Tweety)

4. **Mise a jour references**:
   - Papers 2023-2025 sur argument mining, LLMs, hybrid approaches
   - Liens vers benchmarks recents (IBM Debater, etc.)

**Resultats attendus**: 35 + 7 = 42 slides, deck complet et actuel

### Phase 4: Coherence inter-decks
**Objectif**: Resoudre overlap avec Deck 03-Logique

**Actions**:

1. **Audit Deck 03 slides 28-32**:
   - Lire le contenu de l'aparte argumentation
   - Identifier redondances exactes avec Deck S1

2. **Strategie de differenciation**:
   - **Deck 03**: Garder intro rapide (1-2 concepts cls, 5 slides max)
   - **Deck S1**: Developper exhaustivement (42 slides post-phases 1-3)

3. **Navigation explicite**:
   - Deck 03 slide 28: Callout "Approfondissement dans deck Argumentum (S1)"
   - Deck S1 slide 2: "Prerequis: section argumentation du cours Logique"

4. **Cross-references visuelles**:
   - Icone "Argumentum" dans Deck 03 slides 28-32 (branding)
   - Meme code couleur pour concepts communs (coherence visuelle)

**Resultats attendus**: Deux decks complementaires sans redondance genante

### Phase 5: Interactivite et engagement
**Objectif**: Rendre un sujet abstrait concret et memorable

**Actions**:

1. **Exemples vivants**:
   - Debats politiques recents deconstruits (Trump vs Biden, Brexit, etc.)
   - Publicites analysees (techniques rhetorique)
   - Fact-checks de fake news celebres

2. **Quiz interactifs**:
   - "Identifiez le sophisme" avec 5 exemples + reponses
   - "Construisez un argument valide" etape par etape
   - "Evaluez la solidite" avec justification

3. **Demos live**:
   - Tweety AF construction en direct (via notebook projete)
   - LLM generation d'arguments (ChatGPT vs Claude comparison)
   - Argument mining pipeline sur texte reel

4. **Ressources supplementaires**:
   - Cheatsheet des fallacies (PDF teleargeable, QR code)
   - Liste de debats celebres pour analyse (YouTube links)
   - Exercices d'entrainement avec corrections (notebooks)

**Resultats attendus**: Engagement +100%, feedback "abstrait devenu concret"

### Metriques de succes

**Avant**:
- 30 slides, 9 images (0.3 image/slide - faible)
- Jun 2023 (ancien)
- Peu de liens notebooks
- Overlap non resolu avec Deck 03

**Apres Phase 1**:
- 30 slides, ~27 images (0.9 image/slide - excellent)
- Visuellement rehabilite

**Apres Phase 2**:
- 35 slides, ~32 images (0.91 image/slide)
- Integration Tweety complete
- QR codes systematiques

**Apres Phase 3**:
- 42 slides, ~40 images (0.95 image/slide)
- Actualise a 2025
- LLMs et applications modernes integres

**Apres Phase 4**:
- Coherence avec Deck 03 etablie
- Navigation inter-decks fluide
- Redondances eliminees

**Apres Phase 5**:
- Deck interactif et memorable
- Exemples concrets et actuels
- Taux d'engagement estime +100%

### Contraintes respectees
- **Questions? slides**: Conservees (pauses critiques pour sujet dense)
- **Branding "Argumentum"**: Preserve (identite unique)
- **Footer**: Maintenu distinct de "CS 405" (Deck 03)
- **Overlap Deck 03**: Gere par differenciation explicite (intro vs profondeur)
- **Notebooks SymbolicAI**: 5 notebooks Argument_Analysis exploites systematiquement

### Priorite immediate
**Action #1**: Phase 1 (rehabilitation visuelle 9→27 images) - CRITIQUE pour ratio faible
**Action #2**: Phase 2 (integration Tweety) - Exploiter les 5 notebooks disponibles
**Action #3**: Phase 4 (coherence Deck 03) - Eviter confusion etudiants
