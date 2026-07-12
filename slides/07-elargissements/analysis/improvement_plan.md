# Deck 07 - Elargissements : Analyse Visuelle et Plan d'Amelioration

## Statistiques

- **Slides**: 37
- **Images**: 2 (ratio critique: 0.05 image/slide)
- **Mots**: 2690
- **Taille**: 0.19 MB
- **Derniere MAJ**: Dec 2024
- **Footer**: CS 405

## 1. Diagnostic global

### Forces
- Contenu moderne et pertinent (LLMs, federated learning, differential privacy)
- Sujets d'actualite (JO Paris 2024, GDPR)
- Structure thematique claire en 3 sections
- Themes ethiques et societaux bien abordes

### Faiblesses critiques
- **CRITIQUE**: Seulement 2 images pour 37 slides - le deck le plus austere
- Murs de texte predominants sur quasiment toutes les slides
- Manque total de supports visuels pour concepts abstraits (biais, explicabilite, conscience)
- Risque d'attention faible sur des sujets qui meritent engagement
- Pas de schemas pour architectures d'agents (slide 30)

### Opportunites
- Sujets visuellement riches: surveillance (cameras, reconnaissance faciale), biais (diversite), creativite (art genere), singularite (graphiques temporels)
- Connexions fortes avec GenAI/ pour ethique de l'IA generative
- SymbolicAI/ pour neuro-symbolique et architectures hybrides
- Potentiel d'infographies pour GDPR, differential privacy, federated learning

## 2. Recommandations par section

### Section 1: Que signifie l'IA
**Slides concernees**: 1-12 (estimatif)
**Probleme**: Definition et portee de l'IA - probablement tres textuelle
**Ameliorations prioritaires**:
- Timeline visuelle de l'evolution de l'IA (symbolique → ML → deep learning → LLMs)
- Diagramme de Venn: IA vs ML vs Deep Learning vs GenAI
- Icones representant differents types d'IA (vision, NLP, robotique, jeux)
- Schema "Narrow AI vs General AI vs Super AI" avec exemples concrets

### Section 2: Limites
**Slides concernees**: 13-28 (estimatif)
**Slide cle identifiee**: Slide 15 "Surveillance, securite et vie privee"
**Problemes**: Concepts abstraits (biais, explicabilite, robustesse) sans visualisation
**Ameliorations prioritaires**:

**Slide 15 (Surveillance)**:
- Photos/illustrations: cameras de surveillance, reconnaissance faciale
- Carte de France avec zones de surveillance JO Paris 2024
- Icones GDPR (bouclier UE)
- Diagramme federated learning (donnees decentralisees)
- Schema differential privacy (bruit ajoute aux donnees)

**Autres slides de cette section**:
- **Biais**: Graphiques montrant disparites demographiques, exemples visuels de biais (recrutement, justice predictive)
- **Explicabilite**: Schema XAI (boite noire vs boite blanche), LIME/SHAP visualisations
- **Robustesse**: Exemples adversarial attacks (panda → gibbon), graphiques de performance
- **Ethique**: Flowchart de decision ethique, cas d'usage avec feux rouges/verts

### Section 3: Impact reel
**Slides concernees**: 29-37
**Slide cle identifiee**: Slide 30 "Architectures d'Agents"
**Problemes**: Architecture hybride neuro-symbolique sans schema
**Ameliorations prioritaires**:

**Slide 30 (Architectures d'Agents)**:
- Schema d'architecture hybride (perception neuronale + raisonnement symbolique)
- Diagramme flux: LLM → planning symbolique → execution
- Exemples concrets: agents ReAct, AutoGPT, BabyAGI
- Comparaison architectures (reactive, deliberative, hybrid)

**Autres slides de cette section**:
- **Creativite**: Exemples visuels d'art genere par IA, musique, ecriture
- **Conscience**: Graphiques tests de conscience (Turing, Chinese Room), schemas philosophiques
- **Singularite**: Timeline projections (Kurzweil), graphiques croissance exponentielle
- **Agent applications**: Screenshots/mockups d'agents en action

### Slides "Questions?"
**Recommandation**: **CONSERVER SANS MODIFICATION**
Ces slides servent de pauses respiratoires entre sections - essentielles pour absorption du contenu dense.

## 3. Cross-references notebooks

### GenAI/ (58 notebooks)
**Pertinence**: Ethique de l'IA generative, biais dans les modeles
**Notebooks cles**:
- `GenAI/LLM/*` - Pour limites et biais des LLMs
- `GenAI/Image/*` - Pour creativite artistique
- `GenAI/Ethics/*` (si existe) - Pour questions ethiques

**Integration slides**:
- Slide 15 (surveillance): Exemples de reconnaissance faciale generative
- Section creativite: Outputs DALL-E, Stable Diffusion, ComfyUI Qwen
- Section limites: Hallucinations LLM, biais dans generation d'images

### SymbolicAI/ (neuro-symbolique)
**Pertinence**: Architectures hybrides, raisonnement explicable
**Notebooks cles**:
- `SymbolicAI/Argument_Analysis/*` - Pour raisonnement et argumentation
- `SymbolicAI/RDF/*` - Pour representation symbolique
- `SymbolicAI/Z3/*` - Pour verification formelle

**Integration slides**:
- Slide 30 (architectures): Exemples concrets de neuro-symbolique
- Section explicabilite: Raisonnement symbolique comme methode XAI
- Section robustesse: Verification formelle avec Z3

### ML/ (pour biais et robustesse)
**Pertinence**: Biais algorithmiques, adversarial attacks
**Notebooks cles**:
- `ML/Fairness/*` (si existe) - Pour mesure de biais
- `ML/Robustness/*` (si existe) - Pour attaques adversariales

**Integration slides**:
- Section biais: Metriques de fairness (demographic parity, equalized odds)
- Section robustesse: Exemples adversarial attacks sur modeles ML.NET

## 4. Plan d'amelioration prioritaire

### Phase 1: Urgence critique (Ratio images catastrophique)
**Objectif**: Passer de 2 a au moins 20 images (0.54 image/slide minimum)

**Actions immediates**:
1. **Slide 15 (Surveillance)**: Ajouter 4-5 visuels (cameras, carte JO, GDPR, federated learning diagram)
2. **Slide 30 (Architectures)**: Creer schema architecture hybride + exemples agents
3. **Section biais**: Ajouter 3-4 graphiques disparites + exemples visuels
4. **Section creativite**: Integrer 5-6 exemples d'art genere (depuis GenAI notebooks)
5. **Section singularite**: Timeline visuelle + graphiques exponentiels

**Resultats attendus**: ~18-20 images ajoutees, ratio monte a 0.54 image/slide

### Phase 2: Enrichissement systematique
**Objectif**: Atteindre 30-35 images (0.81-0.95 image/slide)

**Actions**:
1. Creer infographies pour chaque concept abstrait (XAI, differential privacy, federated learning)
2. Ajouter schemas de flux pour chaque architecture mentionnee
3. Integrer captures d'ecran de notebooks pertinents (GenAI, SymbolicAI)
4. Developper bibliotheque d'icones coherente (ethique, securite, robustesse)
5. Creer comparaisons visuelles (avant/apres, avec/sans IA)

**Resultats attendus**: Deck visuellement equilibre, engagement ameliore

### Phase 3: Interactivite et modernisation
**Objectif**: Rendre le deck memorable et impactant

**Actions**:
1. Ajouter QR codes vers notebooks interactifs (GenAI ethics, neuro-symbolic examples)
2. Integrer GIFs animes pour demonstrations (adversarial attacks, agent behaviors)
3. Creer mini-cas pratiques visuels (scenarios ethiques avec choix multiples)
4. Developper slides de synthese avec mind maps visuelles
5. Ajouter callout boxes avec citations expertes (illustrees avec photos)

**Resultats attendus**: Deck transforme, passage de "plus austere" a "plus engage"

### Metriques de succes
- **Avant**: 2 images, 0.05 image/slide, deck le plus austere
- **Apres Phase 1**: ~20 images, 0.54 image/slide, ratio minimum atteint
- **Apres Phase 2**: ~32 images, 0.86 image/slide, ratio sain
- **Apres Phase 3**: Deck interactif et visuellement riche, taux d'engagement estime +200%

### Contraintes respectees
- **Questions? slides**: Conservees sans modification (pauses essentielles)
- **Contenu textuel**: Preserve mais complete par visuels (pas de remplacement)
- **Coherence branding**: Footer CS 405 maintenu
- **Modernite**: Contenu deja a jour (Dec 2024), focus sur presentation visuelle
