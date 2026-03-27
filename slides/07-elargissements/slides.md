---
theme: ../theme-ia101
title: "Intelligence Artificielle - Elargissements"
info: IA 101 - Philosophie, ethique, securite et avenir de l'IA
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Elargissements

Intelligence Artificielle - VII

**Que signifie l'IA?**
Quelles sont ses limites?
Son impact reel?

---

# Plan du cours

- I. Introduction
- II. Resolution de problemes
- III. Bases de connaissances et logique
- IV. Incertitude et modeles probabilistes
- V. Apprentissage
- VI. Traitement du langage naturel
- **VII. Elargissements** <- *vous etes ici*

---

# Sommaire

- Philosophie, ethique et securite de l'IA
  - Les limites de l'IA
  - Les machines peuvent-elles penser?
  - L'ethique de l'IA
- Avenir de l'IA
  - Composants des agents
  - Architectures d'IA

---

# Les limites de l'IA -- Histoire et aujourd'hui

- **Philosophie des limites**
  - Peut-on formaliser l'intelligence humaine?
  - Distinction entre:
    - **IA faible**: simuler l'intelligence
    - **IA forte**: conscience, comprehension reelle
- **Grandes critiques historiques** (Turing, Dreyfus):
  - Argument de l'informalite
  - Argument du handicap
  - Objection mathematique
- **Avancees recentes**
  - GPT 5.2, Claude Opus 4.5, Gemini Pro 3
  - Raisonnement, ARC, Maths, Developpement

---
layout: dense
---

# L'informalite des comportements humains

- **Critique de Dreyfus et GOFAI**
  - Les regles logiques sont insuffisantes
  - Importance de l'embodied cognition
  - Comprendre passe par l'interaction avec le monde physique
- **Reponse moderne**
  - Les LLMs (GPT-5, Claude 4.x, Gemini 3) capturent certains aspects de l'informalite
  - Mais: absence de corps et d'interaction limite leur "comprehension"
- **Exemple moderne**
  - Robots incarnes: Ameca, Figure 02, Tesla Optimus
  - Combinent LLMs et capteurs physiques
- **Nouvelles architectures proposees**
  - Exemple de LeCun/Meta: Jepa
- **Discussion rapide**
  - "Les LLMs modernes repondent-ils aux critiques de l'epoque GOFAI?"

---
layout: dense
---

# L'argument de l'incapacite

- **Critique de Turing**
  - "Une machine ne pourra jamais faire X (etre gentille, creative, drole)"
- **Avancees recentes**
  - L'IA cree de l'art: Stable Diffusion, DALL-E, Flux, Z-Image, Nano Banana
  - Resout des problemes scientifiques: AlphaFold
  - Amuse: chatbots avances
  - Creativite musicale: Suno, Udio (bouleverse l'industrie musicale)
- **Critiques recentes**
  - "Stochastic Parrots" (Emily Bender, Timnit Gebru)
  - Comprehension, biais, impact, monopolisation, desinformation
- **Limites persistantes**
  - Hallucinations, manque de "comprehension"
  - L'IA reste incapable d'emotions ou de conscience reelle
  - Autonomie simulee = meta-programmes (prompts systemes)

---
layout: dense
---

# L'objection mathematique

- **L'argument de Godel**
  - Godel (1931): Tout systeme formel suffisamment puissant est limite
  - Il existe des enonces vrais mais impossibles a prouver dans ce systeme
- **Critique historique**
  - Lucas (1961), Penrose (1989): "Les humains comprennent des verites inaccessibles aux machines"
- **Reponse moderne**
  - Les humains ne sont pas exempts d'erreurs (ex: probleme des 4 couleurs)
  - Les machines modernes (reseaux neuronaux, LLMs) ne sont pas des systemes formels rigides
    - Elles peuvent changer leurs regles (apprentissage automatique)
    - Elles revoient leurs conclusions (metaraisonnement)
  - 2025: AlphaProof, AlphaGeometry -> Medaille d'or IMO
- **Limite persistante**
  - Les systemes humains et artificiels restent soumis aux contraintes des mathematiques

---
layout: dense
---

# Mesurer l'intelligence

<!-- Image: images/turing_test.png -->

- **Le Turing Test (1950)**
  - Objectif: Evaluer l'intelligence par une conversation convaincante
  - Limite: Test de la "tromperie" plutot que de l'intelligence reelle
  - 2023: GPT-4 a surpasse les performances humaines, mais insuffisant pour evaluer l'AGI
  - Nouveaux criteres: Resolution de taches complexes, explicabilite, ethique
- **La course aux benchmarks**
  - 1960s--2022: Tests specialises (enigmes, reconnaissance d'images)
  - 2023: Saturation de GSM8K (maths) et MMLU (connaissances), depasses par GPT-4, Claude
  - 2024: ARC-AGI (Francois Chollet) mesure la generalisation, depasse par O3 en 2024
  - 2025: ARC-AGI2 (GPT-5.2 a 52,9%), SWE-bench Verified (Claude Opus 4.5 a 80,9%)
- **Defi**
  - Concevoir des tests mesurant l'acquisition de nouvelles competences, la generalisation et l'ethique

---

# Machines et pensee

- **Les debats philosophiques depuis Turing**
  - Pensee simulee vs pensee reelle
  - La "polite convention" (Turing): nous attribuons la pensee par convention sociale
- **Metaphore de Dijkstra**
  - "Les machines pensent-elles?" est aussi pertinent que de demander si les sous-marins nagent
- **Question ouverte**
  - "Si une IA simule parfaitement la pensee, est-ce suffisant pour dire qu'elle pense?"

---

# La chambre chinoise (Searle, 1980)

- **Explication**
  - Un humain, sans comprendre le chinois, utilise un livre de regles pour simuler des reponses
  - Conclusion de Searle: Simuler n'est pas comprendre
- **Reponses modernes**
  - La comprehension peut emerger du systeme global (theorie des systemes)
  - Les LLMs illustrent ce debat: production coherente sans comprehension intrinseque
- **Reflexion rapide**
  - "Comment distinguer comprehension reelle et apparente chez une IA?"

---

# Theories de la conscience (1/2)

- **Definir la conscience**
  - Qualia: Les experiences subjectives (ressentir la chaleur, la douleur)
  - Conscience comme modele de soi et du monde
- **Global Workspace Theory (GWT)**
  - La conscience est un espace de travail ou differentes parties du cerveau partagent des informations
  - Applications: Modeles d'attention, taches complexes
  - Role important de l'inconscient
- **Integrated Information Theory (IIT)**
  - La conscience est mesuree par le degre d'integration de l'information (Phi)
  - Introduit la notion de systemes physiques conscients

---

# Theories de la conscience (2/2)

- **Higher-Order Theory (HOT)**
  - La conscience necessite une pensee sur ses propres etats mentaux (metacognition)
  - Cf FOL et logiques d'ordres superieures
  - Emergence de structures fractales
- **Predictive Coding**
  - Le cerveau comme machine predictive minimisant l'incertitude
  - Minimisation de l'energie libre
  - Compatible avec les LLMs, explique les hallucinations
  - Cf Podcast Curt Jaimungal

---
layout: dense
---

# Integrated Information Theory (IIT)

- **La conscience est integree et informationnelle**
  - Chaque experience consciente est un tout indivisible (integration)
  - Elle contient une riche quantite d'informations differenciees (information)
- **Quantification par Phi ("phi")**
  - Plus Phi est eleve, plus le systeme est conscient
  - Cerveau humain: Phi eleve, ordinateur traditionnel: Phi bas
- **Cinq axiomes fondamentaux**
  - Existence: La conscience existe intrinsequement
  - Composition: Structuree en sous-elements (couleurs, formes, sons)
  - Information: Chaque experience est differente
  - Integration: Unifiee et indivisible
  - Exclusion: Certaines experiences sont conscientes, d'autres non
- **Applications et implications**
  - La conscience peut exister dans tout systeme integrant l'information
  - Reste difficile a tester experimentalement
- **Activite**: Decouverte de PyPhi

---

# L'ethique de l'IA

<!-- Image: images/trolley_problem.png -->

- **L'IA comme double tranchant**
  - **Avantages**: Amelioration des soins medicaux, prediction des catastrophes, automatisation
  - **Risques**: Inegalites economiques, surveillance de masse, biais dans les decisions critiques
- **Objectif ethique**
  - Maximiser les benefices
  - Minimiser les risques
- **Question pour reflexion**
  - "Comment garantir que l'IA sert l'interet collectif et non des interets individuels?"

---
layout: dense
---

# Armes autonomes letales

- **Definition**
  - Armes capables de selectionner et de tuer des cibles sans supervision humaine
- **Exemples**
  - Harop Missile (Israel)
  - Kargu Quadcopter (Turquie)
  - Ukraine vs Russie (EWs)
- **Controverses**
  - Morale: "La decision de tuer doit-elle etre confiee a une machine?"
  - Pratiques: Fiabilite, risque de pertes civiles
- **Conflits actuels**
  - Utilisation massive de drones autonomes et d'IA de ciblage en Ukraine et a Gaza
  - Appel du secretaire general de l'ONU a une interdiction des LAWS sans supervision humaine
- **Vers une regulation ou une course a l'armement?**

---
layout: dense
---

# Surveillance, securite et vie privee

<!-- Image: images/federated_learning.png -->

- **Problemes**
  - Surveillance de masse (cameras, microphones)
  - Exemple: JO Paris 2024, laboratoire pour la videosurveillance algorithmique
  - Cyberattaques utilisant l'IA
  - Propagande amplifiee par les LLMs
- **Solutions**
  - Regulation: GDPR, HIPAA
  - Approches techniques: Anonymisation (k-anonymity, differential privacy)
- **Exemples concrets**
  - Federated learning (modele sans base de donnees centralisee)
  - Deep learning confidentiel
  - Chiffrement homomorphe
  - Augmentation

---

# Biais et equite

- **Types de biais**
  - **Biais de donnees**: minorites sous-representees
  - **Biais dans les algorithmes**: justice americaine (COMPAS), reconnaissance faciale
  - **Biais de preferences**: Exemple LLMs
- **Solutions**
  - Oversampling des classes minoritaires (SMOTE)
  - Transparence et documentation des donnees (data sheets)
- **Exemple concret**
  - Inclusive Images Competition (Google/NeurIPS)

---
layout: dense
---

# Transparence et confiance

<!-- Image: images/decision_tree_xai.png -->

- **Exigences de confiance**
  - Verification et validation (V&V)
  - Certification (ISO, UL)
- **Explainable AI (XAI)**
  - Exemples: "Pourquoi votre pret a-t-il ete refuse?"
  - Avancees: SHAP (Shapley, imputation des caracteristiques) ou LIME (Local Interpretable)
- **Exemple concret**
  - Comparaison entre explications humaines et machines
- **Question ouverte**
  - "Les explications des IA sont-elles fiables ou simplement convaincantes?"
- **Applications**
  - TP: XAI simple avec ML.Net
  - Scikit-learn: Scikit-Explain API
  - Anthropic:
    - Towards Monosemanticity
    - Scaling Monosemanticity
    - On the Biology of a Large Language Model
    - When Models Manipulate Manifolds

---

# L'avenir de l'emploi

- **Impacts**
  - Court terme: Augmentation de la productivite
  - Long terme: Risque de chomage technologique
- **Solutions societales**
  - Education continue
  - Revenu de base universel
- **Exemple concret**
  - Reinvention des metiers (radiologie augmentee par IA)
- **Question ouverte**
  - Une societe sans travail reste-t-elle envisageable?

---

# Droits des robots

- **Debat philosophique**
  - Conscience et qualia comme conditions
- **Questions ethiques**
  - "La reprogrammation est-elle une forme d'esclavage?"
  - Cas extreme: Robots votants
- **Exemples**
  - Sophia (citoyennete en Arabie Saoudite)
  - Romance: Replika & co
- **Prudence**
  - Eviter la confusion entre outils et entites conscientes
- **Question ouverte**
  - Si une IA simule la souffrance, a-t-on le droit de la faire souffrir?

---
layout: two-cols
---

# Securite de l'IA

- **Problemes**
  - Alignement des valeurs (value alignment)
  - Effets secondaires non prevus
  - Exemple: Supprimer tous les cancers?
- **Solutions**
  - Failure Mode and Effects Analysis (FMEA)
  - Fault Tree Analysis
  - Grilles de securite IA (AI Safety Gridworlds)
  - AI Safety Levels (ASLs)
- **Exemple concret**
  - Agents "cheatants" dans les simulations
- **Anthropic**
  - Responsible Scaling Policy
  - Constitutional AI

::right::

![w:300](../_assets/images/slide_20_img_000.png)
![w:200](../_assets/images/slide_20_img_001.png)

---

# Construire un futur ethique pour l'IA

- **Resume des defis ethiques majeurs**
  - Justice, transparence, securite, droits, travail
- **Appel a l'action**
  - Cooperation entre ingenieurs, decideurs, et citoyens
  - Former une nouvelle generation d'ingenieurs ethiques
- **La singularite et le transhumanisme**
  - Singularite technologique (Good, Kurzweil)
  - Transhumanisme: Fusion homme-machine
  - Optimisme vs dangers (controle, survie humaine)
- **Question ouverte**
  - "Quel futur voulons-nous co-creer avec l'IA?"

---
layout: section
---

# Questions?

---

# Avenir de l'IA

- **Objectif**
  - Explorer les tendances, defis, et opportunites de l'IA
- **Progres recents en IA**
  - Applications, materiel, composants
- **Perspectives d'avenir**
  - IA generale et architecturee
  - Questions ethiques et societales

---

# Progres actuels de l'IA

- **Avancees majeures**
  - Large deploiement: medecine, finance, transport, communication
  - Deep learning: depassement des capacites humaines dans des taches specifiques
- **Estimation des experts**
  - IA generale dans 10 a 100 ans
  - Trillions de dollars ajoutes a l'economie chaque annee dans la prochaine decennie
- **Defis**
  - Ethique: biais, equite, potentielle letalite
  - Developpement durable et controle de l'impact global

---

# Composants - Capteurs et Actionneurs

- **Progres technologiques**
  - Lidar: cout reduit ($75k -> $1k -> $10 prevision)
  - Capteurs MEMS: gyroscopes, cameras haute resolution
  - Imprimantes 3D et bioprinting pour prototypage rapide
  - Calculateurs miniatures: Arduino, NVIDIA Orin
- **Applications emergentes**
  - Robots industriels: environnements controles, taches repetitives
  - Defis pour le marche domestique: variabilite des environnements et taches complexes

---

# Composants - Representation du Monde

- **Etat de l'art**
  - Algorithmes de filtrage et perception: reconnaissance d'objets simples
  - Reseaux recurrents: representation temporelle d'environnements
- **Limites actuelles**
  - Reconnaissance des relations complexes entre objets
  - Difficultes a generaliser sans exemples exhaustifs
- **Defis**
  - Integration des logiques probabilistes et des algorithmes de vision avances

---

# Composants - Selection d'Actions

- **Complexite**
  - Plans a long terme: milliards d'etapes primitives (ex: obtenir un diplome)
  - Defis dans les environnements partiellement observables (POMDP)
- **Progres recents**
  - Representations hierarchiques (MDP hierarchiques)
  - Algorithmes pour decomposer le comportement en niveaux successifs
- **Perspectives**
  - Developpement de methodes pour representer efficacement les etats et actions sur de longues periodes

---

# Composants - Definir les Objectifs

- **Difficultes**
  - Modelisation des preferences humaines complexes
  - Interaction entre preferences individuelles et equite sociale
- **Progres**
  - Apprentissage par renforcement inverse: apprentissage a partir de demonstrations
  - Langages pour specifier les preferences (logique temporelle lineaire)
- **Exemples concrets**
  - Agents capables de maximiser des objectifs multi-dimensionnels sous incertitude

---
layout: dense
---

# Apprentissage et Deep Learning

<!-- Image: images/gan_architecture.png -->

- **Progres spectaculaires**
  - Vision par ordinateur, langage naturel, apprentissage par renforcement
- **Limites**
  - Dependance excessive a des donnees annotees massives
  - Difficultes avec des donnees rares ou non structurees
- **Progres recents**
  - Self-supervised learning, Apprentissage contrastif (GPT)
  - Reinforcement Learning with Human Feedback (ChatGPT)
  - Foundation Models
  - RL finetuning (O1, Deepseek)
- **Axes futurs**
  - Apprentissage par transfert: reutiliser les connaissances
  - Integration apprentissage/connaissance: fusion de l'experience et du raisonnement

---

# Ressources et Infrastructures

- **Evolution des infrastructures**
  - Cloud computing pour partager des modeles prets a l'emploi
  - Outils de diffusion et de deploiement: HuggingFace, Azure ML
  - Augmentation exponentielle des capacites de traitement (GPU, TPU, FPGA)
- **Defis**
  - Validation et gestion des donnees massives (crowdsourcing, validation par LLM)
  - Conception de systemes robustes pour des domaines complexes
- **Opportunites**
  - Modeles universels reutilisables pour plusieurs taches
  - Modeles open-source (Llama, Gemma, Qwen, Phi) + fine-tunes (LoRAs) et quants

---

# Architectures d'Agents

- **Approches hybrides**
  - Symbolique: raisonnement et chaines de logique complexe
  - Connexionniste: reconnaissance de patterns dans des donnees bruyantes
- **Concepts avances**
  - Algorithmes "anytime": amelioration progressive en fonction du temps disponible
    - Exemple: Arbres de jeux et MCMC
  - Metaraisonnement: optimisation du raisonnement base sur la valeur des calculs
    - Exemple: Valeur de l'information parfaite
  - Apprentissage symbolique et architectures neuro-symboliques
    - Enrichissement des bases de connaissance, guidage par LLM

---

# IA Generale

<!-- Image: images/recursive_self_improvement.png -->

- **Objectif**
  - Creer des agents capables de maitriser plusieurs taches diverses
- **Probleme**
  - Aujourd'hui, les systemes sont concus pour des taches specifiques
  - Manque de diversite comportementale et de generalisation
- **Progres recents**
  - Systemes multi-langues ou multi-taches bases sur des modeles de grande taille (ex: GPT)

---

# Ingenierie de l'IA

- **Etat actuel**
  - IA encore difficile a deployer pour les non-experts
  - Besoin d'un ecosysteme de developpement accessible et robuste
- **Proposition de Jeff Dean (Google)**
  - Construire un enorme modele universel, puis en extraire les parties pertinentes pour des taches specifiques
- **Exemples**
  - Transformers (GPT-4+) avec des milliards de parametres
  - Montee de l'Open-source
  - Distillation des grands modeles
  - Nombreuses variations / specialisations

---
layout: dense
---

# L'IA Scientifique

- **Revolution silencieuse**
  - Impact aussi profond que les LLMs: acceleration de la science
- **AlphaFold 3 (2024)**
  - Predit la forme des proteines
  - Les interactions avec l'ADN, l'ARN, et les medicaments potentiels
  - Accelerateur massif pour la biologie
- **GNoME**
  - A decouvert 2,2 millions de nouveaux cristaux stables
  - = 800 ans de recherche humaine
  - Applications pour les batteries et panneaux solaires de prochaine generation
- **Nouvelle frontiere des sciences physiques**
  - Prix Nobel 2024: Physique (Hopfield, Hinton), Chimie (Hassabis, Jumper)
  - Nouvelle approche de l'emergence
  - 2023: Michael Levin: Classical Sorting Algorithms as a Model of Morphogenesis

---

# Souverainete & Geopolitique

- **Clusters IA**
  - USA, Chine, UE (Mistral), Moyen-Orient (Falcon)
- **Guerre des puces**
  - Nvidia vs Huawei
- **Modeles proprietaires vs Open-source**
  - USA vs Chine
- **Sovereign AI**
  - Chaque nation veut son "cerveau numerique"
- **Infrastructure**
  - Course a l'armement (Datacenters, GPUs)

---
layout: dense
---

# Compression, Esthetique et Cosmologie

- **Jurgen Schmidhuber**
  - L'un des peres de l'IA moderne, controverse
- **Compression et Beaute**
  - Principe cle: Intelligence et esthetique reposent sur la capacite a decouvrir et compresser des regularites
  - Low Complexity Art: Beaute = Surprise liee a une structure compressible non evidente
  - L'attrait diminue une fois la compression exploitee
  - Applications: Algorithmes generant des motifs artistiques revelant des regularites
- **Cosmologie: Le Grand Programmeur Universel**
  - L'univers comme programme compressible
  - Les lois physiques refletent une faible complexite algorithmique (similaire a Wolfram)
  - Role des intelligences: Decouvrir et optimiser ces regularites, participant a une evolution universelle
- **Impact en IA et Philosophie**
  - En IA: Optimisation algorithmique, comme les reseaux LSTM
  - En cosmologie: Une quete computationnelle naturaliste maximisant l'efficacite algorithmique
  - Physique Numerique: TEDx Talk

---
layout: section
---

# Questions?

---

# Pour aller plus loin : Notebooks

- **Conscience et IIT**: `IIT/` - notebooks PyPhi
- **IA Symbolique**: `SymbolicAI/Argument_Analysis/` - argumentation formelle
  - `SymbolicAI/Lean/` - verification formelle
- **Explicabilite (XAI)**: `ML/` - ML.NET tutorials
- **IA Generative et ethique**: `GenAI/` - 58 notebooks
  - DALL-E, Stable Diffusion, ComfyUI, LLMs
- **Theorie des jeux**: `GameTheory/` - 26 notebooks OpenSpiel

---
layout: end
---

# Merci

Jean-Sylvain Boige
jsboige@myia.org
