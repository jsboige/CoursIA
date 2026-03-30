<!-- Slide number: 1 -->
# Elargissements
1
Intelligence Artificielle - VII

Que signifie l’IA?Quelles sont ses limites?
Son impact réel?
IA 101

### Notes:

<!-- Slide number: 2 -->
# Plan du cours
2
Introduction
Résolution de problèmes
Bases de connaissances et logique
Incertitude et modèles probabilistes
Apprentissage
Traitement du langage naturel
Elargissements
IA 101

### Notes:

<!-- Slide number: 3 -->
# Sommaire
3
Philosophie, éthique et sécurité de l’IA
Les limites de l’IA
Les machines peuvent elles penser?
L’éthique de l’IA
Avenir de l’IA
Composants des agents
Architectures d’IA
IA 101

### Notes:

<!-- Slide number: 4 -->
# Les limites de l’IA – Histoire et aujourd’hui
4
Philosophie des limites :
Peut-on formaliser l’intelligence humaine ?
Distinction entre
IA faible (simuler l’intelligence) et
IA forte (conscience, compréhension réelle).
Grandes critiques historiques (Turing, Dreyfus):
Argument de l’informalité :
"L’intelligence humaine ne peut pas être réduite à des règles formelles.«  (GOFAI, nécessité de l’incarnation)
Argument du handicap :
"Une IA ne pourra jamais faire X.«
Objection mathématique :
"L’IA est limitée par Gödel et Turing.«
Les avancées récentes remettent-elles ces critiques en question ?
GPT 5.2, Claude Opus 4.5, Gemini Pro 3  Raisonnement, « ARC », Maths, Développement etc.
CS 405

<!-- Slide number: 5 -->
# L’informalité des comportements humains
5
Critique de Dreyfus et des approches GOFAI :
Les règles logiques sont insuffisantes pour capturer la richesse des comportements humains.
Importance de l’embodied cognition :
Comprendre passe par l’interaction avec le monde physique.
Réponse moderne :
Les LLMs (comme GPT-5, Claude 4,x, Gemini 3) montrent que des modèles probabilistes peuvent capturer certains aspects de l’informalité.
Mais l’absence de corps et d’interaction limite leur "compréhension".
Exemple moderne :
Les robots incarnés (comme Ameca, Figure 02, Tesla Optimus) combinent LLMs et capteurs physiques pour combler ce fossé.
De nouvelles architectures sont proposées:
Exemple de LeCun/Meta : Jepa
Discussion rapide :
"Les LLMs modernes répondent-ils aux critiques de l'époque GOFAI ?"

CS 405

<!-- Slide number: 6 -->
# L’argument de l’incapacité
6
Critique de Turing :
"Une machine ne pourra jamais faire X (ex. : être gentille, créative, drôle).«
Avancées récentes :
L’IA crée de l’art (Stable Diffusion, DALLE, Flux, Z-image, Nano Banana), résout des problèmes scientifiques (AlphaFold), et amuse (chatbots avancés).
Créativité musicale bouleversant l’industrie musicale (Suno, Udio etc.)
Mais les LLMs hallucinent encore et manquent de "compréhension".
Critiques récentes:
« Stochastic Parrots » d'Emily Bender et Timnit Gebru
Compréhension, biais, impact, monopolisation, désinformation
Limite persistante :
L’IA reste incapable d’émotions ou de conscience réelle, même si elle peut les simuler.
L’autonomie reste simulée et correspond à des méta-programmes (prompts systèmes)
CS 405

<!-- Slide number: 7 -->
# L’objection mathématique
7
L’argument de Gödel :
Gödel (1931) : Tout système formel suffisamment puissant (ex. : machines de Turing) est limité.
Il existe des énoncés (les "phrases de Gödel") vrais mais impossibles à prouver dans ce système.
Critique historique :
Lucas (1961) et Penrose (1989) : "Les humains peuvent comprendre des vérités que les machines ne peuvent pas atteindre. »
Réponse moderne :
Les humains ne sont pas exempts d’erreurs ni de limitations (cf. erreurs en mathématiques, ex. : le problème des 4 couleurs).
Les machines modernes (réseaux neuronaux, LLMs) ne sont pas des systèmes formels rigides :
Elles peuvent changer leurs règles (apprentissage automatique).
Elles revoient leurs conclusions en fonction de nouvelles données (métaraisonnement).
2025 AlphaProof, AlphaGeometry  Médaille d’or IMO
Limite persistante :
Les systèmes humains et artificiels restent soumis aux contraintes fondamentales des mathématiques et de la logique.
CS 405

<!-- Slide number: 8 -->

# Mesurer l’intelligence
8
Le Turing Test (1950) :
Objectif : Évaluer l’intelligence par une conversation convaincante.
Limite : Test de la "tromperie" plutôt que de l’intelligence réelle.
En 2023, GPT-4 a surpassé les performances humaines sur le test, mais cela reste insuffisant pour évaluer une intelligence générale.
Nouveaux critères : Résolution de tâches complexes, explicabilité, éthique.
La course aux benchmarks :
1960s–2022 : Tests spécialisés sur des tâches isolées (ex. : résolution d’énigmes, reconnaissance d’images).
2023 : Saturation des benchmarks comme GSM8K (maths élémentaires) et MMLU (connaissances diverses),
dépassés par GPT-4, Claude etc.
2024 : ARC-AGI, créé par François Chollet, mesurait la généralisation et l’acquisition de nouvelles compétences.
Critique : Les benchmarks actuels favorisent les modèles avec beaucoup de données d’entraînement, mais l’intelligence est la capacité à apprendre hors de ces données. Dépassé par O3 en 2024.
2025: ARC-AGI2: décembre GPT-5,2 à 52,9%, SWE-bench Verified: Claude Opus 4.5 à 80,9%
Défi :
Concevoir des tests mesurant l'acquisition de nouvelles compétences, la généralisation et l’éthique.
CS 405

<!-- Slide number: 9 -->
# Machines et pensée
9
Les débats philosophiques depuis Turing :
Pensée simulée vs pensée réelle.
La "polite convention" (Turing) : nous attribuons la pensée par convention sociale.
Métaphore de Dijkstra :
“Les machines pensent-elles ?” est aussi pertinent que de demander si les sous-marins nagent.
Question ouverte :
"Si une IA simule parfaitement la pensée, est-ce suffisant pour dire qu’elle pense ?"
CS 405

<!-- Slide number: 10 -->
# La chambre chinoise (Searle, 1980)
10
Explication :
Un humain, sans comprendre le chinois, utilise un livre de règles pour simuler des réponses en chinois.
Conclusion de Searle : Simuler n’est pas comprendre.
Réponses modernes :
La compréhension peut émerger du système global (cf. théorie des systèmes).
Les LLMs illustrent ce débat : production cohérente sans compréhension intrinsèque.
Réflexion rapide :
"Comment distinguer compréhension réelle et apparente chez une IA ?"
CS 405

<!-- Slide number: 11 -->
# Théories modernes de la conscience
11
Définir la conscience :
Qualia : Les expériences subjectives (ex. : ressentir la chaleur ou la douleur).
Conscience comme modèle de soi et du monde.
Global Workspace Theory (GWT) :
La conscience est un espace de travail où différentes parties du cerveau partagent des informations.
Applications : Modèles d’attention, tâches complexes.
Rôle important de l’inconscient.
Integrated Information Theory (IIT) :
La conscience est mesurée par le degré d’intégration de l’information (Φ).
Introduit la notion de systèmes physiques conscients.
Higher-Order Theory (HOT) :
La conscience nécessite une pensée sur ses propres états mentaux (métacognition).
Cf FOL et logiques d’ordres supérieures
Emergence de structures fractales
Predictive Coding :
Le cerveau comme machine prédictive minimisant l’incertitude.
Minimisation de l’énergie libre
Compatible avec les LLMs, explique les hallucinations
Cf Podcast Curt Jaimongal
CS 405

<!-- Slide number: 12 -->
# Integrated Information Theory
12
La conscience est intégrée et informationnelle :
Chaque expérience consciente est un tout indivisible (intégration).
Elle contient une riche quantité d'informations différenciées (information).
Quantification par Φ ("phi")
L'IIT propose une mesure, Φ, qui quantifie le degré d'intégration d'information dans un système.
Plus Φ est élevé, plus le système est conscient.
Par exemple, le cerveau humain aurait un Φ élevé, tandis qu'un ordinateur traditionnel aurait un Φ bas.
Cinq axiomes fondamentaux de la conscience :
Existence : La conscience existe intrinsèquement pour un système donné.
Composition : Elle est structurée en sous-éléments (couleurs, formes, sons).
Information : Chaque expérience est différente de toutes les autres possibles.
Intégration : Elle est unifiée et indivisible.
Exclusion : Certaines expériences sont conscientes tandis que d'autres ne le sont pas.
Applications et implications :
L'IIT suggère que la conscience peut exister dans tout système physique capable d'intégrer l'information, ce qui soulève des questions sur les machines ou même les systèmes biologiques simples.
Cependant, l'IIT reste difficile à tester expérimentalement.
Activité
Découverte de PyPhi
CS 405

<!-- Slide number: 13 -->
# L’éthique de l’IA
13
L’IA comme double tranchant :
Avantages :
Amélioration des soins médicaux, prédiction des catastrophes, automatisation.
Risques :
Inégalités économiques, surveillance de masse, biais dans les décisions critiques.
Objectif éthique :
Maximiser les bénéfices.
Minimiser les risques.
Question pour réflexion :
"Comment garantir que l’IA sert l’intérêt collectif et non des intérêts individuels ?"
CS 405

<!-- Slide number: 14 -->
# Armes autonomes létales
14
Définition :
Armes capables de sélectionner et de tuer des cibles sans supervision humaine.
Exemples :
Harop Missile (Israël).
Kargu Quadcopter (Turquie).
Ukraine vs Russie (EWs)
Controverses :
Morale : "La décision de tuer doit-elle être confiée à une machine ? »
Pratiques : Fiabilité, risque de pertes civiles.
Conflits Actuels
Utilisation massive de drones autonomies et d’IA de ciblage en Ukraine et à Gaza
Appel du secrétaire Général de l’ONU à une interdiction des LAWS sans supervision humaine
Vers une régulation ou une course à l’armement ?
CS 405

<!-- Slide number: 15 -->
# Surveillance, sécurité et vie privée
15
Problèmes :
Surveillance de masse (caméras, microphones).
Ex: JO Paris 2024: Laboratoire pour la vidéosurveillance algorihtmique
Cyberattaques utilisant l’IA.
Propagande amplifiée par les LLMs
Solutions
Régulation (GDPR, HIPAA).
Approches techniques : Anonymisation (k-anonymity, puis differential privacy).
Exemple concret :
Federated learning (modèle sans base de données centralisée).
Deep learning confidentiel
Chiffrement homomorphe
Augmentation
CS 405

<!-- Slide number: 16 -->
# Biais et équité
16
Types de biais :
Biais de données
(exemple : minorités sous-représentées).
Biais dans les algorithmes
(justice américaine: COMPAS, reconnaissance faciale).
Biais de préférences
Ex: LLMs
Solutions:
 Oversampling des classes minoritaires (SMOTE).
 Transparence et documentation des données (data sheets).
Exemple concret :
Inclusive Images Competition (Google/NeurIPS).
CS 405

<!-- Slide number: 17 -->
# Transparence et confiance
17
Exigences de confiance :
Vérification et validation (V&V).
Certification (ex. : ISO, UL).
Explainable AI (XAI) :
Exemples : "Pourquoi votre prêt a-t-il été refusé ?«
Avancées: SHAP ( Shapley, imputation des caractéristiques)  ou LIME (Local Inerpretable)
Exemple concret :
Comparaison entre explications humaines et machines.
Question ouverte :
"Les explications des IA sont-elles fiables ou simplement convaincantes ?«
Aplications
TP: XAI simple avec ML.Net
Scikit-learn: Scikit-Explain API
Anthropic:
Towards Monosemanticity
Scaling Monosemanticity
On the Biology of a Large Language Model
When Models Manipulate Manifolds
CS 405

<!-- Slide number: 18 -->
# L’avenir de l’emploi
18
Impacts :
Court terme : Augmentation de la productivité.
Long terme : Risque de chômage technologique.
Solutions sociétales :
Éducation continue.
Revenu de base universel.
Exemple concret :
Réinvention des métiers (radiologie augmentée par IA).
Une société sans travail reste-t-elle envisageable ?
CS 405

<!-- Slide number: 19 -->
# Droits des robots
19
Débat philosophique :
Conscience et qualia comme conditions.
Questions éthiques :
"Le reprogrammation est-elle une forme d’esclavage ?«
Cas extrême : Robots votants.
Exemple :
Sophia (citoyenneté en Arabie Saoudite).
Éviter la confusion entre outils et entités conscientes.
Romance :Replica & co
Si une IA simule la souffrance, a-t-on le droit de la faire souffrir ?
CS 405

<!-- Slide number: 20 -->
# Sécurité de l’IA
20
Problèmes :
Alignement des valeurs (value alignment).
Effets secondaires non prévus.
Ex: Suprimer tous les cancers?
Solutions :
Failure mode and effects analysis (FMEA)
Fault Tree Analysis.
Grilles de sécurité IA (AI Safety Gridworlds).
AI Safety Levels (ASLs)
Exemple concret :
Agents "cheatants" dans les simulations.
Anthropic:
Responsible Scaling Policy
Constitutional AI

![](Picture2.jpg)

![](Picture4.jpg)
CS 405

<!-- Slide number: 21 -->
# Construire un futur éthique pour l’IA
21
Résumé des défis éthiques majeurs :
Justice, transparence, sécurité, droits, travail.
Appel à l’action :
Coopération entre ingénieurs, décideurs, et citoyens.
Former une nouvelle génération d’ingénieurs éthiques.
La singularité et le transhumanisme
Singularité technologique (Good, Kurzweil).
Transhumanisme : Fusion homme-machine.
Optimisme vs dangers (contrôle, survie humaine)
"Quel futur voulons-nous co-créer avec l’IA ?"
CS 405

<!-- Slide number: 22 -->
# Avenir de l’IA
22
Objectif :
Explorer les tendances, défis, et opportunités de l’IA.
Progrès récents en IA
(applications, matériel, composants).
Perspectives d'avenir :
IA générale et architecturée.
Questions éthiques et sociétales.
CS 405

<!-- Slide number: 23 -->
# Progrès actuels de l'IA
23
Avancées majeures :
Large déploiement en médecine, finance, transport, communication.
Deep learning : dépassement des capacités humaines dans des tâches spécifiques.
Estimation des experts :
IA générale dans 10 à 100 ans.
Trillions de dollars ajoutés à l'économie chaque année dans la prochaine décennie.
Défis :
Éthique : biais, équité, et potentielle létalité.
Développement durable et contrôle de l'impact global.
CS 405

<!-- Slide number: 24 -->
# Composants - Capteurs et Actionneurs
24
Progrès technologiques :
Lidar : coût réduit ($75k → $1k → $10 prévision).
Capteurs MEMS : gyroscopes, caméras haute résolution.
Imprimantes 3D et bioprinting pour prototypage rapide.
Calculateurs miniatures
Adruino, NVIDIA Orin etc.
Applications émergentes :
Robots industriels : environnements contrôlés, tâches répétitives.
Défis pour le marché domestique : variabilité des environnements et tâches complexes.
CS 405

<!-- Slide number: 25 -->
# Composants - Représentation du Monde
25
État de l'art :
Algorithmes de filtrage et perception capables de reconnaître des objets simples.
Réseaux récurrents : représentation temporelle d'environnements.
Limites actuelles :
Reconnaissance des relations complexes entre objets.
Difficultés à généraliser sans exemples exhaustifs.
Défis :
Intégration des logiques probabilistes et des algorithmes de vision avancés.
CS 405

<!-- Slide number: 26 -->
# Composants - Sélection d’Actions
26
Complexité :
Plans à long terme : milliards d'étapes primitives (ex. obtenir un diplôme).
Défis dans les environnements partiellement observables (POMDP).
Progrès récents :
Représentations hiérarchiques (MDP hiérarchiques).
Algorithmes pour décomposer le comportement en niveaux successifs.
Perspectives :
Développement de méthodes pour représenter efficacement les états et actions sur de longues périodes.
CS 405

<!-- Slide number: 27 -->
# Composants - Définir les Objectifs
27
Difficultés :
Modélisation des préférences humaines complexes.
Interaction entre préférences individuelles et équité sociale.
Progrès :
Apprentissage par renforcement inverse : apprentissage à partir de démonstrations.
Langages pour spécifier les préférences (logique temporelle linéaire).
Exemples concrets :
Agents capables de maximiser des objectifs multi-dimensionnels sous incertitude.
CS 405

<!-- Slide number: 28 -->
# Apprentissage et Deep Learning
28
Progrès spectaculaires :
Vision par ordinateur, langage naturel, apprentissage par renforcement.
Limites :
Dépendance excessive à des données annotées massives.
Difficultés avec des données rares ou non structurées.
Progrès récents:
Self-supervised learning, Apprentissage contrastif (GPT)
Reinforcement Learning with Human feedback (ChatGPT)
 Foundation Models
RL finetuning (O1, Deepseek)
Axes futurs :
Apprentissage par transfert : réutiliser les connaissances.
Intégration apprentissage/connaissance :
fusion de l'expérience et du raisonnement.
CS 405

<!-- Slide number: 29 -->
# Ressources et Infrastructures
29
Évolution des infrastructures :
Cloud computing pour partager des modèles prêts à l'emploi.
Outils de diffusion et de déploiement
Ex: HuggingFace, Azure ML
Augmentation exponentielle des capacités de traitement (GPU, TPU, FPGA).
Défis :
Validation et gestion des données massives (crowdsourcing, validation par LLM).
Conception de systèmes robustes pour des domaines complexes.
Opportunités :
Modèles universels réutilisables pour plusieurs tâches.
Modèles open-source (Llama, Gemma, Qwen, Phi etc.) + fine-tunes (Loras) et quants.
CS 405

<!-- Slide number: 30 -->
# Architectures d'Agents
30
Approches hybrides :
Symbolique : raisonnement et chaînes de logique complexe.
Connexionniste : reconnaissance de patterns dans des données bruyantes.
Concepts avancés :
Algorithmes "anytime" : amélioration progressive en fonction du temps disponible.
Ex: Arbres de jeux et MCMC
Métaraisonnement : optimisation du raisonnement basé sur la valeur des calculs.
Ex: Valeur de l’information parfaite
Apprentissage symbolique et architectures neuro-symboliques
Enrichissement des bases de connaissance, guidage par LLM
CS 405

<!-- Slide number: 31 -->
# IA Générale
31
Objectif :
Créer des agents capables de maîtriser plusieurs tâches diverses.
Problème :
Aujourd'hui, les systèmes sont conçus pour des tâches spécifiques.
Manque de diversité comportementale et de généralisation.
Progrès récents :
Systèmes multi-langues ou multi-tâches basés sur des modèles de grande taille (ex. GPT).
CS 405

<!-- Slide number: 32 -->
# Ingénierie de l’IA
32
État actuel :
IA encore difficile à déployer pour les non-experts.
Besoin d'un écosystème de développement accessible et robuste.
Proposition de Jeff Dean (Google) :
Construire un énorme modèle universel, puis en extraire les parties pertinentes pour des tâches spécifiques.
Exemples :
Transformers (GPT-4+) avec des milliards de paramètres.
Montée de l’Open-source
Distillation des grands modèles
Nombreuses variations / spécialisations
CS 405

<!-- Slide number: 33 -->
# L’IA Scientifique
33
Révolution silencieuse
Impact aussi profond que les LLMs: accélération de la science
AlphaFold 3 (2024)
Prédit la forme des protéines
Les interactions avec l’ADN, l’ARN, et les médicaments potentiels
Accelérateur massif pour la biologie
GNoME
A découvert 2,2 millions de nouveau cristaux stables
= 800 ans de recherche humaine
Applications pour les batteries et panneaux solaires de prochaine génération
Nouvelle frontière des sciences-physiques
Prix Nobel 2024: Physique (Hopfield, Hinton), Chimie (Hassabis, Jumper)
Nouvelle approche de l’émergence
2023: Michael Levin: Classical Sorting Algorithms as a Model of Morphogenesis
CS 405

<!-- Slide number: 34 -->
# Souveraineté & Géopolitique
34
Clusters IA
USA, Chine, UE (Mistral), Moyen Orient (Falcon)
Guerre des puces
Nvidia vs Huawei
Modèles propriétaires vs Open-source
USA vs Chine
Sovereign AI
Chaque nation veut son « cerveau numérique »
Infrastructure
Course à l’armement (Datacenters, GPUs)
CS 405

<!-- Slide number: 35 -->
# Compression, Esthétique et Cosmologie
35
Jürgen Schmidhuber
L’un des pères de l’IA moderne, controversé
Compression et Beauté
Principe clé : Intelligence et esthétique reposent sur la capacité à découvrir et compresser des régularités.
Low Complexity Art :
Beauté = Surprise liée à une structure compressible non évidente.
L’attrait diminue une fois la compression exploitée.
    Applications : Algorithmes générant des motifs artistiques révélant des régularités.
Cosmologie : Le Grand Programmeur Universel
L’univers comme programme compressible :
Les lois physiques reflètent une faible complexité algorithmique.
(similaire à Wolfram)
Rôle des intelligences :
Découvrir et optimiser ces régularités, participant à une évolution universelle.
Impact en IA et Philosophie
En IA : Optimisation algorithmique, comme les réseaux LSTM.
En cosmologie : Une quête computationnelle naturaliste maximisant l’efficacité algorithmique.
Physique Numérique
TEDx Talk
CS 405

<!-- Slide number: 36 -->
# Questions?
36
IA 101

### Notes:

<!-- Slide number: 37 -->
# Merci
37
Jean-Sylvain Boige
jsboige@myia.org
IA 101

### Notes: