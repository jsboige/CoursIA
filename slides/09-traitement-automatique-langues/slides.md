---
theme: ../theme-ia101
title: "09 Traitement Automatique des Langues"
info: Cours Intelligence Artificielle
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Traitement Automatique des Langues

Intelligence Artificielle -- IX

**Jean-Sylvain Boige**
MRes CSAI, Sussex University, Brighton UK
Aricie -- DNN -- PKP -- My Intelligence Agency

> Migration pédagogique : 34 diapositives historiques (2018, anglais) → parcours
> **classique → probabiliste → symbolique → neuronal → moderne**, sans réduire
> le TAL aux LLM.

---
layout: default
---

# Parcours du chapitre

<ul>
  <li>Modèles de langue (caractères, mots, n-grammes)
    <ul><li>Markov, lissage, perplexité</li></ul>
  </li>
  <li v-click>Traitement de l'information
    <ul><li>Classification, recherche d'information (IR), extraction d'information (IE)</li></ul>
  </li>
  <li v-click>Formalismes grammaticaux
    <ul><li>Hiérarchie de Chomsky, CFG/PCFG, parsing CYK</li></ul>
  </li>
  <li v-click>Sémantique, pragmatique, actes de parole</li>
  <li v-click>Traduction automatique et reconnaissance de la parole</li>
  <li v-click>Modèles neuronaux : RNN, LSTM, seq2seq, attention, Transformers</li>
  <li v-click>Agents conversationnels</li>
</ul>

---
layout: default
---

# Plan détaillé

1. Modèles de langue (caractères, n-grammes) — slides 4-7
2. Classification, IR, extraction d'information — slides 8-14
3. Grammaires formelles et probabilistes — slides 17-21
4. Sémantique, complications, argument mining — slides 22-24
5. Traduction et reconnaissance de la parole — slides 25-27
6. Modèles profonds : RNN, LSTM, seq2seq, attention — slide 28
7. Agents conversationnels — slide 29

---

# Couverture moderne (notebooks du dépôt)

| Concept | Owner dans le dépôt |
|---|---|
| Token, BPE, vocabulaire | [04-Tokenisation-From-Scratch](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/04-Tokenisation-From-Scratch.ipynb) |
| Lemmes, POS, dépendances, NER | [23_TAL_Du_Mot_Aux_Dependances](../../MyIA.AI.Notebooks/GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb) |
| n-grammes, perplexité, lissage | **GAP** — pas de notebook dédié (23_TAL ne les couvre pas) |
| IR : métriques, reranking, HyDE | [02-Retrieval-Avance](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/02-Retrieval-Avance.ipynb) |
| Recherche hybride (lexical + vecteurs) | [08-KernelMemory-Hybrid-Search](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/08-KernelMemory-Hybrid-Search.ipynb) |
| Embeddings (skip-gram from scratch) | [03-Embeddings-From-Scratch](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/03-Embeddings-From-Scratch.ipynb) |
| Vectoriel serveur, HNSW exact/ANN | [05b-Stockage-Vectoriel-Serveur](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/05b-Stockage-Vectoriel-Serveur.ipynb) |
| Automates finis, transducteurs | sous-module [SMT/Automata](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Automata/) (C#) |
| CRF / structured prediction | **GAP** — pas de notebook dédié |
| Parsing CFG/PCFG, CYK | **GAP** — le parsing du dépôt est dépendanciel (23_TAL), pas constituant |
| Sémantique, graphes de connaissances | [SW-11-Python-KnowledgeGraphs](../../MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb), [SW-13-Python-Reasoners](../../MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-13-Python-Reasoners.ipynb) |
| Fouille d'arguments, sophismes | [AA-1-informal](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-1-informal.ipynb), [AA-5-jtms](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-5-jtms.ipynb) |
| Reconnaissance de la parole | [01-2-OpenAI-Whisper-STT](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-2-OpenAI-Whisper-STT.ipynb), [01-4-Whisper-Local](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-4-Whisper-Local.ipynb) |
| Attention (MHA, MQA, GQA, SWA) | [TV-00b-Attention-Variants](../../MyIA.AI.Notebooks/GenAI/Texte/TransformerVariants/TV-00b-Attention-Variants-from-scratch.ipynb) |
| Agents conversationnels | [03-Chat-Streaming-QA-OWUI](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/03-chat-streaming/03-Chat-Streaming-QA-OWUI.ipynb), [configurer-chatbots](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots/configurer-chatbots-par-l-api.ipynb) |

> Aucun arc n'est perdu : chaque ligne pointe un **owner réel** ou un **GAP**
> assumé, à fermer par un notebook atomique dédié.

---
layout: section
---

# I. Modèles de langue

Caractères, mots, n-grammes et lissage

---
layout: default
---

# 4. Modèles de langue

**Objectifs du TAL**

- Communication avec les humains
- Acquisition d'information → Connaissance
- Classification, recherche d'information, extraction

**Modèles de langue**

- Une **distribution de probabilité** sur des séquences de tokens (caractères,
  syllabes, mots, phrases)
- Token = unité atomique de l'alphabet considéré
- Modèles de langues formelles (Java, Python) : **récursion** + **vocabulaire clos**

**Perplexité** : mesure standard de qualité d'un modèle de langue (plus c'est bas,
mieux c'est). Un modèle triviale (uniforme) donne une perplexité ≈ taille du vocabulaire.

*Notebooks : [04-Tokenisation-From-Scratch](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/04-Tokenisation-From-Scratch.ipynb) (le token construit à la main : BPE, la taille de vocabulaire comme hyperparamètre) · [23_TAL_Du_Mot_Aux_Dependances](../../MyIA.AI.Notebooks/GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb) (mots vs BPE comparés frontalement sur corpus français)*

---

# 5. n-grammes

- Modèles **n-gramme** : P(c₁:N) ≈ ∏ P(cᵢ | cᵢ₋ₙ₊₁:ᵢ⁻¹)
- Markov d'ordre n − 1
- Valable pour caractères, syllabes, mots, phrases
- Estimation par comptage sur corpus + **lissage** (Laplace, Kneser-Ney)

**Exemple (mot "the")** : P("the") = 0.027 sur un grand corpus anglais.

**Modèle bigramme** : P("the cat") = P("the") × P("cat" | "the").

> **Gap du dépôt** : aucun notebook n'implémente les modèles n-grammes, la
> perplexité ni le lissage — les notebooks de tokenisation s'arrêtent au token,
> pas à la distribution sur les séquences. Piste de notebook atomique.

---

# 6-7. Calculs et modèles mots

**Calcul** : estimation par comptage sur corpus annoté, lissage pour les
séquences absentes.

**Modèles mots** (vs caractères) :

- Vocabulaire plus large → besoin du symbole hors vocabulaire `<UNK>`
- Symboles spéciaux : `<NUM>`, `<EMAIL>`, etc.
- **Unigramme** : perplexité ≈ 891 sur Book ; **Bigramme** : perplexité ≈ 142

**Exemples random** :
- Unigramme : « logical are as are confusion a may right tries agent goal the was ... »
- Bigramme : mieux, mais toujours agrammatical

---
layout: section
---

# II. Classification, RI, IE

Inférence opérationnelle sur texte

---
layout: default
---

# 8. Classification de texte

**Catégorisation** : assigner une classe à un document.

- Identification de langue, genre, analyse de sentiment
- **Détection de spam** : Bayes naïf sur n-grammes

**Bayes naïf** :

$$P(\text{spam} | \text{message}) \propto P(\text{message} | \text{spam}) P(\text{spam})$$

**Approche ML** : message = vecteur de features (n-grammes), classifieur supervisé
(sVM, LR, ou Bayes).

**Bag-of-words** : unigrammes avec comptage d'occurrences, longueur ~100 000,
**pas d'ordre** conservé.

---

# 9-11. Recherche d'information (IR)

**Objectif** : trouver des documents pertinents dans un corpus.

- Corpus (fichier, page, paragraphe), requêtes (booléennes), ensemble de résultats
- **Modèle booléen** initial : pertinence binaire, rigide

**Évaluation** :

- **Précision** = |pertinents ∩ résultats| / |résultats|
- **Rappel** = |pertinents ∩ résultats| / |pertinents|
- **P@10** = précision dans les 10 premiers résultats
- **F1** = 2PR/(P+R)

**Algorithmes** :

- **TF-IDF** : pondération classique par fréquence inverse documentaire
- **PageRank** (Google, 1997) : surfer aléatoire + vote par in-links, récursif jusqu'à convergence

*Notebooks : [02-Retrieval-Avance](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/02-Retrieval-Avance.ipynb) (précision, rappel et métriques de rang **from scratch**, puis HyDE et reranking cross-encoder benchmarkés) · [08-KernelMemory-Hybrid-Search](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/08-KernelMemory-Hybrid-Search.ipynb) (la recherche hybride du dépôt : le lexical et le vectoriel combinés, héritier direct du booléen + TF-IDF)*

---

# 12-13. Extraction d'information (IE)

**Objectif** : extraire des **champs structurés** depuis du texte non structuré.

- Adresses, prévisions météo, entités nommées

**Approches** :

- **Automates finis** : regex pour motifs simples (`[$][0-9]+([.][0-9][0-9])?` matche `$249.99`)
- **Templates** : priorité entre motifs, valeurs par défaut
- **Extraction d'ontologie** depuis grands corpus (Hearst patterns)

**Pattern Hearst** : « NP such as NP (, NP)* ((and|or) NP)? » extrait des
hyperonymes (sous-catégories) depuis le web.

*Notebooks : [23_TAL_Du_Mot_Aux_Dependances](../../MyIA.AI.Notebooks/GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb) (§5 : entités nommées sur corpus juridique et technique français, avec mesure contre un jeu d'or) · sous-module [SMT/Automata](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Automata/) (automates finis et transducteurs exécutables en C#)*

---

# 14. Synthèse section II

**Points clés** :

- n-grammes probabilistes : très puissants (identification, orthographe,
  classification, reconnaissance d'entités)
- Millions de features → **sélection** et **prétraitement** indispensables
- Classification : Bayes naïf n-grammes OU tout classifieur ML (Deep Learning)
- Compression ≈ modèle de langue
- RI : TF-IDF, PageRank, F1 pour l'évaluation

---
layout: default
---

# 14bis. Du sac de mots aux embeddings — la sémantique vectorielle

**Le chaînon manquant du parcours historique** : entre le bag-of-words (slide 8)
et les Transformers (slide 28), la révolution de 2013 — représenter un **mot par
un vecteur** dont la géométrie porte le sens.

**Word2vec, skip-gram avec échantillonnage négatif** :

- Entraîner un réseau minuscule à **prédire le contexte** d'un mot
- La matrice de poids **est** la représentation : chaque ligne = un mot → un vecteur
- La sémantique **avant** l'apprentissage est déjà mesurable : co-occurrences et PMI

**Ce qui émerge** : des relations régulières dans l'espace vectoriel — les mots
similaires se rapprochent, les contrastes s'organisent en directions.

**Du lexical au recherche sémantique** : indexer ces vecteurs dans un index ANN
(HNSW) permet de chercher **par sens** et non plus par chaîne exacte — c'est le
passage de la RI classique (TF-IDF) au RAG moderne.

*Notebooks : [03-Embeddings-From-Scratch](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/03-Embeddings-From-Scratch.ipynb) (skip-gram NSG from scratch, PMI, la géométrie qui émerge avant/après entraînement) · [05-Stockage-Vectoriel](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/05-Stockage-Vectoriel.ipynb) et [05b-Stockage-Vectoriel-Serveur](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/05b-Stockage-Vectoriel-Serveur.ipynb) (l'index HNSW du dépôt : construction prouvée par `indexed_vectors_count`, compromis exact/ANN mesuré sur `hnsw_ef`) · [05_RAG_Modern](../../MyIA.AI.Notebooks/GenAI/Texte/05_RAG_Modern.ipynb) (le RAG de bout en bout sur API)*

---
layout: default
---

# 15. Questions ?

**Discussion** :

- Tradeoff perplexité / couverture ?
- Bayes vs Deep Learning pour la classification ?
- Quand un automate suffit-il ?

---
layout: section
---

# III. Grammaires formelles

De Chomsky à CYK

---
layout: default
---

# 17. Grammaires

**Communication** = échange d'information par production/perception de signes.

**Modèles de communication** : plus complexes que la simple classification.

**Formalismes grammaticaux** : classes de capacité générative (Chomsky).

| Classe | Machine | Exemple |
|---|---|---|
| Récursivement énumérable | Turing machine | Langages naturels (?) |
| Sensible au contexte | LBA | Langages naturels |
| **Hors contexte** (CFG) | Automate à pile | Syntaxe de la plupart des langages de programmation |
| Régulier | DFA | Patterns, regex |

---
layout: image-overlay
image: ./images/slide_18_img_7fb42adf.png
---

# 18. Grammaires probabilistes

**PCFG** = CFG + probabilités sur les règles.

- Non-terminaux + terminaux + **règles pondérées**

**Exemple minimal** (monde du Wumpus) :

```
S → NP VP  [0.9]
S → VP     [0.1]
NP → DET N [0.6]
NP → NAME  [0.4]
VP → V NP  [0.4]
VP → V     [0.6]
```

**Lexique** : listes de mots autorisés par catégorie (noms, verbes, adjectifs,
mots fonctionnels). Classes ouvertes (mots ajoutés au fil du temps).

*Figure historique (PCFG)* : extrait du PPTX original 2018.

---
layout: image-overlay
image: ./images/slide_19_img_fe5c88d1.png
---

# 19. Analyse syntaxique — Parsing

**Objectif** : retrouver la **structure en syntagmes** d'une phrase.

- Approches **top-down** ou **bottom-up**
- Risque d'inefficacité → **backtracking**

**Exemple classique d'ambiguïté** :

> « Have the students in section 2 of Computer Science 101 take the exam. »

vs.

> « Have the students in section 2 of Computer Science 101 taken the exam? »

**Solution** : stocker les résultats intermédiaires → **Chart parsing**, **CYK**.

*Notebooks : [23_TAL_Du_Mot_Aux_Dependances](../../MyIA.AI.Notebooks/GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb) (§4 : **dépendances syntaxiques** sur corpus français — étiquettes `nsubj`/`obj`/`obl:mod`/`det`, le jeu de relations d'Universal Dependencies — l'autre grande tradition du parsing, où l'arbre porte les relations de tête à subordonné plutôt que les syntagmes) · CYK/PCFG constituant : gap du dépôt confirmé (aucun notebook, mesures au mot près)*

*Figure historique (Chart parsing)* : extrait du PPTX original 2018.

---

# 20-21. Apprentissage des PCFG

**Données d'entraînement** : corpus annoté = **treebank**
(Penn Treebank 1993, 3M mots).

**Apprentissage** : PCFG par **comptage** des règles dans le treebank.

$$\hat{P}(\alpha \to \beta) = \frac{\text{count}(\alpha \to \beta)}{\text{count}(\alpha)}$$

**Améliorations** :

- Lissage des règles peu fréquentes
- **Grammaires augmentées** : lexicalisation, sous-catégorisation, head-to-head
- **Definite Clause Grammar** (DCG) → logique du premier ordre (Prolog)

---
layout: section
---

# IV. Sémantique et complications

Du sens au contexte

---
layout: image-overlay
image: ./images/slide_22_img_752cd77a.png
---

# 22. Interprétation sémantique

**Sémantique compositionnelle** : le sens d'une expression est **fonction** du sens
de ses parties.

**Exemple (expressions arithmétiques)** : ajouter une variable dans l'arbre syntaxique.

**Règles sémantiques** : arbre syntaxique annoté d'une **interprétation sémantique**.

**Verbes** : prédicats au même titre que les syntagmes verbaux (VP).

**Entraînement** : à partir d'exemples annotés (parallélisme syntaxe-sémantique).

*Notebooks : [SW-11-Python-KnowledgeGraphs](../../MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb) (représenter le sens en graphe de connaissances RDF) · [SW-13-Python-Reasoners](../../MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-13-Python-Reasoners.ipynb) (raisonner dessus : les raisonneurs de logiques de description)*

*Figure historique (sémantique compositionnelle)* : extrait du PPTX original 2018.

---

# 23. Complications

**Temps et aspect** → **event calculus** (intervales, fluents).

**Quantification** → quasi-logical form (Skolem, etc.).

**Pragmatique** : injecter du **contexte** :

- **Indexicaux** (« je », « aujourd'hui »)
- **Actes de parole** (commandes, assertions, promesses, avertissements)
- **Dépendances longue distance** :

> « Who did the agent tell you to give the gold to? » → trace `_`licenciée par `who`

---
layout: image-overlay
image: ./images/slide_24_img_765dfaa8.png
---

# 24. Fouille d'arguments

**Objectif** : extraire la **structure inférentielle** depuis un texte argumentatif.

**Efforts conjoints** : CMNA, COMMA, ACL.

**Outils** :

- DisLog Language, Topic-Based Modelling
- **AIF** (Argument Interchange Format) + RDF
- Outils d'annotation : **OVA+**

**Applications** : détection de sophismes, journalisme automatisé, aide à la décision.

*Notebooks : [AA-1-informal](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-1-informal.ipynb) (détection de sophismes par taxonomie : 7 familles, descente dans la ramification) · [AA-2-formal](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-2-formal.ipynb) (l'analyse formelle : graphes d'arguments et acceptabilité) · [AA-5-jtms](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-5-jtms.ipynb) (Truth Maintenance System : rétractation et cascade non-monotone sur les justifications IN/OUT)*

*Figure historique (AIF / RDF)* : extrait du PPTX original 2018.

---
layout: section
---

# V. Traduction et parole

---

# 25-26. Traduction automatique

**Types** :

- **Rough** : contient des erreurs, post-correction humaine
- **Pre-edited** : traduction humaine après pré-édition
- **Restricted-source** : entièrement automatique sur domaines stéréotypés

**Difficultés** :

- Les langues catégorisent différemment
- Besoin d'une **langue intermédiaire (interlingua)** pour représenter l'universal

**Traduction statistique** (la plus efficace, ex. Google Translate) :

- Pas besoin d'ontologie complexe ni de grammaires artisanales
- Juste des **exemples de traduction**
- Maximise P(f) × P(e|f) (modèle cible × modèle de traduction)

> **Gap du dépôt** : aucun notebook de traduction dédié (les LLM auto-hébergés du
> dépôt traduisent, mais aucune cellule n'isole P(f) × P(e|f)). Piste de notebook atomique.

---

# 27. Reconnaissance de la parole

**Objectif** : signal acoustique → phrase.

**Difficultés** : ambiguïté + bruit.

> « recognize speech » vs « wreck a nice beach »

**Solutions** :

- **Segmentation** : espaces
- **Coarticulation** : « nice beach » → « sp »
- **Homophones** : « to / too / two »
- **Séquence la plus probable** :
  P(acoustic | words) × P(words | language model)

**Modèle acoustique** : P(sound₁:ₜ | word₁:ₜ). **Modèle de langue** :
P(word₁:ₜ) — vu en section I.

---
layout: default
---

# 27bis. La parole dans le dépôt — Whisper en pratique

**Le pipeline du dépôt déroule exactement la chaîne de la slide précédente** :
modèle acoustique (Whisper), décodage avec modèle de langue, transcription
structurée — sur audio réel, API et local.

**Whisper, deux voies** :

- **API OpenAI** : [01-2-OpenAI-Whisper-STT](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-2-OpenAI-Whisper-STT.ipynb) — transcription, timestamps, langues
- **Local** : [01-4-Whisper-Local](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-4-Whisper-Local.ipynb) — le même modèle auto-hébergé, sans données en sortie de machine

**Vers les applications** :

- **Pipeline de transcription** : [04-2-Transcription-Pipeline](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-2-Transcription-Pipeline.ipynb) — du fichier audio au texte exploitable, enchaîné
- **Prosodie** : [04-10-Annotation-Prosodique](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-10-Annotation-Prosodique.ipynb) — l'annotation prosodique : ce que la courbe mélodique ajoute au mot
- **Voix temps réel** : [03-3-Realtime-Voice-API](../../MyIA.AI.Notebooks/GenAI/Audio/03-Orchestration/03-3-Realtime-Voice-API.ipynb) — la boucle complète écouter-répondre

> La reconnaissance de la parole n'est plus un exemple de manuel : le dépôt la
> fait tourner, la mesure et la compose. C'est le pendant **pratique** de la
> théorie P(acoustic | words) × P(words) de la section V.

---
layout: section
---

# VI. Modèles neuronaux

De RNN à Transformers

---
layout: image-overlay
image: ./images/slide_28_img_4b6f2b7a.png
---

# 28. Modèles profonds

**Réseaux récurrents (RNN)** : mémoire interne = contexte.

- **seq2seq** : encodeur / décodeur
- Couches **LSTM** (longue mémoire)
- **Attention** : focus dynamique sur la séquence source

**Tâches** : traduction, sous-titrage, Q&A, génération de texte.

**Transformers** (2017) : self-attention multi-têtes, parallélisable, fondation des
LLM modernes.

*Notebooks : [TV-00b-Attention-Variants](../../MyIA.AI.Notebooks/GenAI/Texte/TransformerVariants/TV-00b-Attention-Variants-from-scratch.ipynb) (l'attention multi-têtes **from scratch**, et ses variantes de production : MHA, MQA, GQA, SWA — le cache KV comme vrai coût à l'inférence) · [10b_Inference_Mechanics](../../MyIA.AI.Notebooks/GenAI/Texte/10b_Inference_Mechanics.ipynb) (TTFT et ITL mesurés sur LLM réel)*

> Cette migration historique s'arrête à 2018. Pour les architectures
> post-2018 (BERT, GPT, T5, etc.), voir `GenAI/Texte/10*` et `GenAI/Texte/13*`
> du dépôt.

*Figure historique (seq2seq + attention)* : extrait du PPTX original 2018.

---
layout: image-overlay
image: ./images/slide_29_img_0094ef69.png
---

# 29. Agents conversationnels

**Agents à base de règles avec NLP UX** :

- Microsoft Bot Framework + LUIS
- Google Dialogflow
- Recast, Facebook Wit.ai, Salesforce Einstein

**Architecture** :

- Connecteurs vers canaux (Slack, Teams, Messenger, web)
- Déclencheurs synchrones / asynchrones
- Appels NLP (LUIS, Dialogflow) pour l'intent et les entités

*Notebooks : [03-Chat-Streaming-QA-OWUI](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/03-chat-streaming/03-Chat-Streaming-QA-OWUI.ipynb) (Open WebUI testé de bout en bout : auth, chat, streaming, RAG, tools) · [configurer-chatbots-par-l-api](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots/configurer-chatbots-par-l-api.ipynb) (le chatbot WordPress : configuration, mémoire éphémère, données structurées — les intents et entités de LUIS, en version moderne) · [19_OWUI_Orchestration](../../MyIA.AI.Notebooks/GenAI/Texte/19_OWUI_Orchestration.ipynb)*

*Figure historique (architecture bot)* : extrait du PPTX original 2018.

---
layout: default
---

# 30. Synthèse TAL historique

**Théorie des langages formels** : utile pour la syntaxe.

- Syntagmes, grammaires hors contexte
- Parsing efficace avec PCFG
- Apprentissage depuis treebank
- Augmentation (DCG → FOL)

**Vers le moderne** : embeddings, RNN, LSTM, seq2seq, attention, Transformers.

> Le TAL historique n'est pas obsolète : il pose les **fondations théoriques**
> des architectures modernes. Comprendre n-grammes et PCFG reste indispensable
> pour interpréter les sorties LLM.

---

# 31. Questions ?

**Discussion** :

- Quelle place pour les grammaires dans les LLM ?
- PCFG vs Transformers : opposition ou complémentarité ?
- Traduction statistique vs neuronale : quand l'une surpasse-t-elle l'autre ?

---
layout: section
---

# VII. Références au dépôt

---

# 32. Couverture TAL dans le dépôt

<style scoped>
.slidev-layout { font-size: 0.88em; }
</style>

| Concept historique | Notebook moderne |
|---|---|
| Token, BPE | [04-Tokenisation-From-Scratch](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/04-Tokenisation-From-Scratch.ipynb) |
| Lemmes, POS, dépendances, NER | [23_TAL_Du_Mot_Aux_Dependances](../../MyIA.AI.Notebooks/GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb) |
| Automates finis, transducteurs | sous-module [SMT/Automata](../../MyIA.AI.Notebooks/SymbolicAI/SMT/Automata/) |
| IR : métriques, reranking | [02-Retrieval-Avance](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/02-Retrieval-Avance.ipynb) · [08-KernelMemory-Hybrid-Search](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/08-KernelMemory-Hybrid-Search.ipynb) |
| Embeddings, sémantique vectorielle | [03-Embeddings-From-Scratch](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/03-Embeddings-From-Scratch.ipynb) · [05b-Stockage-Vectoriel-Serveur](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/05b-Stockage-Vectoriel-Serveur.ipynb) |
| Sémantique, graphes | [SW-11-Python-KnowledgeGraphs](../../MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-11-Python-KnowledgeGraphs.ipynb) · [SW-13-Python-Reasoners](../../MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-13-Python-Reasoners.ipynb) |
| Fouille d'arguments, sophismes | [AA-1-informal](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-1-informal.ipynb) · [AA-5-jtms](../../MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-5-jtms.ipynb) |
| Reconnaissance de la parole | [01-2-OpenAI-Whisper-STT](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-2-OpenAI-Whisper-STT.ipynb) · [01-4-Whisper-Local](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-4-Whisper-Local.ipynb) · [04-2-Transcription-Pipeline](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-2-Transcription-Pipeline.ipynb) |
| RNN, LSTM, seq2seq, attention | [TV-00b-Attention-Variants](../../MyIA.AI.Notebooks/GenAI/Texte/TransformerVariants/TV-00b-Attention-Variants-from-scratch.ipynb) · [10b_Inference_Mechanics](../../MyIA.AI.Notebooks/GenAI/Texte/10b_Inference_Mechanics.ipynb) |
| Transformers, LLMs | [11_Quantization](../../MyIA.AI.Notebooks/GenAI/Texte/11_Quantization.ipynb) · [13_Agentic_Orchestration](../../MyIA.AI.Notebooks/GenAI/Texte/13_Agentic_Orchestration.ipynb) |
| Bots conversationnels | [03-Chat-Streaming-QA-OWUI](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/03-chat-streaming/03-Chat-Streaming-QA-OWUI.ipynb) · [configurer-chatbots-par-l-api](../../MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-1-Chatbots/configurer-chatbots-par-l-api.ipynb) |

**Gaps confirmés par mesure** : n-grammes/perplexité/lissage (zéro occurrence dans 23_TAL) · HMM/Viterbi (`Probas/Infer/*` couvre l'inférence probabiliste, pas l'alignement de séquences) · CRF · CYK/PCFG constituant (le parsing du dépôt est dépendanciel).

> **Note** : les lignes « n-grammes → 23_TAL » et « HMM, Viterbi → Probas/Infer/* »
> des versions antérieures étaient des **labels menteurs** par excès d'optimisme —
> mesurés, corrigés en _gap_, avec les owners réels cités pour ce qui est
> réellement couvert.

---

# 33. Projets étudiants suggérés (héritage 2018)

**Conception de bots de service pour réseaux sociaux** :

- Chat Bots, AIML, Reddit et agents de service, NLP, RDF, APIs

**Modèle d'inférence pour analyse de sentiment** :

- Probabilités, Infer.NET, expérimental, Reddit

**Stratégies d'entraînement pour trading crypto** :

- Bitcoin, DN/Encog, machine learning

> Ces projets sont **historiques** (2018). Pour les projets modernes équivalents,
> voir le syllabus courant (`GradeBookApp/`, racine du dépôt — moteur de notation, pas le syllabus).

---

# Annexe — Figures historiques préservées (référence)

Le dépôt ne conserve désormais que les **six PNG strictement nécessaires**
(assets référencés par le rendu) — un par slide d'`image-overlay` (slides 18,
19, 22, 24, 28, 29). Tous les autres diagrammes du PPTX canonique (≥30 KB ou non)
sont accessibles dans le PPTX source hors Git. La voie canonique pour intégrer
des figures complémentaires au deck est `image-overlay` (jamais `bg right` /
`image-right` issus de convertisseurs, règle projet).

**Source** : PPTX canonique `Artificial Intelligence - 6 - Natural Language Processing.pptx`
hors dépôt (GDrive *Bibliographie IA*, Tell bibliography-hygiene règle : hors dépôt, licence d'origine préservée).

Voir slide suivante pour le tableau détaillé des six figures retenues.

---

# Annexe B — Tableau des figures retenues (référence)

| Slide | Fichier | Taille | Intégré |
|---|---|---:|---|
| 18 | `slide_18_img_7fb42adf.png` | 91 KB | **oui** |
| 19 | `slide_19_img_fe5c88d1.png` | 72 KB | **oui** |
| 22 | `slide_22_img_752cd77a.png` | 35 KB | **oui** |
| 24 | `slide_24_img_765dfaa8.png` | 158 KB | **oui** |
| 28 | `slide_28_img_4b6f2b7a.png` | 63 KB | **oui** |
| 29 | `slide_29_img_0094ef69.png` | 135 KB | **oui** |

Tableau de référence — chacune des six lignes renvoie à un PNG référencé par
un slide `image-overlay` du corps du deck. Le tableau complet figure ici pour
traçabilité, hors du flux de présentation principal.

---

# 34. Merci

**Jean-Sylvain Boige**
jsboige@myia.org

> Migration pédagogique : 34 slides TAL historiques → Slidev FR classique →
> moderne. Aucun arc perdu silencieusement, chaque concept pointe vers un
> owner exécutable du dépôt.
