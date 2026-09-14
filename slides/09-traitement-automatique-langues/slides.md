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
| n-grammes, modèles de langue | `GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb` |
| Markov caché (HMM), Viterbi | `Probas/Infer/Infer-*` |
| Automates finis, transducteurs (morphologie) | `Search/Z3/Sudoku/Lean` |
| CRF / structured prediction | `Probas/Infer/CRF` |
| Parsing CFG/PCFG, CYK | `SymbolicAI/Lean` |
| Sémantique compositionnelle | `SymbolicAI/SemanticWeb` |
| Word embeddings, RNN, LSTM, seq2seq, Transformers | `GenAI/Texte/10*` |
| Agents conversationnels, LUIS, Dialogflow | `GenAI/Plateformes-Conversationnelles` |

> Aucun des 8 arcs n'est perdu silencieusement : chacun renvoie vers un **owner
> exécutable** du dépôt. Les gaps restent à fermer par des notebooks atomiques
> additionnels (jamais autofermés).

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

---

# 5. n-grammes

- Modèles **n-gramme** : P(c₁:N) ≈ ∏ P(cᵢ | cᵢ₋ₙ₊₁:ᵢ₋₁)
- Markov d'ordre n − 1
- Valable pour caractères, syllabes, mots, phrases
- Estimation par comptage sur corpus + **lissage** (Laplace, Kneser-Ney)

**Exemple (mot "the")** : P("the") = 0.027 sur un grand corpus anglais.

**Modèle bigramme** : P("the cat") = P("the") × P("cat" | "the").

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/slide_05_img_403ca3e2.png" alt="Bande de formules de probabilité de n-gramme : P(c_i | c_{i−2:i−1})" style="width:100%; height:110px; object-fit:contain;">
<img src="./images/slide_05_img_fd28e615.png" alt="Équations de décodage : recherche du n-gramme qui maximise P(c_i | c_{i−2:i−1})" style="width:100%; height:110px; object-fit:contain;">
</div>

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

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/slide_06_img_30934f19.png" alt="Formule de la perplexité d'un modèle de langue pour la séquence c_{1:N}" style="width:100%; height:100px; object-fit:contain;">
<img src="./images/slide_06_img_33419806.png" alt="Formule du lissage par interpolation linéaire des modèles unigramme, bigramme et trigramme (poids lambda)" style="width:100%; height:100px; object-fit:contain;">
</div>

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

<img src="./images/slide_08_img_052698a9.png" alt="Formule de décision bayésienne naïve : c = argmax_c P(message | c) · P(c)" style="display:block; margin:4px auto 0; max-height:150px; width:auto; max-width:100%; object-fit:contain;">

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

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/slide_09_img_05183bd8.png" alt="Bande de 130 × 27 px, aucun texte lu par OCR à la résolution fournie" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_09_img_306ecf77.png" alt="Formule de la pondération IDF d'un terme de requête en recherche d'information" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_09_img_52bce069.png" alt="Bande de 486 × 90 px, aucun texte lu par OCR à la résolution fournie" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_09_img_650df41f.png" alt="Formule de la fonction de classement BM25" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_11_img_7c03b7e6.png" alt="Formules de précision et de rappel d'un moteur de recherche" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_11_img_a8595e2d.png" alt="Figure de 326 × 276 px, aucun texte lu par OCR à la résolution fournie" style="width:100%; height:70px; object-fit:contain;">
</div>

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

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/slide_12_img_3b62caa7.png" alt="Chaîne de catégories grammaticales annotées (nom propre, article, adjectif) extraite d'un texte" style="width:100%; height:78px; object-fit:contain;">
<img src="./images/slide_12_img_6330909f.png" alt="Formule d'un modèle de Markov caché (transitions et émissions) pour l'étiquetage de séquences" style="width:100%; height:78px; object-fit:contain;">
<img src="./images/slide_12_img_63ac30a8.png" alt="Formule de la probabilité jointe d'une séquence d'étiquettes conditionnée par les observations" style="width:100%; height:78px; object-fit:contain;">
</div>
<img src="./images/slide_12_img_077838bf.png" alt="Table de motifs à préfixe, cible et suffixe (Prefix, Target, Postfix) remplissant les champs d'une annonce de séminaire (orateur, date, lieu)" style="display:block; margin:4px auto 0; max-height:78px; width:auto; max-width:100%; object-fit:contain;">
<img src="./images/slide_13_img_e0b7882c.png" alt="Table des motifs Hearst d'extraction d'hyperonymes (type, modèle, exemple, fréquence), de 38 % pour le motif verbal à 1 %" style="display:block; margin:4px auto 0; max-height:78px; width:auto; max-width:100%; object-fit:contain;">

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

<img src="./images/slide_17_img_ac26386a.png" alt="Bande de 351 × 73 px dont seul le mot Grammatica est lu par OCR" style="display:block; margin:4px auto 0; max-height:140px; width:auto; max-width:100%; object-fit:contain;">

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

<div style="display:grid; grid-template-columns:repeat(4,1fr); gap:6px; align-items:center;">
<img src="./images/slide_18_img_262ef8b0.png" alt="Bande de règles PCFG pondérées (VP vers verbe et syntagme nominal)" style="width:100%; height:60px; object-fit:contain;">
<img src="./images/slide_18_img_7fb42adf.png" alt="Table des règles PCFG du monde du Wumpus et de leurs probabilités (NP VP 0,90 ; S Conj S 0,10 ; …)" style="width:100%; height:60px; object-fit:contain;">
<img src="./images/slide_18_img_806f7e0f.png" alt="Tableau des probabilités syntaxiques et lexicales du Wumpus (NP vers VP, Article, Nom, Verbe)" style="width:100%; height:60px; object-fit:contain;">
<img src="./images/slide_18_img_9b5e1bf2.png" alt="Lexique probabiliste du monde du Wumpus : catégories (Nom, Verbe, Adjectif, Pronom, Article) et probabilités de chaque mot" style="width:100%; height:60px; object-fit:contain;">
</div>

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

<img src="./images/slide_19_img_fe5c88d1.png" alt="Pseudo-code de l'algorithme CYK d'analyse syntaxique probabiliste" style="display:block; margin:4px auto 0; max-height:130px; width:auto; max-width:100%; object-fit:contain;">

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

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/slide_21_img_02221c4a.png" alt="Bande de 484 × 49 px, texte illisible à la résolution fournie" style="width:100%; height:66px; object-fit:contain;">
<img src="./images/slide_21_img_505c3599.png" alt="Règle de réécriture avec contrainte d'accord : NP(n) vers Article(a) Adjs(j) Noun(n), Compatible(i, n)" style="width:100%; height:66px; object-fit:contain;">
<img src="./images/slide_21_img_a1c48329.png" alt="Table de subdivision des catégories syntaxiques (syntagmes nominaux et verbaux, pronoms, noms) en sous-catégories" style="width:100%; height:66px; object-fit:contain;">
<img src="./images/slide_21_img_c8fd66ea.png" alt="Règles lexicalisées et leurs probabilités de réécriture (VP, NP, Article, Nom)" style="width:100%; height:66px; object-fit:contain;">
<img src="./images/slide_21_img_e92de5f3.png" alt="Règles de grammaire augmentée par traits de tête : S(head), NP(Sbj, pn, h), VP(pn, head), et leurs instances lexicales" style="width:100%; height:66px; object-fit:contain;">
</div>

---
layout: section
---

# IV. Sémantique et complications

Du sens au contexte

---
layout: default
---

# 22. Interprétation sémantique

**Sémantique compositionnelle** : le sens d'une expression est **fonction** du sens
de ses parties.

**Exemple (expressions arithmétiques)** : ajouter une variable dans l'arbre syntaxique.

**Règles sémantiques** : arbre syntaxique annoté d'une **interprétation sémantique**.

**Verbes** : prédicats au même titre que les syntagmes verbaux (VP).

**Entraînement** : à partir d'exemples annotés (parallélisme syntaxe-sémantique).

<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/slide_22_img_0a59a88d.png" alt="Arbre syntaxique annoté d'une interprétation sémantique : S(pred(obj)), NP(obj), VP(pred), Loves(x, y)" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_22_img_5bfa3171.png" alt="Bande de 537 × 51 px, texte illisible à la résolution fournie" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_22_img_752cd77a.png" alt="Grammaire d'attachement sémantique des expressions arithmétiques : Exp, Operator, Nombre, Chiffre" style="width:100%; height:70px; object-fit:contain;">
<img src="./images/slide_22_img_a95ab5ff.png" alt="Arbre sémantique d'une expression arithmétique, décomposé en Exp, Number et Digit" style="width:100%; height:70px; object-fit:contain;">
</div>

---

# 23. Complications

**Temps et aspect** → **event calculus** (intervales, fluents).

**Quantification** → quasi-logical form (Skolem, etc.).

**Pragmatique** : injecter du **contexte** :

- **Indexicaux** (« je », « aujourd'hui »)
- **Actes de parole** (commandes, assertions, promesses, avertissements)
- **Dépendances longue distance** :

> « Who did the agent tell you to give the gold to? » → trace `_`licenciée par `who`

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/slide_23_img_4bff67f5.png" alt="Bande de 476 × 49 px, texte illisible à la résolution fournie" style="width:100%; height:80px; object-fit:contain;">
<img src="./images/slide_23_img_e60ebcf7.png" alt="Formule de forme quasi-logique : il existe i tel que Loves(John, Mary) et During(Now, Extent(Ei))" style="width:100%; height:80px; object-fit:contain;">
</div>

---

# 24. Fouille d'arguments

**Objectif** : extraire la **structure inférentielle** depuis un texte argumentatif.

**Efforts conjoints** : CMNA, COMMA, ACL.

**Outils** :

- DisLog Language, Topic-Based Modelling
- **AIF** (Argument Interchange Format) + RDF
- Outils d'annotation : **OVA+**

**Applications** : détection de sophismes, journalisme automatisé, aide à la décision.

<img src="./images/slide_24_img_765dfaa8.png" alt="Graphe d'argumentation AIF sur la question « Should we invade Syria? » : supports et conflits entre affirmations" style="display:block; margin:4px auto 0; max-height:120px; width:auto; max-width:100%; object-fit:contain;">

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

<img src="./images/slide_25_img_fd120b4e.png" alt="Niveaux de transfert en traduction (interlingua, sémantique, syntaxe, mots) illustrés par John loves Mary devenant Jean aime Marie" style="display:block; margin:4px auto 0; max-height:90px; width:auto; max-width:100%; object-fit:contain;">
<div style="display:grid; grid-template-columns:repeat(3,1fr); gap:6px; align-items:center;">
<img src="./images/slide_26_img_06684b0d.png" alt="Bande de 259 × 47 px, texte illisible à la résolution fournie" style="width:100%; height:64px; object-fit:contain;">
<img src="./images/slide_26_img_8ad251a0.png" alt="Exemple de traduction alignée français-anglais (There is a smelly wumpus / Il y a un wumpus malodorant) avec les probabilités du modèle" style="width:100%; height:64px; object-fit:contain;">
<img src="./images/slide_26_img_f78922be.png" alt="Formule du modèle de traduction statistique : f* = argmax P(f|e) = argmax P(e|f) · P(f)" style="width:100%; height:64px; object-fit:contain;">
</div>

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

<div style="display:grid; grid-template-columns:repeat(4,1fr); gap:6px; align-items:center;">
<img src="./images/slide_27_img_00db902b.png" alt="Signal acoustique analogique, échantillonné et quantifié, puis découpé en trames décrites par des traits" style="width:100%; height:58px; object-fit:contain;">
<img src="./images/slide_27_img_0cc1bbb9.png" alt="Modèle de Markov caché d'un phone : états Onset, Mid et End avec probabilités de transition et de sortie" style="width:100%; height:58px; object-fit:contain;">
<img src="./images/slide_27_img_59f517a6.png" alt="Formule de décodage de la parole : argmax P(mots | son) = argmax P(son | mots) · P(mots)" style="width:100%; height:58px; object-fit:contain;">
<img src="./images/slide_27_img_68ee27c5.png" alt="Modèles de mots avec variation dialectale et coarticulation (transitions entre phones)" style="width:100%; height:58px; object-fit:contain;">
</div>

---
layout: section
---

# VI. Modèles neuronaux

De RNN à Transformers

---
layout: default
---

# 28. Modèles profonds

**Réseaux récurrents (RNN)** : mémoire interne = contexte.

- **seq2seq** : encodeur / décodeur
- Couches **LSTM** (longue mémoire)
- **Attention** : focus dynamique sur la séquence source

**Tâches** : traduction, sous-titrage, Q&A, génération de texte.

**Transformers** (2017) : self-attention multi-têtes, parallélisable, fondation des
LLM modernes.

> Cette migration historique s'arrête à 2018. Pour les architectures
> post-2018 (BERT, GPT, T5, etc.), voir `GenAI/Texte/10*` et `GenAI/Texte/13*`
> du dépôt.

<div style="display:grid; grid-template-columns:repeat(4,1fr); gap:6px; align-items:center;">
<img src="./images/slide_28_img_2aa4b968.png" alt="Modèle sémantique convolutif latent (CLSM) : couche de n-grammes, couche de trigrammes de lettres, convolution, max-pooling et matrice sémantique" style="width:100%; height:56px; object-fit:contain;">
<img src="./images/slide_28_img_461e72ef.png" alt="Exemples de documents retournés par le modèle CLSM (requête et titre du document le mieux classé)" style="width:100%; height:56px; object-fit:contain;">
<img src="./images/slide_28_img_4b6f2b7a.png" alt="Traduction neuronale avec attention : encodeur et décodeur alignant les mots source et cible (hallo geht wie dir es / hello how are you)" style="width:100%; height:56px; object-fit:contain;">
<img src="./images/slide_28_img_6219fefe.png" alt="Schéma many to many des architectures de traduction neuronale (117 × 199 px)" style="width:100%; height:56px; object-fit:contain;">
</div>

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

**Voir** : `GenAI/Plateformes-Conversationnelles/*` pour les notebooks modernes
(open-webUI, Qwen, etc.).

<div style="display:grid; grid-template-columns:repeat(2,1fr); gap:6px; align-items:center;">
<img src="./images/slide_29_img_0094ef69.png" alt="Architecture Microsoft Bot Framework : code du bot, Bot Connector Service, canaux (Web Chat, Skype, Slack, Telegram) et Cognitive Services" style="width:100%; height:74px; object-fit:contain;">
<img src="./images/slide_29_img_95c7e198.png" alt="Interface d'étiquetage d'intentions et d'entités : énoncé de réservation, intention Book Holiday(1), entité Colleague" style="width:100%; height:74px; object-fit:contain;">
</div>

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

| Concept historique | Notebook moderne |
|---|---|
| n-grammes, modèles de langue | `GenAI/Texte/23_TAL_Du_Mot_Aux_Dependances.ipynb` |
| HMM, Viterbi | `Probas/Infer/*` |
| Automates finis, transducteurs | `Search/Z3/Sudoku/Lean` |
| CRF, structured prediction | `Probas/Infer/*` |
| Parsing CFG/PCFG | `SymbolicAI/Lean` |
| Sémantique | `SymbolicAI/SemanticWeb` |
| RNN, LSTM, seq2seq, attention | `GenAI/Texte/10*` |
| Transformers, LLMs | `GenAI/Texte/11*`, `13*` |
| Bots conversationnels | `GenAI/Plateformes-Conversationnelles/*` |

---

# 33. Projets étudiants suggérés (héritage 2018)

**Conception de bots de service pour réseaux sociaux** :

- Chat Bots, AIML, Reddit et agents de service, NLP, RDF, APIs

**Modèle d'inférence pour analyse de sentiment** :

- Probabilités, Infer.NET, expérimental, Reddit

**Stratégies d'entraînement pour trading crypto** :

- Bitcoin, DN/Encog, machine learning

> Ces projets sont **historiques** (2018). Pour les projets modernes équivalents,
> voir le syllabus courant (`MyIA.AI.Notebooks/GradeBookApp/`).

---

# 34. Merci

**Jean-Sylvain Boige**
jsboige@myia.org

> Migration pédagogique : 34 slides TAL historiques → Slidev FR classique →
> moderne. Aucun arc perdu silencieusement, chaque concept pointe vers un
> owner exécutable du dépôt.
