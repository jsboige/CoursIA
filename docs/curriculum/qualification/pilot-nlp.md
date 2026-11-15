# Série pilote `NLP` — qualification complète

Onze carnets, onze valeurs justifiées. La série `MyIA.AI.Notebooks/NLP` a été
choisie comme pilote parce qu'elle est **assez petite pour être qualifiée
valeur par valeur** (onze carnets) et **assez large pour couvrir l'étendue**
des deux axes : du `D2` au `D4`, du `R1` au `R2`.

Toutes les mesures vivent dans [manifest.json](manifest.json) et y sont
**relues sur l'arbre** par l'organe (`--check` / `--refresh`) ; aucune n'est
écrite à la main. Ce document porte le jugement (pourquoi cette difficulté,
pourquoi cette dimension recherche) et renvoie au manifeste pour les nombres.

## Vue d'ensemble

| Carnet | Difficulte | Recherche | P | O | A | Kernel |
|---|---|---|---|---|---|---|
| 01_TAL_Du_Mot_Aux_Dependances.ipynb | **D2** | R1 | 1 | 3 | 2 | Python 3 (coursia-ml-training) |
| 02_NGrammes_Modeles_De_Langue.ipynb | **D2** | R1 | 2 | 3 | 2 | coursia-ml-training |
| 03_CRF_Etiquetage_Sequentiel.ipynb | **D3** | R2 | 3 | 2 | 3 | Python 3 (ipykernel) |
| 04_PCFG_CYK_Parsing.ipynb | **D3** | R1 | 3 | 2 | 3 | Python 3 (coursia-ml-training) |
| 05-HMM-Viterbi.ipynb | **D3** | R2 | 2 | 2 | 3 | Python 3 (ipykernel) |
| 06-Recherche-Information-TFIDF-BM25.ipynb | **D2** | R1 | 1 | 1 | 2 | Python 3 |
| 07-Vecteurs-de-Mots-Coocc-PPMI-SVD.ipynb | **D2** | R1 | 2 | 1 | 2 | Python 3 |
| 08-Word2Vec-CBOW-SkipGram.ipynb | **D3** | R2 | 2 | 1 | 3 | Python 3 |
| 09-FastText-Subword-Vectors.ipynb | **D3** | R2 | 2 | 1 | 3 | Python 3 |
| 10-Classement-Texte-NaiveBayes-FromScratch.ipynb | **D2** | R1 | 2 | 2 | 2 | Python 3 |
| 11-Classement-Texte-RegressionLogistique-FromScratch.ipynb | **D4** | R2 | 3 | 2 | 4 | Python3 |

## Ce que la série montre

- **Aucun `D1`** : les onze carnets demandent au moins une adaptation et une
  vérification chiffrée. Un `D1` existe dans l'échelle, il n'a pas de
  représentant ici — c'est un fait mesuré, pas un trou de la grille.
- **Aucun `R3`** : la série enseigne des techniques établies. Son composant
  « recherche » est de l'outillage (`R1`, six carnets) et de l'exploration
  contrôlée (`R2`, cinq carnets), pas du front.
- **Aucun carnet ne réclame d'API, de GPU, de cloud ni de WSL** : la série est
  CPU-only et hors-ligne. Deux carnets demandent en revanche un téléchargement
  à la charge de l'étudiant — le modèle spaCy `fr_core_news_sm` (01) et les
  données `punkt`/`punkt_tab` de NLTK (02) — c'est ce que note le critère
  d'outillage `O3`.
- **Aucune densité sous le plancher** : le carnet 09, seul à y être, a été
  enrichi (#24930) et repasse au-dessus du plancher de densité.

## Les onze qualifications

### 01_TAL_Du_Mot_Aux_Dependances.ipynb

**D2 · R1** — prérequis 1, outillage 3, autonomie 2

Prérequis : aucun hors Python — le carnet est auto-contenu (P1). Outillage : spaCy + modèle français `fr_core_news_sm` téléchargé par l'étudiant, dont il doit lire les sorties (MORPH, ents, arcs) (O3). Autonomie : les trois exercices sont des analyses sur le corpus (lemme le plus polymorphe, sujets elliptiques, recherche par étiquette), pas des implémentations (A2). Niveau D2 = max(1, 2). Recherche R1 : le §7 « Analyse d'erreurs — mesurer contre un jeu d'or » construit un protocole d'évaluation annoté, réutilisable ; aucune question ouverte n'est posée.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3 (coursia-ml-training)` · exigences api=False gpu=False cloud=False wsl=False

### 02_NGrammes_Modeles_De_Langue.ipynb

**D2 · R1** — prérequis 2, outillage 3, autonomie 2

Prérequis : notions de probabilité (MLE, perplexité, lissage) — niveau licence (P2). Outillage : NLTK (`punkt`, `punkt_tab` téléchargés par l'étudiant) (O3). Autonomie : les exercices étendent le vocabulaire, comparent add-k et add-1, complètent la courbe de perplexité — adaptation de formule et vérification, pas d'implémentation complète (A2). Niveau D2 = max(2, 2). Recherche R1 : le §7 « Courbe de perplexité vs n » est un instrument de choix reproductible ; le verdict sur le lissage est connu d'avance, ce n'est pas une exploration.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `coursia-ml-training` · exigences api=False gpu=False cloud=False wsl=False

### 03_CRF_Etiquetage_Sequentiel.ipynb

**D3 · R2** — prérequis 3, outillage 2, autonomie 3

Prérequis : le carnet déclare « Python 3.10+, NumPy, scikit-learn » et un prérequis hors série (TAL/entités nommées) ; le formalisme CRF, le forward-backward et la descente de gradient sont hors du programme de la série (P3). Outillage : sklearn-crfsuite et seqeval comme témoins, API à maîtriser (O2). Autonomie : le CRF linéaire de zéro (scores, forward/backward, Viterbi, NLL, gradient) est à implémenter et vérifié numériquement (A3). Niveau D3 = max(3, 3). Recherche R2 : le §8 « Ablation mesurée — quelle famille de caractéristiques porte le CRF ? » pose une question falsifiable dont le verdict n'est pas connu d'avance, et le témoin §7 (sklearn-crfsuite) fournit l'étalon externe.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3 (ipykernel)` · exigences api=False gpu=False cloud=False wsl=False

### 04_PCFG_CYK_Parsing.ipynb

**D3 · R1** — prérequis 3, outillage 2, autonomie 3

Prérequis : grammaires formelles, forme normale de Chomsky, PCFG et treebank — formalisme hors série, non enseigné ailleurs dans le corpus (P3). Outillage : NLTK (`PCFG`, `ChartParser`) comme témoin de concordance (O2). Autonomie : le recognizer CYK en programmation dynamique, puis Viterbi et inside, sont à implémenter (A3). Niveau D3 = max(3, 3). Recherche R1 : le §6 « Ambiguïté mesurée » et le §7 « Témoin NLTK » forment un instrument de vérification, mais la concordance attendue est connue d'avance — ce n'est pas une exploration, c'est un contrôle.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3 (coursia-ml-training)` · exigences api=False gpu=False cloud=False wsl=False

### 05-HMM-Viterbi.ipynb

**D3 · R2** — prérequis 2, outillage 2, autonomie 3

Prérequis : le carnet déclare explicitement « avoir parcouru 02 (MLE, lissage, perplexité) » ; le HMM et le décodage de Viterbi y sont enseignés (P2). Outillage : hmmlearn et NLTK exécutés comme deux témoins (O2). Autonomie : forward en log-espace et Viterbi avec backpointers sont à implémenter (A3). Niveau D3 = max(2, 3). Recherche R2 : le §5 « Le cas non dégénéré — là où le contexte renverse la décision » pose une question falsifiable (le contexte change-t-il vraiment la décision ?) et la mesure ; le §6 fixe le plancher à battre, le §9 analyse les six tokens qui résistent.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3 (ipykernel)` · exigences api=False gpu=False cloud=False wsl=False

### 06-Recherche-Information-TFIDF-BM25.ipynb

**D2 · R1** — prérequis 1, outillage 1, autonomie 2

Prérequis : aucun hors Python/NumPy — le carnet construit TF-IDF et BM25 devant le lecteur sur un corpus auto-contenu de huit documents (P1). Outillage : aucun outil du domaine ; NumPy et matplotlib seuls (O1). Autonomie : les exercices réimplémentent l'idf, la contribution BM25 d'un terme et le Recall@k — adaptation de formules données, avec vérification chiffrée (A2). Niveau D2 = max(1, 2). Recherche R1 : le §4 « Classer, puis mesurer la qualité » construit un jeu de requêtes annotées et une métrique (Recall@3) réutilisables ; le verdict sur BM25 vs TF-IDF est connu d'avance.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3` · exigences api=False gpu=False cloud=False wsl=False

### 07-Vecteurs-de-Mots-Coocc-PPMI-SVD.ipynb

**D2 · R1** — prérequis 2, outillage 1, autonomie 2

Prérequis : algèbre linéaire (SVD, cosinus) et probabilités (PPMI) — notions de licence, non enseignées ailleurs dans la série (P2). Outillage : aucun outil du domaine ; NumPy seul (O1). Autonomie : les exercices portent sur la co-occurrence, la valeur de PPMI et les plus proches voisins — adaptation, pas d'algorithme à réécrire (A2). Niveau D2 = max(2, 2). Recherche R1 : le §5 « Mesurer le gain » pose le test décisif (écart entre cosinus congénère et cosinus d'un autre domaine). Le carnet 08 confronte ses vecteurs appris à l'espace SVD du carnet 07, et le carnet 09 confronte à 08 ; aucun des deux ne rejoue ce test congénère contre un autre domaine — l'instrument discriminant reste propre au carnet 07.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3` · exigences api=False gpu=False cloud=False wsl=False

### 08-Word2Vec-CBOW-SkipGram.ipynb

**D3 · R2** — prérequis 2, outillage 1, autonomie 3

Prérequis : le §7 confronte directement au carnet 07 (statistique) ; descente de gradient, softmax et échantillonnage négatif sont des notions de licence (P2). Outillage : aucun outil du domaine ; NumPy seul (O1). Autonomie : CBOW et skip-gram sont écrits de zéro, y compris la perte, le gradient et l'échantillonnage négatif (A3). Niveau D3 = max(2, 3). Recherche R2 : le §5 « Les vecteurs ont-ils une structure ? » est une question de mesure falsifiable (similarité cosinus), et le §7 la confrontation paire par paire avec l'espace SVD du carnet 07 ; le verdict n'est pas connu d'avance.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3` · exigences api=False gpu=False cloud=False wsl=False

### 09-FastText-Subword-Vectors.ipynb

**D3 · R2** — prérequis 2, outillage 1, autonomie 3

Prérequis : dépend du carnet 08 (word2vec), dont il reprend le modèle et le protocole ; la décomposition en sous-mots est une notion nouvelle (P2). Outillage : aucun outil du domaine ; NumPy seul (O1). Autonomie : le modèle fastText (table de sous-mots, somme, gradient) est écrit de zéro (A3). Niveau D3 = max(2, 3). Recherche R2 : le §4 « La capacité distinctive : généraliser aux mots OOV » et le §5 « Confrontation 08 vs 09 » posent la question falsifiable de la généralisation OOV ; le verdict (word2vec n'a aucun vecteur, fastText replacé) est mesuré, non supposé.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3` · exigences api=False gpu=False cloud=False wsl=False

### 10-Classement-Texte-NaiveBayes-FromScratch.ipynb

**D2 · R1** — prérequis 2, outillage 2, autonomie 2

Prérequis : probabilités — Bayes, MLE, espace log, lissage — notions de licence (P2). Outillage : scikit-learn (`CountVectorizer`, `MultinomialNB`) comme témoin, plus `token_pattern` à aligner explicitement (O2). Autonomie : l'implémentation est donnée ; les exercices demandent une variante (Bernoulli présence/absence, avec le dénominateur à changer), une explication de prédiction et un traitement des mots vides — adaptation et vérification (A2). Niveau D2 = max(2, 2). Recherche R1 : le §3 « Cross-check SOTA » et le §4 « l'effet de α, mesuré » sont des instruments de mesure réutilisables ; le carnet signale lui-même que sa résolution de 12,5 points ne permet pas de distinguer un plateau, ce qui en fait un contrôle et non une exploration.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3` · exigences api=False gpu=False cloud=False wsl=False

### 11-Classement-Texte-RegressionLogistique-FromScratch.ipynb

**D4 · R2** — prérequis 3, outillage 2, autonomie 4

Prérequis : le carnet se place explicitement après 10 et suppose optimisations convexe, entropie croisée et régularisation L2 — hors série (P3). Outillage : scikit-learn n'intervient que comme « juge extérieur » (O2). Autonomie : l'étudiant doit construire un banc dont le verdict n'est pas connu d'avance — le §1 montre que le corpus du carnet 10 est « un plafond », le §5 constate que « l'attendu n'est pas reproduit », et les trois exercices, « Chacun se juge sur une mesure, pas sur une impression » (A4). Niveau D4 = max(3, 4). Recherche R2 : la question « que fait la régularisation, et que ne fait-elle pas ? » est posée puis mesurée sur un banc construit pour l'occasion ; le carnet rapporte un résultat qui contredit l'attente théorique. Ce n'est pas du front (R3) : la question est tranchée à l'intérieur du carnet.

Mesures : [manifest.json](manifest.json) porte les compteurs du carnet (exercices, cellules, prose, densité) · kernel `Python 3` · exigences api=False gpu=False cloud=False wsl=False

## Ce qui reste à faire sur cette série

| Geste | Nature |
|---|---|
| Étendre la qualification aux autres séries | grain à faire ; le manifeste accepte une série par entrée |
| Crocher le générateur sur les deux champs | suite de #24994 (le fichier `generate_catalog.py` est claimé par une autre lane) |

## Voir aussi

- [echelle-difficulte.md](echelle-difficulte.md) — l'échelle et ses critères.
- [dimension-recherche.md](dimension-recherche.md) — l'axe recherche.
- [manifest.json](manifest.json) — la donnée, une justification par carnet.
- [README.md](README.md) — l'organisation du répertoire et l'organe.
