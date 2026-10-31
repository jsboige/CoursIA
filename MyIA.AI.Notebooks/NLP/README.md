# NLP — Traitement automatique des langues

Série dédiée aux **fondations du traitement automatique des langues** : du modèle symbolique et probabiliste classique (mots, morphologie, dépendances, n-grammes, CRF, grammaires probabilistes) jusqu'aux témoins modernes. Elle est distincte de la série [`GenAI/Texte`](../GenAI/Texte/README.md), centrée sur l'ingénierie des LLM (prompts, RAG, fine-tuning, scaling au moment du test) — les deux traditions se citent mutuellement.

Point d'entrée transversal : le deck Slidev [`slides/09-traitement-automatique-langues/`](../../slides/09-traitement-automatique-langues/slides.md) (progression classique → moderne, carte des notebooks du dépôt par sujet).

Origine : EPIC [#16271](https://github.com/jsboige/CoursIA/issues/16271) — migration des notebooks TAL depuis `GenAI/Texte` vers une série à owner propre.

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire** un pipeline linguistique de bout en bout (tokenisation → lemmes → POS → dépendances → NER) et mesurer ses erreurs contre un gold
2. **Estimer** un modèle de langue n-gramme par MLE puis par lissage (Laplace add-1, Kneser-Ney), et tracer la courbe de perplexité en fonction de n
3. **Implémenter** un CRF linéaire from scratch (forward/backward log-space, gradient, Viterbi) et vérifier l'écart nul avec `sklearn-crfsuite`
4. **Convertir** une CFG en CNF puis appliquer l'algorithme CYK avec backpointers, et mesurer l'ambiguïté sur des phrases de référence
5. **Décoder** par Viterbi un HMM markovien, mesurer le renversement de décision par rapport à un classifieur token par token, et confronter à `hmmlearn`/`nltk`
6. **Représenter** un mot comme un vecteur (07) : la représentation distributionnelle par co-occurrence, PPMI et SVD tronquée — séparer le signal d'association du bruit de fréquence, et mesurer la similarité de sens par cosinus
7. **Décomposer** un mot en n-grammes de caractères (subwords) pour généraliser aux mots inconnus (OOV), et mesurer l'écart de robustesse par rapport à une représentation de mot atomique

## Notebooks

| # | Notebook | Description | Durée |
|---|----------|-------------|-------|
| 01 | [`01_TAL_Du_Mot_Aux_Dependances.ipynb`](01_TAL_Du_Mot_Aux_Dependances.ipynb) | Pipeline **spaCy** `fr_core_news_sm` (CPU) : lemmes/POS/morphologie, arcs de dépendance + tripleaux SVO (displacy), NER avec rendu surligné, comparaison mots/lemmes/BPE sur le corpus exact du NB-04 (`GenAI/RAG-et-Memoire-Semantique`), analyse d'erreurs contre gold (lemmes 8/8, NER 2/5 : dates manquées, ORG/PER instables), recherche lemmatisée vs surface | 60 min |
| 02 | [`02_NGrammes_Modeles_De_Langue.ipynb`](02_NGrammes_Modeles_De_Langue.ipynb) | **Modèles de langue n-grammes from scratch** (CPU) : unigramme/bigramme/trigramme MLE, perplexité, explosion des zéros, lissage **Laplace add-1**, **Kneser-Ney interpolé**, courbe perplexité vs n sur corpus borné, 3 exercices C.1 | 45 min |
| 03 | [`03_CRF_Etiquetage_Sequentiel.ipynb`](03_CRF_Etiquetage_Sequentiel.ipynb) | **CRF linéaire from scratch** sur corpus NER français BIO : émissions, transitions, log-partition forward/backward, NLL et Viterbi ; gradient vérifié numériquement, baseline token-wise, témoin `sklearn-crfsuite`, métriques token/entité, ablation et analyse d'erreurs | 75 min |
| 04 | [`04_PCFG_CYK_Parsing.ipynb`](04_PCFG_CYK_Parsing.ipynb) | **Parsing PCFG/CYK from scratch** (CPU) : CFG française explicite convertie en CNF bornée avec préservation des probabilités, recognizer CYK en table triangulaire visualisée, probabilités MLE sur mini-treebank embarqué (biais d'attachement mesuré), Viterbi + backpointers avec reconstruction de l'arbre, ambiguïté mesurée (2 dérivations, 89,7 %/10,3 %), témoin **NLTK** en concordance exacte, 3 exercices C.1 | 55 min |
| 05 | [`05-HMM-Viterbi.ipynb`](05-HMM-Viterbi.ipynb) | **HMM et décodage Viterbi from scratch** (CPU) : corpus POS français miniature **synthétique à provenance explicite** (5 mots ambigus NOM/VER, 3 clitiques DET/PRON, phrase à double lecture *le matelot voile la voile*), estimation MLE + lissage add-1 avec `<UNK>`, forward log-espace, Viterbi/backpointers avec treillis visualisé, **17 renversements mesurés** du contexte de séquence (12 vers l'or, accuracy 0,717 → 0,887), baseline majoritaire par mot, témoin **hmmlearn** en concordance exacte (7·10⁻¹⁵ sur le forward, 0 divergence de chemin), contre-témoin **NLTK** sans lissage (0,491 — ce que le add-1 achète), 3 exercices C.1 | 55 min |
| 06 | [`06-Recherche-Information-TFIDF-BM25.ipynb`](06-Recherche-Information-TFIDF-BM25.ipynb) | **Recherche d'information from scratch** (CPU) : bag-of-words et classement brut par fréquence, **TF-IDF** (`idf = log(N/df)`) et **BM25** de Robertson (saturation du terme `k1`, normalisation de longueur `b`) ; corpus embarqué de 8 documents à terme omniprésent, **`Recall@3` mesuré** sur 3 requêtes étiquetées — le terme omniprésent est le discriminateur (classement brut 0,889 vs TF-IDF = BM25 = 1,000), 3 exercices C.1 | 45 min |
| 07 | [`07-Vecteurs-de-Mots-Coocc-PPMI-SVD.ipynb`](07-Vecteurs-de-Mots-Coocc-PPMI-SVD.ipynb) | **Vecteurs de mots from scratch** (CPU) : matrice de co-occurrence (fenêtre ±3) sur corpus embarqué de 13 phrases / 3 domaines, **PPMI** (correction par l'attente au hasard, `max(0, log(coo·N/(row·col)))`), **SVD tronquée** (centrage + 2 premières valeurs singulières) ; **séparation des domaines mesurée** — écart de cosinus congener/autre-domaine ≈ 1,24–1,74 après PPMI+SVD contre ≈ 0,07–0,24 au comptage brut, 3 exercices C.1 | 45 min |
| 09 | [`09-FastText-Subword-Vectors.ipynb`](09-FastText-Subword-Vectors.ipynb) | **fastText from scratch** (CPU) : la même mécanique skip-gram que le carnet 08, mais l'entrée d'un mot est la somme des vecteurs de ses n-grammes de caractères (subwords) — gradient analytique vérifié numériquement, et la capacité distinctive mesurée : 4/4 dérivés jamais vus (OOV) replacés près de leur radical (le repli est morphologique, mesuré avec un contrôle sans radical qui retombe dans le bruit), là où word2vec n'a aucun vecteur ; confrontation 08 vs 09, 3 exercices C.1 | 45 min |
| 10 | [`10-Classement-Texte-NaiveBayes-FromScratch.ipynb`](10-Classement-Texte-NaiveBayes-FromScratch.ipynb) | **Classification de texte Naive Bayes from scratch** (CPU) : sac-de-mots, priors de classe + probabilités de mot par **MLE + lissage Laplace** en log-espace ; corpus embarqué de 32 documents (4 catégories × 8), **précision out-of-sample mesurée** 7/8, **cross-check `sklearn`** (`CountVectorizer` + `MultinomialNB`) sur le même split — précision identique 7/8 et **accord 8/8** des prédictions, mesure du lissage α (sans lissage : 3 documents indéterminés, 4 corrects, 1 mal classé (`finance` → `science`), soit 4/8 = 50 % ; précision 87,5 % pour α > 0, sur 8 documents), 3 exercices C.1 | 45 min |
| 11 | [`11-Classement-Texte-RegressionLogistique-FromScratch.ipynb`](11-Classement-Texte-RegressionLogistique-FromScratch.ipynb) | **Classification de texte discriminative from scratch** (CPU) : sac de mots en fréquences relatives, **softmax stable**, entropie croisée et descente de gradient sous forme fermée `(P − Y)/n` ; banc à classes **chevauchantes** (240 documents, 31,2 % ambigus) pour que la tâche ne se résolve pas d'elle-même ; **75,00 % de précision hors échantillon** contre **21,88 %** de baseline majoritaire, cross-check `scikit-learn` en juge extérieur (même précision, accord des prédictions 81,25 %, cosinus des poids 0,7419) ; le balayage de `lambda` mesure que **L2 dégrade** ici, conséquence rapportée et expliquée plutôt que masquée, 3 exercices C.1 | 45 min |

## Progression

1. **Le mot et ses dépendances** (01) : le pipeline linguistique observé — lemmes, morphosyntaxe, entités — avec analyse d'erreurs mesurée.
2. **La phrase et sa probabilité** (02) : le modèle de langue n-gramme, du MLE au lissage — la tradition probabiliste avant les réseaux.
3. **La séquence et ses étiquettes** (03) : la structured prediction par CRF linéaire — du local au global par la log-partition.
4. **La syntaxe et ses arbres** (04) : grammaires probabilistes et parsing CYK — l'ambiguïté quantifiée, la dérivation la plus probable.
5. **La chaîne d'états cachés** (05) : le HMM génératif et le décodage de Viterbi — le contexte de séquence qui renverse la décision, pont historique du n-gramme (02) vers le CRF discriminatif (03).
6. **La question inversée** (06) : TF-IDF et BM25 — de « quelle est la probabilité de ce texte ? » à « quel document répond à cette requête ? », la pondération par rareté qui fait tomber le terme omniprésent.
7. **Le mot comme un vecteur** (07) : la représentation distributionnelle par co-occurrence, PPMI et SVD tronquée — séparer le signal d'association du bruit de fréquence, et rendre la similarité de sens mesurable par cosinus.
8. **Le mot et ses subwords** (09) : fastText — la représentation d'entrée passe du mot atomique à la somme des n-grammes de caractères, et la généralisation aux mots inconnus (OOV) devient mesurable.
9. **La frontière apprise** (11) : la régression logistique discriminative — softmax et entropie croisée en numpy pur, la précision hors échantillon mesurée contre une baseline, et une régularisation qui, sur ce banc précis, dégrade au lieu d'améliorer.

## Prérequis

- Python 3.10+ (les notebooks de la série sont **CPU-only**)
- `spaCy` + modèle `fr_core_news_sm` (notebook 01)
- `sklearn-crfsuite` (témoin du notebook 03), `nltk` (témoin des notebooks 04 et 05), `hmmlearn` (témoin du notebook 05)
- Aucune clé API requise
