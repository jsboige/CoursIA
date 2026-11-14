# NLP — du mot aux modèles du langage

[↑ Parcours de notebooks](../README.md) · [GenAI/Texte](../GenAI/Texte/README.md)

Comment transformer un texte en objets que l'on peut analyser, comparer ou classer ? Cette série de traitement automatique des langues part des mots, des étiquettes grammaticales et des dépendances. Elle construit ensuite des modèles probabilistes de séquences, des représentations vectorielles et des classifieurs. Les petits corpus permettent de suivre les calculs et d'examiner les erreurs au niveau d'une phrase ou d'une prédiction.

Le parcours s'adresse aux étudiants et enseignants connaissant Python et les probabilités élémentaires. Le calcul matriciel et les gradients deviennent utiles pour les représentations et les modèles appris ; les carnets en explicitent les opérations. Les expériences fonctionnent sur CPU, sans clé d'API. Le [support de cours TAL](../../slides/09-traitement-automatique-langues/slides.md) situe ces fondations dans le passage aux modèles de langage modernes.

**Une série plate.** Tous les carnets vivent à la racine, sans dossier intermédiaire : ils tracent un seul arc du mot aux modèles de langage, la numérotation continue ordonne la progression, et les approfondissements vivent dans les carnets eux-mêmes plutôt que dans des compagnons séparés. C'est un choix de niveau déclaré (règle 2 de [niveau-serie.md](../../docs/reference/niveau-serie.md)), pas un oubli.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) permet de choisir sa profondeur de lecture.

- **Vous découvrez** : suivez les numéros nus. Le premier carnet donne des observations linguistiques concrètes ; les suivants construisent les modèles qui permettent de les interpréter.
- **Vous creusez un palier** : reprenez ses exercices, ses contrôles de calcul et ses comparaisons avec une bibliothèque. Les approfondissements de ce parcours sont dans les carnets eux-mêmes.
- **Vous cherchez des prolongements** : « Pour aller plus loin » précise ce que permettent les expériences et donne les points de passage vers tokenisation, recherche documentaire et LLM.

À l'issue du parcours, vous pourrez analyser les sorties d'un pipeline linguistique, construire un modèle de séquence ou de classification, comparer des représentations de mots et concevoir une évaluation qui distingue calcul correct et généralisation.

## Parcours principal — Découverte et Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Du mot aux dépendances](01_TAL_Du_Mot_Aux_Dependances.ipynb) | Observer tokens, lemmes, catégories grammaticales, dépendances et entités avec spaCy ; examiner leurs erreurs sur de courts textes français. | Découverte ; Python. | Comparer mots, lemmes et unités de tokenisation. |
| 02 | [N-grammes et modèles de langue](02_NGrammes_Modeles_De_Langue.ipynb) | Estimer les probabilités de suites de mots, comprendre les probabilités nulles et comparer les lissages par la perplexité. | Licence ; probabilités conditionnelles. | Distinguer perplexité d'entraînement et de test. |
| 03 | [CRF et étiquetage séquentiel](03_CRF_Etiquetage_Sequentiel.ipynb) | Apprendre conjointement les étiquettes d'une séquence ; calculer la normalisation et décoder avec Viterbi. | Licence ; étiquettes de 01, probabilités et gradients. | Contrôle numérique du gradient, ablation et comparaison à CRFsuite. |
| 04 | [Grammaires probabilistes et CYK](04_PCFG_CYK_Parsing.ipynb) | Convertir une grammaire en forme normale de Chomsky, reconstruire un arbre syntaxique et quantifier une ambiguïté. | Licence ; grammaires et programmation dynamique. | Comparaison à NLTK et effet des règles non observées. |
| 05 | [HMM et Viterbi](05-HMM-Viterbi.ipynb) · [C#](05-HMM-Viterbi-CSharp.ipynb) | Modéliser des étiquettes cachées et leurs observations ; voir comment le contexte change une décision locale. | Licence ; probabilités de 02 et décodage de séquences. | Comparer des implémentations à paramètres identiques. |
| 06 | [Recherche d'information : TF-IDF et BM25](06-Recherche-Information-TFIDF-BM25.ipynb) · [C#](06-Recherche-Information-TFIDF-BM25-CSharp.ipynb) | Classer des documents pour une requête en pondérant rareté des termes, répétition et longueur. | Licence ; fréquences et logarithmes. | Interpréter la mesure de rappel choisie. |
| 07 | [Cooccurrences, PPMI et SVD](07-Vecteurs-de-Mots-Coocc-PPMI-SVD.ipynb) | Construire des vecteurs de mots à partir de leurs contextes, corriger l'effet des fréquences et réduire la dimension. | Licence ; matrices et produit scalaire. | Passage aux vecteurs appris en 08. |
| 08 | [Word2vec : CBOW et skip-gram](08-Word2Vec-CBOW-SkipGram.ipynb) | Apprendre des vecteurs par prédiction du contexte ; entraîner CBOW et comprendre le coût de l'échantillonnage négatif. | Licence ; après 07, dérivation et gradient. | Entraînement de skip-gram proposé en exercice. |
| 09 | [FastText et sous-mots](09-FastText-Subword-Vectors.ipynb) | Composer un vecteur à partir de fragments de caractères pour représenter un mot absent de l'entraînement. | Licence ; après 08. | Distinguer régularité morphologique et proximité de sens. |
| 10 | [Classification Naive Bayes](10-Classement-Texte-NaiveBayes-FromScratch.ipynb) | Classer un document à partir des probabilités de ses mots ; mesurer l'effet du lissage et vérifier les prédictions avec scikit-learn. | Licence ; estimation et lissage de 02. | Contrôler la séparation entraînement/test. |
| 11 | [Classification par régression logistique](11-Classement-Texte-RegressionLogistique-FromScratch.ipynb) | Apprendre directement une frontière de décision avec softmax et entropie croisée ; tester la régularisation. | Licence ; après 10, matrices et gradient. | Comparer précision, prédictions et paramètres séparément. |

### Le fil du parcours — Licence

Le premier changement de perspective est celui du **contexte**. Une étiquette attribuée mot par mot peut être plausible localement et incohérente dans la phrase. Les CRF de 03 et les HMM de 05 ([Python](05-HMM-Viterbi.ipynb) · [C#](05-HMM-Viterbi-CSharp.ipynb)) modélisent des relations entre étiquettes ; le jumeau C# utilise Python.NET pour les témoins hmmlearn et NLTK ; CYK, en 04, représente plutôt une structure d'arbre. Le HMM fournit aussi une relecture générative du problème traité par le CRF discriminatif : on peut revenir de 05 à 03 pour comparer les hypothèses.

Le second changement porte sur la **représentation**. Une fréquence brute favorise les mots omniprésents, souvent peu utiles à une recherche. TF-IDF et BM25 corrigent cette pondération en 06. Les cooccurrences de 07 font du contexte un vecteur ; 08 apprend ces vecteurs par optimisation ; 09 partage des fragments entre mots pour traiter des formes jamais vues. Une proximité calculée peut ainsi venir d'un contexte commun ou d'une ressemblance morphologique : le contrôle choisi doit permettre de les distinguer.

Enfin, 10 et 11 relient représentation et décision. Naive Bayes ([Python](10-Classement-Texte-NaiveBayes-FromScratch.ipynb) · [C#](10-Classement-Texte-NaiveBayes-FromScratch-CSharp.ipynb)) estime un modèle des mots dans chaque classe ; la régression logistique apprend directement les probabilités des classes. Le jumeau C# appelle le témoin scikit-learn via Python.NET. Les implémentations explicites et leurs témoins de bibliothèque permettent d'examiner la vraisemblance, le lissage, l'optimisation et les erreurs sans les confondre.

## Approfondissements — Licence

Les exercices prolongent chaque palier : modifier le lissage ou le vocabulaire de 02, contrôler les gradients et les transitions de 03, explorer l'ambiguïté de 04, puis comparer les décodages de 05. Dans l'arc vectoriel, 08 définit la perte et le gradient de skip-gram ; son entraînement et sa vérification sont laissés à l'exercice. Le passage à 09 demande de comprendre cette représentation et la somme des vecteurs de sous-mots.

Pour l'évaluation, reprendre les mêmes données et les mêmes paramètres est essentiel. Le témoin `hmmlearn` de 05 utilise les paramètres du modèle étudié ; le témoin NLTK n'utilise pas le même lissage. Leur comparaison ne répond donc pas à la même question. En 11, une même précision finale ne signifie pas que les modèles prédisent la même classe pour chaque document.

## Installation — Découverte et pratique

Créer un environnement Python 3.10 ou ultérieur et le sélectionner comme noyau du notebook. Les besoins dépendent du palier :

| Usage | Dépendances |
|---|---|
| Calculs et figures | `numpy`, `pandas`, `matplotlib`, IPython/Jupyter |
| Pipeline français de 01 | `spacy` et modèle `fr_core_news_sm` |
| Probabilités et grammaires | `nltk` pour 02, 04 et 05 ; `hmmlearn` pour le témoin de 05 |
| Étiquetage de 03 | `scikit-learn`, `sklearn-crfsuite`, `seqeval` |
| Classification de 10–11 | `scikit-learn` |

Installer le modèle français dans l'environnement du noyau avec `python -m spacy download fr_core_news_sm`. Commencer par [01](01_TAL_Du_Mot_Aux_Dependances.ipynb), lire les annotations d'une phrase, puis comparer aux annotations attendues. Les téléchargements de paquets et du modèle nécessitent un accès réseau ; les expériences linguistiques utilisent ensuite les corpus embarqués.

## Pour aller plus loin — Recherche

### Lire une expérience au bon niveau

Les petits corpus servent à isoler un mécanisme. En 02, le lissage évite des probabilités nulles, mais Kneser–Ney n'obtient pas une meilleure perplexité de test que Laplace sur le corpus affiché. La diminution de perplexité à l'entraînement ne suffit pas à choisir un modèle.

En 03, le CRF pédagogique obtient un F1 par entité de 0,947 sur le petit test, contre 1,000 pour CRFsuite. L'accord avec `seqeval` porte sur le **calcul de la métrique appliqué aux mêmes prédictions**, pas sur l'identité des prédictions de ces modèles. C'est un exemple utile de deux validations différentes : contrôler l'évaluation et comparer les systèmes.

De même, le rappel `Recall@3` de 06 mesure les documents pertinents retrouvés parmi les premiers résultats, sans distinguer leur ordre interne. La précision@k à k fixé compte les pertinents du préfixe sans départager leur ordre ; MRR et nDCG binaires ne différencient pas deux documents ayant le même grade positif. Les voisins et analogies de 07–09 sont observés sur des corpus construits ; les bons résultats sur des dérivés morphologiques ne constituent pas une évaluation sémantique générale. Les classifieurs de 10–11 montrent comment bâtir un protocole hors échantillon, avec des conclusions limitées à leurs bancs.

### Passer aux systèmes de recherche et aux LLM

La comparaison des unités textuelles de 01 se prolonge dans [RAG-04 — Tokenisation](../GenAI/RAG-et-Memoire-Semantique/04-Tokenisation-From-Scratch.ipynb). La recherche lexicale de 06 prépare [RAG-02 — Recherche avancée](../GenAI/RAG-et-Memoire-Semantique/02-Retrieval-Avance.ipynb), tandis que les vecteurs de 07–09 donnent des repères pour [RAG-03 — Embeddings](../GenAI/RAG-et-Memoire-Semantique/03-Embeddings-From-Scratch.ipynb).

La série [GenAI/Texte](../GenAI/Texte/README.md) étudie ensuite l'usage des LLM : prompts, génération, outils et évaluation. [Texte-22 — Évaluer le texte généré](../GenAI/Texte/22_Evaluating_Generated_Text.ipynb) prolonge la question commune de ce parcours : quelle observation autorise réellement la conclusion annoncée ?

## Ressources — tous niveaux

- [Support de cours TAL](../../slides/09-traitement-automatique-langues/slides.md) : carte des concepts classiques et modernes, avec les parcours associés.
- [spaCy](https://spacy.io/usage/linguistic-features) : annotations linguistiques utilisées en 01.
- [NLTK](https://www.nltk.org/) : grammaires et modèles probabilistes ; témoins de 04–05.
- [scikit-learn](https://scikit-learn.org/stable/) : représentations et classifieurs de référence, à comparer sur un protocole commun.
- Les références fondatrices et les détails de calcul accompagnent chaque modèle dans son carnet.

[Retour aux notebooks](../README.md) · [Catalogue du dépôt](../../COURSE_CATALOG.generated.md)
