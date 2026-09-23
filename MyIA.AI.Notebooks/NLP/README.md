# NLP — Traitement automatique des langues

Série dédiée aux **fondations du traitement automatique des langues** : du modèle symbolique et probabiliste classique (mots, morphologie, dépendances, n-grammes, CRF, grammaires probabilistes) jusqu'aux témoins modernes. Elle est distincte de la série [`GenAI/Texte`](../GenAI/Texte/README.md), centrée sur l'ingénierie des LLM (prompts, RAG, fine-tuning, scaling au moment du test) — les deux traditions se citent mutuellement.

Point d'entrée transversal : le deck Slidev [`slides/09-traitement-automatique-langues/`](../../slides/09-traitement-automatique-langues/slides.md) (progression classique → moderne, carte des notebooks du dépôt par sujet).

Origine : EPIC [#16271](https://github.com/jsboige/CoursIA/issues/16271) — migration des notebooks TAL depuis `GenAI/Texte` vers une série à owner propre.

## Notebooks

| # | Notebook | Description | Durée |
|---|----------|-------------|-------|
| 01 | [`01_TAL_Du_Mot_Aux_Dependances.ipynb`](01_TAL_Du_Mot_Aux_Dependances.ipynb) | Pipeline **spaCy** `fr_core_news_sm` (CPU) : lemmes/POS/morphologie, arcs de dépendance + tripleaux SVO (displacy), NER avec rendu surligné, comparaison mots/lemmes/BPE sur le corpus exact du NB-04 (`GenAI/RAG-et-Memoire-Semantique`), analyse d'erreurs contre gold (lemmes 8/8, NER 2/5 : dates manquées, ORG/PER instables), recherche lemmatisée vs surface | 60 min |
| 02 | [`02_NGrammes_Modeles_De_Langue.ipynb`](02_NGrammes_Modeles_De_Langue.ipynb) | **Modèles de langue n-grammes from scratch** (CPU) : unigramme/bigramme/trigramme MLE, perplexité, explosion des zéros, lissage **Laplace add-1**, **Kneser-Ney interpolé**, courbe perplexité vs n sur corpus borné, 3 exercices C.1 | 45 min |
| 03 | [`03_CRF_Etiquetage_Sequentiel.ipynb`](03_CRF_Etiquetage_Sequentiel.ipynb) | **CRF linéaire from scratch** sur corpus NER français BIO : émissions, transitions, log-partition forward/backward, NLL et Viterbi ; gradient vérifié numériquement, baseline token-wise, témoin `sklearn-crfsuite`, métriques token/entité, ablation et analyse d'erreurs | 75 min |
| 04 | [`04_PCFG_CYK_Parsing.ipynb`](04_PCFG_CYK_Parsing.ipynb) | **Parsing PCFG/CYK from scratch** (CPU) : CFG française explicite convertie en CNF bornée avec préservation des probabilités, recognizer CYK en table triangulaire visualisée, probabilités MLE sur mini-treebank embarqué (biais d'attachement mesuré), Viterbi + backpointers avec reconstruction de l'arbre, ambiguïté mesurée (2 dérivations, 89,7 %/10,3 %), témoin **NLTK** en concordance exacte, 3 exercices C.1 | 55 min |

## Progression

1. **Le mot et ses dépendances** (01) : le pipeline linguistique observé — lemmes, morphosyntaxe, entités — avec analyse d'erreurs mesurée.
2. **La phrase et sa probabilité** (02) : le modèle de langue n-gramme, du MLE au lissage — la tradition probabiliste avant les réseaux.
3. **La séquence et ses étiquettes** (03) : la structured prediction par CRF linéaire — du local au global par la log-partition.
4. **La syntaxe et ses arbres** (04) : grammaires probabilistes et parsing CYK — l'ambiguïté quantifiée, la dérivation la plus probable.

## Prérequis

- Python 3.10+ (les quatre notebooks sont **CPU-only**)
- `spaCy` + modèle `fr_core_news_sm` (notebook 01)
- `sklearn-crfsuite` (témoin du notebook 03), `nltk` (témoin du notebook 04)
- Aucune clé API requise
