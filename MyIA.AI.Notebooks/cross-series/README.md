# Projets cross-séries

Ce répertoire rassemble des **projets transversaux** qui mobilisent simultanément plusieurs séries pédagogiques du cursus (Search, GameTheory, GenAI, ML, SymbolicAI, Probas…). Là où chaque série enseigne *une* famille de techniques, un projet cross-séries montre comment **les combiner** sur une application concrète de bout en bout.

## Pourquoi des projets cross-séries ?

Les séries du cours isolent volontairement les concepts pour les rendre enseignables : on apprend la recherche dans `Search/`, l'appariement et les jeux dans `GameTheory/`, les embeddings et le RAG dans `GenAI/`, le matching supervisé dans `ML/`. Mais une application réelle ne respecte pas ces frontières — elle assemble ce qui marche, d'où qu'il vienne.

Ces projets servent donc d'**exemples-capstones** : chacun est autonome (son propre README, ses dépendances, ses tests) et illustre une **intégration multi-domaines** que les notebooks mono-série ne peuvent pas montrer seuls. L'objectif n'est pas d'introduire de nouveaux concepts, mais de **rejouer plusieurs concepts déjà vus** dans un même système, et de comparer leurs comportements sur un problème commun.

## Projets

| Projet | Description | Séries mobilisées |
|--------|-------------|-------------------|
| [matching-cv/](matching-cv/) | Application web Flask qui compare trois algorithmes d'appariement CV ↔ fiche de poste : mots-clés (baseline), similarité sémantique par embeddings, et appariement stable de Gale-Shapley. | GameTheory, GenAI, ML |

## Focus — `matching-cv` : trois lectures d'un même problème

Le projet [`matching-cv/`](matching-cv/) prend un problème unique — apparier des CV de consultants à des fiches de poste — et le résout de **trois façons**, chacune ancrée dans une série différente. C'est précisément ce contraste qui en fait un projet cross-séries :

| Algorithme | Principe | Série d'origine |
|------------|----------|-----------------|
| **Simple (mots-clés)** | Comptage des mots-clés partagés entre CV et offre — une baseline transparente. | **ML** / `Search` (matching par recherche lexicale, baseline de classification) |
| **Sémantique (meilleur score)** | Embeddings OpenAI `text-embedding-3-small` (via Semantic Kernel), similarité cosinus, cache vectoriel ChromaDB. | **GenAI** (embeddings, vector store) |
| **Sémantique (stable)** | Appariement *stable* par l'algorithme de Gale-Shapley (variante Hospital-Resident) sur les scores sémantiques. | **GameTheory** (appariement stable ; cf. `GameTheory/` 15x et `social_choice_lean/`) |

La leçon transversale est que **le « meilleur » appariement dépend du critère** : le meilleur score individuel (algorithme 2) n'est pas le même que l'appariement globalement stable au sens de Gale-Shapley (algorithme 3), où aucune paire candidat/poste n'a intérêt à se ré-apparier. Comparer les deux sur les mêmes données rend visible la différence entre *optimisation locale* et *stabilité globale*.

> **Note pédagogique.** `matching-cv` a été produit sous orchestration automatisée comme extension d'un atelier élémentaire ; sa trace d'orchestration n'a pas été conservée. Sa valeur tient à l'**illustration** de l'intégration cross-séries plus qu'à un déroulé pas-à-pas — voir son [README dédié](matching-cv/README.md) et son [introduction](matching-cv/docs/INTRODUCTION.md) pour le détail.

---

*Version anglaise d'origine préservée : [README.en.md](README.en.md) (Epic #1650, Phase 0.5).*
