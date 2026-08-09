# Projets cross-séries

Ce répertoire rassemble des **projets transversaux** qui mobilisent simultanément plusieurs séries pédagogiques du cursus (Search, GameTheory, GenAI, ML, SymbolicAI, Probas…). Là où chaque série enseigne *une* famille de techniques, un projet cross-séries montre comment **les combiner** sur une application concrète de bout en bout.

## Pourquoi des projets cross-séries ?

Les séries du cours isolent volontairement les concepts pour les rendre enseignables : on apprend la recherche dans `Search/`, l'appariement et les jeux dans `GameTheory/`, les embeddings et le RAG dans `GenAI/`, le matching supervisé dans `ML/`. Mais une application réelle ne respecte pas ces frontières — elle assemble ce qui marche, d'où qu'il vienne.

Ces projets servent donc d'**exemples-capstones** : chacun est autonome (son propre README, ses dépendances, ses tests) et illustre une **intégration multi-domaines** que les notebooks mono-série ne peuvent pas montrer seuls. L'objectif n'est pas d'introduire de nouveaux concepts, mais de **rejouer plusieurs concepts déjà vus** dans un même système, et de comparer leurs comportements sur un problème commun.

## Projets

| Projet | Description | Séries mobilisées |
|--------|-------------|-------------------|
| [matching-cv/](matching-cv/) | Application web Flask qui compare trois algorithmes d'appariement CV ↔ fiche de poste : mots-clés (baseline), similarité sémantique par embeddings, et appariement stable de Gale-Shapley. | GameTheory, GenAI, ML |
| [socle-metadata-driven/](socle-metadata-driven/) | Notebook .NET (C#) démontrant le socle transverse [`MyIA.AI.Shared`](../../MyIA.AI.Shared/) : découverte par décoration, sérialisation JSON/XML, et prédicat métier low-code (Flee). | socle partagé (.NET) |

## Focus — `matching-cv` : trois lectures d'un même problème

Le projet [`matching-cv/`](matching-cv/) prend un problème unique — apparier des CV de consultants à des fiches de poste — et le résout de **trois façons**, chacune ancrée dans une série différente. C'est précisément ce contraste qui en fait un projet cross-séries :

| Algorithme | Principe | Série d'origine |
|------------|----------|-----------------|
| **Simple (mots-clés)** | Comptage des mots-clés partagés entre CV et offre — une baseline transparente. | **ML** / `Search` (matching par recherche lexicale, baseline de classification) |
| **Sémantique (meilleur score)** | Embeddings OpenAI `text-embedding-3-small` (via Semantic Kernel), similarité cosinus, cache vectoriel ChromaDB. | **GenAI** (embeddings, vector store) |
| **Sémantique (stable)** | Appariement *stable* par l'algorithme de Gale-Shapley (variante Hospital-Resident) sur les scores sémantiques. | **GameTheory** (appariement stable ; cf. `GameTheory/` 15x et `game_theory_lean/SocialChoice/`) |

La leçon transversale est que **le « meilleur » appariement dépend du critère** : le meilleur score individuel (algorithme 2) n'est pas le même que l'appariement globalement stable au sens de Gale-Shapley (algorithme 3), où aucune paire candidat/poste n'a intérêt à se ré-apparier. Comparer les deux sur les mêmes données rend visible la différence entre *optimisation locale* et *stabilité globale*.

> **Note pédagogique.** `matching-cv` a été produit sous orchestration automatisée comme extension d'un atelier élémentaire ; sa trace d'orchestration n'a pas été conservée. Sa valeur tient à l'**illustration** de l'intégration cross-séries plus qu'à un déroulé pas-à-pas — voir son [README dédié](matching-cv/README.md) et son [introduction](matching-cv/docs/INTRODUCTION.md) pour le détail.

## Focus — `socle-metadata-driven` : le socle partagé démontré

À l'inverse de `matching-cv` qui **combine** plusieurs séries sur une même application, [`socle-metadata-driven/`](socle-metadata-driven/Socle-MetadataDriven-Csharp.ipynb) illustre ce qui est **partagé** par toutes les familles .NET du cursus : le socle transverse [`MyIA.AI.Shared`](../../MyIA.AI.Shared/) (EPIC #7265). Ce socle factorise trois besoins transverses — découverte, persistance, logique déclarative — qu'autrement chaque série ré-écrirait. Le notebook les met en scène sur un domaine factice (facturation / catalogue) en trois moments :

| Moment | Principe démontré | API du socle |
|--------|-------------------|--------------|
| **Décoration → introspection** | Des attributs (`[MainCategory]`, `[AttributeContainer]`) rendent les types découvrables *sans aucun appel d'enregistrement* ; un conteneur de réflexion les groupe par catégorie et par rôle. | `ReflectedProviderContainer.FromAssembly<T>()` |
| **Sérialisation round-trip** | Le même graphe d'entités (hiérarchie `IChildEntity` sur 3 niveaux) part et revient intact en JSON **et** en XML, référence parent re-liée. | `MetadataJsonSerializer`, `MetadataXmlSerializer` |
| **Prédicat métier low-code (Flee)** | Une règle métier est une **chaîne** — venue d'un fichier, d'un CSV, d'un utilisateur non-développeur — compilée une fois puis appliquée à N instances. C'est la différence entre coder N branches `if` et piloter la logique métier par les données. | `ExpressionContext` + `CompileGeneric<bool>` (Flee 2.0.0) |

La leçon transversale est qu'un **socle** fait basculer ce qui était ré-écrit dans chaque projet (comment découvre-t-on mes types ? comment persiste-t-on ma configuration ? où vit ma règle métier ?) vers une **convention partagée et testée une fois pour toutes**. Le notebook inclut trois exercices stub (enregistrement explicite, sérialisation personnalisée, règle à seuil variable) qui déclinent chacun des moments. Le socle expose par ailleurs un [`FleePredicateBuilder`](../../MyIA.AI.Shared/ComponentModel/Rules/FleePredicateBuilder.cs) (ancre B4) qui industrialise le troisième moment.

---

*Version anglaise d'origine préservée : [README.en.md](README.en.md) (Epic #1650, Phase 0.5).*
