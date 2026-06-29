# 01 - Pourquoi la mémoire sémantique ?

[← RAG et Mémoire Sémantique](../README.md) | [→ Infrastructure Qdrant](02-Infrastructure-Qdrant.md)

Ce document explique le **besoin** auquel répond une base de données vectorielle dans un système d'agents de codage. Avant de déployer quoi que ce soit (document 02), il faut comprendre *pourquoi* on le déploie.

## 1. Le problème : un agent n'a pas de mémoire

Un assistant de codage comme Claude Code ou Roo Code raisonne dans une **fenêtre de contexte** limitée. Tout ce qui n'y tient pas est, du point de vue de l'agent, inexistant. Concrètement, cela produit trois pathologies récurrentes :

- **L'amnésie inter-sessions.** À chaque nouvelle session, l'agent repart de zéro. Une décision d'architecture prise hier, un bug déjà diagnostiqué la semaine dernière, un script déjà écrit : rien de tout cela n'est « su » par défaut.
- **La re-exploration coûteuse.** Faute de mémoire, l'agent relit les mêmes fichiers, repose les mêmes questions, refait les mêmes recherches. C'est lent et cela consomme des jetons.
- **L'hallucination par manque d'ancrage.** Privé du contexte réel, le modèle comble les trous par des plausibilités. Il « se souvient » d'une fonction qui a été renommée, propose une approche déjà testée et rejetée, ou affirme un état du projet périmé.

La mémoire sémantique attaque ces trois problèmes en donnant à l'agent un **magasin externe et durable** qu'il peut interroger à la demande : l'historique des conversations et le code des dépôts, indexés de telle sorte qu'une question en langage naturel retrouve les fragments pertinents.

## 2. Pourquoi « sémantique » et pas juste `grep` ?

La recherche lexicale (`grep`, `Ctrl+F`, `LIKE '%mot%'`) cherche des **suites de caractères**. Elle est rapide, exacte et irremplaçable quand on connaît le terme précis. Mais elle est aveugle au **sens** :

- Une recherche `grep "limitation de débit"` ne trouvera pas un passage qui parle de *rate limiting*, de *throttling* ou de *quota d'appels* — pourtant le même concept.
- À l'inverse, `grep "base"` ramènera la base de données, la base d'un cas récursif, la classe de base et le camp de base, sans distinction.

La recherche **sémantique** compare des *significations*. Chaque texte est projeté dans un espace vectoriel où la proximité géométrique reflète la proximité de sens. « Limiter le nombre de requêtes par seconde » et « rate limiting » y tombent côte à côte, même sans aucun mot commun.

Les deux approches sont **complémentaires**, pas concurrentes. Une bonne méthodologie d'agent croise systématiquement :

- le **lexical** (`grep`, `glob`) quand on connaît le symbole exact,
- le **sémantique** (recherche vectorielle) quand on cherche un concept, une intention, « le truc qui faisait à peu près ça ».

## 3. Plongements et similarité : l'idée en une page

Un **plongement** (*embedding*) est un vecteur de nombres réels — par exemple 2560 dimensions dans notre infrastructure — produit par un modèle de langage entraîné pour que des textes de sens proche aient des vecteurs proches.

```text
"limiter les requêtes par seconde"  →  [0.12, -0.04, 0.88, ... ]  (2560 nombres)
"throttling des appels API"          →  [0.11, -0.05, 0.86, ... ]  (vecteur voisin)
"recette de la tarte aux pommes"     →  [-0.7,  0.33, 0.01, ... ]  (vecteur éloigné)
```

La **similarité** entre deux vecteurs se mesure le plus souvent par le **cosinus** de l'angle qui les sépare (1 = identique, 0 = sans rapport). Rechercher, c'est donc : embarquer la requête, puis trouver les *k* points de la base dont le vecteur est le plus proche. Sur des millions de points, un balayage exhaustif serait trop lent ; c'est pourquoi Qdrant utilise un index approché **HNSW** (détaillé au [document 02](02-Infrastructure-Qdrant.md)).

C'est le socle du motif **RAG** (*Retrieval-Augmented Generation*) : au lieu de tout demander au modèle de mémoire, on **récupère** d'abord les fragments pertinents dans la base vectorielle, puis on les **injecte** dans le contexte pour que la génération soit ancrée sur des faits réels.

> **Pont vers le RAG appliqué au texte.** Cette section traite le RAG du point de vue de l'*infrastructure* — la base vectorielle qui sert de mémoire à une flotte d'agents. Pour le même motif vu *en application* sur des documents, la section [Texte](../../Texte/) propose deux notebooks complémentaires : [`5_RAG_Modern.ipynb`](../../Texte/5_RAG_Modern.ipynb) (un pipeline RAG complet de bout en bout) et [`14_Persistent_Memory.ipynb`](../../Texte/14_Persistent_Memory.ipynb) (donner une mémoire persistante à un agent conversationnel). Et pour manipuler Qdrant soi-même sans rien installer, le [notebook pratique de cette section](../01-Hands-On-Grounding.ipynb).

## 4. La base vectorielle comme mémoire d'une flotte

Dans notre cas, plusieurs machines de développement exécutent des agents en continu. Chacune produit des conversations, des décisions, des diagnostics. Tout est indexé dans une collection centrale (nommée ici `roo_tasks_semantic_index`). Le résultat est une **mémoire partagée** :

- Un agent sur la machine A peut retrouver, par le sens, ce qu'un agent sur la machine B a résolu trois jours plus tôt.
- Les leçons d'incidents (cf. [document 04](04-Incidents-et-Lecons.md)) deviennent interrogeables : « comment a-t-on récupéré la dernière dérive de montage ? ».
- Le code de dizaines de dépôts est indexé séparément, de sorte que `codebase_search` retrouve l'implémentation d'un concept sans connaître le nom du fichier.

C'est cette mutualisation qui justifie d'investir dans une infrastructure robuste : la base n'est pas un cache jetable, c'est un actif. D'où l'importance des sauvegardes et des garde-fous anti-corruption décrits plus loin.

## 5. SDDD : ancrer le travail dans trois sources

La méthode que nous appliquons s'appelle **SDDD** (*Semantic-Documentation-Driven-Design*). Son principe : ne jamais agir sur une seule source d'information, mais **croiser trois ancrages** avant toute tâche significative.

| Ancrage | Source | Outil typique |
|---------|--------|---------------|
| **Technique** | Le code, qui fait foi | lecture de fichiers, `grep`, `git` |
| **Conversationnel** | L'historique des échanges | navigation dans les conversations indexées |
| **Sémantique** | La recherche par le sens | `codebase_search`, recherche vectorielle |

Deux pratiques en découlent :

- **Le motif « serre-livres » (bookend).** On lance une recherche sémantique *au début* d'une tâche (pour ne pas refaire ce qui existe et trouver la doc afférente) et *à la fin* (pour vérifier que le travail est retrouvable et la documentation à jour).
- **Le scepticisme.** Une information non vérifiée n'est jamais propagée telle quelle. On qualifie ce que l'on rapporte : vérifié dans le code, rapporté par une source, ou supposé.

La mémoire sémantique n'est donc pas un gadget : c'est l'outil qui rend l'ancrage *conversationnel* et *sémantique* possible à l'échelle d'un historique que personne ne pourrait relire à la main.

## 6. Ce qu'il faut retenir

- Un agent de codage est, par construction, **amnésique** au-delà de sa fenêtre de contexte.
- Une base vectorielle lui fournit une **mémoire externe, durable et interrogeable par le sens**.
- La recherche sémantique **complète** la recherche lexicale, elle ne la remplace pas.
- À l'échelle d'une flotte, cette mémoire devient un **actif partagé** qu'il faut traiter avec le sérieux qu'on accorde à une base de production (sauvegardes, garde-fous).
- La méthode **SDDD** opérationnalise tout cela : croiser technique, conversationnel et sémantique, en serre-livres, avec scepticisme.

---

Document suivant : [02 - Infrastructure Qdrant](02-Infrastructure-Qdrant.md) — comment cette mémoire est concrètement déployée.

[← Retour au README de la section](../README.md)
