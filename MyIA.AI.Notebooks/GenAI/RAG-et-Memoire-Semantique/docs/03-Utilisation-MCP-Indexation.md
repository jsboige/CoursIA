# 03 - Utilisation et indexation

[← 02 Infrastructure](02-Infrastructure-Qdrant.md) | [RAG et Mémoire Sémantique](../README.md) | [→ 04 Incidents et leçons](04-Incidents-et-Lecons.md)

Une base vectorielle déployée (document 02) ne sert à rien tant qu'elle n'est ni **alimentée** ni **interrogée**. Ce document décrit comment l'agent s'y connecte (MCP), comment le contenu y est indexé, et comment on l'interroge efficacement.

## 1. Le pont MCP : brancher l'agent sur Qdrant

Un agent de codage ne parle pas directement à Qdrant. Il passe par un **serveur MCP** (*Model Context Protocol*), qui expose des outils de recherche et d'indexation directement dans l'agent, comme s'il s'agissait de fonctions natives.

Dans notre infrastructure, ce pont est assuré par un serveur MCP maison (`roo-state-manager`) qui, entre autres :

- indexe les **conversations** des agents et le **code** des dépôts dans Qdrant ;
- expose des outils de recherche (`codebase_search`, `roosync_search`) que l'agent appelle pendant une tâche ;
- gère la coordination multi-machines (hors scope de ce document).

Pour un usage plus simple, l'écosystème propose aussi un **serveur MCP Qdrant officiel** (`mcp-server-qdrant`), qui suffit à exposer deux outils génériques — `qdrant-store` (indexer un fragment) et `qdrant-find` (rechercher) — sur une collection existante. C'est un bon point de départ pour des travaux pratiques.

```jsonc
// Exemple de configuration MCP (extrait — clé en placeholder)
{
  "mcpServers": {
    "qdrant": {
      "command": "uvx",
      "args": ["mcp-server-qdrant"],
      "env": {
        "QDRANT_URL": "http://localhost:6333",
        "QDRANT_API_KEY": "<votre-cle-api>",
        "COLLECTION_NAME": "code_search",
        "EMBEDDING_MODEL": "sentence-transformers/all-MiniLM-L6-v2"
      }
    }
  }
}
```

## 2. Comment le contenu est indexé

L'indexation transforme du texte brut en points interrogeables. Le pipeline est toujours le même (cf. schéma du [README](../README.md)) :

1. **Collecte** — on récupère la matière : transcriptions de conversations, fichiers source d'un dépôt.
2. **Découpage** (*chunking*) — on segmente en fragments de taille raisonnable. Trop gros, le vecteur devient flou (il « moyenne » trop de sens) ; trop petit, on perd le contexte. Un découpage par échange (question + réponse) ou par bloc logique (fonction, classe) fonctionne bien.
3. **Embedding** — chaque fragment passe dans le service d'embeddings (document 02) et devient un vecteur de 2560 dimensions.
4. **Upsert** — le vecteur est inséré dans Qdrant avec sa **charge utile** : la source, l'horodatage, le type de fragment, l'identifiant de tâche… Ces champs serviront à filtrer.

Deux familles de collections cohabitent dans notre déploiement :

- **La mémoire conversationnelle** (`roo_tasks_semantic_index`) : l'historique des échanges d'agents. C'est l'actif **irremplaçable** — on ne peut pas le régénérer.
- **Les index de code** (une collection par dépôt, préfixées `ws-*`) : le code indexé. Ils sont **régénérables** : en cas de perte, on relance l'indexation du dépôt.

Cette distinction guide les priorités de sauvegarde (document 04) : on protège d'abord l'irremplaçable.

## 3. Interroger par le sens

Côté agent, la recherche se résume à un appel d'outil. L'outil embarque la requête, lance la recherche HNSW dans Qdrant, et renvoie les *k* fragments les plus proches.

```text
codebase_search(
  query     = "rate limiting for embedding requests",
  workspace = "C:/dev/mon-projet",
  limit     = 15
)
→ renvoie les 15 fragments de code les plus proches du concept,
  avec leur fichier, leur score, et un extrait.
```

Pour la mémoire conversationnelle, l'outil équivalent (`roosync_search`) accepte deux modes :

- **`semantic`** — recherche vectorielle (par le sens), avec repli automatique si l'index n'est pas disponible ;
- **`text`** — recherche lexicale dans le cache (par les mots).

## 4. Bonnes pratiques de requête

L'expérience a dégagé quelques règles qui changent radicalement la qualité des résultats :

- **Interroger dans la langue du code.** Le code et ses commentaires sont majoritairement en anglais. Une requête sémantique en anglais, avec le vocabulaire du domaine (`authentication middleware`, `connection pool`, `retry with backoff`), tombe bien plus juste qu'une paraphrase en langage naturel.
- **Chercher un concept, pas une chaîne exacte.** Si vous connaissez le symbole exact, utilisez `grep` ; la recherche sémantique brille sur l'intention (« le truc qui limite les appels »).
- **Toujours passer le workspace explicitement.** Ne pas compter sur une auto-détection : nommer le dépôt cible évite des résultats hors-sujet.
- **Procéder par passes.** Une requête large d'abord, puis affiner : restreindre à un sous-répertoire, basculer sur `grep` pour le terme exact repéré, ou reformuler avec un autre angle.

## 5. Le motif « serre-livres » en pratique

Comme vu au [document 01](01-Pourquoi-Memoire-Semantique.md), la méthode SDDD recommande d'encadrer chaque tâche significative par deux recherches sémantiques :

- **Au début** — pour ne pas réinventer ce qui existe : « ce problème a-t-il déjà été résolu ? où est la doc afférente ? qui a travaillé dessus ? ».
- **À la fin** — pour vérifier que le nouveau travail est **retrouvable** (indexé) et que la documentation trouvée au début a été mise à jour.

Ce simple réflexe évite une grande partie des doublons et des régressions : on construit *sur* la mémoire plutôt que de la contourner.

## 6. Filtrer avec les payload indexes

La recherche pure par similarité peut être affinée par des **filtres** sur la charge utile, à condition que les champs concernés soient indexés. Dans notre collection, des payload indexes existent sur l'horodatage, la source (`claude`, `roo`…), le type de fragment et l'identifiant de tâche. On peut ainsi demander « les fragments sémantiquement proches de X, **et** provenant de Claude, **et** postérieurs à telle date ». Sans payload index, un tel filtre forcerait un balayage coûteux ; avec, il reste rapide.

> Note de prudence opérationnelle : avant toute suppression en masse de points (par exemple pour purger des doublons), **profiler d'abord**. Certaines combinaisons de champs ne sont pas indexées, et une purge mal ciblée peut être lente ou destructrice. Le drain asynchrone des suppressions peut prendre du temps avant que l'espace soit réellement récupéré.

## 7. Ce qu'il faut retenir

- L'agent parle à Qdrant via un **serveur MCP** ; un serveur officiel simple existe pour démarrer.
- L'indexation suit toujours **collecte → découpage → embedding → upsert** avec une charge utile riche.
- On sépare la **mémoire conversationnelle** (irremplaçable) des **index de code** (régénérables).
- Une bonne requête est **en anglais, conceptuelle, ciblée sur un workspace, et procède par passes**.
- Le motif **serre-livres** (recherche au début et à la fin d'une tâche) est le réflexe qui rentabilise la mémoire.

---

Document suivant : [04 - Incidents et leçons](04-Incidents-et-Lecons.md) — ce que les pannes nous ont appris.

[← Retour au README de la section](../README.md)
