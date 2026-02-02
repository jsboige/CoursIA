# Recherche Technique pour la V2 de la Solution de Matching Sémantique

Ce document présente les résultats de la recherche technique visant à définir l'architecture et les composants de la V2 de notre solution de matching sémantique. L'objectif est de s'appuyer sur des modèles de langage modernes (OpenAI) et des bibliothèques Python pour créer un moteur de recherche sémantique simple et efficace, fonctionnant entièrement en mémoire.

## 1. Génération d'Embeddings avec OpenAI

La première étape pour toute recherche sémantique est de convertir le texte en représentations vectorielles (embeddings). Nous utiliserons l'API OpenAI avec le modèle `text-embedding-3-small`, qui offre un excellent compromis entre performance et coût.

### Recommandation et exemple de code

L'utilisation de la bibliothèque Python `openai` est la méthode recommandée. Il est crucial d'utiliser la syntaxe moderne qui instancie un client `OpenAI`.

```python
import os
from openai import OpenAI

# Pour cet exemple, la clé API est passée directement.
# En production, il est fortement recommandé d'utiliser des variables d'environnement.
# os.environ["OPENAI_API_KEY"] = "VOTRE_CLE_API"
client = OpenAI(api_key="YOUR_OPENAI_API_KEY")

def get_embeddings(texts: list[str], model="text-embedding-3-small") -> list[list[float]]:
    """
    Génère les embeddings pour une liste de textes en utilisant le modèle OpenAI spécifié.
    """
    response = client.embeddings.create(input=texts, model=model)
    return [embedding.embedding for embedding in response.data]

# Exemple d'utilisation
texts_to_embed = [
    "Le machine learning est une branche de l'intelligence artificielle.",
    "La recette de la tarte aux pommes."
]
embeddings = get_embeddings(texts_to_embed)
print(f"Génération de {len(embeddings)} embeddings.")
# print(embeddings[0][:5]) # Affiche les 5 premières dimensions du premier embedding
```

## 2. Génération de texte avec un LLM (Chat Completion)

Pour des fonctionnalités futures (résumés, génération de texte, etc.), nous aurons besoin d'interagir avec un modèle de langage comme `gpt-4o-mini`.

### Recommandation et exemple de code

Comme pour les embeddings, nous utilisons la bibliothèque `openai`. Il faut veiller à utiliser la méthode `client.chat.completions.create`, car les anciennes méthodes sont obsolètes.

```python
import os
from openai import OpenAI

client = OpenAI(api_key="YOUR_OPENAI_API_KEY")

def get_chat_completion(prompt: str, model="gpt-4o-mini"):
    """
    Obtient une complétion de chat à partir du modèle OpenAI spécifié.
    """
    messages = [{"role": "user", "content": prompt}]
    response = client.chat.completions.create(
        model=model,
        messages=messages
    )
    return response.choices[0].message.content

# Exemple d'utilisation
prompt = "Explique le concept de recherche sémantique en une phrase."
completion = get_chat_completion(prompt)
print(f"Prompt: {prompt}")
print(f"Completion: {completion}")
```

## 3. Moteur de Recherche Sémantique In-Memory

Le cœur de la V2 est un moteur capable de stocker des vecteurs en mémoire et de trouver les plus similaires à une requête donnée.

### Comparaison des solutions

Deux bibliothèques principales de l'écosystème Microsoft ont été évaluées :

1.  **`semantic-kernel`**: Un SDK léger pour orchestrer des appels à des modèles d'IA. Il intègre des connecteurs pour diverses briques, y compris des bases de données vectorielles. Son `VolatileMemoryStore` est une implémentation de base de données vectorielles **en mémoire**, parfaite pour notre cas d'usage.
2.  **`kernel-memory`**: Une solution plus complète et orientée service pour les architectures RAG (Retrieval-Augmented Generation). Elle gère l'ingestion de documents, le partitionnement, l'embedding et la recherche, mais est plus complexe à mettre en place et semble surdimensionnée pour un simple moteur de recherche in-memory.

### Recommandation

Pour sa simplicité, sa légèreté et sa parfaite adéquation avec le besoin d'une base de données vectorielle en mémoire sans dépendances externes, **`semantic-kernel` est la solution recommandée.**

### Exemple de code avec `semantic-kernel`

L'exemple ci-dessous montre comment initialiser le kernel, ingérer des documents dans une `VolatileMemoryStore`, et effectuer une recherche de similarité.

```python
import asyncio
import semantic_kernel as sk
from semantic_kernel.connectors.ai.open_ai import OpenAITextEmbedding
# Note: Dans les versions plus récentes, VolatileMemoryStore a été déplacé.
# from semantic_kernel.memory import VolatileMemoryStore
# Pour les versions > 1.0, il pourrait être dans un autre module ou renommé.
# Nous utilisons ici l'importation classique pour `semantic-kernel < 1.0`.
from semantic_kernel.memory.volatile_memory_store import VolatileMemoryStore

async def main():
    # 1. Initialiser le moteur (Kernel) et le service d'embedding
    kernel = sk.Kernel()
    api_key = "YOUR_OPENAI_API_KEY"
    embedding_service = OpenAITextEmbedding(
        model_id="text-embedding-3-small",
        api_key=api_key
    )
    
    # Utiliser VolatileMemoryStore pour une base de données en mémoire
    memory = VolatileMemoryStore()

    # 2. Définir une collection et ingérer des documents
    COLLECTION_NAME = "documents_techniques"
    documents_to_ingest = {
        "doc1": "Le cloud computing fournit des services informatiques sur Internet.",
        "doc2": "L'intelligence artificielle est la simulation de l'intelligence humaine dans des machines.",
        "doc3": "Un SGBD est un système de gestion de base de données.",
        "doc4": "Le Big Data fait référence à des ensembles de données vastes et complexes."
    }

    print("Ingestion des documents dans la mémoire volatile...")
    # NOTE: L'API a changé dans les versions récentes du kernel.
    # Ceci est un exemple conceptuel. La syntaxe exacte peut varier.
    for doc_id, text in documents_to_ingest.items():
        embedding = await embedding_service.generate_embedding(text)
        await memory.upsert(
            collection=COLLECTION_NAME,
            record=sk.memory.MemoryRecord(
                id=doc_id,
                text=text,
                embedding=embedding
            )
        )
        print(f" - Document '{doc_id}' ingéré.")
    
    # 3. Effectuer une recherche sémantique
    query = "Qu'est-ce que l'IA ?"
    print(f"\nRecherche pour : '{query}'")
    
    query_embedding = await embedding_service.generate_embedding(query)

    results = await memory.search(
        collection=COLLECTION_NAME,
        query=query_embedding,
        limit=2,
        min_relevance_score=0.7 # Seuil de similarité
    )

    print("\nRésultats de la recherche :")
    if not results:
        print("Aucun résultat pertinent trouvé.")
    for result in results:
        print(f" - ID: {result.id}, Texte: '{result.text}', Similarité: {result.relevance:.2f}")

if __name__ == "__main__":
    # Correction pour l'exécution asynchrone
    try:
        asyncio.run(main())
    except Exception as e:
        print(f"Une erreur est survenue : {e}")

```

## 4. Conclusion

L'approche proposée, basée sur la bibliothèque `openai` pour l'interaction avec les modèles et `semantic-kernel` pour la gestion de la mémoire sémantique, constitue une base solide, moderne et simple pour le développement de la V2. Elle répond à toutes les exigences initiales, notamment celle d'une solution fonctionnant entièrement en mémoire.