# 02 - Infrastructure Qdrant

[← 01 Pourquoi](01-Pourquoi-Memoire-Semantique.md) | [RAG et Mémoire Sémantique](../README.md) | [→ 03 Utilisation](03-Utilisation-MCP-Indexation.md)

Ce document décrit le **déploiement réel** de la base vectorielle : le moteur, son conteneur, son stockage, sa quantization, et les garde-fous qui le protègent. Les valeurs et configurations sont tirées d'une infrastructure en production ; les templates anonymisés correspondants sont dans [`configs/`](../configs/).

## 1. Qdrant en deux minutes

[Qdrant](https://qdrant.tech/) est un moteur de recherche vectorielle écrit en **Rust**. Son vocabulaire :

- **Collection** : un ensemble de points partageant la même dimension de vecteur et la même configuration (l'équivalent d'une table).
- **Point** : l'unité stockée = un identifiant + un **vecteur** + une **charge utile** (*payload*) JSON arbitraire (date, source, type de fragment, identifiant de tâche…).
- **Index HNSW** (*Hierarchical Navigable Small World*) : un graphe de navigation qui rend la recherche des plus proches voisins *approchée* mais très rapide, au lieu d'un balayage exhaustif `O(n)`.
- **Payload index** : un index secondaire sur un champ de la charge utile, pour filtrer efficacement (par exemple « seulement les points dont `source = claude` et `date > ...` »).

Qdrant expose deux API : **REST** (HTTP, port 6333) et **gRPC** (port 6334, plus rapide pour les gros volumes).

## 2. Deux instances Docker

L'infrastructure fait tourner **deux** conteneurs Qdrant distincts, pour isoler les charges :

| Instance | Ports (REST/gRPC) | Stockage | Usage |
|----------|-------------------|----------|-------|
| **Production** | 6333 / 6334 | Disque virtuel dédié (VHDX) | Mémoire de la flotte, charge lourde |
| **Étudiants** | 6335 / 6336 | Volumes Docker | Travaux pratiques, charge légère |

Les deux sont pilotés par Docker Compose. Le moteur est **épinglé à une version précise** (`qdrant/qdrant:v1.18.2`) plutôt qu'à un tag mouvant comme `:latest`. C'est une décision délibérée : un `:latest` peut sauter de version au prochain `pull` et introduire un changement de comportement non désiré. Épingler, c'est rendre les mises à niveau **explicites et réversibles** (cf. [document 04](04-Incidents-et-Lecons.md), montée de version).

Commandes de base :

```bash
# Démarrer la production
docker compose -f docker-compose.production.yml up -d

# Vérifier la santé
curl http://localhost:6333/healthz       # production
curl http://localhost:6335/healthz       # étudiants

# Lister les collections (l'authentification est détaillée plus bas)
curl -H "api-key: $QDRANT__SERVICE__API_KEY" http://localhost:6333/collections
```

> Piège opérationnel : ne jamais utiliser `--remove-orphans` quand deux instances partagent le même nom de projet Compose — cela supprimerait les conteneurs de l'autre instance.

## 3. Le service d'embeddings

Qdrant **ne calcule pas** les vecteurs : il les stocke et les compare. Le calcul est délégué à un service d'embeddings séparé.

Notre infrastructure utilise un modèle **auto-hébergé**, `qwen3-4b-awq`, qui produit des vecteurs de **2560 dimensions**. Il a remplacé une API commerciale propriétaire (1536 dimensions), pour deux raisons :

- **Coût** : facturer chaque embedding d'un corpus de plusieurs millions de fragments réindexés en continu devient prohibitif.
- **Souveraineté** : un modèle local évite d'envoyer l'intégralité des conversations et du code à un tiers.

Conséquence structurante : **changer de modèle d'embeddings change la dimension des vecteurs**, donc impose de **recréer toutes les collections** et de tout réindexer. La dimension est un contrat figé à la création de la collection ; on ne migre pas un index 1536d vers 2560d, on le reconstruit.

## 4. Le stockage : un disque virtuel dédié (WSL2 VHDX)

Sur l'hôte Windows, Qdrant tourne dans Docker via WSL2. Les données de production ne vivent **pas** sur le système de fichiers de la distribution Linux par défaut, mais sur un **disque virtuel dédié** (un fichier VHDX, monté dans WSL2 et identifié par un *label* de système de fichiers, ici `qdrant-e`).

Pourquoi cette séparation :

- **Isolation** : les données Qdrant ne sont pas mêlées au reste de la distribution ; on peut les sauvegarder, déplacer ou compacter indépendamment.
- **Capacité** : un VHDX peut être placé sur un disque secondaire spacieux, loin du disque système.

Mais cette architecture introduit un **risque majeur** : si le VHDX n'est pas monté au démarrage du conteneur, le point de montage Docker se résout vers un répertoire **vide** de la distribution par défaut. Qdrant démarre alors sur un magasin vide — et, s'il continue d'indexer, écrit dans le vide pendant que les vraies données restent inaccessibles. C'est exactement le mécanisme d'une perte de données réelle (cf. [document 04](04-Incidents-et-Lecons.md)). La règle d'or qui en découle :

> **On résout le disque par son *label*, jamais par sa lettre de périphérique.** Les lettres (`/dev/sde`, `/dev/sdf`, `/dev/sdg`…) sont **instables** d'un redémarrage à l'autre ; le label, lui, est stable.

Deux garde-fous protègent ce montage — la sentinelle anti-split-brain (section 6) et un *watchdog* de remontage automatique (section 7).

## 5. La quantization TurboQuant : 8× plus compact, sans perte

Un vecteur de 2560 dimensions en virgule flottante 32 bits pèse ~10 Ko. Multiplié par des centaines de milliers de points, la RAM nécessaire pour garder l'index « chaud » explose. La **quantization** compresse les vecteurs pour la recherche, tout en gardant les originaux pour affiner les résultats.

Nous utilisons **TurboQuant 4 bits** (disponible à partir du moteur 1.18.0). Dans la configuration Qdrant, cela correspond à la clé officielle `quantization_config.turbo.bits: bits4`, assortie de `always_ram: true` :

```yaml
quantization_config:
  turbo:
    bits: bits4        # TurboQuant 4 bits — valeurs possibles : bits1, bits2, bits4, bits8
    always_ram: true   # garder les vecteurs quantizés en RAM pour des recherches rapides
```

En REST, le même réglage s'applique sans recréer la collection, via un `PATCH` sur `/collections/<nom>` avec le corps `{"quantization_config":{"turbo":{"bits":"bits4","always_ram":true}}}`. Les faits mesurés sur notre collection principale :

- **Compression 8×** des vecteurs gardés en RAM.
- **Rappel de score `recall@10 = 1.0`** par rapport à la recherche exacte : aucun voisin de qualité inférieure n'est introduit. Autrement dit, **zéro perte de qualité** observable à ce niveau de bits.
- Empreinte RAM de l'ordre de quelques Go pour des centaines de milliers de points — négligeable face à la limite du conteneur.

Deux subtilités importantes :

- Le **ré-affinage** (*rescore*) est un **paramètre de requête** (`params.quantization.rescore`), pas une propriété de la collection. Les vecteurs originaux en pleine précision sont conservés, ce qui permet à tout moment d'obtenir un résultat exact avec `params.quantization.ignore=true` — pratique pour mesurer le rappel après coup.
- La migration vers TurboQuant se fait par un simple `PATCH` de la configuration de quantization ; l'optimiseur re-quantize les segments existants en arrière-plan. **Mais on ne touche jamais une collection précieuse sans sauvegarde préalable vérifiée** (cf. [document 04](04-Incidents-et-Lecons.md)).

## 6. Le garde-fou anti-split-brain (sentinelle)

Pour empêcher le scénario « démarrer sur un magasin vide », l'`entrypoint` du conteneur de production contient une **porte logique** : il vérifie la présence d'un fichier sentinelle qui vit **sur le VHDX** (`/qdrant/storage/.qdrant_vhdx_sentinel`). Si ce fichier est absent — c'est-à-dire si le point de montage pointe vers le répertoire vide au lieu du VHDX — le conteneur **refuse de démarrer** (`exit 1`) au lieu de servir un index vide.

```bash
# Extrait simplifié de l'entrypoint (voir configs/docker-compose.qdrant.example.yml)
if [ ! -f /qdrant/storage/.qdrant_vhdx_sentinel ]; then
  echo "[SENTINEL] FATAL: VHDX non monte. Refus de demarrer." >&2
  exit 1
fi
echo "[SENTINEL] OK: sentinelle presente, demarrage."
exec ./entrypoint.sh
```

Le principe se résume en une phrase : **on ne réindexe pas dans le vide**. Mieux vaut un service en panne, bruyant et visible, qu'un service en apparence sain qui corrompt silencieusement la mémoire. Ce garde-fou a fait ses preuves en production sur une vraie dérive de montage : panne franche, zéro perte de données. À ne jamais contourner en supprimant la sentinelle pour « forcer » le démarrage.

## 7. Le watchdog de remontage

Un second garde-fou complète la sentinelle : une tâche planifiée vérifie périodiquement (toutes les deux minutes) que le bon disque est monté — **en vérifiant le label, pas un simple compte de collections** (un répertoire vide peut contenir des restes trompeurs). En cas de dérive, elle remonte le VHDX et relance proprement le conteneur.

Deux leçons de conception y sont gravées :

- La remédiation doit avoir un **auto-délai** (*self-timeout*) : un appel système bloqué (par exemple une commande WSL qui pend) ne doit pas figer le watchdog pendant des heures.
- Le remontage doit se faire **dans le bon espace de noms** : Docker résout les montages depuis l'espace de noms du processus d'init de la distribution, pas depuis une session WSL fraîche.

Le détail de ces mécanismes et des incidents qui les ont motivés est dans le [document 04](04-Incidents-et-Lecons.md).

## 8. Limites de ressources et anti-freeze

La configuration vise un équilibre entre débit et stabilité. Les points saillants (template complet dans [`configs/qdrant.production.example.yaml`](../configs/qdrant.production.example.yaml)) :

| Paramètre | Valeur | Raison |
|-----------|--------|--------|
| RAM (limite Docker) | 60 Go | Marge large au-dessus de l'empreinte réelle |
| CPU (limite Docker) | 12 cœurs | Parallélisme des recherches |
| `max_indexing_threads` | 10 | Sous le max CPU, pour laisser respirer les recherches |
| `max_optimization_threads` | 4 | Éviter la contention optimiseur vs écritures |
| `indexing_threshold_kb` | 6000 | Indexer dès ~1000 points (sinon balayage complet) |
| HNSW `on_disk` | true | Économiser la RAM |
| `grpc_timeout_ms` | 60000 | Éviter les requêtes bloquantes éternelles |

Côté conteneur, un **healthcheck** envoie une vraie requête HTTP `/healthz` toutes les 30 s (il détecte un *freeze*, pas seulement un crash), et un conteneur **autoheal** redémarre Qdrant après plusieurs échecs. Détail crucial : la **période de grâce au démarrage** (`start_period`) doit être assez longue pour couvrir la recovery à froid (plusieurs minutes sur un gros index) ; trop courte, l'autoheal tue le conteneur avant la fin de la recovery et provoque une boucle de redémarrage.

## 9. Authentification

Chaque instance a sa propre clé d'API, stockée dans un fichier d'environnement (`.env`) **jamais versionné**. La variable se nomme `QDRANT__SERVICE__API_KEY` (double tiret bas, convention Qdrant pour les variables imbriquées). Règle absolue : **on ne lit la clé que dans une variable, on ne l'affiche jamais** dans un log ou une sortie de commande. Le template [`configs/qdrant.env.example`](../configs/qdrant.env.example) ne contient que des placeholders.

## 10. Ce qu'il faut retenir

- Qdrant **stocke et compare** des vecteurs ; le **calcul** des embeddings est externe.
- Le moteur est **épinglé** à une version précise — les mises à niveau sont explicites et réversibles.
- Le stockage sur disque virtuel dédié apporte de l'isolation mais crée un **risque de dérive de montage**, neutralisé par la résolution **par label**, la **sentinelle** et le **watchdog**.
- **TurboQuant 4 bits** offre une compression 8× sans perte de qualité mesurable.
- Les garde-fous (sentinelle, healthcheck, autoheal, période de grâce) privilégient toujours **l'échec visible** à la corruption silencieuse.

---

Document suivant : [03 - Utilisation et indexation](03-Utilisation-MCP-Indexation.md).

[← Retour au README de la section](../README.md)
