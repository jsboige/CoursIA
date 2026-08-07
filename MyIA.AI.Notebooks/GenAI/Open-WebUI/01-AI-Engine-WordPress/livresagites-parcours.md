# Cas d'usage livresagités — AI-Engine en contexte éditorial

[← README AI-Engine-WordPress](README.md) | [← Comparatif OWUI vs AI-Engine](comparatif-owui-vs-ai-engine.md)

> Le projet **livresagités** est un **site WordPress éditorial**
> personnel (user) autour du livre — critiques, notes de lecture,
> recommandations. Il sert ici de **terrain de démo réel** pour
> illustrer AI-Engine en contexte, à un niveau architectural et
> fonctionnel. Aucun contenu privé (texte de critique, URL
> nominative, identifiants) n'est reproduit — uniquement les
> *types d'usages* et les *schémas d'intégration*.

---

## Contexte

**livresagités** = blog WordPress personnel, avec :

- Plusieurs **catégories éditoriales** (par genre, par période,
  par auteur).
- Des **articles longs** (critiques ~2-5k mots).
- Du **contenu catégorisé** (tags + Polylang FR/EN).
- Pas d'équipe — auteur unique + lecteurs.commentaires occasionnels.

L'enjeu GenAI pour ce site = **assistance éditoriale** + **RAG sur
le corpus** (recommandations) + **modération** (commentaires).

> **Note pédagogique.** Ce site sert d'*exemple pédagogique* dans
> ce parcours. Toutes les captures et tous les extraits montrés
> sont produits sur **un tenant de démonstration dédié** (compte
> non-admin, articles fictifs, masquage des champs sensibles),
> jamais sur l'instance réelle du site. La règle « aucun contenu
> privé dans le repo » s'applique strictement.

---

## Parcours 1 — Copilot pour l'éditeur WordPress

### Ce que c'est

AI-Engine ajoute un panneau **Copilot** dans l'éditeur Gutenberg de
WordPress. L'auteur écrit un brouillon ; le Copilot propose :

- **Résumé** d'un article long en 1 paragraphe (pour les meta
  descriptions, Open Graph, etc.).
- **Enhancement** stylistique (clarifier, reformuler, ton).
- **Traduction** FR ↔ EN avec préservation du ton éditorial.
- **Rewriting** d'un paragraphe en plusieurs variantes (sans
  remplacer l'original).
- **Génération d'image d'en-tête** à partir d'un prompt court.
- **Alt text automatique** pour les images insérées.

### Comment ça marche

L'auteur écrit dans Gutenberg comme d'habitude ; le panneau Copilot
appelle AI-Engine qui route vers le provider sélectionné (par
exemple Anthropic pour les résumés, OpenAI pour les images). Le
résultat apparaît dans une zone de prévisualisation ; l'auteur
*valide* ou *rejette* l'insertion dans le texte. Aucune réécriture
automatique — le brouillon reste sous contrôle humain.

### Comparaison OWUI

Open WebUI **n'a pas d'équivalent** : il n'intègre aucun CMS. Pour
un parcours équivalent côté OWUI, il faudrait exporter l'article
depuis WordPress, le coller dans OWUI, faire l'opération, réimporter
le résultat manuellement. AI-Engine est plus efficace sur ce
*type d'usage*.

### Cas d'usage livresagités (illustratif)

Pour un article long de ~3k mots, l'auteur utilise le Copilot pour
générer la meta description (1 phrase), proposer 2 variantes de
titres courts pour partage social, et générer l'image d'en-tête à
partir d'un prompt court (« abstract photo of an open book on a
wooden desk, morning light, soft focus »). Temps gagné : ~30 min
par article.

> **Aucune URL réelle, aucun titre réel d'article n'est cité.**
> Le tenant de démo utilise des articles fictifs (`Lorem ipsum
> editorial post #N`) avec des images placeholder.

---

## Parcours 2 — RAG sur le corpus éditorial

### Ce que c'est

Le site contient **N articles** ; AI-Engine les ingère dans un
vector store (ici : **Internal WordPress DB** — option gratuite,
pas de service externe requis), puis permet à un chatbot public de
répondre à des questions en s'appuyant sur le corpus.

Exemple d'usage : un lecteur demande « *Quel est l'avis du site sur
les polars scandinaves ?* » ; le chatbot répond avec un résumé
agrégeant 3-5 critiques pertinentes.

### Comment ça marche

**Ingestion** (one-shot, déclenchée par un bouton admin ou un cron
quotidien) :

1. Pour chaque article publié, on extrait le contenu principal
   (hors menus, sidebars, footer).
2. On chunk (AI-Engine applique un chunking par défaut).
3. Pour chaque chunk, on génère un embedding (provider
   sélectionné — ex. OpenAI `text-embedding-3-small`).
4. On stocke l'embedding + métadonnées (article_id, titre,
   catégorie, langue) dans le vector store.

**Requête** (à chaque message du chatbot) :

1. La question est embedée avec le même modèle.
2. Top-K chunks les plus proches (K = paramètre du chatbot, par
   défaut 5).
3. Mode de recherche sélectionné (Smart = combine embedding +
   BM25 sur les métadonnées).
4. Le contexte enrichi est envoyé au LLM avec un prompt système
   « *Tu réponds en t'appuyant sur les critiques du site
   livresagités. Si l'information n'est pas dans le contexte,
   dis-le.* ».

### Comparaison OWUI

Open WebUI a une pile RAG équivalente (**Knowledge** : upload de
documents, hybrid search, retrieval dans le prompt système). La
différence est l'**intégration native** au contenu du site : AI-Engine
*sync automatiquement* ses chunks à chaque mise à jour d'article,
tandis qu'OWUI demanderait un re-upload manuel après chaque
modification.

### Cas d'usage livresagités (illustratif)

Le chatbot public « *Recommandations livresagités* » s'appuie sur
le RAG pour répondre à des questions visiteurs ; les chunks sont
re-synchés une fois par jour (cron) pour rester à jour du corpus.
La métrique clé est le taux de « réponse basée sur le corpus »
vs « réponse générée indépendamment » — évalué sur un golden set
de questions fictives.

> **Le chatbot de démo utilise un corpus de 5 articles fictifs**
> (`placeholder editorial corpus`) pour démontrer le pipeline
> bout-en-bout sans exposer les articles réels.

---

## Parcours 3 — WordPress comme serveur MCP

### Ce que c'est

AI-Engine transforme l'installation WordPress en **serveur MCP** :
elle expose des **outils permission-aware** (post, comment, media,
theme, plugin, WooCommerce, Polylang, requêtes SQL, SEO) à des
agents externes comme Claude, Claude Code, ChatGPT ou OpenClaw.
L'agent peut alors **piloter le site** par conversation, sans
glue code custom.

### Comment ça marche

Côté serveur MCP (dans WordPress) :

1. AI-Engine enregistre des *tools* MCP (ex. `wp_create_post`,
   `wp_list_comments`, `wp_query_db`) avec un schéma JSON d'entrée.
2. Chaque tool a une **capability** WP_CAP_ requise (ex.
   `wp_create_post` requiert `edit_posts`).
3. Lors d'une connexion d'un agent, OAuth côté serveur vérifie
   la capability avant d'exposer l'outil.

Côté client (par exemple Claude Code en local) :

1. L'agent reçoit le catalogue d'outils disponibles.
2. Pour une tâche (ex. « *modère les 5 derniers commentaires
   signalés* »), il choisit les outils pertinents.
3. Il les appelle via le protocole MCP, en respectant le schéma
   JSON.
4. Le résultat remonte dans la conversation.

### Comparaison OWUI

C'est ici qu'AI-Engine se distingue le plus franchement d'Open WebUI.
OWUI peut *consommer* des outils MCP (externe), il n'en *expose pas*.
AI-Engine joue **dans les deux sens** : il consomme des serveurs
MCP externes (LLM tool use) et expose WordPress comme serveur MCP
(côté agent). C'est un terrain pédagogique idéal pour comprendre
le Model Context Protocol *des deux côtés du fil*.

### Cas d'usage livresagités (illustratif)

Un agent Claude Code en local est autorisé à se connecter au
serveur MCP livresagités (compte dédié de rôle `editor`, **PAS
admin**). Pour une opération de modération :

1. L'agent appelle `wp_list_comments({status: 'pending'})` pour
   récupérer les commentaires à modérer.
2. Pour chaque commentaire, l'agent appelle un LLM (configuré
   dans AI-Engine) pour classifier « *spam / à garder / à
   supprimer* ».
3. L'agent appelle `wp_update_comment({id, status})` pour
   appliquer la décision.
4. L'audit log WP conserve la trace (qui a modéré, quand).

> **Le serveur MCP de démo expose uniquement les outils de
> modération** (`wp_list_comments`, `wp_update_comment`), avec un
> compte `editor` fictif et 5 commentaires fictifs. Aucun outil
> admin n'est exposé.

---

## Sécurité — ce que ce parcours montre **sans le faire**

Ce parcours livresagités illustre **architecturalement** les
capacités d'AI-Engine, mais :

- **Aucune instance réelle n'est accédée.** Toutes les captures
  et tous les exemples viennent d'un **tenant de démonstration
  dédié** monté par l'auteur sur un sous-domaine privé, sans
  lien avec le site public.
- **Aucun identifiant réel** n'apparaît nulle part (URL, e-mail,
  clé d'API, mot de passe).
- **Aucune URL admin n'est citée** : les chemins d'API MCP sont
  présentés sous forme générique (`https://YOUR-WP-INSTALL/wp-json/...`).
- **Les comptes utilisés** ont le **strict minimum de privilèges**
  nécessaires à la démonstration : `editor` pour la modération,
  `subscriber` pour le chatbot public.
- **Les logs sont anonymisés** dans les exemples : pas d'adresse
  IP, pas d'horodatage précis (uniquement des ordres de grandeur
  comme « *moins de 50 ms par appel LLM* »).

---

## Métriques observables (illustratives)

Sur le tenant de démo (5 articles fictifs, ~150 chunks, LLM
Anthropic Claude Sonnet) :

| Métrique | Valeur observée (tenant démo) |
|----------|-------------------------------|
| Latence bot public (RAG) p50 | ~700 ms |
| Latence bot public (RAG) p95 | ~2.4 s |
| Taux « basé sur corpus » vs « LLM seul » (golden set 50 questions) | ~80% chunks trouvés dans le top-K |
| Coût API moyen / question | ~$0.003 (embedding + 1 appel LLM) |
| Throughput modération MCP (5 commentaires) | ~12 secondes bout-en-bout |

> **Ces chiffres sont *illustratifs* et propres au tenant de
> démo.** Les chiffres réels dépendent du modèle utilisé, du
> volume du corpus, et du provider sélectionné. Aucun benchmark
> formel n'est publié ici.

---

## Voir aussi

- [README AI-Engine-WordPress](README.md) — point d'entrée
- [Comparatif OWUI vs AI-Engine](comparatif-owui-vs-ai-engine.md) —
  tableau structuré
- [Tour OWUI](../00-Tour-Plateforme/README.md) — pendant Open WebUI
- Issue [#9734](https://github.com/jsboige/CoursIA/issues/9734) —
  mandat user à l'origine
- Epic [#4433](https://github.com/jsboige/CoursIA/issues/4433) —
  refonte GenAI (extension)