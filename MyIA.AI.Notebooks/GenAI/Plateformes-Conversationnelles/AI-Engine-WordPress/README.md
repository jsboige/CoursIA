# AI-Engine (WordPress) — extension GenAI côté contenu

[← Documentation GenAI](../../README.md) | [↑ Plateformes conversationnelles](../README.md) | [Open-WebUI](../Open-WebUI/README.md) | [Tour OWUI](../Open-WebUI/00-Tour-Plateforme/README.md) | [QA Playwright-OWUI](../Open-WebUI/Playwright-OWUI/README.md)

> **Parcours découverte.** Ce dossier présente **AI-Engine**, l'extension
> WordPress de Jordy Meow, comme **presqu'équivalent d'Open WebUI** côté
> *site de contenu*. La question n'est pas « quel produit choisir en
> absolu » — les deux ciblent des usages différents — mais « quand l'un
> est plus adapté que l'autre » pour un projet donné.

---

## Pourquoi une plateforme voisine d'Open WebUI ?

La série voisine **[Open-WebUI](../Open-WebUI/README.md)** documente la plateforme éponyme :
auto-hébergée, multi-tenant, centrée *chat LLM*. Mais ce n'est pas la
seule interface GenAI réaliste : beaucoup de sites de contenu (blogs,
forums, boutiques WooCommerce, sites éditoriaux) ont déjà un WordPress
installé. Plutôt que de poser Open WebUI *à côté* de WordPress, on peut
**ajouter la couche GenAI directement dans WordPress** via l'extension
**AI-Engine**. C'est ce que ce parcours explore — en gardant Open WebUI
comme point de comparaison pour les fonctionnalités communes (chat,
RAG, outils MCP, personas).

Le projet **livresagités** — une installation WordPress de maison
d'édition, avec workflow de manuscrits, comité de lecture et catalogue
WooCommerce — sert de **terrain d'observation** concret. Aucune donnée
de ce site n'est reproduite ici : ce dossier ne transmet que des
structures et des comptages, sans contenu, sans nom, et sans capture
d'écran (voir la note de méthode du
[parcours détaillé](livresagites-parcours.md#note-de-méthode--pourquoi-il-ny-a-aucune-capture)).

---

## À qui s'adresse ce parcours ?

- À toute personne qui **a déjà un site WordPress** et veut y ajouter
  des fonctionnalités GenAI sans empiler une plateforme séparée.
- À toute personne qui **évalue Open WebUI** et veut savoir si une
  alternative WordPress couvre (partiellement) ses besoins.
- À toute personne curieuse de voir **comment MCP s'intègre nativement
  dans un CMS** — AI-Engine transforme WordPress en *serveur MCP*, ce
  qui en fait un terrain pédagogique de choix pour le protocole.

Aucun prérequis technique pour les sections 1 à 4 ; la section 5
(MCP server) suppose une familiarité superficielle avec Model Context
Protocol.

## Comment lire ce parcours

Chaque section suit le même rythme :

1. **Ce que c'est** — la fonctionnalité en deux phrases.
2. **Comment ça marche** — l'architecture et la séquence d'appels.
3. **Comparaison OWUI** — l'équivalent (ou l'absence d'équivalent) côté
   Open WebUI.
4. **Référence livresagités** — un cas d'usage réel, sans PII.

Un fichier complémentaire [`comparatif-owui-vs-ai-engine.md`](../comparatif-owui-vs-ai-engine.md)
synthétise les différences fonctionnelles en tableau ; un fichier
[`livresagites-parcours.md`](livresagites-parcours.md) détaille le cas
d'usage livresagités bout-en-bout (sans contenu privé).

Un notebook exécutable [`eval-choisir-son-modele.ipynb`](eval-choisir-son-modele.ipynb)
complète le parcours par la question qu'il laisse ouverte : **quel modèle
brancher derrière un chatbot public ?** Il teste cinq propriétés
discriminantes contre n'importe quel endpoint compatible OpenAI — ancrage,
refus hors-contexte, respect du format, stabilité de langue, discipline
d'appel d'outil — et remplace « je l'ai essayé, il répond bien » par un
tableau reproductible. Configuration : copier [`.env.example`](.env.example)
vers `.env`.

Un second notebook [`ingestion-corpus-long-rag.ipynb`](ingestion-corpus-long-rag.ipynb)
traite l'amont du chatbot : **comment découper un catalogue de plusieurs
ouvrages** (chacun en chapitres) avant de l'indexer. Il compare un chunking
naïf (taille fixe) à un chunking structuré (par chapitre) et montre que la
dégradation du retrieval vient du découpage, pas du modèle d'embeddings —
démontré avec un vectoriseur TF-IDF déterministe, sans clé d'API.

Un troisième notebook [`auditer-un-serveur-mcp.ipynb`](auditer-un-serveur-mcp.ipynb)
est le compagnon exécutable du Parcours 3 (WordPress comme serveur MCP). Il
convertit en **mesure reproductible** la leçon centrale du dossier — *un
serveur MCP utile expose les verbes du métier, pas les tables de la base* :
étant donné le catalogue d'outils d'un serveur, il classe chaque outil en
CRUD générique ou verbe métier et mesure sa distance au schéma de
persistance. Le catalogue audité est synthétique (Maison Valmont) ; un
chemin live optionnel permet de le rejouer sur son propre serveur via `.env`.

Un notebook compagnon [`consommer-vs-exposer-le-mcp.ipynb`](consommer-vs-exposer-le-mcp.ipynb)
traite la confusion la plus fréquente du dossier — *les deux sens du fil MCP*.
AI-Engine expose WordPress comme serveur MCP **et** consomme des serveurs MCP
externes (module Orchestration). Le notebook monte les deux côtés sur le même
fixture synthétique (Maison Valmont) et mesure le **chevauchement
cross-catalogue** : quand un outil exposé et un outil consommé font la même
chose, l'agent doit choisir, et le double-écrit devient un risque. Indice de
Jaccard sur les signatures normalisées `(verbe, cible)` pour distinguer la
redondance de lecture (tolérable) de la redondance d'écriture (dangereuse).

Un quatrième notebook [`separer-les-environnements-de-vecteurs.ipynb`](separer-les-environnements-de-vecteurs.ipynb)
est le compagnon exécutable du Parcours 2 (RAG et piège du
multi-environnement). Il convertit en **mesures reproductibles** les deux
défaillances que la prose décrit : étant donné un vector store partitionné
en six régimes d'accès, il démontre (1) la **fuite cross-environnement**
— un retrieval émis sans filtre renvoie des chunks d'un régime réservé,
mesurée par un taux de fuite — et (2) **l'accident de réindexation** —
`reindexer(..., environnement=None)` écrase silencieusement un corpus
voisin. Déterministe, numpy, sans clé ni réseau ; fixture synthétique à 100 %
(Maison Valmont).

Un notebook compagnon [`auditer-un-formulaire-conditionnel.ipynb`](auditer-un-formulaire-conditionnel.ipynb)
traite la feature **AI Forms** — l'une des deux fonctionnalités GenAI cœur
qui n'avait ni section de parcours ni notebook. Thèse : *un formulaire à
logique de branchement est une machine à états implicite*. Le notebook
construit un formulaire de soumission synthétique (Maison Valmont) à champs
conditionnels et **énumère les chemins terminaux atteignables** : sept
champs engendrent treize états distincts, dont près des deux tiers
déclenchent un appel LLM, et un champ déclaré n'est visible sur aucun
chemin (champ mort). La leçon : le schéma n'est pas le formulaire — les
trois grandeurs (chemins, coût LLM, champs morts) sont émergentes. stdlib
pure, aucune clé, aucun réseau.

Un dernier notebook compagnon [`mesurer-la-derive-dun-copilot.ipynb`](mesurer-la-derive-dun-copilot.ipynb)
traite le **Copilot Gutenberg** (Parcours 1) — la seconde et dernière
fonctionnalité GenAI cœur qui restait sans notebook. Thèse : *le gate humain
à chaque étape ne protège pas de la dérive d'une chaîne*. Les six
transformations du Copilot (résumé, enhancement, traduction, rewriting,
image, alt text) ont des effets informationnels distincts — certaines
ajoutent, d'autres réécrivent, d'autres **détruisent** (résumé, traduction).
Le notebook modélise chaque transformation comme une fonction vectorielle
déterministe et mesure le **rappel de l'original** (projection normalisée,
bornée) après des séquences validées : une chaîne de transformations
destructrices complémentaires perd environ la moitié du document, quand une
chaîne de réversibles préserve 100 % — alors que chaque étape, isolément,
passait le gate. numpy, sans clé ni réseau ; fixture synthétique 100 %.

Un notebook transversal [`auditer-la-conformite-visuelle.ipynb`](auditer-la-conformite-visuelle.ipynb)
traite non pas une fonctionnalité mais une **classe de défaut** que toutes
partagent : *le rendu visuel*. Un smoke test structurel (statut 200, balise
`<main>` non vide, élément d'action présent) passe sur une page dont le rendu
viole la charte — CTA en bleu Bootstrap, texte sous le seuil de contraste
WCAG, lien semi-transparent sans affordance de bouton. Le notebook construit
quatre pages synthétiques (Maison Valmont) portant une violation délibérée
chacune, écrit trois détecteurs dédiés (contraste WCAG par luminance,
dominance des primaires, affordance des CTA), et montre que le smoke test est
aveugle aux trois classes de défauts. C'est la classe *visuelle* du motif « la
sonde ment » documenté pour la classe *système* dans
[`verification-verte-systeme-casse.md`](../../../../docs/reference/verification-verte-systeme-casse.md).
stdlib pur, sans clé ni réseau.

---

## Sections

### 1. [Vue d'ensemble](../comparatif-owui-vs-ai-engine.md)

AI-Engine en deux pages : ce que c'est, qui l'utilise, pourquoi on en
parle à côté d'Open WebUI. Statistiques publiques (100K+ installations
actives, 4.9/5 étoiles, version 3.7.0 août 2026, license GPL).

### 2. [Fonctionnalités GenAI cœur](../comparatif-owui-vs-ai-engine.md#fonctionnalités-cœur)

Chatbots, Workspace (plein écran dans wp-admin), Copilot pour l'éditeur
WordPress, AI Forms (text/image/audio/file avec logique conditionnelle),
génération d'image et de vision. Comparaison avec les surfaces
équivalentes d'Open WebUI (chat, canaux, prompts).

### 3. [Multi-provider et self-hosting](../comparatif-owui-vs-ai-engine.md#multi-provider-et-self-hosting)

AI-Engine supporte **neuf providers distants** (OpenAI, Anthropic,
Google, Mistral, xAI/Grok, Perplexity, OpenRouter, Replicate, Azure)
plus un connecteur **Custom OpenAI-compatible** pour les moteurs
auto-hébergés (Ollama, LM Studio, vLLM, llama.cpp, LocalAI). Côté
Open WebUI, c'est la même philosophie avec OpenAI-compatible + Ollama
natif ; la différence est qu'AI-Engine ne fournit pas son propre
moteur local — il s'appuie sur l'écosystème WordPress existant.

### 4. [RAG et embeddings](../comparatif-owui-vs-ai-engine.md#rag-et-embeddings)

Cinq vector stores supportés (Chroma, Qdrant, Pinecone, OpenAI Vector
Store, **Internal WordPress DB**). PDF import avec chunking
automatique, filtres de synchro (catégories, langues, Polylang),
trois modes de recherche (Simple, Context-Aware, Smart).
Comparaison avec la pile RAG native d'Open WebUI (Knowledge,
documents, hybrid search).

### 5. [MCP server natif](../comparatif-owui-vs-ai-engine.md#mcp-server-natif)

AI-Engine transforme WordPress en **serveur MCP** : des outils
permission-aware (post, comment, media, theme, plugin, WooCommerce,
Polylang, requêtes SQL, SEO) exposés à des agents comme Claude,
Claude Code, ChatGPT et OpenClaw. OAuth supporté pour les clients
desktop. AI-Engine peut aussi **consommer** des serveurs MCP
externes. C'est l'une de ses spécificités les plus marquantes côté
intégration agentique — un terrain de comparaison avec les **Tools /
MCP** d'Open WebUI.

### 6. [Cas d'usage livresagités](livresagites-parcours.md)

Le projet WordPress **livresagités** sert de **terrain d'observation
réel** : une maison d'édition, et non un blog — dépôt de manuscrits,
comité de lecture, catalogue e-commerce. Le parcours détaille
l'architecture en modules d'AI-Engine, la séparation du RAG en
**six environnements d'embeddings** distincts (un contrôle d'accès,
pas une commodité), et surtout le catalogue MCP réellement exposé :
**88 outils**, dont 64 natifs génériques et **24 outils métier**. Cet
écart porte la leçon d'architecture la plus transposable du dossier —
*un serveur MCP utile expose les verbes du métier, pas les tables de
la base*.

Aucun contenu du site n'est reproduit, et le dossier ne contient
aucune capture d'écran : la
[note de méthode](livresagites-parcours.md#note-de-méthode--pourquoi-il-ny-a-aucune-capture)
explique pourquoi une capture de `wp-admin` n'est pas assainissable.

---

## Sécurité — pas de secret dans les supports

Comme pour le dossier Open-WebUI voisin :

- **Aucun secret exposé** : pas d'URL d'admin, pas de clé d'API, pas
  de token MCP, pas de credentials WordPress.
- **Aucune capture d'écran**, ce qui est le moyen le plus sûr de
  tenir la ligne précédente. Un écran de `wp-admin` expose son
  contexte — compte connecté, domaines, extensions installées —
  indépendamment de la page affichée, et une capture retouchée n'est
  pas vérifiable par le lecteur. La
  [note de méthode](livresagites-parcours.md#note-de-méthode--pourquoi-il-ny-a-aucune-capture)
  détaille l'arbitrage et ce qu'illustrer proprement supposerait.
- **Aucun contenu privé livresagités** : le cas d'usage est décrit à
  un niveau architectural (structures, comptages, familles d'outils),
  jamais avec les contenus réels du site — ni texte de manuscrit, ni
  nom de personne, ni titre d'ouvrage.
- **Documentation de patterns, pas de credentials** : les exemples
  PHP dans ce dossier utilisent des *constantes de substitution*
  (`YOUR_OPENAI_API_KEY`, `YOUR_VECTOR_STORE_ID`), jamais des
  valeurs réelles.

Les fichiers `.env` réels ne sont jamais commités (`*.env` est
gitignoré) — seuls les `*.env.example` documentent les variables
attendues.

---

## Voir aussi

- [Plateformes conversationnelles](../README.md) — point d'entrée de la catégorie
- [README d'Open-WebUI](../Open-WebUI/README.md) — dossier voisin
- [Tour OWUI](../Open-WebUI/00-Tour-Plateforme/README.md) — pendant « chat
  LLM » centré
- [QA Playwright-OWUI](../Open-WebUI/Playwright-OWUI/README.md) — pendant «
  assurance qualité » de bout en bout
- [`comparatif-owui-vs-ai-engine.md`](../comparatif-owui-vs-ai-engine.md)
  — tableau structuré
- [`livresagites-parcours.md`](livresagites-parcours.md) — cas
  d'usage concret
- [`eval-choisir-son-modele.ipynb`](eval-choisir-son-modele.ipynb) —
  banc d'évaluation reproductible, cinq propriétés discriminantes
- [`ingestion-corpus-long-rag.ipynb`](ingestion-corpus-long-rag.ipynb) —
  ingestion RAG d'un corpus long structuré, chunking naïf vs par chapitre
- [`auditer-un-serveur-mcp.ipynb`](auditer-un-serveur-mcp.ipynb) —
  classifier CRUD générique vs verbes métier, mesurer la distance au schéma
- [`consommer-vs-exposer-le-mcp.ipynb`](consommer-vs-exposer-le-mcp.ipynb) —
  les deux sens du fil MCP, chevauchement cross-catalogue et risque de double-écrit
- [`separer-les-environnements-de-vecteurs.ipynb`](separer-les-environnements-de-vecteurs.ipynb) —
  fuite cross-environnement et accident de réindexation, mesurés sur un vector store partitionné
- [`auditer-un-formulaire-conditionnel.ipynb`](auditer-un-formulaire-conditionnel.ipynb) —
  AI Forms conditionnelles comme machine à états, énumération des chemins et champs morts
- [`mesurer-la-derive-dun-copilot.ipynb`](mesurer-la-derive-dun-copilot.ipynb) —
  Copilot Gutenberg : dérive d'une chaîne de transformations, le gate par étape ne protège pas la chaîne
- [`auditer-la-conformite-visuelle.ipynb`](auditer-la-conformite-visuelle.ipynb) —
  smoke test structurel vs conformité visuelle : contraste WCAG, primaires Bootstrap, affordance des CTA
- Epic [#4433](https://github.com/jsboige/CoursIA/issues/4433) —
  refonte pédagogique GenAI (ce parcours en est une extension)
- Issue [#9734](https://github.com/jsboige/CoursIA/issues/9734) —
  mandat user à l'origine de ce dossier