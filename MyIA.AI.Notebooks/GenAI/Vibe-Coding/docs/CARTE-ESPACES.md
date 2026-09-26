# Carte des espaces Vibe-Coding — audit structurel (#14526)

[← Vibe-Coding](../README.md) | [← docs](.) | [Orchestration cluster](CLUSTER-ORCHESTRATION.md)

**État mesuré au 2026-09-19** sur `main` (`21dd39bec82f` +). Cette carte est le livrable d'acceptance de [#14526](https://github.com/jsboige/CoursIA/issues/14526) : elle établit la structure **depuis le disque**, classe chaque élément (workspace / sous-thème / consommateur / transverse), relève les contenus éclatés et doublons, et propose une arborescence cible avec table de migration. **Rien n'est déplacé ici** — les `git mv` attendent la validation de cette carte (garde-fou de l'issue).

## 1. Inventaire mesuré (disque)

| Espace | Fichiers | Notebooks | Markdown | Rôle constaté |
|---|---:|---:|---:|---|
| [`Claude-Code/`](../Claude-Code/) | 61 | 5 | 42 | Ateliers Claude Code : 5 parcours numérotés (01-découverte → 05-automatisation-avancée) + `Scripts/` + `docs/` + `notebooks/` + `workspaces/` |
| [`Roo-Code/`](../Roo-Code/) | 279 | **0** | **187** | Ateliers Roo Code : 5 parcours numérotés miroirs + `Corrections/` + `Demo-Roo-Capabilities/` + `ateliers-avances/` + `Scripts/` + `docs/` + `workspaces/` — corpus **entièrement markdown** |
| [`Claw-Systems/`](../Claw-Systems/) | 16 | 0 | 12 | Agents autonomes (NanoClaw, OpenClaw, philosophie agentic engineering) + `configs/` |
| [`Claudish/`](../Claudish/) | 8 | 1 | 3 | Proxy multi-provider (routes assistants → Anthropic/GLM/Qwen) + `configs/` |
| [`analyzers/`](../analyzers/) | 7 | 0 | 1 | **Projet C# exécutable** `AgentSafetyAnalyzer` (+ `.Tests`) — hors paradigme notebook |
| [`docs/`](.) | 11 | 2 | 7 | Transverse : `CLUSTER-ORCHESTRATION.md`, `COMPARAISON-CLAUDE-ROO.md`, `INTRO-GENAI.md`, 2 notebooks transverses, `activites/`, `sessions/`, `csharprepl-demo/` |

**Notebooks pédagogiques déclarés au catalogue** : 8 (marqueur `CATALOG-STATUS` du README — l'écart avec les comptes bruts ci-dessus vient des notebooks d'outillage transverses, non comptés pédagogiques).

### Les voisins cités par l'issue — où ils vivent réellement

| Voisin | Localisation constatée | Statut |
|---|---|---|
| vLLM | [`docker-configurations/services/vllm-zimage`](../../../../docker-configurations/services/vllm-zimage/) | espace **infra** (stack Docker GenAI), hors arbre notebooks |
| OpenWebUI | [`GenAI/Plateformes-Conversationnelles/Open-WebUI`](../../Plateformes-Conversationnelles/Open-WebUI/) | série voisine **GenAI**, candidate rattachement |
| sk-agent | MCP documenté : [`docs/reference/slide-analyzer-sk-agent.md`](../../../../docs/reference/slide-analyzer-sk-agent.md) + tableau [CLUSTER-ORCHESTRATION](CLUSTER-ORCHESTRATION.md#les-mcps-maison-spécialisés) | espace **outil** (MCP maison), documenté transversalement |
| LivresAgités | **non-résident dans CoursIA** (aucun chemin sur le disque) | espace annoncé sans ancrage — à créer dans un sous-dossier dédié si le sujet entre au dépôt |

## 2. Classification (workspace / sous-thème / consommateur / transverse)

| Élément | Classe | Justification |
|---|---|---|
| `Claude-Code/` | **Workspace** | Espace de connaissance complet d'un produit : parcours + scripts + docs + workspaces propres |
| `Roo-Code/` | **Workspace** | Idem, produit miroir |
| `Claw-Systems/` | **Workspace** | Espace autonome (agents conteneurisés) avec sa philosophie et ses configs |
| `Claudish/` | **Workspace** | Espace autonome (proxy) avec configs + notebook |
| `Claude-Code/01..05`, `Roo-Code/01..05` | **Sous-thèmes** | Parcours pédagogiques numérotés au sein de leur workspace |
| `Roo-Code/ateliers-avances`, `Demo-Roo-Capabilities`, `Corrections` | **Sous-thèmes** | Extensions latérales du workspace Roo |
| `analyzers/AgentSafetyAnalyzer` | **Consommateur** | Projet C# qui **consomme** les modèles (analyse de sécurité agentique) sans documenter l'espace — c'est un artefact de code, pas un atelier |
| `docs/` (CLUSTER-ORCHESTRATION, COMPARAISON, INTRO, notebooks transverses, activites, sessions, csharprepl-demo) | **Transverse** | Contenus multi-workspaces |

## 3. Problèmes relevés (éclatés, doublons, liens)

1. **9 noms de fichiers partagés entre Claude-Code/ et Roo-Code/** (`README.md`, `composants-web.md`, `documentation-scripts.md`, `exemples-questions.md`, `guide-agent.md`, `methodologie-recherche.md`, `modeles-evenements.md`, `plan.md`, `taches-demo.md`) — la structure parallèle est **assumée** (ateliers jumeaux), mais elle rend les liens ambigus depuis l'extérieur : toujours qualifier par l'espace, jamais par le nom seul.
2. **Déchet versionné** : `docs/activites/Activités - IA Générative.old.md` — un `.old.md` qui traîne (remplacé par `Activités-GenAI.md`).
3. `docs/` éclaté en 4 sous-intérêts (`activites/`, `sessions/`, `csharprepl-demo/`, transverses racine) sans page d'index autre que le README de série.
4. `analyzers/` est un binaire de projet C# (.csproj + Tests) **sans README de rattachement** (1 seul md) — un lecteur ne sait pas pourquoi il est dans une série notebooks.
5. Voisins dispersés : Open-WebUI vit dans `Plateformes-Conversationnelles/`, vLLM dans `docker-configurations/` — aucun renvoi depuis le README Vibe-Coding vers ces espaces frères.

## 4. Arborescence cible proposée

**Principe** (garde-fou #14526) : les séries existantes SONT les espaces de connaissances — pas de racine générique concurrente. La cible ne crée **aucun** nouveau dossier racine ; elle consolide l'existant :

```text
Vibe-Coding/
├── README.md                    # PAGE COLLECTIVE UNIQUE (validée par #15787) : parcours + carte (ce document)
├── Claude-Code/                 # workspace — inchangé
├── Roo-Code/                    # workspace — inchangé
├── Claw-Systems/                # workspace — inchangé
├── Claudish/                    # workspace — inchangé
├── analyzers/                   # consommateur — + README de rattachement (PR atomique A2)
└── docs/
    ├── CLUSTER-ORCHESTRATION.md # transverse — inchangé (livré #15787)
    ├── COMPARAISON-CLAUDE-ROO.md
    ├── INTRO-GENAI.md
    ├── CARTE-ESPACES.md         # CE DOCUMENT (nouveau)
    ├── activites/               # − Activités - IA Générative.old.md (PR atomique A1)
    ├── sessions/
    └── csharprepl-demo/
```

**Emplacement de la page collective unique** : le `README.md` de la série — confirmé, il est déjà le parcours consolidé depuis #15787 ; cette carte s'y référence et le complète. Aucun dossier individuel supplémentaire n'est créé.

**Articulation avec le niveau cluster** : la « page collective » visée ici est celle des **espaces de cette série** (parcours interne à Vibe-Coding). La galerie nominative des identités `machine:workspace` et le parcours inter-séries relèvent du niveau cluster, déjà couverts par [CLUSTER-ORCHESTRATION.md § Séries-workspaces et page collective](CLUSTER-ORCHESTRATION.md#séries-workspaces-et-page-collective) (EPIC #14525/#14529) — cette carte ne duplique pas ce registre-là.

## 5. Table de migration ancien → nouveau

| # | Ancien | Nouveau | PR atomique | Risque |
|---|---|---|---|---|
| A1 | `docs/activites/Activités - IA Générative.old.md` | *(supprimé — déchet, contenu remplacé par `Activités-GenAI.md`)* | A1 | nul : vérifier 0 lien entrant avant suppression |
| A2 | *(absent)* | `analyzers/README.md` — rôle du projet, comment il consomme les espaces | A2 | nul : ajout pur |
| A3 | *(absent)* | Renvois frères dans le README série : Open-WebUI, vLLM, sk-agent, LivresAgités (non-résident) | A3 | nul : ajout de liens |
| — | tout le reste | **inchangé** (workspaces validés en place) | — | — |

Les voisins (`Open-WebUI`, `vllm-zimage`, sk-agent) **restent dans leur série actuelle** : les déplacer vers Vibe-Coding créerait la racine générique que l'interdit parental (#14525) proscrit. Ils entrent dans la carte par renvoi, pas par absorption.

## 6. Plan de PRs atomiques (après validation de cette carte)

| PR | Contenu | Taille estimée | Garde |
|---|---|---|---|
| **A1** | Suppression du `.old.md` après preuve de 0 lien entrant (`grep -r`) | 1 fichier, −N lignes | lien mort interdit ; citer le grep dans le body (mesuré au 2026-09-19 : 0 lien entrant hors la présente carte) |
| **A2** | `analyzers/README.md` de rattachement (rôle, usage, lien aux ateliers) | 1 fichier | FR-first |
| **A3** | Section « Espaces frères » du README série (4 renvois mesurés §1) | 1 fichier | liens vérifiés contre le disque ; marqueur `CATALOG-STATUS` byte-identique |

**Risques catalogue et traductions** (mesurés au 2026-09-19) : A1-A3 ne touchent **aucun notebook pédagogique** (suppression d'un `.old.md`, création d'un README, prose de README) → aucune entrée du catalogue générée ne bouge ; le README série porte un marqueur `CATALOG-STATUS` (1 occurrence) qui doit rester **byte-identique** sur A3 ([catalog-pr-hygiene](../../../../.claude/rules/catalog-pr-hygiene.md)). Aucun livrable de traduction dans le périmètre : les CSV présents sous `Roo-Code/` sont des **datasets d'atelier** (exercices analyse de données), pas des tables de traduction dérivées — le moteur `translation-sync` n'a rien à resynchroniser ici.

Aucun `git mv` de dossier n'est proposé : l'inventaire ne révèle **aucun éclatement qui le justifie** — les 4 workspaces sont cohérents, la numérotation 01-05 parallèle est un choix pédagogique assumé (ateliers jumeaux Claude/Roo), et `docs/` regroupe réellement du transverse.

## 7. Ce qui n'a pas été vérifié (portée)

- Le contenu détaillé des 187 md de Roo-Code (la carte mesure la **structure**, pas la qualité de chaque atelier — l'audit de fond des parcours est hors scope #14526).
- Les `workspaces/` des deux ateliers (espaces participants, volontairement volatils) : comptés, non audités.
- LivresAgités : absence constatée par `find` sur l'arbre dépôt ; si l'espace vit dans un autre dépôt, ce constat reste vrai pour CoursIA.
