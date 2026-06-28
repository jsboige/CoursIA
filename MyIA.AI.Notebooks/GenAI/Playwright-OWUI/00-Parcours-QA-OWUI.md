# Parcours QA-OWUI — Cadrage de la mission

> **Document de cadrage (Phase 0 de la refonte #4433).** Ce fichier pose le fil rouge narratif, la carte de la mission, le projet de certification final (capstone) et les acquis d'apprentissage de la série. Il sert de fondation au notebook chapeau `00-Parcours-QA-OWUI.ipynb` (livré en Phase 1) et à l'enrobage pédagogique des cinq modules existants.

[← Documentation GenAI](../README.md) | [Série Playwright-OWUI](./README.md) | [→ Vibe-Coding](../Vibe-Coding/README.md)

---

## 1. Pourquoi un fil rouge ?

La série Playwright-OWUI est techniquement solide : cinq modules, des tests E2E réels qui tournent contre une vraie plateforme de production (Open WebUI), des helpers propres et une approche multilingue. Mais, dans sa forme initiale, elle se présentait comme **une suite de fichiers de tests unitaires** : on apprenait des API Playwright isolées, sans qu'une narration ne relie les modules entre eux ni ne donne de sens au geste.

Le reste du domaine GenAI de CoursIA fonctionne par **parcours** : un objectif concret porte l'étudiant de bout en bout (générer une image, construire un agent, raisonner sur un corpus). Cette refonte aligne Playwright-OWUI sur cette pédagogie en lui donnant un fil rouge **réel et vivant** — celui qui correspond exactement au travail d'exploitation de la flotte qui héberge ces cours.

## 2. Le fil rouge — « QA Engineer d'une flotte GenAI multi-tenant »

> Tu rejoins l'équipe SRE/QA d'un hébergeur de plateformes d'IA générative. La flotte compte plusieurs instances **Open WebUI** en production, partagées par des écoles différentes (multi-tenant). Ta mission, au fil des cinq modules : **valider de bout en bout cette flotte**, depuis la prise en main de l'outillage jusqu'à la **certification d'une montée de version critique**. À la fin, tu sais répondre à la seule question qui compte un jour de mise en production : « Peut-on livrer, oui ou non ? »

Ce fil rouge n'est pas un décor. Il calque le travail réel décrit dans la documentation d'exploitation de la flotte : sept tenants, montées de version régulières, smoke tests post-déploiement, isolation multi-tenant à garantir. Chaque module devient **une étape de mission**, pas un chapitre de manuel.

## 3. Carte de la mission

| Module | Étape de la mission | Compétences Playwright | Durée |
|--------|---------------------|------------------------|-------|
| [01 — Découverte](./01-decouverte/) | « Prends en main la plateforme et ton outillage » | sélecteurs (ID/ARIA/rôle), auto-wait, mode headed, screenshots | 2-3 h |
| [02 — Navigation & Auth](./02-navigation-authentification/) | « Sécurise ton accès et explore l'admin » | `storageState`, RBAC, navigation SvelteKit, labels multilingues | 2-3 h |
| [03 — Chat & Streaming](./03-chat-streaming/) | « Valide le cœur métier : le chat IA en streaming » | non-déterminisme, polling, `waitForFunction`, éditeur TipTap, skip gracieux | 3 h |
| [04 — RAG, outils & canaux](./04-rag-tools-avances/) | « Certifie les fonctions avancées : RAG, outils MCP, canaux » | flux complexes, tests conditionnels, attente sur état applicatif | 3 h |
| [05 — Multi-tenant & CI/CD](./05-multi-tenant-ci/) | « Certifie l'isolation multi-tenant et industrialise en CI » | API-first (`APIRequestContext`), isolation, comparaison cross-instance, GitHub Actions | 3-4 h |

La progression est délibérée : on part de l'interface visible (modules 01-03), on descend vers les fonctions transverses (04), puis on bascule **API-first** (05) — exactement le chemin que suit un ingénieur QA quand il passe d'un test exploratoire manuel à une suite industrialisée qui tourne sans navigateur en intégration continue.

## 4. Le capstone — rapport de certification de montée de version

Le parcours se termine par un livrable que l'étudiant **produit lui-même**, et qui est aussi un vrai artefact d'exploitation :

> **Mission finale.** Une nouvelle version d'Open WebUI doit être déployée sur la flotte. Lance la suite E2E contre **deux tenants** (ton instance de cours + une instance secondaire), interprète les résultats, et rédige un **rapport de certification** qui tranche : *go / no-go pour la mise en production*.

Le rapport attendu (gabarit fourni en Phase 1) couvre :

1. **Périmètre testé** — modules exécutés, tenants ciblés, version visée.
2. **Résultats bruts** — passés / échoués / ignorés (skip), avec la raison de chaque skip (service non configuré ≠ régression).
3. **Analyse du non-déterminisme** — distinguer un échec réel d'un *flake* (LLM lent, surcharge), et comment l'auteur l'a établi.
4. **Drift d'interface** — sélecteurs ou libellés cassés par la nouvelle version, et la correction proposée.
5. **Verdict** — go / no-go argumenté, avec les conditions de levée si no-go.

Ce capstone transforme « j'ai écrit des tests qui passent » en « **je sais certifier une livraison** » — la compétence qui fait la valeur d'un QA en production.

## 5. Acquis d'apprentissage (niveau série)

À l'issue du parcours, l'étudiant est capable de :

1. **Écrire et exécuter** une suite de tests E2E Playwright contre une application web réelle, en TypeScript.
2. **Choisir des sélecteurs robustes** (ID, rôle ARIA, `getByRole`) qui résistent au drift d'interface, plutôt que des sélecteurs CSS fragiles.
3. **Tester du contenu non-déterministe** (réponses LLM en streaming) : polling, `waitForFunction`, assertions tolérantes, et distinction échec réel / flake.
4. **Gérer l'authentification et les sessions** via `storageState`, en respectant les contraintes réelles (rate limiting, RBAC).
5. **Écrire des tests API-first** avec `APIRequestContext`, sans navigateur, pour la vitesse et la robustesse en CI.
6. **Raisonner sur une architecture multi-tenant** : vérifier l'isolation des données entre instances et identifier ce qui est légitimement partagé.
7. **Industrialiser** une suite de tests en intégration continue (GitHub Actions : exécution, rapports, artefacts).
8. **Certifier une montée de version** : produire un rapport go/no-go étayé à partir de résultats de tests interprétés.

## 6. Format pédagogique — hybride notebook + tests

Cette refonte adopte un **format hybride**, validé pour le parcours :

- Un **notebook chapeau** (`00-Parcours-QA-OWUI.ipynb`, Phase 1) porte la narration de la mission, orchestre l'exécution des tests (`npx playwright test` lancé depuis des cellules), affiche et interprète les résultats, et propose des **cellules `## Exercice` exécutables**.
- Les **fichiers `.spec.ts` sont conservés** comme moteur de test réel (backend). On ne jette rien : la matière première (helpers, sélecteurs multilingues, approche API-first) est excellente et reste la suite E2E qui tourne contre une vraie plateforme.

On obtient le meilleur des deux mondes : un format catalogable et interactif au standard CoursIA (notebooks `.ipynb` avec exercices), **et** une suite de tests de bout en bout qui valide une application de production.

## 7. État de la refonte (#4433)

Refonte conduite sous la gouvernance de l'Epic-parapluie **#4427** (coordination ai-01:CoursIA), par phases atomiques (une PR par jalon) :

| Phase | Objet | État |
|-------|-------|------|
| **P0** | Cadrage : fil rouge, carte de mission, capstone, acquis d'apprentissage (ce document) | **en cours** |
| **P1** | Notebook chapeau `00-Parcours-QA-OWUI.ipynb` (narration + orchestration + exercices) | à venir |
| **P2** | Couche notebook par module (×5), `.spec.ts` conservés en backend | à venir |
| **P3** | Revalidation réelle sur **Open WebUI v0.9.6** (drift DOM, payload chat `chat_id`+`id`) | à venir |
| **P4** | Intégration au catalogue + fil rouge transverse (README parent, diagramme de mission) | à venir |

> **Note de version.** La cible de revalidation de la suite est désormais **Open WebUI v0.9.6** (la flotte a été montée de version le 2026-06-27). Le `WHATS-NEW-v0.9.1.md` actuel et la mention « revalidée v0.9.1 » du README sont **périmés** et seront repris en Phase 3 — tant que cette revalidation n'est pas faite, aucun claim de compatibilité v0.9.6 n'est porté.

---

*Phase 0 — refonte pédagogique #4433 (Part of #4427). Document de cadrage, FR-first.*
