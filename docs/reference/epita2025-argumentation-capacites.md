# Argumentation EPITA 2025 — catalogue de traçabilité par capacité

**Part de** [#16457](https://github.com/jsboige/CoursIA/issues/16457) (Axe 2 — distillation-outil) · **porté par** [#26422](https://github.com/jsboige/CoursIA/issues/26422)
**Mesuré** 2026-11-13 via l'API GitHub sur `jsboigeEpita/2025-Epita-Intelligence-Symbolique` (repo de 297 Mo, non cloné : lecture des arbres par API).

Ce document ne **refait pas** le catalogue : celui-ci existe déjà **au niveau des sujets** dans le repo étudiant. Ce qu'il ajoute est la **trace** manquante — sujet → implémentation réelle → interface réutilisable → verdict de portabilité.

## 1. Ce qui existe déjà (ne pas refaire)

| Doc existante (repo étudiant) | Ce qu'elle couvre |
|---|---|
| `docs/projets/SYNTHESE_THEMATIQUE_PROJETS.md` | Synthèse **par thème** (logiques formelles, frameworks Dung, taxonomies, maintenance de la vérité, planification/vérification) |
| `docs/projets/matrice_interdependances.md` | Dépendances **sujet → sujet** (17 sujets, notation `N.N.N`) |

Le « catalogue par numérotation, pas par capacité » est donc **faux au niveau sujet** : une vue thématique existe déjà. Le verrou réel est en aval.

## 2. Le verrou réel (mesuré)

Le registre de compétences de la plateforme, `argumentation_analysis/core/capability_registry.py`, fournit une composition dynamique propre :

```
CapabilityRegistry
  ComponentRegistration(
      name, component_type {AGENT|PLUGIN|SERVICE},
      capabilities: List[str], requires: List[str],
      parameters, metadata,
      invoke: async (input_text, context) -> Any
  )
```

Il sait **ce qu'un composant fournit** (`capabilities`) et **ce qu'il exige** (`requires`). Il ne sait **pas d'où vient** chaque capacité : **aucun champ de provenance** (`origin` / `source_project`). Sans ce champ, la distillation dans CoursIA ne peut ni documenter la généalogie d'une capacité, ni détecter les **duplications** entre projets étudiants qui produisent la même capacité.

> **Décision de charter A — Provenance.** Ajouter un champ `source_project` (optionnel) à `ComponentRegistration`, peuplé depuis ce catalogue. C'est la condition de tout travail de consolidation qui suit.

## 3. Catalogue par capacité (ancrage sur chemins réels)

Portabilité : **Portable** = Python pur, pas de binaire vendoré, pas de risque licence à la distillation. **Non portable** = blocage licence/redistribution mesuré. **À décider** = dépend d'un choix de stack.

**Base des chemins** : `core/`, `services/`, `plugins/`, `orchestration/`, `agents/`, `evaluation/` sont **relatifs à `argumentation_analysis/`** ; les **surfaces** (`interface_web/`, `api/`, `apps/`, `CaseAI/`) sont **à la racine** du repo. Il existe **deux** `api/` distincts : `api/` (racine, FastAPI, `openapi.snapshot.json`) et `argumentation_analysis/api/` (endpoints JTMS).

| Capacité | Implémentation réelle (mesurée) | Origine projet (correspondance structurelle) | Portabilité |
|---|---|---|---|
| Registre de compétences (composition dynamique) | `core/capability_registry.py` | plateforme | Portable — **sans provenance** (décision A) |
| JTMS / révision de croyances | `services/jtms/`, `services/jtms_service.py`, `plugins/atms_plugin.py`, `plugins/belief_revision_plugin.py`, `agents/jtms_agent_base.py`, `agents/sherlock_jtms_agent.py` | 1.4.1 TMS — `1.4.1-JTMS/` (`jtms.py`, `atms.py`, `belifs_loader.py`) | Portable |
| Argumentation Dung / AIF | `abs_arg_dung/` (`agent.py`, `aif_adapter.py`, `backends/`), `plugins/aspic_plugin.py`, `orchestration/dung_labelling_trajectory.py` | 1.2.1 Dung AF | Portable |
| Prouveurs FOL / automatiques | `core/eprover_runner.py`, `ext_tools/EProver/eprover.exe` + `cygwin1.dll`, `ext_tools/spass/SPASS.exe` + `spass_eml_adapter.bat` | 1.1.x FOL | **Non portable** (voir §4) |
| Détection de sophismes (règles symboliques + ML) | `plugins/french_fallacy_plugin.py`, `plugins/fallacy_workflow_plugin.py`, `services/fallacy_taxonomy_service.py`, `services/fallacy_family_definitions.py`, `core/fallacy_attribution.py`, `agents/concrete_agents/informal_fallacy_agent.py` | 2.3.2 — `2.3.2-detection-sophismes/` (`symbolic_rules.py`, `fallacy_pipeline.py`, `train_camembert.py`) | Portable (pipeline hybride) |
| Contre-argument / débat dialogique | `orchestration/collaborative_debate.py`, `orchestration/group_chat.py`, `orchestration/conversation_orchestrator.py`, `plugins/narrative_synthesis_plugin.py` | 2.3.3 — `2.3.3-generation-contre-argument/` ; 1.2.7 — `1_2_7_argumentation_dialogique/` | Portable |
| Gouvernance multi-agents | `plugins/governance_plugin.py`, `core/capability_registry.py`, `evaluation/capability_eval.py` | 2.1.6 — `2.1.6_multiagent_governance_prototype/` (`governance/`, `metrics/`, `reporting/`) | Portable |
| Canaux de communication agentique | `core/communication/` (`channel_interface.py`, `collaboration_channel.py`, `data_channel.py`, `hierarchical_channel.py`, `pub_sub.py`, `request_response.py`, `middleware.py`, `message.py`) | plateforme | Portable (abstraction à fort rendement) |
| Indexation sémantique / KB | `Arg_Semantic_Index/` (`kernel_memory/`, `UI_streamlit.py`), `services/extract_service.py`, `services/argument_ids.py` | plateforme | Portable |
| Harness d'évaluation falsifiable | `evaluation/` (`benchmark_runner.py`, `fallacy_benchmark.py`, `multi_model_benchmark.py`, `model_registry.py`, `judge.py`, `designate_contract.py`, `leak_patterns.py`, `corpus/`, `env_manifest.py`) | plateforme | Portable (à fort rendement : contrats désignés + détection de leak) |
| Vérification factuelle | `orchestration/fact_checking_orchestrator.py`, `services/fact_verification_service.py` | plateforme | Portable |
| Logique formelle (Tweety via JPype) | `plugins/kb_to_tweety_plugin.py`, `plugins/coordinated_logic_plugin.py`, `plugins/logic_agent_plugin.py` | 1.1.x | À décider (dépend JVM/JPype) |
| Surfaces d'interaction | **à la racine** : `interface_web/` (Starlette+React), `api/` (FastAPI, 25+ routes, `openapi.snapshot.json` — **distinct** de `argumentation_analysis/api/`), `apps/gradio_demo/`, `CaseAI/` (SPA) ; + `3.1.5_Interface_Mobile/` (Expo) | 3.1.5 mobile | À décider (choisir UNE surface) |
| LLM local | `2.3.6_local_llm/` (`local_llm/`, `benchmarks.csv`) | 2.3.6 | À décider (dépend de la stack locale) |
| Qualité d'argument | `2.3.5_argument_quality/src/` | 2.3.5 | À décider |

> « Correspondance structurelle » : l'ancrage provenance est déduit des **noms de modules** du projet étudiant qui correspondent à la capacité de la plateforme — pas une généalogie historique. Il sera confirmé/renversé au premier `source_project` réel (décision A).

## 4. Contrainte de portabilité mesurée (blocage licence)

Deux arbres vendorisent des binaires. `ext_tools/` :

```
ext_tools/EProver/eprover.exe
ext_tools/EProver/cygwin1.dll
ext_tools/spass/SPASS.exe
ext_tools/spass/spass_eml_adapter.bat
```

`libs/` porte une **troisième chaîne de prouveurs** (Prover9), des **solveurs SAT** et un **gros JAR** :

```
libs/prover9/bin/   prover9.exe, mace4.exe, prooftrans.exe, isofilter*.exe, interpformat.exe, cygwin1.dll
libs/native/        lingeling.dll, minisat.dll, picosat.dll
libs/java/          org.tweetyproject.tweety-full-1.28-with-dependencies.jar
```

**16 binaires au total, aucun accompagné d'un fichier de licence, aucun source, aucune README** — des exécutables Windows PE / un JAR fat vendus tels quels. EProver, SPASS et Prover9 sont sous licence GPL/académique : les re-vendrer dans le repo public CoursIA est un **blocage de redistribution** et une charge de license-incompatibility. Le recensement complet est produit par l'organe `scripts/research/argumentation_capacity_dedup.py` (commande `dedup`, section exposition licence ; organe livré par la PR jumelle du sous-grain #26422, en vol au moment de l'écriture — le chemin devient un lien actif à son merge).

> **Décision de charter B — Prouveurs externes.** Les capacités de prouvé FOL ne sont **pas** distillées en binaire. CoursIA les expose comme **dépendances externes optionnelles** : `eprover_runner.py` appelle l'exécutable si présent sur le `PATH`, sinon le notebook documente et route vers une machine qui l'a (règle F, exception GPU/outil — pas un « workaround dégradé »). Le runner reste portable ; le binaire, non.

## 5. Friction de numérotation (mesurée)

La matrice de sujets utilise la notation `N.N.N` (`1.2.7`), mais les **dossiers** du repo divergent :

- `1.4.1-JTMS` — notation à **points** ;
- `1_2_7_argumentation_dialogique` — notation à **underscores** pour le **même** sujet `1.2.7` de la matrice.

Un même sujet est écrit **deux façons** dans le même repo. C'est précisément la friction « catalogue par numérotation » : la clé de tri n'est pas stable. Toute consolidation doit **réconcilier la notation** (mapper `1_2_7` ↔ `1.2.7`) avant de cross-référencier.

## 6. Ce que la distillation exigera ensuite (hors scope de ce grain)

1. **Décision A** : ajouter `source_project` à `CapabilityRegistry.ComponentRegistration` et peupler depuis ce catalogue.
2. **Déduplication** : une fois les provenances posées, repérer les capacités produites par **plusieurs** projets (candidates d'extraction en toolbox partagée).
3. **Choix de surface** (UI) et de **stack locale** (LLM, JVM) avant toute extraction — ce sont des arbitrages, pas des constats.

Ce document est la **première brique** de la charte Axe 2. Il ne ferme ni #26422 ni l'umbrella #16457.
