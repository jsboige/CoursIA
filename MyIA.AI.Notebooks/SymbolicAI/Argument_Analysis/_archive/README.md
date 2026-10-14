# `_archive/` — chaîne legacy `*_agent` de la série Argument_Analysis

Registre de décisions (convention `_archive/`, cf [`docs/reference/_archive-convention.md`](../../../../docs/reference/_archive-convention.md)).
Ces carnets ne sont **pas** une poubelle : chaque ligne dit ce qui les a supplantés et où le verdict est enregistré.

## Contexte

L'arc narratif de la série (issue #17547, décision coordinateur du 2026-09-24) conserve une chaîne **déterministe et outillée** (`Argumentation-00..08e`, Onto/Obs) et archive la chaîne **`*_agent`** — quatre carnets définissant des agents Semantic Kernel pilotés par LLM, dont la sémantique a été vendangée dans la shim `argumentation_lib` (PR #2856, « B.2 core vendoring »).

La règle appliquée est « consolider n'est pas archiver » : avant le `git mv`, un inventaire **par carnet** a nommé, pour chaque capacité, le successeur vivant — la cellule de la chaîne conservée qui la porte, ou la shim qui la vendore. Cet inventaire vit dans l'en-tête de chaque carnet archivé (cellule markdown `[0]`) et dans le corps de la PR d'archivage.

## Table

| Notebook | Verdict | Superseded by | Verdict recorded in |
|----------|---------|---------------|---------------------|
| `Argument_Analysis_Agentic-0-init_agent.ipynb` | SUPERSEDED — bootstrap Semantic Kernel (état partagé, service LLM, agent PM) | `argumentation_lib/_shared_state.py`, `_state_manager_plugin.py`, `_runner.py` (`create_pm_agent`) ; consommateur `Argumentation-08b-Executor-Python.ipynb` | PR (3/3) de #17547, en-tête du carnet, `_archive/README.md` (ce fichier) |
| `Argument_Analysis_Agentic-1-informal_agent.ipynb` | SUPERSEDED — agent informel LLM (taxonomie des sophismes) | `argumentation_lib/_informal_definitions.py` (plugin vendu) + `Argumentation-02-Fallacies-Detection-Python.ipynb` (équivalent déterministe) | PR (3/3) de #17547, en-tête du carnet |
| `Argument_Analysis_Agentic-2-pl_agent.ipynb` | SUPERSEDED — agent de logique propositionnelle (LLM pilote Tweety) | `argumentation_lib/_pl_handler.py` (sémantique Tweety) + `Argumentation-05-Formal-Verification-Python.ipynb` (appel direct, sans wrapper LLM) | PR (3/3) de #17547, en-tête du carnet |
| `Argument_Analysis_Agentic-3-orchestration_agent.ipynb` | SUPERSEDED — orchestration conversationnelle SK ; sorties committées figées sur une **exception papermill** (`An Exception was encountered at 'In [5]'`, 2026-06-03) | `argumentation_lib/_runner.py` (`AnalysisRunner`) + `Argumentation-07-Orchestration-Python.ipynb` (paradigmes déterministes) | PR (3/3) de #17547, en-tête du carnet |

## Capacités sans successeur (assumées, pas silencieuses)

| Capacité | Disposition | Raison |
|---|---|---|
| `PropositionalLogicPlugin` (wrapper Semantic Kernel autour du raisonneur Tweety) | abandonnée en tant que **plugin SK** | la sémantique est portée par le handler `argumentation_lib/_pl_handler.py` et par l'appel direct à Tweety du rung `Argumentation-05` ; le pattern « LLM pilote un raisonneur déterministe » a été délibérément retiré de la chaîne conservée |
| `SimpleTerminationStrategy`, `DelegatingSelectionStrategy` (stratégies d'orchestration SK) | abandonnées | la shim utilise `AgentGroupChat` avec plafond de tours (`AnalysisRunner`) ; les stratégies n'ont pas été reprises |

## Consommateur vivant

`Argumentation-08b-Executor-Python.ipynb` chargeait ces quatre carnets via `%run` (chaîne auto-cohérente « LEGACY `_agent` », commentaire `CRITIQUE 3` de sa cellule d'exécution). Sa greffe sur la shim `argumentation_lib` fait partie de la PR d'archivage : après greffe, **aucun consommateur vivant** ne pointe ici.