# Registre d'archive — Scripts legacy GenAI Stack

Registre de disposition au standard de la [convention `_archive/`](../../../docs/reference/_archive-convention.md)
(colonnes : Script | Verdict | Superseded by | Verdict recorded in).

Ce répertoire contient les fichiers archivés lors de la **consolidation de février 2026**, qui a
remplacé les scripts éparpillés du stack par le CLI unifié `genai.py` (`scripts/genai-stack/genai.py`,
modules `commands/{docker,validate,notebooks,models,gpu,auth}.py` + `config.py`). Tous les verdicts
ci-dessous sont **datés de cette consolidation**, sauf mention contraire.

**Nom de fichier historique préservé.** Le registre s'appelle `ARCHIVE_README.md` (et non
`README.md`) parce que les en-têtes per-fichier `# ARCHIVED: ...` de chaque script archivé, ainsi
que la ligne du README parent (`scripts/genai-stack/README.md`), pointent sur ce nom — le renommer
casserait ces références sans gain de substance.

**Colonne « Verdict recorded in ».** La consolidation de février 2026 **précède l'entrée du répertoire
dans git** : l'intégralité de `scripts/genai-stack/` n'est trackée que depuis #18838 (2026-10-02),
qui a committé ces fichiers déjà archivés, avec leurs en-têtes. Le verdict durable vit donc dans ce
registre ; #18838 en est la preuve d'entrée en git.

## Fichiers depuis `core/`

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `cleanup_comfyui_auth.py` | OBSOLETE — nettoyage one-shot | `genai.py auth` | ce registre ; #18838 |
| `deploy_comfyui_auth.py` | OBSOLETE — déploiement one-shot | `genai.py docker start` | ce registre ; #18838 |
| `diagnose_comfyui_auth.py` | BROKEN — import `docker_qwen_manager` inexistant | `genai.py auth audit` | ce registre ; #18838 |
| `test_correction_setup_complete.py` | BROKEN — import `setup_complete_qwen` inexistant | none — closed dead-end | ce registre ; #18838 |
| `validate_genai_ecosystem.py` | OBSOLETE — volumineux, chevauche `validate.py` | `genai.py validate --full` | ce registre ; #18838 |
| `validate_mission_documentation.py` | OBSOLETE — valide des docs de mission nov 2025 inexistantes | none — closed dead-end | ce registre ; #18838 |

## Fichiers depuis `utils/` (tout le répertoire)

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `benchmark.py` | OBSOLETE — hardcode login/password, auth par cookie obsolète | none — closed dead-end (ne pas ressusciter : identifiants en dur) | ce registre ; #18838 |
| `comfyui_client_helper.py` | OBSOLETE — remplacé par un client plus compact | `core/comfyui_client.py` | ce registre ; #18838 |
| `consolidated_tests.py` | BROKEN — importe `token_manager` + `comfyui_client_helper` (legacy) | `genai.py validate` | ce registre ; #18838 |
| `debug_proxy.py` | OBSOLETE — proxy debug ponctuel | none — closed dead-end | ce registre ; #18838 |
| `diagnostic_model_paths.py` | OBSOLETE — one-shot Phase 29, problème résolu | none — closed dead-end | ce registre ; #18838 |
| `diagnostic_utils.py` | OBSOLETE — jamais appelé depuis aucun script actif | none — closed dead-end | ce registre ; #18838 |
| `docker-setup.ps1` | OBSOLETE — remplacé par `docker_manager.py` / `genai.py docker` | `genai.py docker start` | ce registre ; #18838 |
| `docker-start.ps1` | OBSOLETE — remplacé par `docker_manager.py` / `genai.py docker` | `genai.py docker start` | ce registre ; #18838 |
| `docker-stop.ps1` | OBSOLETE — remplacé par `docker_manager.py` / `genai.py docker` | `genai.py docker stop` | ce registre ; #18838 |
| `reconstruct_env.py` | OBSOLETE — remplacé par `core/auth_manager.py` | `genai.py auth reconstruct-env` (successeur vérifié le 2026-10-04 : action câblée dans `commands/auth.py` → `core/auth_manager.py::reconstruct_env_file`) | ce registre ; #18838 |
| `test_forge_connectivity.py` | OBSOLETE — absorbé dans `commands/validate.py` | `genai.py validate --check-forge` | ce registre ; #18838 |
| `test_forge_notebook.py` | OBSOLETE — simple appel papermill | `genai.py notebooks` | ce registre ; #18838 |
| `token_manager.py` | OBSOLETE — remplacé par `core/auth_manager.py` | `genai.py auth` | ce registre ; #18838 |
| `token_synchronizer.py` | OBSOLETE — remplacé par `core/auth_manager.py` sync | `genai.py auth sync` | ce registre ; #18838 |
| `validate_all_models.py` | OBSOLETE — remplacé par `validate_stack.py --full` | `genai.py validate --full` | ce registre ; #18838 |
| `validate_genai_stack.py` | OBSOLETE — remplacé par `validate_stack.py` puis `commands/validate.py` | `genai.py validate` | ce registre ; #18838 |
| `validate_gpu_cuda.py` | OBSOLETE — absorbé dans `commands/gpu.py` | `genai.py gpu --detailed` | ce registre ; #18838 |
| `validate_mission_documentation.py` | DOUBLON EXACT de `core/validate_mission_documentation.py` | none — doublon | ce registre ; #18838 |
| `validate_tokens_simple.py` | OBSOLETE — remplacé par `core/auth_manager.py` audit | `genai.py auth audit` | ce registre ; #18838 |
| `workflow_utils.py` | OBSOLETE — remplacé par `core/comfyui_client.py` WorkflowManager | `core/comfyui_client.py` | ce registre ; #18838 |

## Fichier depuis la racine

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `manage-genai-stack.ps1` | OBSOLETE — PowerShell remplacé par du Python multi-plateforme | `genai.py docker` | ce registre ; #18838 |

## Date d'archivage

Février 2026 — consolidation genai-stack. Registre reconstruit au standard 4 colonnes le
2026-10-04 (tranche #13749), en préservant l'intégralité des raisons et successeurs du registre
initial.
