# Scripts SmartContracts

Ce répertoire contient les scripts de configuration de l'environnement pour la série SmartContracts (Solidity + Foundry + analyse symbolique). L'environnement principal est cross-plateforme (Mac/Linux natif, Windows via WSL) et utilise un kernel Jupyter dédié `smartcontracts`.

## Scripts disponibles

### Setup principal

- [setup.sh](setup.sh) — Setup cross-plateforme : installe Foundry (`forge`, `cast`, `anvil`), crée un venv Python `~/.smartcontracts-venv`, installe les dépendances, enregistre le kernel Jupyter `smartcontracts`. Détecte automatiquement l'OS (Mac natif / Linux natif / WSL).

  ```bash
  # Mac/Linux (natif)
  bash scripts/setup.sh

  # Windows (depuis PowerShell, délègue à WSL)
  wsl -d Ubuntu -- bash /mnt/d/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts/setup.sh
  ```

### Setup alternatif (Python)

- `setup_env.py` (niveau parent) — Orchestrateur Python cross-plateforme. Détecte l'OS, installe les dépendances, gère le cycle de vie anvil (natif sur Mac/Linux, via WSL sur Windows).

  ```bash
  # Vérification complète de l'environnement
  python setup_env.py --check

  # Setup complet (Mac/Linux natif, Windows via WSL)
  python setup_env.py --setup

  # Démarrer/Arrêter anvil
  python setup_env.py --start-anvil
  python setup_env.py --stop-anvil
  ```

### Setup WSL (Windows uniquement)

- [setup_wsl_smartcontracts.sh](setup_wsl_smartcontracts.sh) — Variante WSL-only de `setup.sh` : installe Foundry, le venv Python avec les paquets Linux-only, et le wrapper de kernel `~/.smartcontracts-kernel-wrapper.sh` qui gère la conversion des chemins Windows -> WSL (workaround pour le bug Jupyter qui mange les backslashes).

  ```bash
  # À exécuter dans WSL Ubuntu
  bash setup_wsl_smartcontracts.sh
  ```

- [setup_wsl_kernel.ps1](setup_wsl_kernel.ps1) — Enregistre le kernel Jupyter `SmartContracts (WSL)` côté Windows, pointe vers le wrapper installé par `setup_wsl_smartcontracts.sh`. À exécuter **après** le script WSL.

  ```powershell
  # PowerShell Windows, après le setup WSL
  .\setup_wsl_kernel.ps1
  ```

### Template

- [_wrapper_template.sh](_wrapper_template.sh) — Template de wrapper de kernel WSL. Gère le bug de conversion des chemins Windows transmis par Jupyter (backslashes mangés par WSL) en recherchant le fichier de connexion dans les locations temp connues. Référence pour créer d'autres wrappers WSL (Tweety, Lean, etc.). **Ne pas exécuter directement** — utilisé comme modèle par `setup_wsl_smartcontracts.sh`.

## Architecture des kernels

| Plateforme | Kernel | Wrapper |
|---|---|---|
| Mac/Linux natif | `smartcontracts` | Aucun (direct `~/.smartcontracts-venv/bin/python`) |
| Windows (via WSL) | `SmartContracts (WSL)` | `~/.smartcontracts-kernel-wrapper.sh` (conversion chemins) |

## Séquence d'installation Windows complète

```bash
# Étape 1 : WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts
bash setup_wsl_smartcontracts.sh
```

```powershell
# Étape 2 : PowerShell Windows
cd D:\CoursIA\MyIA.AI.Notebooks\SymbolicAI\SmartContracts\scripts
.\setup_wsl_kernel.ps1
```

```text
# Étape 3 : Redémarrer VSCode pour que le kernel soit détecté
```

## Dépendances installées

- **Foundry** : `forge` (compilation), `cast` (interaction RPC), `anvil` (local node)
- **Python** : voir `requirements.txt` au niveau de la série SmartContracts (`web3`, `slither-analyzer`, `mythril` sous Linux)
- **JDK 17+** : requis pour certains outils d'analyse symbolique JVM-based

## Troubleshooting

- **Kernel ne démarre pas (Windows)** : vérifier `wsl -d Ubuntu -- cat /tmp/smartcontracts-kernel-wrapper.log` pour les erreurs de conversion de chemin.
- **`forge` introuvable** : le PATH peut ne pas être chargé ; lancer `source ~/.bashrc` dans WSL avant de démarrer Jupyter.
- **Erreur d'installation `mythril` sur Mac** : `mythril` est Linux-only ; l'installation échoue silencieusement sur Mac, c'est attendu.

## Voir aussi

- [SmartContracts/README.md](../README.md) — Vue d'ensemble de la série SmartContracts
- [SymbolicAI/scripts/README.md](../../scripts/README.md) — Scripts SymbolicAI niveau série
- [.claude/rules/wsl-kernels.md](../../../../.claude/rules/wsl-kernels.md) — Règles HARD pour les kernels WSL
