# Scripts SmartContracts

Ce repertoire contient les scripts de configuration de l'environnement pour la serie SmartContracts (Solidity + Foundry + analyse symbolique). L'environnement principal est cross-plateforme (Mac/Linux natif, Windows via WSL) et utilise un kernel Jupyter dedie `smartcontracts`.

## Scripts disponibles

### Setup principal

- [setup.sh](setup.sh) — Setup cross-plateforme : installe Foundry (`forge`, `cast`, `anvil`), cree un venv Python `~/.smartcontracts-venv`, installe les dependances, enregistre le kernel Jupyter `smartcontracts`. Detecte automatiquement l'OS (Mac natif / Linux natif / WSL).

  ```bash
  # Mac/Linux (natif)
  bash scripts/setup.sh

  # Windows (depuis PowerShell, delegue a WSL)
  wsl -d Ubuntu -- bash /mnt/d/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts/setup.sh
  ```

### Setup alternatif (Python)

- `setup_env.py` (niveau parent) — Orchestrateur Python cross-plateforme. Detecte l'OS, installe les dependances, gere le cycle de vie anvil (natif sur Mac/Linux, via WSL sur Windows).

  ```bash
  # Verification complete de l'environnement
  python setup_env.py --check

  # Setup complet (Mac/Linux natif, Windows via WSL)
  python setup_env.py --setup

  # Demarrer/Arreter anvil
  python setup_env.py --start-anvil
  python setup_env.py --stop-anvil
  ```

### Setup WSL (Windows uniquement)

- [setup_wsl_smartcontracts.sh](setup_wsl_smartcontracts.sh) — Variante WSL-only de `setup.sh` : installe Foundry, le venv Python avec les paquets Linux-only, et le wrapper de kernel `~/.smartcontracts-kernel-wrapper.sh` qui gere la conversion des chemins Windows -> WSL (workaround pour le bug Jupyter qui mange les backslashes).

  ```bash
  # A executer dans WSL Ubuntu
  bash setup_wsl_smartcontracts.sh
  ```

- [setup_wsl_kernel.ps1](setup_wsl_kernel.ps1) — Enregistre le kernel Jupyter `SmartContracts (WSL)` cote Windows, pointe vers le wrapper installe par `setup_wsl_smartcontracts.sh`. A executer **apres** le script WSL.

  ```powershell
  # PowerShell Windows, apres le setup WSL
  .\setup_wsl_kernel.ps1
  ```

### Template

- [_wrapper_template.sh](_wrapper_template.sh) — Template de wrapper de kernel WSL. Gere le bug de conversion des chemins Windows transmis par Jupyter (backslashes manges par WSL) en recherchant le fichier de connexion dans les locations temp connues. Reference pour creer d'autres wrappers WSL (Tweety, Lean, etc.). **Ne pas executer directement** — utilise comme modele par `setup_wsl_smartcontracts.sh`.

## Architecture des kernels

| Plateforme | Kernel | Wrapper |
|---|---|---|
| Mac/Linux natif | `smartcontracts` | Aucun (direct `~/.smartcontracts-venv/bin/python`) |
| Windows (via WSL) | `SmartContracts (WSL)` | `~/.smartcontracts-kernel-wrapper.sh` (conversion chemins) |

## Sequence d'installation Windows complete

```bash
# Etape 1 : WSL Ubuntu
cd /mnt/d/CoursIA/MyIA.AI.Notebooks/SymbolicAI/SmartContracts/scripts
bash setup_wsl_smartcontracts.sh
```

```powershell
# Etape 2 : PowerShell Windows
cd D:\CoursIA\MyIA.AI.Notebooks\SymbolicAI\SmartContracts\scripts
.\setup_wsl_kernel.ps1
```

```text
# Etape 3 : Redemarrer VSCode pour que le kernel soit detecte
```

## Dependances installees

- **Foundry** : `forge` (compilation), `cast` (interaction RPC), `anvil` (local node)
- **Python** : voir `requirements.txt` au niveau de la serie SmartContracts (`web3`, `slither-analyzer`, `mythril` sous Linux)
- **JDK 17+** : requis pour certains outils d'analyse symbolique JVM-based

## Troubleshooting

- **Kernel ne demarre pas (Windows)** : verifier `wsl -d Ubuntu -- cat /tmp/smartcontracts-kernel-wrapper.log` pour les erreurs de conversion de chemin.
- **`forge` introuvable** : le PATH peut ne pas etre charge ; lancer `source ~/.bashrc` dans WSL avant de demarrer Jupyter.
- **Erreur d'installation `mythril` sur Mac** : `mythril` est Linux-only ; l'installation echoue silencieusement sur Mac, c'est attendu.

## Voir aussi

- [SmartContracts/README.md](../README.md) — Vue d'ensemble de la serie SmartContracts
- [SymbolicAI/scripts/README.md](../../scripts/README.md) — Scripts SymbolicAI niveau serie
- [.claude/rules/wsl-kernels.md](../../../../.claude/rules/wsl-kernels.md) — Regles HARD pour les kernels WSL
