# Scripts d'environnement — jumeaux Linux/macOS

Scripts de configuration et de réparation de l'environnement d'exécution des
notebooks CoursIA. Chaque script PowerShell (`.ps1`, Windows) possède un
jumeau bash (`.sh`, Linux/macOS) de comportement équivalent.

> Convention de référence : `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Roo-Code/02-orchestration-taches/scripts-multiplateforme/`.
> Voir l'Epic [#10643](https://github.com/jsboige/CoursIA/issues/10643) et la sous-issue [#10644](https://github.com/jsboige/CoursIA/issues/10644).

## Équivalences

| Script | Windows | Linux / macOS | Rôle |
|--------|---------|---------------|------|
| Setup de base | `setup_environment.ps1` | `setup_environment.sh` | Installe packages Python, .NET Interactive, kernels Jupyter (checkpoints/resume) |
| Audit | `audit_environment.ps1` | `_audit_environment.sh` *(à venir)* | Diagnostic complet de l'environnement |
| Automata (build/déploiement) | `automata-build-deploy.ps1` | `_automata-build-deploy.sh` *(à venir)* | Build et déploiement des automates |
| FFmpeg | `install-ffmpeg.ps1` | `install-ffmpeg.sh` | Installation de FFmpeg |
| Z3 (build fork) | `z3-build-deploy.ps1` | `z3-build-deploy.sh` | Build du wrapper Z3.Linq forké |

Les lignes « *(à venir)* » sont des jumeaux bash pas encore écrits — suivis
dans #10644. Les scripts préfixés `_` ci-dessus sont des placeholders
indicatifs, **ils ne sont pas commités** tant que le jumeau n'est pas écrit.

## Usage

### Windows (PowerShell)

```powershell
.\scripts\environment\setup_environment.ps1 -AutoFix
# Optionnels (torch, tensorflow, ...) :
.\scripts\environment\setup_environment.ps1 -AutoFix -InstallOptional
# Reprise après interruption :
.\scripts\environment\setup_environment.ps1 -Resume
```

### Linux / macOS (bash)

```bash
./scripts/environment/setup_environment.sh --auto-fix
# Optionnels :
./scripts/environment/setup_environment.sh --install-optional
# Reprise après interruption :
./scripts/environment/setup_environment.sh --resume
```

Codes de sortie (identiques des deux côtés) :
`0` = succès complet · `1` = avertissements (≤ 2 packages requis en échec) ·
`2` = échec.

## Différences d'implémentation (notes de port)

Le jumeau bash reprend fidèlement la sémantique du `.ps1` (phases d'installation
progressives, système de checkpoints, tests d'import, rapport final). Adaptations
spécifiques Unix :

- **Python** : `python3` est détecté en priorité, repli sur `python` (macOS
  n'expose souvent que `python3`).
- **Répertoire kernels Jupyter** : résolu via `jupyter --data-dir` (pas de
  `APPDATA`, qui n'existe pas sur Unix).
- **Permissions** : pas de contrôle d'administrateur — sur Unix, pip recommande
  un environnement utilisateur (`venv` ou `--user`) ; un avertissement est émis
  si le script tourne en `root`.
- **Checkpoints** : fichier texte simple (un nom par ligne), sans dépendance JSON.

## Cas intrinsèquement Windows

Aucun script de ce répertoire n'est intrinsèquement Windows-only : les outils
sous-jacents (`python`, `dotnet`, `jupyter`) sont multiplateformes. Le seul cas
Windows-only du dépôt est `scripts/genai-stack/Configure-IISAuthentication.ps1`
(IIS n'existe pas sur Mac/Linux) — documenté dans #10644, pas de jumeau bash prévu.
