# Installation des Kernels WSL pour GameTheory

Ce guide couvre l'installation de deux kernels WSL pour la serie GameTheory :

| Kernel | Notebooks | Usage |
|--------|-----------|-------|
| **Python (GameTheory WSL + OpenSpiel)** | 7, 12, 15 | OpenSpiel (CFR, NFSP) |
| **Lean 4 (WSL)** | 16, 19 | Code Lean natif |

Les notebooks 17 et 18 utilisent Python avec `lean_runner.py` et peuvent fonctionner avec le kernel Python standard.

---

# Partie 1 : Kernel Python + OpenSpiel

## Probleme

OpenSpiel (bibliotheque DeepMind pour la theorie des jeux) n'a pas de wheels pre-compiles pour Windows et necessite une compilation C++ complexe.

## Solution

Installer un kernel Python dans WSL Ubuntu avec OpenSpiel, accessible depuis Jupyter Windows.

## Installation Automatique (Recommandee)

### Methode rapide avec scripts

```bash
# 1. Dans WSL Ubuntu
cd /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_openspiel.sh
```

```powershell
# 2. Dans PowerShell Windows
cd C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_wsl_kernel.ps1
```

## Installation Manuelle

### 1. Installer WSL (si pas deja fait)

```powershell
# Dans PowerShell Admin
wsl --install -d Ubuntu
# Redemarrer si demande, puis configurer utilisateur/mot de passe
```

### 2. Dans WSL Ubuntu - Installer OpenSpiel

```bash
# Mettre a jour le systeme
sudo apt update && sudo apt upgrade -y

# Installer les dependances
sudo apt install -y python3-pip python3-venv

# Creer un environnement virtuel dedie
python3 -m venv ~/.gametheory-venv
source ~/.gametheory-venv/bin/activate

# Installer OpenSpiel et dependances
pip install --upgrade pip
pip install open_spiel nashpy numpy scipy matplotlib networkx seaborn pandas tqdm ipykernel

# Verifier l'installation
python -c "import pyspiel; print(f'OpenSpiel OK: {len(pyspiel.registered_names())} jeux')"
```

### 3. Creer le wrapper script (WSL)

VSCode passe les chemins de connexion au format `~\AppData\...`. Le shell WSL **consomme les backslashes**, donc un wrapper bash est necessaire.

**IMPORTANT - Problemes connus:**
1. Les backslashes sont **completement supprimes** par le shell WSL:
   - VSCode envoie: `~\AppData\Roaming\jupyter\runtime\kernel-xxx.json`
   - Le wrapper recoit: `c:UsersjsboiAppDataRoamingjupyterruntimekernel-xxx.json`
2. Le wrapper doit **reconstruire** le chemin avec une regex
3. Les docstrings Python avec `\A`, `\U` causent des SyntaxWarning
4. Utiliser un wrapper **bash** (pas Python directement)

```bash
# Dans WSL - Creer le wrapper bash
cat > ~/.gametheory-kernel-wrapper.sh << 'WRAPPER_SCRIPT'
#!/bin/bash
# Kernel wrapper for WSL - handles Windows path conversion
# Handles multiple path formats:
#   1. Tilde notation: ~\AppData\Roaming\jupyter\runtime\kernel-xxx.json
#   2. Stripped backslashes: c:UsersjsboiAppDataRoamingjupyterruntimekernel-xxx.json
#   3. Normal Windows paths: C:\Users\...\kernel-xxx.json

LOGFILE="/tmp/kernel-wrapper.log"
echo "=== Kernel wrapper started ===" > "$LOGFILE"
echo "Args: $@" >> "$LOGFILE"

ARGS=()
NEXT_IS_CONN=false

for arg in "$@"; do
    if [ "$NEXT_IS_CONN" = true ]; then
        echo "Original path: $arg" >> "$LOGFILE"

        # Case 1: Tilde notation (~\AppData\... or ~/AppData/...)
        if [[ "$arg" == ~* ]]; then
            WIN_HOME=$(cmd.exe /c "echo %USERPROFILE%" 2>/dev/null | tr -d "\r\n")
            arg="${WIN_HOME}${arg:1}"
            echo "After tilde expansion: $arg" >> "$LOGFILE"
        fi

        # Case 2: Backslashes were stripped by shell (c:UsersjsboiAppDataRoaming...)
        # Pattern: c:Users<user>AppDataRoamingjupyterruntimekernel-xxx.json
        if [[ "$arg" =~ ^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$ ]]; then
            USERNAME="${BASH_REMATCH[1]}"
            FILENAME="${BASH_REMATCH[2]}"
            # Reconstruct with proper path separators
            arg="C:\\Users\\${USERNAME}\\AppData\\Roaming\\jupyter\\runtime\\${FILENAME}"
            echo "Reconstructed path: $arg" >> "$LOGFILE"
        fi

        # Convert Windows path to Linux path
        if [[ "$arg" == *":"* ]] || [[ "$arg" == *"\\"* ]]; then
            LINUX_PATH=$(wslpath -u "$arg" 2>/dev/null)
            if [ -n "$LINUX_PATH" ]; then
                arg="$LINUX_PATH"
            fi
        fi

        echo "Final path: $arg" >> "$LOGFILE"
        ARGS+=("$arg")
        NEXT_IS_CONN=false
    elif [ "$arg" = "-f" ]; then
        ARGS+=("$arg")
        NEXT_IS_CONN=true
    else
        ARGS+=("$arg")
    fi
done

echo "Final args: ${ARGS[@]}" >> "$LOGFILE"
echo "Launching ipykernel..." >> "$LOGFILE"

export PATH="$HOME/.gametheory-venv/bin:$PATH"
cd ~
exec ~/.gametheory-venv/bin/python3 -m ipykernel_launcher "${ARGS[@]}"
WRAPPER_SCRIPT

chmod +x ~/.gametheory-kernel-wrapper.sh

# Verifier la syntaxe
bash -n ~/.gametheory-kernel-wrapper.sh && echo "Wrapper OK"
```

### 4. Creer le kernelspec Windows (PowerShell)

```powershell
# Creer le dossier pour le kernel
$kernelPath = "$env:APPDATA\jupyter\kernels\gametheory-wsl"
New-Item -ItemType Directory -Force -Path $kernelPath

# Obtenir le nom d'utilisateur WSL
$wslUser = (wsl -d Ubuntu whoami).Trim()

# Creer le kernel.json avec le wrapper BASH (pas Python!)
@"
{
  "argv": [
    "wsl.exe", "-d", "Ubuntu", "--",
    "bash", "/home/$wslUser/.gametheory-kernel-wrapper.sh",
    "-f", "{connection_file}"
  ],
  "display_name": "Python (GameTheory WSL + OpenSpiel)",
  "language": "python"
}
"@ | Out-File -Encoding utf8 "$kernelPath\kernel.json"

# Verifier l'installation
jupyter kernelspec list
```

### 5. Redemarrer VSCode

Apres installation, redemarrez **completement** VSCode (pas juste recharger la fenetre) et selectionnez le kernel "Python (GameTheory WSL + OpenSpiel)" pour les notebooks qui utilisent OpenSpiel (7, 12, 15).

## Verification

### Test rapide dans WSL

```bash
source ~/.gametheory-venv/bin/activate
python -c "
import pyspiel

# Lister quelques jeux
games = ['matrix_pd', 'kuhn_poker', 'tic_tac_toe', 'leduc_poker']
print('Jeux disponibles:')
for g in games:
    if g in pyspiel.registered_names():
        print(f'  {g}: OK')
    else:
        print(f'  {g}: Non disponible')

# Test rapide du Dilemme du Prisonnier
game = pyspiel.load_game('matrix_pd')
state = game.new_initial_state()
print(f'\nDilemme du Prisonnier: {game.num_players()} joueurs')
"
```

### Test depuis Jupyter Windows

Dans un notebook avec le kernel WSL:

```python
import pyspiel
print(f"OpenSpiel: {len(pyspiel.registered_names())} jeux disponibles")

# Test CFR sur Kuhn Poker
game = pyspiel.load_game("kuhn_poker")
print(f"Kuhn Poker: {game.num_players()} joueurs, {game.num_distinct_actions()} actions")
```

## Notebooks concernes

| Notebook | Utilise OpenSpiel | Alternative |
|----------|-------------------|-------------|
| 1-6 | Non | Nashpy (Windows natif) |
| 7-ExtensiveForm | Optionnel | game_theory_utils.py |
| 12-ImperfectInfo-CFR | Oui (CFR) | game_theory_utils.CFRSolver |
| 15-MultiAgent-RL | Oui (NFSP) | game_theory_utils.FictitiousPlay |

## Depannage

### Le kernel ne demarre pas (backslashes manquants)

**Symptome**: Le log `/tmp/kernel-wrapper.log` montre un chemin sans separateurs:

```
Original path: c:UsersjsboiAppDataRoamingjupyterruntimekernel-xxx.json
```

**Cause**: Le shell WSL consomme **tous** les backslashes avant que le script les recoive

**Solution**: Le wrapper doit reconstruire le chemin avec une regex:

```bash
if [[ "$arg" =~ ^c:Users([a-zA-Z0-9_]+)AppDataRoamingjupyterruntime(.*)$ ]]; then
    arg="C:\\Users\\${BASH_REMATCH[1]}\\AppData\\Roaming\\jupyter\\runtime\\${BASH_REMATCH[2]}"
fi
```

Verifier que le wrapper contient cette regex (voir section 3 ci-dessus).

### Le kernel ne demarre pas (SyntaxWarning)

Si vous voyez `SyntaxWarning: invalid escape sequence '\A'` ou similaire:

1. Le wrapper script contient des docstrings avec backslashes
2. **Solution**: Utiliser des commentaires `#` au lieu de docstrings `"""`
3. Verifier: `wsl -d Ubuntu -- bash -c "python3 -m py_compile ~/.gametheory-kernel-wrapper.py"`

### Le kernel ne demarre pas (timeout 60s)

1. Verifier que WSL fonctionne: `wsl -l -v`
2. Verifier l'environnement: `wsl -d Ubuntu -- bash -c "source ~/.gametheory-venv/bin/activate && python --version"`
3. Verifier le log du wrapper:
   ```bash
   wsl -d Ubuntu -- cat /tmp/kernel-wrapper.log
   ```

### OpenSpiel ne s'importe pas

1. Verifier l'installation dans WSL:
   ```bash
   source ~/.gametheory-venv/bin/activate
   pip show open_spiel
   python -c "import pyspiel; print('OK')"
   ```

2. Reinstaller si necessaire:
   ```bash
   pip uninstall open_spiel -y
   pip install open_spiel --no-cache-dir
   ```

### Probleme de connexion Jupyter

Le fichier de connexion utilise des ports TCP. Verifier que le pare-feu Windows autorise les connexions WSL.

## Alternative: Sans WSL

Si WSL n'est pas disponible, les notebooks utilisent automatiquement `game_theory_utils.py` qui fournit des implementations Python pures:

- `CFRSolver`: Counterfactual Regret Minimization
- `FictitiousPlay`: Apprentissage fictif
- `VCGAuction`: Mecanisme VCG
- `gale_shapley`: Matching stable

Ces implementations sont suffisantes pour comprendre les concepts, meme si elles n'ont pas toutes les optimisations d'OpenSpiel.

---

## Partie 2 : Kernel Lean 4 (WSL)

### Probleme

Le kernel `lean4_jupyter` utilise `signal.SIGPIPE` qui n'existe pas sur Windows. De plus, Lean 4 fonctionne mieux dans un environnement Linux.

### Solution

Installer Lean 4 et lean4_jupyter dans WSL Ubuntu, avec un kernel accessible depuis Jupyter Windows.

### Installation Automatique (Recommandee)

```bash
# 1. Dans WSL Ubuntu
cd /mnt/c/dev/CoursIA/MyIA.AI.Notebooks/GameTheory/scripts
bash setup_wsl_lean4.sh
```

```powershell
# 2. Dans PowerShell Windows
cd C:\dev\CoursIA\MyIA.AI.Notebooks\GameTheory\scripts
.\setup_lean4_kernel.ps1
```

### Installation Manuelle

#### 1. Dans WSL Ubuntu - Installer Lean 4

```bash
# Installer elan (gestionnaire de versions Lean)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source ~/.elan/env

# Installer Lean 4 stable
elan default leanprover/lean4:stable

# Verifier
lean --version
```

#### 2. Creer l'environnement Python pour lean4_jupyter

```bash
# Creer un environnement virtuel
python3 -m venv ~/.lean4-venv
source ~/.lean4-venv/bin/activate

# Installer les dependances
pip install --upgrade pip
pip install lean4_jupyter ipykernel pyyaml
```

#### 3. Installer le REPL (requis par lean4_jupyter)

```bash
# Cloner et compiler le REPL
cd ~
git clone https://github.com/leanprover-community/repl.git
cd repl
lake build

# Copier dans le PATH
cp .lake/build/bin/repl ~/.elan/bin/
```

#### 4. Creer le wrapper (WSL)

Le script `setup_wsl_lean4.sh` cree automatiquement le wrapper `~/.lean4-kernel-wrapper.py` qui gere la conversion des chemins Windows vers WSL.

#### 5. Creer le kernelspec Windows (PowerShell)

```powershell
# Creer le dossier pour le kernel
$kernelPath = "$env:APPDATA\jupyter\kernels\lean4-wsl"
New-Item -ItemType Directory -Force -Path $kernelPath

# Obtenir le nom d'utilisateur WSL
$wslUser = (wsl -d Ubuntu whoami).Trim()

# Creer le kernel.json
@"
{
  "argv": [
    "wsl.exe", "-d", "Ubuntu", "--",
    "/home/$wslUser/.lean4-venv/bin/python3",
    "/home/$wslUser/.lean4-kernel-wrapper.py",
    "-f", "{connection_file}"
  ],
  "display_name": "Lean 4 (WSL)",
  "language": "lean4"
}
"@ | Out-File -Encoding utf8 "$kernelPath\kernel.json"

# Verifier
jupyter kernelspec list
```

### Verification

```bash
# Dans WSL
source ~/.lean4-venv/bin/activate
source ~/.elan/env

# Test du REPL
echo '{"cmd": "#eval 2 + 2"}' | repl

# Test de lean4_jupyter
python3 -c "import lean4_jupyter; print('OK')"
```

### Notebooks concernes

| Notebook | Kernel | Contenu |
|----------|--------|---------|
| 16-Lean-Definitions | Lean 4 (WSL) | Definitions formelles Game, Nash |
| 17-Lean-NashExistence | Python 3 | Python + lean_runner.py |
| 18-Lean-CombinatorialGames | Python 3 | Python + lean_runner.py |
| 19-Lean-SocialChoice | Lean 4 (WSL) | Arrow, Sen en Lean natif |

### Depannage Lean

#### Le kernel ne demarre pas

1. Verifier les logs: `wsl -d Ubuntu -- cat ~/.lean4-wrapper.log`
2. Verifier l'installation: `wsl -d Ubuntu -- bash -c "source ~/.elan/env && lean --version"`
3. Verifier le REPL: `wsl -d Ubuntu -- bash -c "source ~/.elan/env && which repl"`

#### Erreur "repl not found"

Recompiler et reinstaller le REPL:
```bash
cd ~/repl
git pull
lake build
cp .lake/build/bin/repl ~/.elan/bin/
```
