# Installation du Kernel Python WSL avec OpenSpiel

## Probleme

OpenSpiel (bibliotheque DeepMind pour la theorie des jeux) n'a pas de wheels pre-compiles pour Windows et necessite une compilation C++ complexe.

## Solution

Installer un kernel Python dans WSL Ubuntu avec OpenSpiel, accessible depuis Jupyter Windows.

## Etapes

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

### 3. Enregistrer le kernel pour Jupyter Windows

```bash
# Dans WSL, installer le kernel
source ~/.gametheory-venv/bin/activate
python -m ipykernel install --user --name gametheory-wsl --display-name "Python (GameTheory WSL)"
```

### 4. Creer le wrapper script (WSL)

VSCode passe les chemins de connexion au format `~\AppData\...` que `wslpath` ne comprend pas directement. Un script wrapper est necessaire.

**IMPORTANT**: Ne pas utiliser de docstrings avec backslashes (`\A`, `\U`, etc.) - cela cause des SyntaxWarning qui font echouer le kernel.

```bash
# Dans WSL
cat > ~/.gametheory-kernel-wrapper.py << 'EOF'
#!/usr/bin/env python3
# Wrapper for WSL kernel - NO DOCSTRINGS to avoid escape sequence issues
import sys
import subprocess
import os

def get_windows_home():
    result = subprocess.run(["cmd.exe", "/c", "echo", "%USERPROFILE%"],
                          capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else None

def convert_path(win_path):
    if win_path.startswith("~\\") or win_path.startswith("~/"):
        win_home = get_windows_home()
        if win_home:
            win_path = win_home + win_path[1:]
            win_path = win_path.replace("/", "\\")
    result = subprocess.run(["wslpath", "-u", win_path], capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else win_path

args = sys.argv[1:]
for i, arg in enumerate(args):
    if arg == "-f" and i + 1 < len(args):
        conn_file = args[i + 1]
        if ":" in conn_file or conn_file.startswith("~\\") or conn_file.startswith("~/"):
            args[i + 1] = convert_path(conn_file)
        break

os.environ["PATH"] = "/home/$USER/.gametheory-venv/bin:" + os.environ.get("PATH", "")
os.chdir(os.path.expanduser("~"))
os.execvp("/home/$USER/.gametheory-venv/bin/python3",
          ["/home/$USER/.gametheory-venv/bin/python3", "-m", "ipykernel_launcher"] + args)
EOF

# Remplacer $USER par votre nom d'utilisateur WSL
sed -i "s/\$USER/$USER/g" ~/.gametheory-kernel-wrapper.py
chmod +x ~/.gametheory-kernel-wrapper.py

# Verifier qu'il n'y a pas d'erreurs de syntaxe
python3 -m py_compile ~/.gametheory-kernel-wrapper.py && echo "Wrapper OK"
```

### 5. Creer le kernelspec Windows (PowerShell)

```powershell
# Creer le dossier pour le kernel
$kernelPath = "$env:APPDATA\jupyter\kernels\gametheory-wsl"
New-Item -ItemType Directory -Force -Path $kernelPath

# Obtenir le nom d'utilisateur WSL
$wslUser = wsl -d Ubuntu whoami

# Creer le kernel.json avec le wrapper
@"
{
  "argv": [
    "wsl.exe", "-d", "Ubuntu", "--",
    "python3", "/home/$wslUser/.gametheory-kernel-wrapper.py",
    "-f", "{connection_file}"
  ],
  "display_name": "Python (GameTheory WSL + OpenSpiel)",
  "language": "python"
}
"@ | Out-File -Encoding utf8 "$kernelPath\kernel.json"

# Verifier l'installation
jupyter kernelspec list
```

### 6. Redemarrer VSCode

Apres installation, redemarrez VSCode et selectionnez le kernel "Python (GameTheory WSL + OpenSpiel)" pour les notebooks qui utilisent OpenSpiel (7, 12, 15).

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

### Le kernel ne demarre pas (SyntaxWarning)

Si vous voyez `SyntaxWarning: invalid escape sequence '\A'` ou similaire:

1. Le wrapper script contient des docstrings avec backslashes
2. **Solution**: Utiliser des commentaires `#` au lieu de docstrings `"""`
3. Verifier: `wsl -d Ubuntu -- bash -c "python3 -m py_compile ~/.gametheory-kernel-wrapper.py"`

### Le kernel ne demarre pas (timeout 60s)

1. Verifier que WSL fonctionne: `wsl -l -v`
2. Verifier l'environnement: `wsl -d Ubuntu -- bash -c "source ~/.gametheory-venv/bin/activate && python --version"`
3. Verifier la conversion de chemin:
   ```bash
   wsl -d Ubuntu -- bash -c 'python3 ~/.gametheory-kernel-wrapper.py --help 2>&1 | head -5'
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
