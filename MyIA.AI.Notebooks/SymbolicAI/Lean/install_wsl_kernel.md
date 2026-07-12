# Installation du Kernel Lean4 via WSL

## Problème
Le module `lean4_jupyter` utilise `signal.SIGPIPE` qui n'existe pas sur Windows.

## Solution
Installer le kernel dans WSL Ubuntu et l'enregistrer pour Windows.

## Étapes

### 1. Dans WSL Ubuntu

```bash
# Créer un environnement Python virtuel
python3 -m venv ~/.lean4-venv
source ~/.lean4-venv/bin/activate

# Installer les dépendances
pip install lean4_jupyter jupyter pyyaml

# Installer elan et Lean
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source ~/.elan/env
elan default leanprover/lean4:v4.11.0

# Installer le REPL (requis par lean4_jupyter)
cd /tmp
git clone https://github.com/leanprover-community/repl.git
cd repl
git checkout adbbfcb9d4e61c12db96c45d227de92f21cc17dd
lake build
sudo cp .lake/build/bin/repl /usr/local/bin/

# Vérifier l'installation
which repl
lean --version
```

### 2. Créer le kernelspec WSL (dans PowerShell Windows)

```powershell
# Créer le dossier pour le kernel
$kernelPath = "$env:APPDATA\jupyter\kernels\lean4-wsl"
New-Item -ItemType Directory -Force -Path $kernelPath

# Créer le kernel.json
@"
{
  "argv": [
    "wsl", "-d", "Ubuntu", "--",
    "bash", "-c",
    "source ~/.lean4-venv/bin/activate && source ~/.elan/env && python -m lean4_jupyter.kernel -f {connection_file}"
  ],
  "display_name": "Lean 4 (WSL)",
  "language": "lean4"
}
"@ | Out-File -Encoding utf8 "$kernelPath\kernel.json"

# Vérifier
jupyter kernelspec list
```

### 3. Redémarrer VSCode
Après installation, redémarrez VSCode et sélectionnez le kernel "Lean 4 (WSL)".

## Vérification

```bash
# Dans WSL
source ~/.lean4-venv/bin/activate
source ~/.elan/env
echo '{"cmd": "#eval 2 + 2"}' | repl
```

Devrait afficher : `{"messages":[{"severity":"info","data":"4"}]}`
