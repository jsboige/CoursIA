# 🛠️ Installation des prérequis pour les scripts multiplateforme

Ce guide détaille les étapes d'installation nécessaires pour exécuter les scripts multiplateforme sur différents systèmes d'exploitation.

## Prérequis Windows

### PowerShell

Les scripts Windows fournis sont écrits en PowerShell. Windows 10 et 11 sont livrés avec PowerShell 5.1 préinstallé.

#### Vérification de la version

Pour vérifier votre version de PowerShell, ouvrez PowerShell et exécutez :

```powershell
$PSVersionTable.PSVersion
```

#### Installation de PowerShell 7 (recommandé)

PowerShell 7 est une version multiplateforme qui offre des fonctionnalités améliorées :

1. Téléchargez l'installateur depuis [le site officiel de PowerShell](https://github.com/PowerShell/PowerShell/releases)
2. Exécutez l'installateur MSI et suivez les instructions
3. Vérifiez l'installation en ouvrant "PowerShell 7" depuis le menu Démarrer

#### Configuration de l'exécution des scripts

Par défaut, Windows restreint l'exécution des scripts PowerShell. Pour autoriser l'exécution :

1. Ouvrez PowerShell en tant qu'administrateur
2. Exécutez la commande :

```powershell
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

### Modules PowerShell requis

Certains scripts peuvent nécessiter des modules supplémentaires. Pour les installer :

```powershell
Install-Module -Name ModuleName -Scope CurrentUser -Force
```

Modules recommandés :
- `PSReadLine` (amélioration de l'interface en ligne de commande)
- `PSScriptAnalyzer` (analyse de la qualité du code)

## Prérequis macOS

### Bash

macOS est livré avec Bash préinstallé, mais utilise désormais Zsh comme shell par défaut.

#### Vérification de la version

Pour vérifier votre version de Bash :

```bash
bash --version
```

#### Installation de Bash plus récent (optionnel)

Pour installer une version plus récente de Bash via Homebrew :

1. Installez Homebrew si ce n'est pas déjà fait :
   ```bash
   /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
   ```

2. Installez Bash :
   ```bash
   brew install bash
   ```

3. Ajoutez le nouveau shell à la liste des shells autorisés :
   ```bash
   sudo echo /usr/local/bin/bash >> /etc/shells
   ```

4. Changez votre shell par défaut (optionnel) :
   ```bash
   chsh -s /usr/local/bin/bash
   ```

### Outils requis

Installez les outils suivants avec Homebrew :

```bash
brew install jq coreutils findutils
```

- `jq` : Traitement de JSON en ligne de commande
- `coreutils` : Versions GNU des outils Unix de base
- `findutils` : Versions GNU de find, xargs, et locate

### Permissions d'exécution

Pour rendre les scripts Bash exécutables :

```bash
chmod +x chemin/vers/script.sh
```

## Prérequis Linux

### Bash

La plupart des distributions Linux sont livrées avec Bash préinstallé.

#### Vérification de la version

```bash
bash --version
```

#### Mise à jour de Bash (si nécessaire)

Sur les distributions basées sur Debian/Ubuntu :

```bash
sudo apt update
sudo apt install bash
```

Sur les distributions basées sur Red Hat/Fedora :

```bash
sudo dnf update bash
```

### Outils requis

Sur les distributions basées sur Debian/Ubuntu :

```bash
sudo apt update
sudo apt install jq findutils coreutils
```

Sur les distributions basées sur Red Hat/Fedora :

```bash
sudo dnf install jq findutils coreutils
```

### Permissions d'exécution

Pour rendre les scripts Bash exécutables :

```bash
chmod +x chemin/vers/script.sh
```

## Installation de PowerShell Core sur macOS et Linux

Pour une véritable compatibilité multiplateforme, vous pouvez installer PowerShell Core sur macOS et Linux.

### macOS

Avec Homebrew :

```bash
brew install --cask powershell
```

### Linux (Ubuntu)

```bash
# Télécharger le package Microsoft
wget https://packages.microsoft.com/config/ubuntu/$(lsb_release -rs)/packages-microsoft-prod.deb -O packages-microsoft-prod.deb
# Installer le package
sudo dpkg -i packages-microsoft-prod.deb
# Mettre à jour les sources de packages
sudo apt-get update
# Installer PowerShell
sudo apt-get install -y powershell
```

Pour d'autres distributions Linux, consultez [la documentation officielle](https://docs.microsoft.com/fr-fr/powershell/scripting/install/installing-powershell-core-on-linux).

## Vérification de l'installation

### Windows

```powershell
# Vérifier PowerShell
$PSVersionTable.PSVersion

# Vérifier les modules installés
Get-Module -ListAvailable
```

### macOS/Linux

```bash
# Vérifier Bash
bash --version

# Vérifier jq
jq --version

# Vérifier PowerShell (si installé)
pwsh --version
```

## Configuration de l'environnement de développement

### Visual Studio Code

Visual Studio Code est un excellent éditeur multiplateforme pour travailler avec des scripts PowerShell et Bash :

1. Téléchargez et installez [Visual Studio Code](https://code.visualstudio.com/)
2. Installez les extensions recommandées :
   - PowerShell (ms-vscode.powershell)
   - Bash IDE (mads-hartmann.bash-ide-vscode)
   - ShellCheck (timonwong.shellcheck)

### Git Bash pour Windows

Pour tester les scripts Bash sous Windows :

1. Téléchargez et installez [Git pour Windows](https://gitforwindows.org/)
2. Git Bash sera installé, fournissant un environnement Bash sous Windows

## Résolution des problèmes courants

### Windows

- **Erreur "Le script ne peut pas être chargé car l'exécution de scripts est désactivée sur ce système"** :
  Exécutez `Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser` dans PowerShell en tant qu'administrateur.

- **Erreur de module manquant** :
  Installez le module requis avec `Install-Module -Name ModuleName -Scope CurrentUser -Force`.

### macOS/Linux

- **Erreur "Permission denied"** :
  Rendez le script exécutable avec `chmod +x script.sh`.

- **Erreur "command not found"** :
  Assurez-vous que les outils requis sont installés et que le chemin est correct.

- **Erreurs de fin de ligne** :
  Si vous avez édité les scripts sur Windows puis les exécutez sur Linux/macOS, vous pourriez rencontrer des erreurs dues aux différences de fin de ligne. Utilisez `dos2unix script.sh` pour convertir les fins de ligne.

## Conclusion

Avec ces prérequis installés, vous devriez être en mesure d'exécuter les scripts multiplateforme fournis dans ce répertoire. N'hésitez pas à adapter les scripts à vos besoins spécifiques et à explorer les fonctionnalités avancées de PowerShell et Bash.