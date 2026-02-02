# Guide d'utilisation des Scripts d'Organisation de Fichiers

Ce document explique comment utiliser les scripts d'organisation de fichiers disponibles pour Windows (PowerShell) et macOS/Linux (Bash). Ces scripts vous aideront à organiser facilement vos fichiers personnels sans avoir besoin de connaissances techniques avancées.

## À quoi servent ces scripts ?

Ces scripts sont conçus pour vous aider à **organiser automatiquement vos fichiers** (photos, documents, vidéos, etc.) qui s'accumulent souvent dans des dossiers désordonnés. Ils peuvent :

- Trier vos fichiers par **date** (année et mois)
- Trier vos fichiers par **type** (images, documents, vidéos, etc.)
- Trier vos fichiers par **nom** (première lettre)
- Générer un **rapport détaillé** des opérations effectuées

Imaginez que vous ayez des centaines de photos éparpillées dans un dossier. Ces scripts peuvent les organiser automatiquement par date ou par type, vous faisant gagner un temps précieux !

## Avantages pour les utilisateurs

- **Gain de temps** : organisez des centaines de fichiers en quelques secondes
- **Simplicité** : interface conviviale avec des options claires
- **Flexibilité** : plusieurs critères d'organisation disponibles
- **Sécurité** : mode simulation pour prévisualiser les changements avant de les appliquer
- **Transparence** : rapport détaillé des opérations effectuées

## Quelle version utiliser ?

- Si vous utilisez **Windows**, utilisez le script `exemple-script.ps1` (PowerShell)
- Si vous utilisez **macOS** ou **Linux**, utilisez le script `exemple-script.sh` (Bash)

Les deux versions offrent les mêmes fonctionnalités, mais sont adaptées à leur système d'exploitation respectif.

## Comment utiliser les scripts

### Pour les utilisateurs Windows (PowerShell)

1. **Ouvrir PowerShell** :
   - Cliquez sur le menu Démarrer
   - Tapez "PowerShell"
   - Cliquez sur "Windows PowerShell"

2. **Naviguer vers le dossier contenant le script** :
   ```powershell
   cd "chemin/vers/le/dossier"
   ```

3. **Exécuter le script** :
   
   Version simple (avec interface interactive) :
   ```powershell
   .\exemple-script.ps1
   ```
   
   Version avec paramètres :
   ```powershell
   .\exemple-script.ps1 -SourceFolder "C:\Mes Photos" -DestinationFolder "C:\Photos Organisées" -OrganisationCritere "date" -GenererRapport $true
   ```

### Pour les utilisateurs macOS/Linux (Bash)

1. **Ouvrir le Terminal** :
   - Sur macOS : Applications > Utilitaires > Terminal
   - Sur Linux : dépend de votre distribution, généralement accessible via le menu principal

2. **Rendre le script exécutable** (à faire une seule fois) :
   ```bash
   chmod +x exemple-script.sh
   ```

3. **Naviguer vers le dossier contenant le script** :
   ```bash
   cd "chemin/vers/le/dossier"
   ```

4. **Exécuter le script** :
   
   Version simple (avec interface interactive) :
   ```bash
   ./exemple-script.sh
   ```
   
   Version avec paramètres :
   ```bash
   ./exemple-script.sh --source "/Mes Photos" --destination "/Photos Organisées" --critere "date" --rapport true
   ```

## Options disponibles

Les deux scripts acceptent les mêmes options :

| Option | Description | Valeurs possibles | Valeur par défaut |
|--------|-------------|-------------------|-------------------|
| Dossier source | Dossier contenant les fichiers à organiser | Chemin valide | (Demandé à l'utilisateur) |
| Dossier destination | Dossier où les fichiers organisés seront placés | Chemin valide | (Demandé à l'utilisateur) |
| Critère d'organisation | Comment organiser les fichiers | `date`, `type`, `nom` | `date` |
| Générer rapport | Créer un rapport HTML des opérations | `true`, `false` | `true` |
| Mode simulation | Prévisualiser sans déplacer les fichiers | `true`, `false` | `false` |

## Exemples d'utilisation

### Scénario 1 : Organiser des photos de vacances

Vous avez des centaines de photos de vacances dans un dossier et vous souhaitez les organiser par date.

**Windows (PowerShell)** :
```powershell
.\exemple-script.ps1 -SourceFolder "C:\Utilisateurs\Moi\Photos\Vacances" -DestinationFolder "C:\Utilisateurs\Moi\Photos\Vacances Organisées" -OrganisationCritere "date"
```

**macOS/Linux (Bash)** :
```bash
./exemple-script.sh --source "/Users/Moi/Photos/Vacances" --destination "/Users/Moi/Photos/Vacances Organisées" --critere "date"
```

Résultat : Vos photos seront organisées dans des dossiers par année et par mois, par exemple :
```
Vacances Organisées/
  ├── 2023/
  │   ├── 01 - Janvier/
  │   ├── 07 - Juillet/
  │   └── 12 - Décembre/
  └── 2024/
      ├── 04 - Avril/
      └── 05 - Mai/
```

### Scénario 2 : Organiser des documents par type

Vous avez un dossier "Téléchargements" rempli de différents types de fichiers et vous voulez les organiser par type.

**Windows (PowerShell)** :
```powershell
.\exemple-script.ps1 -SourceFolder "C:\Utilisateurs\Moi\Téléchargements" -DestinationFolder "C:\Utilisateurs\Moi\Documents\Organisés" -OrganisationCritere "type"
```

**macOS/Linux (Bash)** :
```bash
./exemple-script.sh --source "/Users/Moi/Téléchargements" --destination "/Users/Moi/Documents/Organisés" --critere "type"
```

Résultat : Vos fichiers seront organisés dans des dossiers par type, par exemple :
```
Organisés/
  ├── Images/
  ├── Documents/
  ├── Videos/
  ├── Audio/
  ├── Archives/
  └── Autres/
```

### Scénario 3 : Prévisualiser l'organisation sans déplacer les fichiers

Vous voulez voir comment vos fichiers seraient organisés sans effectuer les changements.

**Windows (PowerShell)** :
```powershell
.\exemple-script.ps1 -SourceFolder "C:\Mes Documents" -DestinationFolder "C:\Documents Organisés" -ModeSimulation $true
```

**macOS/Linux (Bash)** :
```bash
./exemple-script.sh --source "/Mes Documents" --destination "/Documents Organisés" --simulation true
```

## Comment lire le rapport

Après l'exécution du script, un rapport HTML est généré (sauf si vous avez désactivé cette option). Ce rapport s'ouvre automatiquement dans votre navigateur web et contient :

1. **Résumé** : informations générales sur l'opération
   - Dossier source et destination
   - Critère d'organisation utilisé
   - Nombre de fichiers traités et ignorés

2. **Détails** : informations spécifiques selon le critère d'organisation
   - Pour l'organisation par **date** : nombre de fichiers par année et par mois
   - Pour l'organisation par **type** : nombre de fichiers par type avec graphiques
   - Pour l'organisation par **nom** : nombre de fichiers par première lettre

## Conseils d'utilisation

- **Faites une sauvegarde** de vos fichiers importants avant d'utiliser le script pour la première fois
- Utilisez le **mode simulation** (`-ModeSimulation $true` ou `--simulation true`) pour prévisualiser les changements
- Consultez le **rapport** pour vérifier que l'organisation correspond à vos attentes
- Pour les **grandes collections de fichiers**, prévoyez un peu de temps pour le traitement

## Adapter les scripts à vos besoins

Vous pouvez adapter ces scripts à vos besoins spécifiques :

### Organiser différents types de fichiers

Les scripts reconnaissent déjà de nombreux types de fichiers courants, mais vous pouvez les adapter pour des besoins spécifiques :

- **Photos professionnelles** : organisez-les par projet ou par client en modifiant le critère "nom"
- **Documents de travail** : créez une organisation par projet ou par département
- **Collection musicale** : organisez par artiste, genre ou année

### Automatiser l'organisation régulière

Vous pouvez configurer ces scripts pour qu'ils s'exécutent régulièrement :

- **Windows** : utilisez le Planificateur de tâches pour exécuter le script PowerShell chaque semaine
- **macOS/Linux** : configurez une tâche cron pour exécuter le script Bash à intervalles réguliers

## Résolution des problèmes courants

### Le script ne démarre pas

- **Windows** : Assurez-vous que l'exécution des scripts PowerShell est autorisée sur votre système
  ```powershell
  Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
  ```

- **macOS/Linux** : Vérifiez que le script a les permissions d'exécution
  ```bash
  chmod +x exemple-script.sh
  ```

### Erreurs de permission

Si vous rencontrez des erreurs de permission lors de l'accès aux fichiers :

- **Windows** : Exécutez PowerShell en tant qu'administrateur
- **macOS/Linux** : Utilisez `sudo` pour exécuter le script avec des privilèges élevés (avec précaution)

### Le rapport ne s'ouvre pas automatiquement

Si le rapport ne s'ouvre pas automatiquement après l'exécution :

1. Recherchez un fichier nommé `Rapport_Organisation_[date].html` dans le dossier du script
2. Ouvrez ce fichier manuellement avec votre navigateur web

## Conclusion

Ces scripts d'organisation de fichiers sont conçus pour vous faire gagner du temps et vous aider à maintenir vos fichiers bien organisés. Ils sont suffisamment flexibles pour s'adapter à différents besoins et types de fichiers.

N'hésitez pas à les utiliser régulièrement pour maintenir vos dossiers en ordre !