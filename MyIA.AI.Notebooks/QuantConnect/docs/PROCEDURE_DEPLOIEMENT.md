# Procédure de Déploiement - Local vers Orga Perso

**Organisation cible**: Jean-Sylvain Boige (Researcher PAID)
**Source**: `c:\dev\CoursIA\MyIA.AI.Notebooks\QuantConnect\projects\`

---

## Méthode 1: Via Playwright (Recommandé pour tests)

### Prérequis
```bash
# Vérifier que Playwright est installé
npx playwright install chrome
```

### Étapes

1. **Ouvrir le projet QuantConnect dans le navigateur**
   ```javascript
   // Via Playwright
   await page.goto("https://www.quantconnect.com/terminal");
   ```

2. **Créer un nouveau projet**
   - Cliquer sur "New Algorithm"
   - Nommer le projet (ex: `CSharp-BTC-EMA-Cross`)

3. **Copier le code local vers le projet**
   - Ouvrir le fichier local : `projects/CSharp-BTC-EMA-Cross/Main.cs`
   - Copier le contenu
   - Coller dans l'éditeur QC cloud

4. **Compiler et tester**
   - Cliquer sur "Cloud Build" (Ctrl+Shift+B)
   - Attendre la confirmation de compilation
   - Lancer un backtest pour valider

---

## Méthode 2: Via lean-cli (Recommandé pour production)

### Prérequis
```bash
# lean-cli doit être configuré avec l'organisation Researcher
lean cloud whoami
# Doit afficher: Organization: Jean-Sylvain Boige (Researcher)
```

### Étapes

1. **Créer le projet cloud depuis le local**
   ```bash
   cd C:\dev\CoursIA\MyIA.AI.Notebooks\QuantConnect\projects\CSharp-BTC-EMA-Cross
   lean cloud push --name "CSharp-BTC-EMA-Cross" --open
   ```

2. **Vérifier la compilation**
   ```bash
   lean cloud compile "CSharp-BTC-EMA-Cross"
   ```

3. **Lancer un backtest de validation**
   ```bash
   lean cloud backtest "CSharp-BTC-EMA-Cross"
   ```

---

## Méthode 3: Via MCP QC (Quand disponible)

Le serveur MCP `qc-mcp` n'est actuellement pas configuré sur po-2024. Quand il sera disponible:

```python
# Via MCP tools
mcp__qc_mcp__create_project({
    "name": "CSharp-BTC-EMA-Cross",
    "language": "CSharp"
})

mcp__qc_mcp__update_file_contents({
    "projectId": 12345,
    "name": "Main.cs",
    "content": open("projects/CSharp-BTC-EMA-Cross/Main.cs").read()
})
```

---

## Check-list de Déploiement

Pour chaque projet à déployer:

- [ ] Créer le projet cloud avec le bon nom
- [ ] Copier tous les fichiers nécessaires (Main.cs + éventuels helpers)
- [ ] Compiler sans erreur (BuildSuccess)
- [ ] Lancer un backtest de validation
- [ ] Vérifier que les backtests s'exécutent correctement
- [ ] Documenter le Project ID dans WORKSPACES.md

---

## Structure des Projets C#

### CSharp-BTC-EMA-Cross
```
CSharp-BTC-EMA-Cross/
├── Main.cs           # Fichier principal
└── (pas de dépendances externes)
```

### CSharp-CTG-Momentum
```
CSharp-CTG-Momentum/
├── Main.cs           # Fichier principal
└── (pas de dépendances externes)
```

---

## Prochaines Actions

1. **Nettoyer le doublon** Crypto-MultiCanal (ID: 28733256)
2. **Déployer** CSharp-BTC-EMA-Cross
3. **Déployer** CSharp-CTG-Momentum
4. **Mettre à jour** WORKSPACES.md avec les nouveaux Project IDs
