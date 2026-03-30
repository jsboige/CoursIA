# Guide Agent - Demo 1 : Première Session

Ce guide est destiné aux formateurs et agents IA pour accompagner les apprenants.

## Objectifs de la démo

- Valider l'installation de Claude Code CLI
- Configurer correctement OpenRouter
- Réaliser une première interaction réussie
- Comprendre les différents modes d'utilisation

## Points de vigilance

### Installation

1. **Node.js** doit être en version 18+
   - Commande de vérification : `node --version`
   - Si version < 18, faire upgrader avant de continuer

2. **Droits d'installation npm**
   - Sur Linux/Mac, peut nécessiter `sudo`
   - Sur Windows, ouvrir PowerShell en administrateur si besoin

3. **PATH système**
   - Si `claude` n'est pas trouvé après installation, vérifier :
     ```bash
     npm bin -g  # Affiche le dossier des binaires npm
     ```
   - Ajouter ce dossier au PATH si nécessaire

### Configuration OpenRouter

1. **Clé API**
   - Format attendu : `sk-or-v1-...`
   - Vérifier que la clé est active sur openrouter.ai

2. **Variables d'environnement**
   - Les 3 variables DOIVENT être définies
   - `ANTHROPIC_API_KEY` doit être vide (string vide, pas absent)

3. **Persistance**
   - Rappeler aux apprenants d'ajouter les exports dans leur profil shell
   - Sinon, à redéfinir à chaque nouveau terminal

## Déroulé suggéré

### Phase 1 : Vérifications préalables (5 min)

```bash
# Vérifier Node.js
node --version

# Vérifier npm
npm --version
```

Si problème, résoudre avant de continuer.

### Phase 2 : Installation (5 min)

```bash
npm install -g @anthropic-ai/claude-code
claude --version
```

### Phase 3 : Configuration (10 min)

Guider l'apprenant pour :
1. Récupérer sa clé OpenRouter
2. Définir les variables d'environnement
3. Tester avec `/status`

### Phase 4 : Première interaction (15 min)

Encourager l'apprenant à :
1. Poser une question simple
2. Poser une question de suivi
3. Tester `/help` et `/clear`

### Phase 5 : Exercice (10 min)

Accompagner la création du fichier `mes-premieres-questions.md`.

## Réponses types aux questions fréquentes

### "Pourquoi utiliser OpenRouter plutôt que l'API Anthropic directe ?"

OpenRouter offre :
- Accès à plusieurs modèles (Claude, GPT, Gemini...)
- Tarification à l'usage sans abonnement
- Interface unifiée
- Parfait pour l'apprentissage

### "Quelle est la différence entre les modèles ?"

| Modèle | Tokens/sec | Coût relatif | Usage |
|--------|-----------|--------------|-------|
| Haiku | Très rapide | $ | Questions simples |
| Sonnet | Rapide | $$ | Usage quotidien |
| Opus | Modéré | $$$ | Tâches complexes |

### "Mes conversations sont-elles enregistrées ?"

- Historique local uniquement (dossier `.claude/`)
- Pas de persistance côté serveur au-delà de la session
- Possibilité de `/clear` pour effacer

## Critères de validation

L'apprenant a réussi cette démo si :

- [ ] `claude --version` fonctionne
- [ ] `/status` montre une connexion OK
- [ ] A posé au moins 3 questions différentes
- [ ] Comprend la différence entre `claude` et `claude -p`
- [ ] A créé le fichier `mes-premieres-questions.md`

## Erreurs courantes

### Erreur : "Cannot find module"

**Cause** : Installation npm corrompue

**Solution** :
```bash
npm cache clean --force
npm install -g @anthropic-ai/claude-code
```

### Erreur : "EACCES permission denied"

**Cause** : Droits insuffisants

**Solution Linux/Mac** :
```bash
sudo npm install -g @anthropic-ai/claude-code
```

**Solution Windows** : Ouvrir PowerShell en administrateur

### Erreur : "Invalid API key"

**Cause** : Clé mal copiée ou expirée

**Solution** :
1. Vérifier la clé sur openrouter.ai
2. Vérifier l'absence d'espaces dans la variable
3. Régénérer si nécessaire

## Ressources pour le formateur

- [Troubleshooting officiel](https://docs.anthropic.com/en/docs/claude-code/troubleshooting)
- [OpenRouter documentation](https://openrouter.ai/docs)
