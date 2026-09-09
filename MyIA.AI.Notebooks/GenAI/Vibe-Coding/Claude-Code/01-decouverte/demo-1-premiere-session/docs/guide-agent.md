# Guide Agent - Demo 1 : Première Session

Ce guide est destiné aux formateurs et agents IA pour accompagner les apprenants.

## Objectifs de la démo

- Valider l'installation de Claude Code CLI
- Configurer correctement OpenRouter
- Réaliser une première interaction réussie
- Comprendre les différents modes d'utilisation

## Points de vigilance

### Installation

1. **Chemin canonique : installation native** (défaut de la documentation officielle Anthropic, Node.js non requis)
   - Le binaire vit sous `~/.local/bin`, mise à jour via `claude update`

2. **Node.js 18+ requis uniquement pour** : le proxy OpenRouter (brique d'accès aux modèles) et l'alternative npm
   - Commande de vérification : `node --version`
   - Si version < 18 et poste sans Node : privilégier l'installation native de Claude Code ; le proxy reste un paquet npm (voir le quickstart)

3. **Jamais `sudo npm install -g`** (risque de permissions root sur les paquets globaux)
   - Alternative propre : `npm config set prefix ~/.npm-global` puis ajouter `~/.npm-global/bin` au PATH

4. **PATH système**
   - Si `claude` n'est pas trouvé après installation native : vérifier que `~/.local/bin` est dans le PATH, puis redémarrer le terminal
   - Si installation via npm : `npm bin -g` affiche le dossier des binaires npm, à ajouter au PATH si nécessaire

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
# Vérifier Node.js (requis pour le proxy OpenRouter et l'alternative npm seulement)
node --version
```

Node absent n'est pas bloquant pour l'installation native de Claude Code ; il le devient au moment de configurer le proxy OpenRouter (Étape 2 du README). Résoudre avant de continuer dans ce cas.

### Phase 2 : Installation (5 min)

Chemin canonique : installation native (voir [README de la démo](../README.md), Étape 1). Alternative npm uniquement si le poste l'exige :

```bash
# Alternative npm uniquement
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

### Erreur : "Cannot find module" (si vous avez utilisé l'alternative npm)

**Cause** : Installation npm corrompue

**Solution** :
```bash
npm cache clean --force
npm install -g @anthropic-ai/claude-code
```

Avec l'installation native, cette erreur ne se produit pas — si elle apparaît, repartir de l'installateur officiel.

### Erreur : "EACCES permission denied" (si vous avez utilisé l'alternative npm)

**Cause** : Droits insuffisants sur le dossier global de npm

**Jamais `sudo npm install -g`** : les paquets appartiendraient à root et toute mise à jour future exigerait sudo.

**Solution Linux/Mac** : rediriger le préfixe npm vers votre espace utilisateur :
```bash
npm config set prefix ~/.npm-global
npm install -g @anthropic-ai/claude-code
# puis ajouter ~/.npm-global/bin au PATH
```

**Alternative plus simple** : repartir de l'installation native (chemin canonique), qui ne passe pas par npm.

**Solution Windows** : ouvrir PowerShell en administrateur, ou utiliser l'installation native

### Erreur : "Invalid API key"

**Cause** : Clé mal copiée ou expirée

**Solution** :
1. Vérifier la clé sur openrouter.ai
2. Vérifier l'absence d'espaces dans la variable
3. Régénérer si nécessaire

## Ressources pour le formateur

- [Troubleshooting officiel](https://docs.anthropic.com/en/docs/claude-code/troubleshooting)
- [OpenRouter documentation](https://openrouter.ai/docs)
