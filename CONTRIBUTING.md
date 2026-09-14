# Guide de contribution à CoursIA

Merci de votre intérêt pour contribuer au projet CoursIA ! Ce document fournit des lignes directrices pour contribuer efficacement à ce dépôt de ressources pédagogiques sur l'intelligence artificielle.

## Deux façons de contribuer

### 1. Signaler une erreur ou proposer une amélioration

Vous pouvez [ouvrir une issue](https://github.com/jsboige/CoursIA/issues/new?template=content-feedback.yml) pour :

- signaler une erreur, une coquille ou un lien obsolète ;
- suggérer une clarification ou une amélioration pédagogique ;
- proposer une source, un article, un outil ou un nouveau contenu à **distiller** dans un notebook.

Une Pull Request associée est facultative, mais toujours bienvenue. Une issue bien située, accompagnée si possible d'une source vérifiable et du résultat attendu, constitue déjà une contribution utile. Il n'est pas nécessaire de connaître le harnais interne du dépôt avant de participer.

### 2. Soumettre une correction d'exercice par Pull Request

Vous pouvez aussi résoudre un exercice proposé dans un notebook et soumettre votre correction par Pull Request. Indiquez précisément le notebook et l'exercice concernés, puis fournissez une solution exécutable accompagnée d'une courte explication du raisonnement.

Après validation :

1. la correction devient un **exemple guidé** dans le notebook ;
2. la contribution est créditée, avec le nom ou pseudonyme GitHub souhaité et un lien vers la Pull Request ;
3. un nouvel exercice non résolu, portant sur le même objectif et d'une difficulté comparable, est ajouté afin de préserver la progression pédagogique.

Les mainteneurs et leurs agents peuvent effectuer cette transformation lors de l'intégration. Vous n'avez donc pas à fabriquer vous-même l'exercice de remplacement ni à maîtriser toutes les conventions internes du dépôt.

## Comment vos contributions sont traitées

CoursIA est maintenu par une flotte d'agents IA coordonnée, sous supervision humaine. Le premier triage d'une issue ou d'une Pull Request, ainsi qu'une partie des réponses, peuvent donc être assurés par un agent.

Dans les deux modes de contribution, les agents doivent :

- répondre avec bienveillance et expliquer ce qu'ils ont vérifié ;
- distinguer les faits établis des points encore incertains ;
- aider à préciser ou tester la contribution plutôt que rejeter une demande imprécise ;
- escalader vers un mainteneur humain ou un spécialiste lorsqu'une décision, une source ou un risque dépasse leur périmètre.

La production agentique à grande échelle fait inévitablement apparaître des coquilles, des formulations perfectibles ou des régressions ponctuelles. Le même dispositif permet généralement de les détecter, de les suivre et de les corriger dans la durée. Merci de nous les signaler : la patience et la bienveillance mutuelles facilitent la réparation, sans jamais rendre une erreur acceptable ni définitive.

## 🌟 Types de contributions

Vous pouvez contribuer de plusieurs façons :

1. **Amélioration des notebooks existants** : correction d'erreurs, clarification d'explications, mise à jour de code obsolète
2. **Ajout de nouveaux notebooks** : création de contenu sur des sujets d'IA non encore couverts
3. **Documentation** : amélioration du README, ajout de commentaires dans le code, création de guides
4. **Correction de bugs** : résolution de problèmes dans les notebooks ou le code
5. **Améliorations techniques** : optimisation de l'environnement, ajout de fonctionnalités utiles

## 🚀 Processus de contribution

### 1. Préparation

1. **Forkez le dépôt** vers votre compte GitHub
2. **Clonez** votre fork localement
3. **Configurez l'environnement** en suivant les instructions du README.md

### 2. Développement

1. **Créez une branche** pour votre contribution :

   ```bash
   git checkout -b type/nom-court-descriptif
   ```
   Exemples : `feature/notebook-transformers`, `fix/ml-example-bug`, `docs/improve-readme`

2. **Effectuez vos modifications** en respectant les conventions du projet

3. **Testez vos modifications** :
   - Assurez-vous que les notebooks s'exécutent sans erreur
   - Vérifiez que le code est bien documenté
   - Validez que les explications sont claires et pédagogiques

### 3. Soumission

1. **Committez vos changements** avec des messages clairs et descriptifs :

   ```bash
   git commit -m "Type: description courte de la modification"
   ```
   Exemples : `"Add: notebook sur les Transformers"`, `"Fix: correction d'erreurs dans l'exemple ML.NET"`

2. **Poussez votre branche** vers votre fork :

   ```bash
   git push origin nom-de-votre-branche
   ```

3. **Créez une Pull Request** vers le dépôt principal
   - Décrivez clairement vos modifications
   - Référencez les issues concernées si applicable
   - Expliquez pourquoi cette contribution est utile

## 📝 Conventions et bonnes pratiques

### Structure des notebooks

- **En-tête clair** : Titre, description, objectifs d'apprentissage
- **Structure cohérente** : Introduction, contenu théorique, exemples pratiques, exercices, conclusion
- **Cellules bien organisées** : Alternance équilibrée de texte explicatif et de code
- **Progression pédagogique** : Du simple au complexe, avec des explications adaptées

### Style de code

- **Lisibilité** : Code clair et bien commenté
- **Cohérence** : Suivre les conventions de nommage existantes
- **Documentation** : Documenter les fonctions et classes importantes
- **Performance** : Éviter le code inefficace ou les anti-patterns

### Contenu pédagogique

- **Précision** : Informations exactes et à jour
- **Clarté** : Explications accessibles, même pour les débutants
- **Complétude** : Couvrir les aspects importants du sujet
- **Références** : Citer les sources et proposer des lectures complémentaires

## Tests et validation

Avant de soumettre votre contribution, assurez-vous que :

1. Tous les notebooks s'exécutent sans erreur
2. Le code est conforme aux standards du projet
3. Les explications sont claires et pédagogiquement pertinentes
4. Les dépendances sont correctement documentées

### Validation automatisee

Le depot dispose de scripts de validation pour verifier la qualite des notebooks :

```bash
# Validation structure (verifie metadata, outputs, kernel)
python scripts/notebook_tools/notebook_tools.py validate <path>

# Execution complete (Papermill, verifie que toutes les cellules passent)
python scripts/notebook_tools/notebook_tools.py execute <path>

# Analyse structure (stats cellules, outputs, index NIE)
python scripts/notebook_tools/notebook_tools.py analyze <path>
```

### Hooks pre-commit (securite + H.3)

Le depot embarque un harnais `pre-commit` (`.pre-commit-config.yaml`) qui
intercepte les problemes **au commit**, avant qu'un secret ou un notebook
non-execute n'entre dans l'historique :

- **gitleaks** (scanner de secrets) — un secret est arrete localement (edition,
  zero trace) plutot qu'apres le push (ou sa rotation devient obligatoire).
- **H.3 `check-null-exec`** — refuse un notebook dont une cellule code a
  `execution_count: null` + `outputs: []` (re-utilise les memes tolerances que
  le gate CI : kernels lean, QC Cloud, `metadata.pii_no_output`).
- hooks de strip (banniere probeAddresses, chemin cache NuGet, chemins
  papermill) + garde de rendu markdown.

Ces hooks sont **declare mais inactifs** tant que `pre-commit` n'est pas
installe. Activation idempotente (a faire une fois par machine) :

```bash
python scripts/setup_hooks.py            # installe pre-commit + wire le hook + warm gitleaks
python scripts/setup_hooks.py --check    # releve d'etat de la machine (harnais actif ?)
python scripts/setup_hooks.py --check-parity  # hooks declares vs executables
```

Verifier que le harnais arrete bien un faux secret :

```bash
echo 'AKIA000TEST000KEY000A' > /tmp/fake_secret.txt && git add /tmp/fake_secret.txt
git commit -m "test"   # doit echouer : gitleaks detecte le faux secret
git reset /tmp/fake_secret.txt && rm /tmp/fake_secret.txt
```

Execution manuelle sur tout le depot : `python -m pre_commit run --all-files`.

### Conventions notebooks

- **Pas d'erreur volontaire** : `raise NotImplementedError`, `assert False`, `1/0` sont interdits. Les cellules d'exercice utilisent `pass`, `print("Exercice a completer")`, ou `return None`
- **Outputs inclus** : les notebooks sont committes avec leurs outputs d'execution (sauf donnees sensibles)
- **Configuration documentée** : chaque nouvelle famille de notebooks inclut un `.env.example` sans secret qui décrit les variables requises
- **Pas d'emojis** dans le code, les noms de variables ou les fichiers genere

## 📚 Ressources utiles

- [Documentation Jupyter](https://jupyter.org/documentation)
- [Guide de style Python (PEP 8)](https://www.python.org/dev/peps/pep-0008/)
- [Guide de style C#](https://docs.microsoft.com/en-us/dotnet/csharp/fundamentals/coding-style/coding-conventions)
- [Documentation ML.NET](https://docs.microsoft.com/en-us/dotnet/machine-learning/)
- [Documentation OpenAI](https://platform.openai.com/docs/)

---

Merci de contribuer à rendre l'apprentissage de l'IA plus accessible et plus efficace !
