# Git Workflow Rules

## Branch Naming

```
type/name-short-descriptif
```
Examples: `feature/notebook-transformers`, `fix/ml-example-bug`, `docs/improve-readme`

## Commit Messages

```
Type: description courte de la modification
```
Examples: `Add: notebook sur les Transformers`, `Fix: correction d'erreurs dans l'exemple ML.NET`

## Safety Rules

### 🚨 CRITICAL - NEVER FORCE PUSH

**INCIDENT 2026-03-13** : Force push sur main a potentiellement écrasé des commits
- **Règle** : `git push --force` et `--force-with-lease` sont INTERDITS
- **Exception** : Uniquement urgence extrême avec validation explicite du user AU PRÉALABLE
- **Alternative** : Créer feature branch, cherry-pick, revert, ou nouveaux commits
- **Si PR nécessaire** : Créer feature branch FROM main, ne JAMAIS reset main

---

### Other Safety Rules

- NEVER commit without explicit user approval
- NEVER commit without explicit user approval
- If secrets are accidentally committed, create a new clean branch with cherry-pick rather than rewriting history
- Always commit incrementally to avoid needing force pushes
- Prefer adding specific files by name over `git add -A` or `git add .`

## Notebook-Specific

- When committing notebook files, always verify outputs are intentionally included
- Commit enrichment changes separately from execution output changes
- Use descriptive commit messages mentioning which notebooks were modified and why
