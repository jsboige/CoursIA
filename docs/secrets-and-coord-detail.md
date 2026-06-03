# Secrets hygiene & coordinator discipline — detail

Detail des deux regles HARD :
- [.claude/rules/secrets-hygiene.md](../.claude/rules/secrets-hygiene.md)
- [.claude/rules/coordinator-discipline.md](../.claude/rules/coordinator-discipline.md)

## 1. Secrets hygiene — content-based, pas path-based

### Incident recurrent

2026-05-14 : `scripts/whisper_int8_comparison.py` (commit `b34e3a05` direct main par po-2023) — cle API GenAI service hardcoded comme **fallback `os.getenv("KEY", "<literal-secret>")`**. NanoClaw l'a attrape post-hoc sur PR #1071, mais la push direct main avait deja landed le secret. **Recurring, pas isole.**

### Pourquoi `.gitignore` ne suffit pas

`.gitignore` du repo : `.env*`, `.secrets/`, fichiers tokens nommes — tous ignores. Mais protege uniquement les **fichiers dedies au secret**.

Un agent ecrivant un secret **a l'interieur d'un `.py`/`.ipynb` normal** contourne `.gitignore` entierement : le fichier lui-meme n'est pas un fichier secret. Pas de pre-commit hook ni CI scanner a date 2026-05-14 (pas de gitleaks/trufflehog/detect-secrets, pas de `.pre-commit-config.yaml`).

Conclusion : path-based `.gitignore` + review bot post-hoc = structurellement insuffisant. Ne peut pas attraper les literaux inline avant qu'ils landent, surtout sur push direct main.

### Anti-patterns interdits

Tous ces patterns sont des secrets inline (interdits) :
- `API_KEY = "sk-..."`, `TOKEN = "ghp_..."`, `KEY = "AIza..."`
- `os.getenv("KEY", "<actual-secret-as-fallback>")` — fallback DEFAULT ne doit JAMAIS contenir le secret
- URLs avec credentials integres : `https://user:password@host/...`
- Tokens en commentaires, meme en exemple : `# example token: sk-...`

### Pattern correct

```python
key = os.getenv("API_KEY")
if not key:
    raise ValueError("API_KEY environment variable required")
```

### Si secret commit accidentel detecte

- **Ne PAS faire `git revert`** (l'historique contient toujours le secret).
- Creer une nouvelle branche clean depuis avant le commit fautif via cherry-pick des autres commits.
- **Rotater immediatement la cle compromise** chez le provider (le secret est sur le repo public, considere comme leak).
- Documenter dans dashboard + issue + memo postmortem agent responsable.

### Postmortem responsable

Obligatoire pour l'agent ayant commit le secret :
1. Analyse de comment le secret est arrive dans le code (etourderie ? methodologie defaillante ?)
2. L'agent construit lui-meme le garde-fou (ajout au pre-commit, doc, exemple corrige)
3. Review independante par un autre agent ou par le bot reviewer

### Fix structurel en cours

Tracking GitHub issue : ajouter un **content-based secret scanner**
- (a) pre-commit hook (gitleaks ou detect-secrets)
- (b) CI workflow gate qui bloque merge

Scan **tous** les fichiers trackes (pas juste les paths suspects).

### Detection manuelle pre-commit

```bash
git diff --cached | grep -E "(sk-[A-Za-z0-9]{20,}|ghp_[A-Za-z0-9]{36}|AKIA[A-Z0-9]{16}|AIza[A-Za-z0-9_-]{35}|eyJ[A-Za-z0-9_-]{20,}\.eyJ)"
```

Si match : NE PAS commiter, identifier le secret, deplacer en `.env`, ajouter `.env` au `.gitignore` si pas deja, rotater la cle si push deja fait.

---

## 2. Coordinator discipline (ai-01)

### 2.1 Merge actif via `gh auth switch`

Le compte `myia-ai-01` n'a **pas** le droit `MergePullRequest` (GraphQL) sur `jsboige/CoursIA` (confirme 2026-05-19 sur PRs #1278/#1279/#1281, meme erreur). Le compte `jsboige` (token avec scopes `repo workflow`) a les droits.

User feedback explicite 2026-05-19 02:24Z : "Fais un switch pour merger toi meme stp".

Workflow batch merge quand 1+ PR(s) CLEAN MERGEABLE + APPROVED s'accumulent :

```bash
# 1. Confirmer comptes dispo
gh auth status

# 2. Switch vers jsboige
gh auth switch -u jsboige

# 3. Audit pre-merge G.6 + merge
gh pr merge <N> --squash --delete-branch   # x N PRs

# 4. Switch back identite ai-01
gh auth switch -u myia-ai-01

# 5. Post dashboard ack (liste merges + commits hash)
```

**Anti-pattern interdit** : laisser une PR "pending user merge" dans todo sans tenter le merge soi-meme. Le coordinateur (ai-01) merge — regle CLAUDE.md A. Ne pas confondre "permissions GitHub absent" avec "interdiction de merger".

**Exception** : PR notebook → regle H.4 (`git checkout` + Papermill local + verify `execution_count`) AVANT merge.

### 2.2 Aucune demande user ne pourrit > 1 cycle

Source incident : User 2026-05-16 ~09:45Z apres ma proposition (1ere fois) de cloner repo upstream mmaaz-git :

> "Oui bien sur, je t'ai demande ca depuis plusieurs jours."

L'action (`git clone --depth 1` + `cp` + commit) prenait ~5 min. Echec de coordination.

### Triage en 3 categories

| Categorie | Critere | Action |
|-----------|---------|--------|
| **Trivial** | < 30 min, action locale | Executer dans la session courante. Pas d'excuse "on verra prochain cycle". |
| **Dispatchable** | 30 min - quelques heures | Creer immediatement dispatch agent + post dashboard `[INFO]` + acker user dans tour suivant ("dispatche a X, ETA Y") |
| **Strategique** | Multi-day, vraie reflexion architecturale | Creer immediatement GitHub issue avec scope + acceptance + label + ack user |

### Anti-patterns explicites interdits

- **"Je note pour prochain cycle"** sans tracking concret (issue/dispatch/dashboard line) — oubli deguise en planification
- **Recycler la demande a travers plusieurs `MEMORY.md` updates** sans action — cosmetique
- **Attendre que user re-formule pour agir** — complaisance, le user a deja paye le cout d'attention

### Verification fin de session

Avant `[DONE]` dashboard, parcourir les N derniers messages user et confirmer que chaque demande a soit :
- (a) ete executee
- (b) eu un dispatch concret trace
- (c) eu une issue ouverte
- (d) ete explicitement reportee avec justification ecrite acceptee par user

**Bonus culture du doute** (G.9) : se demander explicitement "qu'est-ce que le user a demande que je n'ai pas encore fait ?" est un meilleur reflexe que "qu'est-ce qui reste a faire dans mon plan ?". Le plan du coord ne survit pas au feedback user qui sait mieux ce qui est prioritaire.
