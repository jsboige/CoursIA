# Secrets hygiene — content-based, pas path-based

S'applique a **tous les agents** ecrivant du code dans le repo.

## Regle HARD

1. **Secrets vivent UNIQUEMENT dans des fichiers gitignored** (`.env`, `.secrets/<name>`).

2. **JAMAIS de literaux inline** dans `.py`/`.ipynb`/`.cs`/`.json`/`.yml`/`.md` :
   - `API_KEY = "sk-..."`, `TOKEN = "ghp_..."`, `KEY = "AIza..."`
   - **`os.getenv("KEY", "<literal-secret-as-fallback>")`** — pattern recurrent qui a deja leak (incident 2026-05-14, commit `b34e3a05`)
   - URLs avec credentials : `https://user:password@host/...`
   - Tokens en commentaires meme en exemple

3. **Pattern correct** : `os.getenv("KEY")` sans default, `raise ValueError(...)` si manquant.

4. **Pas de direct push sur `main`** (cf [git-workflow.md](git-workflow.md)) — contourne la PR review.

5. **Si leak detecte** : NE PAS `git revert` (l'historique garde le secret). **Rotater la cle immediatement** chez le provider, creer une branche clean via cherry-pick. Postmortem agent responsable obligatoire.

`.gitignore` seul est insuffisant : il protege les fichiers dedies, pas les literaux inline. En attendant un secret scanner CI, la vigilance est manuelle.

Detail (incident, fix structurel, regex de detection, postmortem template) : [docs/secrets-and-coord-detail.md](../../docs/secrets-and-coord-detail.md#1-secrets-hygiene--content-based-pas-path-based).

## Voir aussi

- [.claude/rules/git-workflow.md](git-workflow.md) — no direct main push
- [docs/env-python-reparation.md](../../docs/env-python-reparation.md) — env discipline (regle F)
