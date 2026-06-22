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

6. **Corriger la SOURCE, pas seulement la sortie (HARD, mandat user 2026-06-22).** Quand un secret ou un **prefixe de cle** apparait dans un OUTPUT committe (cellule notebook executee, log), redacter l'output **seul** = **fix-symptome INTERDIT** : a la prochaine re-execution la cellule **source** re-imprime le materiel. Il faut **corriger la source** (ou la **tracker par issue** si le fix est hors-scope de la PR). Distinguer deux cas :
   - **env-noise** (chemins filesystem imprimes dynamiquement, racine de checkout, AppData, pip "already satisfied", ipykernel/nuget regeneres a chaque exec) -> **scrub de l'output EST le bon fix** (rien dans la source a corriger).
   - **source-leak** (code source qui **imprime ou hardcode** du materiel sensible : `print(f"...{key[:8]}...")`, `print(f"KEY={key}")`, `os.environ.get("VAR", "<machine-path-default>")`) -> **re-leak garanti** -> **corriger la source** (masquer : `'configuree' if key else '(non configuree)'`, jamais `key[:N]` ; supprimer le default machine-path). Incident fondateur du masque `key[:N]` : lignee de PRs redaction-only #3903 (cause racine ratee) corrigee par #3913 (2026-06-22).

   **Critere bot-review (HARD)** : toute PR qui redacte un secret / prefixe-de-cle dans un output committe **DOIT** identifier ET corriger (ou tracker par issue) la cellule source qui imprime ce materiel — sinon `CHANGES_REQUESTED`. Une redaction-output **seule** = fix-symptome = refus. Un `APPROVED` dessus = complaisance (cf [pr-review-discipline.md](pr-review-discipline.md) §H). L'echec 2026-06-22 = coordination (dispatch scope "scrub N fichiers" au lieu de "corriger les scripts") **ET** bots ayant laisse passer la lignee redaction-only.

`.gitignore` seul est insuffisant : il protege les fichiers dedies, pas les literaux inline. Le scanner CI gitleaks est installe (`.pre-commit-config.yaml` v8.21.2 + `.github/workflows/secret-scan.yml`), mais ne couvre pas tous les patterns : la vigilance reste obligatoire (revue body/contenu PR, lecture `gh pr view --json files`, controle des `os.getenv("KEY", "...")` literal-default).

Detail (incident, fix structurel, regex de detection, postmortem template) : [docs/secrets-and-coord-detail.md](../../docs/reference/secrets-and-coord-detail.md#1-secrets-hygiene--content-based-pas-path-based).

## Centralisation — `.secrets/master.env` (source unique)

Les secrets **partages** (HF, OpenAI, Anthropic, Civitai, API keys par service, tokens ComfyUI) vivent dans **`.secrets/master.env`** (gitignored). Le script [`scripts/secrets/render_envs.py`](../../scripts/secrets/render_envs.py) propage ces valeurs vers chaque `.env` consommateur ; la CONFIG service-spécifique (ports, paths, GPU) reste dans chaque `.env`.

- **Rotater un secret** = éditer `master.env` + `python scripts/secrets/render_envs.py` + `docker compose restart` (OBLIGATOIRE pour ComfyUI-Login : le hash bcrypt n'est régénéré depuis l'env qu'au restart, pas à chaud — source du "drift" qui a fait croire à tort à une clé perdue en juin 2026).
- **Audit drift** = `python scripts/secrets/render_envs.py --check` (exit 1 si un `.env` diffère de master).
- Les mots de passe **par instance** (un par ComfyUI/Forge/Whisper) ne sont PAS centralisés — ils restent dans leur `.env` service.

Detail complet (inventaire, rotation, règle restart, incident fondateur) : [docs/genai/secrets-management.md](../../docs/genai/secrets-management.md).

## Voir aussi

- [.claude/rules/git-workflow.md](git-workflow.md) — no direct main push
- [docs/env-python-reparation.md](../../docs/reference/env-python-reparation.md) — env discipline (regle F)
- [docs/genai/secrets-management.md](../../docs/genai/secrets-management.md) — centralisation master.env + render
