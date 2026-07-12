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

6. **NE JAMAIS hand-editer une SORTIE de cellule committee — corriger la cause et RE-EXECUTER (HARD, mandat user 2026-06-22).** Scrubber / redacter / maquiller a la main une **sortie de cellule** (`outputs` = compte-rendu de ce que le code a reellement produit) est **BANNI** : c'est **falsifier la preuve d'execution = malhonnete**, et le materiel resaute a la prochaine exec. Quoi que contienne l'output indesirable (secret, prefixe de cle, chemin machine, render casse), la **seule** voie honnete = **corriger la cause + RE-EXECUTER** (Stop & Repair, cf CLAUDE.md section F ; [[feedback-no-cell-output-scrubbing]]). Fix hors-scope PR : **tracker par issue**, ne PAS scrubber en attendant. Trier la CAUSE (le scanner ne la distingue pas) :
   - **(A) env / cwd** (chemins benins dynamiques) -> re-exec dans un cwd normalise (papermill `--cwd <dir>`) ou imprimer le `basename`.
   - **(B) outil manquant / cellule cassee** (chemin dans une exception `... introuvable`, `FileNotFoundException`) -> **INSTALLER l'outil + re-exec** (RECOVERABLE-LOCAL, cf [sota-not-workaround.md](sota-not-workaround.md) §F/§H).
   - **(C) source-leak** (code qui imprime/hardcode : `print(f"...{key[:8]}...")`, `WriteLine($"...{filePath}")`, `os.getenv("VAR","<machine-path>")`) -> **corriger la source** (`'configuree' if key else '(non configuree)'`, jamais `key[:N]` ; `basename` pas chemin absolu) **puis re-exec**.

   **Seules normalisations manuelles tolerees** (PAS un scrub d'output) : `metadata.papermill.input/output_path` au `basename` (metadata, pas une sortie) ; quantbooks QC (non-executables via MCP, cf [[feedback-qc-cloud-exec-modalities]]). **Bot-review** : toute PR qui hand-edite une sortie de cellule hors ces deux cas = `CHANGES_REQUESTED` ; `APPROVED` dessus = complaisance ([pr-review-discipline.md](pr-review-discipline.md) §H). Triage A/B/C complet + incidents fondateurs (#3903->#3913, #3952/53/55/56->#3958/59/60) : [docs §1.6](../../docs/reference/secrets-and-coord-detail.md#1-secrets-hygiene--content-based-pas-path-based).

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
