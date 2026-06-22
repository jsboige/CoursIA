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

6. **NE JAMAIS hand-editer une SORTIE de cellule committee — corriger la cause et RE-EXECUTER (HARD, mandat user 2026-06-22).** Scrubber / redacter / maquiller a la main une **sortie de cellule** (le champ `outputs` d'une cellule code = le compte-rendu de ce que le code a reellement produit) est **BANNI** : c'est **falsifier la preuve d'execution = malhonnete**. A la prochaine re-execution le materiel resaute de toute facon. Quoi que contienne l'output indesirable (secret, **prefixe de cle**, **chemin machine**, render casse, bruit), la **seule** voie honnete est d'en **corriger la cause** puis de **RE-EXECUTER** (regle ancestrale **Stop & Repair**, cf CLAUDE.md section F ; [[feedback-no-cell-output-scrubbing]]). Si le fix est hors-scope de la PR : **tracker par issue**, ne PAS scrubber en attendant. La cause tombe dans l'un de TROIS cas (le scanner ne les distingue PAS — c'est a l'agent de trier la CAUSE, pas de toucher l'output) :
   - **(A) env / cwd** (chemins filesystem benins imprimes dynamiquement : racine de checkout, AppData, pip "already satisfied", ipykernel/nuget regeneres) -> **re-executer dans un cwd normalise** (papermill `--cwd <dir-du-notebook>`) ou corriger la source pour imprimer le `basename`/chemin relatif. **Pas de scrub manuel de la sortie.**
   - **(B) outil manquant / cellule cassee** (le chemin est dans un **message d'erreur / exception / "introuvable"** : `process 'dot' ... introuvable` + `.gv save path` quand Graphviz n'est pas installe, `FileNotFoundException`, assembly conflict) -> **cellule en ERREUR maquillee. INSTALLER l'outil + re-exec** (RECOVERABLE-LOCAL, cf [sota-not-workaround.md](sota-not-workaround.md) §F/§H), jamais scrubber le chemin dans l'exception.
   - **(C) source-leak** (code source qui **imprime ou hardcode** du materiel : `print(f"...{key[:8]}...")`, `print(f"KEY={key}")`, `Console.WriteLine($"...{filePath}")`, `os.environ.get("VAR", "<machine-path-default>")`) -> **corriger la source** (masquer : `'configuree' if key else '(non configuree)'`, jamais `key[:N]`/`key[-N:]` ; imprimer le `basename`, pas le chemin absolu ; supprimer le default machine-path) **puis re-exec**.

   **Seules normalisations manuelles tolerees (PAS un scrub d'output)** : (1) **`metadata.papermill.input/output_path`** — c'est de la **metadata notebook, PAS une sortie de cellule** ; la mettre au `basename` est OK (ideal : la produire propre au moment de l'exec via input/output relatifs). (2) **Quantbooks QC** — **exception notable** : le MCP qc-mcp ne permet toujours PAS de les executer, ils passent par le Research Assistant (Playwright / lean-cli), la manipulation manuelle des sorties y est la realite acceptee (cf [[feedback-qc-cloud-exec-modalities]]). **Pour tout le reste, execution reelle obligatoire.**

   **Tell infaillible** : sortie de cellule indesirable -> corrige la CAUSE (A env/cwd, B installe l'outil, C corrige la source) + **re-exec**, jamais hand-edit. `metadata.papermill` ou quantbook QC -> seules normalisations manuelles tolerees. Incidents fondateurs : masque `key[:N]` lignee redaction-only #3903 corrigee par #3913 ; scrub-output-paths Probas/Infer+ML.Net #3952/#3953/#3955/#3956 (Graphviz `dot` jamais installe + `WriteLine($"...{filePath}")`) corriges par re-exec reel #3958/#3959/#3960 (2026-06-22).

   **Critere bot-review (HARD)** : toute PR qui **hand-edite une sortie de cellule** (scrub d'un secret / prefixe-de-cle / chemin machine / render casse) hors `metadata.papermill` et hors quantbook QC = `CHANGES_REQUESTED`. Une redaction-output **seule**, sans correction de la cause + re-exec, = falsification = refus. Un `APPROVED` dessus = complaisance (cf [pr-review-discipline.md](pr-review-discipline.md) §H). L'echec 2026-06-22 = coordination (dispatch scope "scrub N fichiers" au lieu de "corriger les scripts / l'env") **ET** bots ayant laisse passer la lignee redaction-only.

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
