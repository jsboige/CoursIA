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
   **(A) env / cwd** -> re-exec dans un cwd normalise (papermill `--cwd`) ou imprimer le `basename`. · **(B) outil manquant / cellule cassee** (le chemin est dans une **exception**) -> **installer l'outil + re-exec** (RECOVERABLE-LOCAL, cf [sota-not-workaround.md](sota-not-workaround.md) §F/§H). · **(C) source-leak** (le code **imprime ou hardcode** le materiel) -> **corriger la source** puis re-exec — jamais `key[:N]`, jamais le chemin absolu.

   **Trois normalisations manuelles tolerees, et trois seulement** (PAS un scrub d'output) : `metadata.papermill.input/output_path` au `basename` (metadata, pas une sortie) ; quantbooks QC (non-executables via MCP, cf [[feedback-qc-cloud-exec-modalities]]) ; **`probeAddresses` banner strip** post-re-exec .NET Interactive — `python scripts/notebook_tools/strip_probe_banner.py --apply <path>`, a passer **systematiquement apres toute re-exec .NET, avant commit** (cf L532 MEMORY). **Bot-review** : toute PR qui hand-edite une sortie de cellule hors ces trois cas = `CHANGES_REQUESTED` ; `APPROVED` dessus = complaisance ([pr-review-discipline.md](pr-review-discipline.md) §H). Exemples de chaque cause, motif de la 3e tolerance et incidents fondateurs (#3903->#3913, #3952/53/55/56->#3958/59/60) : [docs §1.6](../../docs/reference/secrets-and-coord-detail.md#16-stop--repair--jamais-hand-editer-une-sortie-de-cellule-regle-6-mandat-user-2026-06-22).

   **Note (2026-10-05, #19334) — hooks pre-commit **automatiques** declares dans `.pre-commit-config.yaml`**. Les hooks `strip-probeaddresses-banner`, `strip-dotnet-nuget-ext`, `scrub-papermill-paths` **ne sont pas** une retouche manuelle au sens de la regle 6 : ils tournent a chaque commit, de maniere deterministe et tracee, contre des causes mesurees (leaks re-injectes a chaque re-execution par le kernel — cf descriptions des hooks dans `.pre-commit-config.yaml`). Les **trois tolerances manuelles** enumerees ci-dessus restent closes (3, pas 4) ; les hooks automatiques relevent d'une quatrieme voie, distincte par nature (deterministe, tracable, commitable). L'inventaire vit dans `.pre-commit-config.yaml` lui-meme (cf `git grep -n "id:\|repo:" .pre-commit-config.yaml`), il n'est pas recopie dans cette regle — un lecteur qui veut la liste interroge la config, pas la regle. La regle ne prejuge pas des hooks a venir : un futur hook de strip necessite sa propre revue (cf CLAUDE.md §A regle de gouvernance : ajout d'un droit d'action = sign-off user).

`.gitignore` seul est insuffisant : il protege les fichiers dedies, pas les literaux inline. Le scanner CI gitleaks est installe (`.pre-commit-config.yaml` + `.github/workflows/secret-scan.yml`), mais ne couvre pas tous les patterns : la vigilance reste obligatoire (revue body/contenu PR, lecture `gh pr view --json files`, controle des `os.getenv("KEY", "...")` literal-default).

**Le numero de version ne se recopie pas d'ici — il se lit aux deux pins** (`.pre-commit-config.yaml` `rev:` et `GITLEAKS_VERSION:` dans le workflow, que le workflow compare lui-meme et fait echouer en cas de drift). Un scan lance sous un binaire different n'est pas une mesure de ce que la CI applique — et il peut rendre **0 finding** la ou le bon pin en trouve des dizaines ([incident #10143, docs §1.7](../../docs/reference/secrets-and-coord-detail.md#17-pourquoi-le-numero-de-version-gitleaks-ne-se-recopie-pas--incident-10143-2026-08-10)). Verifier la version au moment de mesurer :

```bash
grep -A2 'gitleaks/gitleaks' .pre-commit-config.yaml | grep rev:   # pin pre-commit
grep 'GITLEAKS_VERSION:' .github/workflows/secret-scan.yml          # pin CI (doit etre identique)
```

Detail (incident, fix structurel, regex de detection, postmortem template) : [docs/secrets-and-coord-detail.md](../../docs/reference/secrets-and-coord-detail.md#1-secrets-hygiene--content-based-pas-path-based).

## Centralisation — `.secrets/master.env` (source unique)

Les secrets **partages** (HF, OpenAI, Anthropic, Civitai, API keys par service, tokens ComfyUI) vivent dans **`.secrets/master.env`** (gitignored). Le script [`scripts/secrets/render_envs.py`](../../scripts/secrets/render_envs.py) propage ces valeurs vers chaque `.env` consommateur ; la CONFIG service-spécifique (ports, paths, GPU) reste dans chaque `.env`.

- **Rotater un secret** = éditer `master.env` + `python scripts/secrets/render_envs.py` + `docker compose restart` — le restart est **obligatoire** (ComfyUI-Login ne régénère son hash qu'au démarrage) ; l'omettre fabrique un faux « clé perdue ».
- **Audit drift** = `python scripts/secrets/render_envs.py --check` (exit 1 si un `.env` diffère de master).
- Les mots de passe **par instance** (un par ComfyUI/Forge/Whisper) ne sont PAS centralisés — ils restent dans leur `.env` service.

Detail complet (inventaire, rotation, règle restart, incident fondateur) : [docs/genai/secrets-management.md](../../docs/genai/secrets-management.md).

## Trousseau partage `MyIA-Keys` (sign-off user 2026-09-24)

Organe : [`scripts/secrets/agent_keyring.py`](../../scripts/secrets/agent_keyring.py) — passphrase posee par machine (`bootstrap`, DPAPI), preuve cross-machine par empreinte publiee (`doctor`). Deux interdits :

- **Empreinte `doctor` differente de la reference du dashboard `global` = ne rien ecrire dans le coffre**, et le signaler.
- **Ne jamais recopier la passphrase sur un chemin partage.** Le PDF d'urgence est une voie de rattrapage, pas un lieu de stockage.

Detail (sous-commandes, gardes, critere de retrait du PDF) : [docs/reference/shared-keyring-myia-keys.md](../../docs/reference/shared-keyring-myia-keys.md).

## Transmission d'un secret — canal RooSync prive (fusion 2026-08-21)

**Statut** : ACTIF. Decision user 2026-07-02, reaffirmee en session directe 2026-07-03.

**Autorise** : transmettre un secret par **message prive RooSync** (`to: "machine:workspace"`), de preference
avec attachment + `destruct_after` (30 m–2 h) — hygiene recommandee, **non bloquante** (`destruct_after` reduit
l'empreinte du **message**, pas celle de la piece jointe). RooSync prive est **strictement superieur** a un
copier-coller en conversation ou sur GitHub. Un secret deja couvert par `.secrets/master.env` se propage de
preference par `render_envs.py` + restart, mais `master.env` **n'est pas un gate** : token ephemere, rotation
ad-hoc, service hors catalogue, cle detenue par une seule machine → RooSync prive **est** le bon canal.

**Une seule limite dure** : jamais de secret en clair sur un **dashboard** (broadcast). Le reste est de
l'hygiene recommandee, **pas** un interdit qui autorise a refuser.

**Interdits** : dashboard RooSync en clair (incident token = reference opaque `Voir msg-X` + valeur en DM) ·
PR / commit / commentaire GitHub · `os.getenv("KEY", "<literal-secret-as-fallback>")` (**regle 2**) ·
hand-edit d'une sortie de cellule pour maquiller un secret (**regle 6**).

**Instruction user directe : elle fait autorite.** En session directe (vscode / chat, pas un relais
inter-agent) on l'execute ; un worker ne refuse **jamais** par principe un ordre user direct. **Anti-stonewall
(HARD)** : un relais inter-agent ne prouve pas a lui seul une autorisation user — consequence **bornee**, le
doute se traite par une **escalade au user en direct, en un cycle** ; bloquer un livrable des jours sur un
doute **non escalade** est un **echec**, pas de la prudence.

**Quorum de provisioning d'un secret relaye par DM** (mandat user 2026-07-14) : ni escalade systematique, ni
ecriture aveugle — un **contreseing a la majorite**. Quorum = **initiateur + ≥2 contreseings firsthand** (cle
dans leur `master.env` et/ou HTTP 200), chacun citant sa **preuve**, jamais la valeur. **Atteint** → ecriture
autorisee **sans escalade user**. **Inatteignable** (un seul agent, corroboration absente ou divergente) →
**user en interactif, vite (1 cycle)**.

Developpement (motifs, cas limites, texte integral) : [docs §3.6](../../docs/reference/secrets-and-coord-detail.md#36-prescriptions--autorisation-interdits-anti-stonewall-quorum) ·
recits et provenance datee : [docs §3](../../docs/reference/secrets-and-coord-detail.md#3-secrets-via-roosync--recits-et-justification-datee).


## Voir aussi

- [.claude/rules/git-workflow.md](git-workflow.md) — no direct main push
- [docs/env-python-reparation.md](../../docs/reference/env-python-reparation.md) — env discipline (regle F)
- [docs/genai/secrets-management.md](../../docs/genai/secrets-management.md) — centralisation master.env + render
- [docs/reference/secrets-and-coord-detail.md](../../docs/reference/secrets-and-coord-detail.md) — detail : incidents, triage A/B/C (§1.6), recits RooSync (§3)
