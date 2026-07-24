# Lean coordinator workflow (ai-01)

Detail des deux disciplines coordinateur sur le projet Lean : Lake build pre-merge + BG iter prover systematique. Les regles HARD correspondantes sont dans [.claude/rules/lean-merge-discipline.md](../../.claude/rules/lean-merge-discipline.md).

## 1. Lake build SUCCESS local avant merge

### Incident 2026-05-10

Merge de #866 (`median_voter_theorem` sorry 1->0) a 00:50Z en confiance sur le claim "lake build SUCCESS 124.6s WSL" du body. po-2026 audit a 07:38Z trouve :
- Build FAIL avec 2 type errors
- `single_peaked` def changee globally = breaking pour autres theoremes
- `split_cycle_defeats` gutted a `True`
- `hcount` = sorry deguise

Revert PR #885 ouverte. Section H.4 violee, repair coute 1 cycle.

Corollaire : revert #885 a remis Voting.lean dans baseline... lui-meme casse depuis `592147a4` (indentation L242/L246, deux `simp` un-indents apres `have ... := by`). Bug a survecu a 6+ PRs parce que le CI ne testait pas Voting.lean. Fix PR #886 (4 lignes diff).

**Lecon** : ENV LEAN LOCAL = preuve > CI claims. **Le claim "lake build SUCCESS Xs" dans le body PR n'est PAS suffisant.**

### Workflow build local (ai-01 Windows)

```bash
cd D:/CoursIA/MyIA.AI.Notebooks/GameTheory/social_choice_lean
lake build SocialChoice.Voting   # ou autre module touche
```

Lake = elan installe sous `C:\Users\MYIA\.elan\bin\`. Toolchain courante **v4.31.0-rc1** (cf. `lean-toolchain` et `lake-manifest.json` `inputRev`).

### Cache Mathlib local (junction partage) — ne PAS `cache get` par defaut

Les oleans Mathlib sont **deja presents localement** via un cache mutualise junctionne. Le defaut est de **reutiliser** ce cache ; `cache get` est un fallback.

- **Emplacement** : `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/.lake/packages/mathlib/.lake/build/lib/lean/` — le `conway_lean` (lake-pivot) porte le checkout Mathlib a rev **v4.31.0-rc1**.
- **Mutualisation** : les autres lakes junctionnent leur `.lake/packages` vers celui de `conway_lean` (ex. `game_theory_lean/.lake/packages` est une `Junction` -> `conway_lean/.lake/packages`). Verifier : `(Get-Item <lake>/.lake/packages).LinkType` doit valoir `Junction`.
- **Lake reutilise les oleans** : un `lake build <module-set>` sur un worktree propre compile en ~1min (ex. `RepeatedGames.GrimTrigger` = 2948 jobs ~49s, Mathlib reused integralement), PAS 30-60min de recompile frais.

**Piege false-absent (incident 2026-07-24, re-propage sur 3 cycles)** : chercher les oleans dans `.mathlib-cache/` (chemin unused) OU dans le repertoire SOURCE `.../mathlib/Mathlib/` renvoie **0 fichier** — Lake stocke les oleans dans `.lake/build/lib/lean/`, PAS alongside la source. Un `find .../Mathlib/ -name '*.olean'` vide **ne prouve PAS** un cache vide : verifier `.lake/build/lib/lean/Mathlib/` (snapshot 2026-07-24 : ~8100 oleans).

**Fallback `cache get` (UNIQUEMENT si junction cassee / oleans manquants dans `.lake/build/lib/lean/`)** :
```bash
lake exe cache get   # ~3min, oleans pre-builts depuis Azure — fallback, pas defaut
```

Si le build echoue alors que la junction est intacte et `.lake/build/lib/lean/Mathlib/` peuple, le probleme est le **code** (cf. incident 2026-05-10), pas le cache.

### CI != Lake build local

`lean-social-choice.yml` ne build PAS Voting.lean (juste Arrow/Sen/Framework/Basic pour no-sorry check). **CI SUCCESS != Voting.lean compile**.

### Si pas d'env Lean local

- Ne pas merger seul
- Dispatcher po-2026 avec criteres :
  1. Build log complet colle (pas extrait)
  2. `grep -c sorry` avant/apres par fichier
  3. Diff sur defs partagees (signatures, instances)

### Discipline temporelle

- Dashboard `[DEFER]` AVANT le merge, pas apres
- Pour PRs strict-vs-weak preferences ou def globale : demander la liste des theoremes downstream qui dependent de la def

---

## 2. BG iter prover systematique post-PR/msg po-2026

### Source user 2026-05-16

Apres reply Decision A po-2026 sur gale_shapley, ~13:55Z :

> "Pour gale shapley, stp fais une iteration de ton cote en BG (ca devrait etre systematique apres chaque PR ou message de po-2026). Visiblement le script n'est toujours pas bon, car avec la correction sous les yeux, ca devrait etre plie depuis longtemps"

### Diagnostic double

1. **Comparaison parallele** ai-01 BG + po-2026 manual = 2 paths convergents (ou divergents)
2. **Forensic actif** : si le BG re-echoue malgre nouveau contexte (upstream PR #1181 mergee donnant acces `Properties.lean:48-120` upstream), c'est que SearchAgent/CoordinatorAgent n'utilisent pas effectivement le repo upstream comme RAG. **Bug script**.

### Action immediate ai-01

```bash
cd /d/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests
"C:/Users/MYIA/miniconda3/envs/coursia-ml-training/python.exe" -u run_prover_bg.py \
    <DEMO_ID> --provider zai --director-provider openrouter \
    --max-iter 20 --workflow-timeout 2400 2>&1 | tee bg_logs/ai01_demo<N>_cycle<NN>_$(date +%s).log
```

`DEMO_ID` (index dans `prover/config.py` `DEMOS` dict) :

| DEMO | Cible |
|------|-------|
| 6 | shapley |
| 9 | median_voter |
| 13 | banks_set |
| 14 | median_voter GT |
| 15 | gale_shapley_stable |

`--provider zai` (GLM-5.1) + `--director-provider openrouter` (Opus 4.7 strategic guidance, cher mais necessaire pour very_hard).

Lancer avec `Bash run_in_background=true`. Sauvegarder `bash_id` + path `.output`. Continuer FG work (min 2 tracks, cf CLAUDE.md "Productivite operations longues" HARD 2026-05-11).

### Forensic interpretation guide

| Outcome BG ai-01 | Outcome manual po-2026 | Diagnostic |
|------------------|------------------------|------------|
| FAIL (sorry inchange) | FAIL (sorry inchange) | Sorry vraiment **intractable** (Mathlib gaps, formalisation incomplete). Defer ou bouger contexte. |
| FAIL (sorry inchange) | SUCCESS (sorry elimine) | **Script defectueux** : prover ne fait pas ce qu'humain/agent expert fait. Forensic POSTMORTEM. |
| SUCCESS (sorry elimine) | FAIL (sorry inchange) | Script meilleur que manual sur ce point — incident a investiguer. |
| SUCCESS | SUCCESS | Convergence — verifier que les 2 preuves coincident (ou different mais valides). |

### Forensic capture sur echec N iter

- Issue `prover/script-defect-<n>` OU tracking `agent_tests/prover/POSTMORTEM.md`
- Logs `bg_logs/ai01_demo<N>_*.log` = source forensic primary
- Croiser avec [prover_iteration_history.md](prover_iteration_history.md) sections "BUILD-FAIL Pattern Categories" et "Architecture Evolution"

### Anti-pattern et verification fin de cycle

- **Anti-pattern interdit** : "Le BG a deja FAILED hier, pas la peine de relancer". Le contexte change a chaque iteration manual po-2026.
- **Reporting** : status BG (DELTA sorry, RESULT_SUCCESS, elapsed) dans dashboard cycle suivant. Ne PAS reporter "BG running, voila".
- **Fin de cycle** : avant `[DONE]`, repondre "Est-ce qu'il y a eu un PR ou msg po-2026 ce cycle ? Si oui, BG iter a-t-il ete lance ?".

---

## 3. Gotchas operationnels — dual-session & prover BG

Lecons durables tirees d'un episode ou deux sessions coordinateur ai-01 ont tourne simultanement sur la meme machine en partageant UN working tree. Les `#PR`/SHA ephemeres vivent sur le dashboard ; ici, seulement les mecanismes durables et les pieges reproductibles.

### 3.1 Dual-session sur arbre partage = destruction mutuelle

Deux REPL ai-01 sur le meme `d:\CoursIA` se detruisent : un `run` prover ecrase le candidat build-passing d'un autre via contention `.lake` + line-drift ; deux merges/closes concurrents = les deux fermes (incident SocialChoice : deux PRs jumelles fermees simultanement en double-yield, module orphelin, `reopenPullRequest` refuse sur PR DIRTY-at-close).

Regles :
- **Un seul** REPL porte `/coordinate` + le BG prover **par arbre**. L'autre YIELD (pas de merge/tree/gh/prover concurrents).
- **Signal d'activite peer** : le HEAD du working tree qui **bouge sans ton propre `pull`** (`git fetch`/reads ne deplacent pas le HEAD) = un peer opere a l'instant → YIELD ou isole.
- Toute PR individuelle sous dual-session = **worktree isole** (`git worktree add <path> -b <branch> origin/main`), **docs-only** de preference (pas de build → pas de contention `.lake`), push + PR comme `jsboige` **sans `gh auth switch`** (le peer garde `jsboige` pour ses merges), laissee **OPEN** pour la passe de merge du peer. Un worktree a son propre HEAD/index : le peer qui avance `main` ne peut pas le corrompre.
- Le **lockfile par-arbre** `agent_tests/prover/tree_lock.py` (`.prover.lock`, exit 3, `--force-lock`) garde le prover : un exit 3 = « un autre acteur tient l'arbre » → attendre/escalader, **jamais forcer**.
- **Dedup = decision user** : chaque session ne voit que SON `CronList` (le cron du peer vit dans SA session). Garder UNE session, stopper l'autre REPL — **jamais** un `CronDelete` aveugle (supprimer sa propre cron = risque zero-coordinateur).

### 3.2 Line-drift → AutoFix cible le mauvais sorry

Le harness AutoFix vise le sorry le plus proche d'une ligne cible. Un scaffolding inline **decale les lignes** : un `--line N` cale sur une ligne CLEAN devient, apres insertion, « le sorry le plus proche » = un AUTRE quadrant (cas vecu sur la decomposition P4 de `HashlifeCorrectness.lean` : une DEMO pointee sur le quadrant `ne` a derive vers `nw`, un grain DO-NOT-TARGET du bridge G3 manuel po-2026).

- **Factoriser le lemme AVANT tout BG** (pattern `p4_nw_shift_lemma` : sortir les steps hors du monolithe). Le monolithe P4 inline est **INTRACTABLE** : budget whnf (~200000 heartbeats) epuise sur la tete de declaration ; le budget se **reinitialise par declaration** → un lemme court compile la ou l'inline timeout. La voie productive est le **factoring manuel** (grains po-2026), pas le BG inline.
- `--demo N` **OVERRIDE** `--line` : re-pointer la DEMO dans `prover/config.py` (`DEMOS` dict), ne pas passer `--line` a la main sur un fichier au layout mouvant.

### 3.3 Logs BG = arbre du lanceur, pas l'arbre principal

Un BG lance depuis la copie `agent_tests` d'un worktree (`/mnt/c/dev/CoursIA-*`, `C:/wtprover`) logue dans le `bg_logs/` de CE worktree, pas dans celui de `d:\CoursIA`. Un `bg_logs/` du tree principal qui ne montre que des logs anciens **n'est pas** la preuve « aucun run » — chercher dans l'arbre du lanceur. Cross-checker l'outcome via le dashboard/DM du peer plutot que relancer un BG redondant (le lockfile 3.1 le refuserait de toute facon).
