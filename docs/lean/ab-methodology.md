# Méthodologie d'A/B pour le harnais prover Lean

Comparer deux (ou plusieurs) LLM providers du harnais prover (`agent_tests/prover/`) sur les mêmes cibles Lean — par ex. évaluer un modèle Lean-spécialisé (Leanstral) contre le workhorse courant (GLM-5.1, GPT-5.5). Référence : A/B Leanstral #5475, EPIC #3801 (axe-2 SOTA).

## 1. Piège fondateur : contamination write-back (HARD)

Le harnais **persiste les preuves partielles** via le mécanisme `persist_on_success` de `lean_utils.verify_sorry_replacement` (write-back, #4075 / #4039) : quand une tactique fait baisser le compte de sorry (même sans résoudre entièrement), la mutation du fichier `.lean` est conservée sur disque à la fin du run.

**Conséquence pour l'A/B** : si le runner exécute les providers **séquentiellement sur le même fichier** (provider A puis provider B), le provider A mute le fichier → le provider B tourne sur un fichier ** contaminé**. La comparaison est invalide.

### Diagnostic observé (#5475, cycle c.258)

- `knot_lean/Knots/Invariant.lean` : 6 sorries sur `origin/main` → 4 sorries après un run openrouter (5→4 partial-progress persisté) → le run mistral suivant a lu `original_sorry:4` (pas 5) et a été **REFUSED** par le garde FX-5 (`true_placeholder_goal`) à la **ligne 8** (pas 242) à cause du shift des numéros de ligne induit par le write-back.
- Le seul signal différentiel (openrouter 5→4) n'avait **pas de comparateur mistral valide**.

## 2. Méthodologie d'isolation

Chaque cellule de l'A/B doit tourner sur un fichier **pristine** (byte-identique au baseline). Trois variantes acceptables :

1. **Restauration par cellule** (recommandée, simple) : `git checkout origin/main -- <file>` avant chaque appel au prover.
   ```bash
   run_cell () {  # $1=label $2=file $3=line $4=provider
     git -C /c/dev/CoursIA checkout origin/main -- "$2" 2>>"$LOG"
     timeout 900 python run_prover_bg.py --file "$2" --line "$3" \
       --mode autonomous --iterations 3 --provider "$4" >> "$LOG" 2>&1
   }
   ```
2. **Copie fraîche par cellule** : `cp` le fichier d'une référence immuable vers un worktree dédié par provider.
3. **Randomisation + moyenne** : randomiser l'ordre des providers sur N seeds (≥4) pour diluer l'effet d'un ordering biaisé — utile en complément, pas en substitut de l'isolation.

**Pré-requis** : `git fetch origin main` avant le run pour que `origin/main` soit frais (sinon isolation sur un `origin/main` stale).

## 3. Choix du domaine de cibles

L'A/B se fait sur **nos sorries research-level** (combinatoire : mariage stable, voting, jeux coopératifs, Hashlife, théorie des nœuds), **pas** sur les benchmarks de compétition (miniF2F, PutnamBench). Caveat `docs/lean/sota-2026-analysis.md` §6.3 : notre niche est un régime différent où « même les systèmes SOTA échoueraient ». Un verdict « aucun provider ne solve » est donc **attendu et honnête**, pas un échec de la méthodologie.

### Cible dégénérée à exclure

Le garde FX-5 refuse les sorry dont le goal est la proposition triviale `True` (placeholder dégénéré, ex. Hashlife L2471 `p4_half_steps_compose`, L2853 `p5_large_n_jump`). Le vrai énoncé mathématique est en commentaire, pas dans le theorem. Ces cibles **n'exercent pas le LLM** — les exclure de l'A/B. Vérifier chaque target avec une lecture du theorem (pas juste le numéro de ligne).

## 4. Métriques par cellule

Pour chaque (target × provider), capturer depuis le `*_result.json` :

| Métrique | Champ JSON | Lecture |
|----------|-----------|---------|
| Provider | `provider` | openrouter / mistral / zai |
| Verdict cellule | `result_kind` | `solved` / `sorry_decreased` / `no_progress` |
| Sorry initial→final | `original_sorry` → `final_sorry` | ex. 5→4 |
| Delta | `sorry_delta` | négatif = progrès |
| Iters réelles/budget | `actual_iterations` / `iterations` | distingue timeout early-exit |
| Temps wall-clock | `elapsed_s` | comparaison coût |
| Tactiques vérifiées | `result.verified_tactic_count` | 0 = aucune tactique compilée |
| Best sorry atteint | `result.best_sorry` | 999 = jamais amélioré |

**Toujours** relever le code de sortie du processus (`exit=124` = timeout `timeout 900` = pas de donnée réelle).

## 5. Verdict (honnête, pas « promising »)

Sur l'ensemble des cellules :

- **BEATS** : le provider candidat solve strictement plus de targets que le baseline, avec au moins une target résolue exclusivement par le candidat.
- **NO BEATS** : le baseline solve strictement plus, avec au moins une target résolue exclusivement par le baseline.
- **INCONCLUSIVE** : aucun solve des deux côtés, OU tie, OU comparaison contaminée. **Ne jamais** reformuler un INCONCLUSIVE en « promising » ou « encourageant » — c'est de la complaisance (CLAUDE.md §G.2).

Sur research-level, le verdict attendu est souvent INCONCLUSIVE (aucun solve). C'est un résultat **valide** : il documente le plafond atteignable sur notre terrain, pas un échec à corriger par retry indéfini.

## 6. Caveats à reporter

Tout rapport d'A/B doit expliciter :

- **Domaine** : research-level ≠ miniF2F/Putnam (ne pas extrapoler).
- **Tier API** : free-tier vs paid (Leanstral free-tier plafonne, rate-limit possible).
- **Budget** : nombre d'itérations, timeout par cellule, seeds.
- **Baseline stability** : si le baseline rate-limit-crash (ex. zai/glm-5.1, #1459), pivoter vers un baseline stable (openrouter/GPT-5.5) et le documenter.
- **Isolation** : confirmer qu'aucune contamination write-back n'a eu lieu (vérifier `git diff` du fichier post-run = vide).

## Références

- Issue #5475 : A/B Leanstral 1.5 vs GPT-5.5 (cycle c.258, finding contamination).
- EPIC #3801 : axe-2 SOTA (vrai outil SOTA installé/invoqué, pas workaround).
- `docs/lean/sota-2026-analysis.md` §6.3 : régime research-level.
- `docs/lean/prover_iteration_history.md` : historique write-back (#4075, fix 2026-06-23).
- CLAUDE.md §G.2 : métriques honnêtes, pas binaires.
