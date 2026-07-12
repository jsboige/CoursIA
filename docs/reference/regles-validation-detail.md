# Règles validation H.1-H.7 — pas de complaisance sur notebooks (detail)

Résumé opérationnel : CLAUDE.md section H.

S'applique a TOUS les agents (exécutants, coordinateur, reviewers humains, bots). Aucune dérogation.

**Incident origine (2026-05-09)** : 5+ vagues de "fix" cosmétiques sur Sudoku-13 (5 commits structurels depuis mars 2026, `execution_count=null` sur 11/11 cellules code — jamais execute depuis sa creation) ne l'ont jamais detecte, parce que toutes les "validations" ont ete superficielles (rule C.2 vérifiée sur structure JSON, jamais sur l'execution reelle).

---

## H.1 — Validation = execution complete + outputs verifies (HARD)

"Validate", "fix", "OK", "completed", "DONE" sur un notebook = uniquement si TOUS les criteres :

1. Toutes les code cells ont `execution_count != null` ET `outputs` non vide (sauf assignation pure prouvee via log Papermill)
2. ZERO cellule avec `output_type: error`
3. Papermill `<nb>` ou kernel cell-by-cell (.NET / WSL) execute end-to-end SANS skip
4. Body PR colle la trailer Papermill (30 dernieres lignes log) OU les outputs sont commites + visibles dans la diff

Sans ces 4 preuves : la PR n'est PAS validee. Peu importe qui la signe. La verification "structure JSON OK" (rule C.2 historique) est UN sous-ensemble de H.1, pas un substitut.

---

## H.2 — Tous les agents installent l'env complet (HARD)

Chaque machine cluster (po-2023, po-2024, po-2025, po-2026, ai-01) doit pouvoir executer N'IMPORTE QUEL notebook du repo. Inventaire minimum (cf [docs/kernels-runtime.md](kernels-runtime.md)) :

- Python 3.10+ + envs Conda dédiés (`coursia-ml-training`, `epita_symbolic_ai`, `mcp-jupyter`)
- .NET 9.0 SDK + `dotnet-interactive` Jupyter kernels (.NET notebooks Sudoku/SymbolicAI/ML/Probas/Search/SmartContract)
- WSL kernels (GameTheory + OpenSpiel + Lean 4)
- Lean `elan` toolchain
- Docker + acces aux services GenAI (po-2023 host) ou env de bypass

Si un agent ne peut pas executer un notebook → il INSTALLE l'env (peut demander UAC user). Pas de "skip car env manquant", pas de "delegation a un autre agent". Réparation env > contournement (extension de la regle F — cf [docs/env-python-reparation.md](env-python-reparation.md)).

---

## H.3 — Aucun commit de notebook non-execute (HARD)

Interdit de commiter un notebook ou n'importe quelle cellule code a `execution_count: null` ET `outputs: []`. Verification pre-commit obligatoire :

```bash
python -c "import json,sys; nb=json.load(open(sys.argv[1])); \
bad=[i for i,c in enumerate(nb['cells']) \
     if c['cell_type']=='code' \
     and c.get('execution_count') is None \
     and not c.get('outputs')]; \
sys.exit(1 if bad else 0)" "$nb"
```

Si fail → agent doit :

- (a) executer localement (env complet H.2), OU
- (b) executer via dispatch RooSync sur machine compatible, OU
- (c) deplacer le notebook dans `_pending_execution/` avec issue ouverte detaillant le blocage

Pas de 4ème option, pas de "je commit quand meme c'est juste structurel".

### Hook pre-commit notebook (.pre-commit-config.yaml)

Le repo inclut un hook pre-commit **local** dans `.pre-commit-config.yaml` qui s'exécute sur les `*.ipynb` staged :

- **`strip-probeaddresses-banner`** — strip automatique du banner `probeAddresses` (data["text/html"] output du kernel `.NET Interactive` `dotnet-interactive`). Sans ce hook, le banner re-injecte à chaque kernel re-exec les IPs machine (LAN IPv4, WSL/Docker bridge, link-local IPv6, IPv6 publique GUA — ex: `2a01:e0a:...` Orange-FR `/32`). Strip output-only (pas de modification des sources, `execution_count` préservé). Régression de #2727/#2733 (scrub one-shot non-durable, 183 notebooks source re-affectés au moment du fix, 202 total incluant `_output` papermill) — fix structurel : voir #6309.

Activation : `pip install pre-commit && pre-commit install`. Exécution manuelle : `pre-commit run --all-files`. Strip CI/standalone : `python scripts/notebook_tools/strip_probe_banner.py --scan-all --check` (exit 1 si banners résiduels), `--apply-all` (fix repo-wide). Tests unitaires : `pytest scripts/notebook_tools/tests/test_strip_probe_banner.py` (18/18 PASS — couvre list-form, string-form, mixed list+string, idempotence, byte-stability, regression `]`-in-string via bracket scanner).

Détail du stripper : `scripts/notebook_tools/strip_probe_banner.py`. Le scanner de bornes de blocs `"text/html": [ ... ]` est **JSON-string-aware** (track profondeur de brackets en sautant les caractères dans les chaînes JSON) — une regex naive `[^\]]*` échoue sur les .NET notebooks réels dont l'inline JS `probeAddresses(["http://...","..."])` contient un `]` qui pré-ment clore la liste. Le scanner reconstruit `body_start, body_end` corrects même en présence de crochets imbriqués, et la suppression drop l'élément bannerisé + sa virgule suivante (ou précédente si dernier élément) sans casser le shape `[...]`.

---

## H.4 — Merges coordinateur ne sont JAMAIS complaisants (HARD)

ai-01 (ou tout coordinateur) ne merge PAS une PR notebook sans :

1. Lire le body PR + trailer Papermill colle
2. `git fetch && git checkout <branch>` puis `python scripts/notebook_tools/notebook_tools.py execute <nb>` LOCALEMENT
3. Verifier `execution_count != null` + `errors == 0` apres execution locale

**Relaxation forensic JSON acceptable** : si body PR contient log Papermill 13/13 cellules SUCCESS + static SUCCESS + scope OK, ai-01 peut merger sans relancer localement. Mais le verdict reste sur la preuve d'execution, pas sur le claim.

Cascade merge sans audit individuel = violation H.4 = revert + post-mortem dashboard. **Le contre-exemple a ne pas reproduire** : cascade 8 PRs de la nuit 8→9/05 mergee en ~30min en confiant l'audit aux body-PRs sans re-execution locale.

---

## H.5 — Bots reviewers : audit commit-level forensique (HARD)

Tout bot reviewer (clusterManager-Myia, jsboige self-bot, futurs) doit poster sur chaque PR notebook une analyse statique structuree :

- **Diff par cellule** : source modifiée oui/non, execution_count avant/apres, outputs ajoutes/retires/modifies, output_type:error present
- **Detection "fix superficiel"** : source code cell change ET `execution_count` reste null OU identique, OU outputs vides apres modification source = **RED FLAG**
- **Detection "regression silencieuse"** : outputs avec `error_type`, execution_count decremente, kernel mismatch dans metadata
- **Verdict explicite** : `EXEC_PROVED` / `STRUCTURAL_ONLY` / `SUSPECT_REGRESSION`

Si STRUCTURAL_ONLY ou SUSPECT_REGRESSION et le PR claim "fix" / "validate" / "OK" → CHANGES_REQUESTED automatique. Le coordinateur ne peut PAS merger sans que le bot ait poste EXEC_PROVED.

Les bots ne peuvent pas executer les notebooks (pas d'env complet) mais ils peuvent et DOIVENT prouver l'execution via parsing JSON de la diff.

---

## H.6 — Audit historique notebook = responsabilite bot, pas humain

Avant ouverture d'une issue ou PR "le notebook X est casse" / "X n'a jamais marche" : obligation d'invoquer d'abord un bot reviewer avec `audit-history MyIA.AI.Notebooks/path/to/X.ipynb`. Le bot retourne :

- Liste des N derniers commits (hash, date, auteur, type modif: source/output/both)
- Date du dernier commit avec preuve d'execution (Papermill log presence OU outputs non-vides apres source change)
- Verdict : `LAST_REAL_EXEC <date> <commit>` ou `NEVER_EXECUTED_SINCE_<creation>`

Sudoku-13 aurait du sortir `NEVER_EXECUTED_SINCE_<creation>` au premier appel — ca aurait économisé les 5 PRs cosmétiques accumulees depuis mars 2026.

---

## H.7 — Plan de sortie du cycle perpetuel (incident 2026-05-09)

L'audit du 2026-05-09 a révélé un pattern systemique : 988 notebooks repo, dont une fraction inconnue n'a jamais ete reellement exécutée malgre des dizaines de commits "fix" cosmétiques.

**Plan de remediation 4 phases** :

- **P0** : gel des "vagues de fix C.x / cosmetique / enrichissement" sur tous les agents jusqu'a inventaire complet
- **P1** (48h) : forensique massif sur HEAD courant → `STABLE_SNAPSHOT.md` (matrice 988 notebooks : `ALL_NULL` / `ALL_EXEC` / `PARTIAL` + errors_count + LAST_REAL_EXEC)
- **P2** (1 semaine) : pour chaque NEVER_EXECUTED → soit slot agent dedie executant pour de vrai, soit archive avec mention pedagogique explicite "non exécutable en l'etat"
- **P3** (2 semaines) : workflow GitHub Actions `notebook-execution-required.yml` qui execute via Papermill toute notebook touchee dans une PR. Failure → merge bloque. Runner = Docker compose (.NET + Python + Lean + WSL bypass)
- **P4** (continu) : `STABLE_SNAPSHOT.md` regenere mensuel, gravant `sha + date + matrice exec_status` → point de reference factuel quand quelqu'un dit "X est valide"

Cf [docs/archive/STABLE_SNAPSHOT.md](../archive/STABLE_SNAPSHOT.md).

---

## References connexes

- [.claude/rules/notebook-conventions.md](../../.claude/rules/notebook-conventions.md) — Rules C.1/C.2/C.3 notebook
- [docs/regles-vigilance-detail.md](regles-vigilance-detail.md) — Règles G.1-G.9 anti-complaisance
- [docs/env-python-reparation.md](env-python-reparation.md) — Réparation env Python (regle F)
- [docs/kernels-runtime.md](kernels-runtime.md) — Inventaire kernels par machine
- [docs/archive/STABLE_SNAPSHOT.md](../archive/STABLE_SNAPSHOT.md) — Matrice exec_status des notebooks
