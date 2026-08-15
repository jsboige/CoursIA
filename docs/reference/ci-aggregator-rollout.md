# CI aggregator — rollout Step 2 (issue #9819)

> **Statut au 2026-08-08.** Étape 1 LIVRÉE par **PR #9822 MERGED**
> (`ci/pr-gate-aggregator-9819`, commit `229391aca`, 2026-08-07T06:10Z) :
> `scripts/pr_gate.py` (300 LOC) + `.github/workflows/pr-gate.yml`
> (77 LOC) + `scripts/tests/test_pr_gate.py` (242 LOC, 20/20 verts).
> Le job `PR gate` tourne sur **toute PR**, sans filtre `paths:`,
> poll jusqu'à stabilisation (2 sondages calmes consécutifs), biais
> à l'échec (timeout / conclusion inconnue ⇒ exit 1), déduplication
> par nom de check (le dernier run gagne, résout le cas
> `Quarto Pages Deploy cancelled sur 401a68cd8`).
>
> **Étape 2 — flip `required_status_checks` — APPLIQUÉ le 2026-08-08.**
> La protection est **live** (vérifiée firsthand, §« Vérifier ») :
> `required_status_checks.contexts = ["PR gate"]`, `strict = false`,
> `enforce_admins = false`. Le contexte `PR gate` est requis en
> vigueur — toute PR (y compris celle-ci) le subit. Ce document est
> désormais le **record + vérification + rollback** de ce flip, plus
> la whitelist des gates protégés et le protocole de durcissement.

## Pourquoi le flip du repo setting n'est PAS dans #9822

GitHub n'autorise **pas** un workflow à modifier les protections
d'une branche de `main` — l'endpoint
`/branches/main/protection/required_status_checks` exige `repo`
admin-scoped que `GITHUB_TOKEN` n'a pas. La PR #9822 stipule
explicitement (corps, section « Ce que cette PR ne fait PAS ») :

> « Activer le check est un réglage de dépôt
> (`Settings > Branches > main > Require status checks > "PR gate"`),
> **owner-only** — hors de portée de tout workflow, comme
> `can_approve_pull_request_reviews` l'était. Cette PR livre la
> moitié qui ne dépend pas du propriétaire, pour que le flip soit
> un clic plutôt qu'un problème de conception. »

Préférence ai-01 sur le flip : **plus tôt c'est fait, mieux c'est**.
On a un merge qui passe par jour sans friction, et l'absence de
gate a déjà coûté 5 heures (main rouge 00:22-05:21Z le 2026-08-07,
incident #9762).

## La commande exacte (user-only) — APPLIQUÉE le 2026-08-08

Préférence : **token-scoped**, exécutée dans la session user
(Visual Studio Code, compte `jsboige`), pas via CI.

**Pourquoi un `PUT` sur `/protection` (pas un `PATCH` sur la
sous-ressource).** La sous-ressource
`.../protection/required_status_checks` n'existe que si les
required status checks sont **déjà actifs** — tant qu'ils ne le
sont pas, un `GET` renvoie `404 Required status checks not
enabled`, et un `PATCH` n'a rien à mettre à jour. Le **premier**
passage doit donc `PUT` l'objet de protection **complet** (les 4
clés de tête sont obligatoires, `null`-ables). Une fois la
sous-ressource créée, un `PATCH` suffit pour l'ajuster.

```bash
# 1. S'assurer d'être sur le bon compte (compte owner, scope repo+workflow)
gh auth status

# 2. Activer required_status_checks sur main.
#    PAS de slash de tête sur l'endpoint : MSYS/gitbash réécrit
#    /repos/... en chemin de fichier ("C:/Program Files/Git/repos/...").
#    Le JSON --input - rend les 4 clés sans ambigüité de -f/-F.
gh api --method PUT repos/jsboige/CoursIA/branches/main/protection --input - <<'JSON'
{
  "required_status_checks": { "strict": false, "contexts": ["PR gate"] },
  "enforce_admins": false,
  "required_pull_request_reviews": null,
  "restrictions": null
}
JSON

# 3. Vérifier ( firsthand, état mesuré au 2026-08-08 )
gh api repos/jsboige/CoursIA/branches/main/protection \
  --jq '{contexts: .required_status_checks.contexts, strict: .required_status_checks.strict, enforce_admins: .enforce_admins.enabled}'
# Attendu: {"contexts": ["PR gate"], "strict": false, "enforce_admins": false}
```

**`strict: false`** (valeur appliquée). `strict: true` exigerait
que la PR se re-base sur `main` pour considérer les checks à jour ;
le choix initial est `false` (mode laxiste par défaut de GitHub),
à durcir vers `true` au Cycle 3 si 0 incident (§« Protocole »).

**`enforce_admins: false` (valeur appliquée) — décision rendue.** Le
choix entre `true` et `false` se décide par **qui merge au
quotidien**, pas par préférence. Mesuré firsthand : l'identité de
routine `myia-ai-01` a les droits `push` mais **pas** `admin` —
donc à `false` elle reste **intégralement soumise** au gate (elle
ne peut pas merger rouge : le gate garde ses dents là où 100 % des
merges de routine passent). Seul `jsboige` (admin) conserve une
sortie de secours. À `true`, en revanche, **personne** ne pourrait
merger — y compris la PR qui réparerait un gate cassé — ce qui
fabrique précisément le blocage que le user a exclu de son Go
(« *Si ça sécurise et tu as toujours un chemin propre de merging,
Go. Si on se retrouve dans une situation de blocage, no-Go* »).
`false` satisfait les deux moitiés ; `true` satisfait la première
et produit la seconde. Application chirurgicale par
`DELETE .../protection/enforce_admins` (et **non** un `PUT` sur
`/protection`, qui rejouerait l'objet entier et réinitialiserait
les clés absentes du corps — dont `allow_force_pushes`, qui porte
l'interdit de force-push sur `main`).

**`contexts: ["PR gate"]`** = le **name** du job dans
`.github/workflows/pr-gate.yml`, **case-sensitive**. Le nom du
contexte requis doit rester byte-identique au nom du job YAML :
renommer le job détache silencieusement la règle de protection, et
une règle qui pointe un check que personne ne produit est
*pending forever* (le deadlock même que le gate existe pour
éviter). Pour vérifier le nom côté PR :

```bash
gh pr checks <PR_NUMBER> --json name,bucket | jq '.[] | select(.name | contains("PR gate"))'
```

## Rollback — revenir à l'état d'avant le flip

Le retour propre est la **suppression** de la sous-ressource, pas
un `contexts: []` (qui laisse la sous-ressource active et vide — un
état différent de l'initial `404 Required status checks not
enabled`) :

```bash
gh api --method DELETE repos/jsboige/CoursIA/branches/main/protection/required_status_checks
# Vérifier le retour à l'état initial:
gh api repos/jsboige/CoursIA/branches/main/protection/required_status_checks
# Attendu: HTTP 404 {"message":"Required status checks not enabled"}
```

Si le besoin est seulement de **retirer un contexte** (garder la
protection, enlever `PR gate`), un `PATCH` sur la sous-ressource
(désormais existante) suffit :

```bash
gh api --method PATCH repos/jsboige/CoursIA/branches/main/protection/required_status_checks \
  -f strict=false -f 'contexts[]=<autre contexte>'
```

Le rollback n'est pas une opération anodine : sans required status
check, une PR rouge redevient mergeable (retour à l'état
#9762/#9858). À n'utiliser que sur incident prouvé, pas sur
inconfort.

## Auto-test : ce PR modifie `pr-gate.yml`, donc le gate se juge lui-même

C'est documenté dans le corps de #9822 :

> « Cette PR modifie `pr-gate.yml`, et comme le workflow n'a pas
> de filtre `paths:`, il tourne **sur cette PR même** — le gate
> se juge donc lui-même dès son premier commit. C'est la
> contrainte de #8712 (« un gate dont la première exécution est
> post-merge n'est pas un gate ») satisfaite par construction
> plutôt que par une liste de chemins à maintenir. »

C'est l'**auto-validation** : la première exécution du gate
est sa propre exécution. Pas de chicken-and-egg.

## La whitelist « pourquoi CE check est gate »

Le PR #9822 code cette whitelist en dur dans `scripts/pr_gate.py`
(`critical_jobs` / `tolerated_states`). Le tableau ci-dessous
ré-audite chacune des entrées contre l'incident fondateur qui
justifie sa présence. Référence : `CLAUDE.md` §A (coordination,
GitHub = code pas rapport), §G.6 (audit avant merge cascade).

| Entrée (`PR gate` whitelist) | Type | Incident fondateur |
|---|---|---|
| `ci / Lean CI (*)` | required | **#9762** — Lean CI failure mergé sans alerte, `main` rouge 5h |
| `ci / Proof integrity (*)` | required | fondation proving — `sorry` ne se voit pas au `grep -c` |
| `ci / Lake build` | required | un lake qui ne build pas = cascade upstream |
| `ci / Static validation (H.1/H.3/C.1)` | required | notebooks committés sans `execution_count` |
| `ci / Golden-set execution (H.7 P3)` | required | régression silencieuse sur le golden set |
| `ci / No cell-ordering regression in changed notebooks` | required | ordre des cellules = pedagogie cassée |
| `ci / Exercice-solution HIGH delta guard` | required | leak des solutions etudiant / EPITA |
| `ci / probeAddresses banner guard (main-repo notebooks)` | required | strip post-re-exec .NET (L532 MEMORY) |
| `ci / markdown-rendering guard (main-repo notebooks)` | required | supersize H2 setext (cf #9082) |
| `ci / No fabricated text output in changed notebooks` | required | C.4 doc-honesty (#8052) |
| `ci / No degenerate figure in changed notebooks` | required | GenAI rendering (cf #6541) |
| `ci / No bare cross-dir #load in changed notebooks` | required | coupling cellule cross-répertoire |
| `ci / Notebook catalog drift (read-only)` | advisory | catalog-pr-hygiene R1 — détecteur read-only ; le garde bloquant `catalog-pr-guard.yml` est retiré (#11012) |
| `ci / Gitleaks secret scanner` | required | secrets-hygiene |
| `hooks-parity gate` | required | #8782 — gate qui ne peut plus rougir |

**Préférence** : toute future entrée suit le pattern
`<famille> / <gate-name> (contexte)` pour la lisibilité dans
l'UI GitHub. Le `PR gate` job les matche par substring
case-insensitive pour survivre aux renommages cosmétique.

## Après le flip — protocole de durcissement

Une fois `required_status_checks.contexts = ["PR gate"]` appliqué,
trois cycles d'observation minimum :

1. **Cycle 1 (J+0 → J+1)** : observer le comportement sur PR
   notebooks vs PR Lean vs PR docs-only. Doit toujours
   **rouge si rouge, vert si vert, jamais pending permanent.**
2. **Cycle 2 (J+1 → J+7)** : si un edge case apparaît (ex. SHA
   pré-merge sans check-runs), ouvrir une issue `#9819.<edge>`
   et **ne pas** désactiver le required.
3. **Cycle 3 (J+7 → J+30)** : si 0 incident, durcir vers
   `strict: true` (la PR doit alors se re-baser sur `main` pour
   que ses checks soient considérés à jour). La valeur appliquée
   au flip est `strict: false` (mode laxiste par défaut de GitHub) ;
   `strict: true` est le durcissement optionnel post-stabilisation.

## Cas dégradé : le gate est OK structurellement mais le check-run n'est pas vu

Symptôme : `PR gate` rapporte `[PASS]` localement (rq de
`scripts/pr_gate.py --repo jsboige/CoursIA --sha <sha>`) mais
GitHub affiche `pending` ou un check blanc.

Causes probables par ordre de plausibilité :

1. **Le SHA n'est pas encore propagé à l'API check-runs** (race
   ~5s). Réessayer 30s plus tard.
2. **Le job `PR gate` a démarré avant les autres** (poll
   `<2` sondages calmes). Conséquence : un check timeout
   GitHub-préemptif a supprimé un run, le dédup a perdu le
   « dernier run ». **Fix** : étendre le poll à 4 sondages
   consécutifs (vs 2 dans #9822) — ouvrir une issue #9819.4.
3. **Le dédup par nom a élu un run cancelled comme dernier**
   (rare post-#9822 mais théoriquement possible si un
   utilisateur annule un job *après* le poll). Symétrie au
   cas #9822 — `cancelled` après dédup ne peut vouloir dire
   que « supplanté » : doit FAIL. Si FAIL ne se produit pas,
   c'est que le dédup a élu un run plus ancien. Piste.

## Tests structurels

`scripts/tests/test_pr_gate.py` (20 tests, 100% PASS en 0.08s) —
déjà dans #9822. Couvrent :

- `test_self_exclusion_is_not_a_loose_prefix` (auto-exclusion
  du gate par préfixe strict `"PR gate / "`)
- `test_classify_empty_list` (edge case API vide)
- `test_classify_dedup_last_run_wins` (race de concurrence)
- `test_classify_cancelled_after_dedup_fails` (cas Quarto)
- `test_the_9762_shape_fails` (replay post-mortem #9762 — la
  preuve de non-régression centrale)
- `test_pr_state_runs` (commit statuses unionnés aux check runs)

## Voir aussi

- Issue #9819 — diagnostic fondateur
- Issue #9762 — PR rogue mergée rouge (incident)
- Issue #9818 — fix-forward de `main` post-#9762
- PR #9822 — Étape 1 (job `PR gate` aggregator MERGED)
- PR #9824 — doublon de #9822 (CLOSED, propre Leçon L898 ★★★)
- `CLAUDE.md` §A (coordination, GitHub = code pas rapport)
- `CLAUDE.md` §G.6 (audit avant merge cascade)
- `scripts/pr_gate.py` — la whitelist canonique
