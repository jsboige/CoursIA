# Sous-modules — maintenance active, jamais un dépôt dormant

S'applique au **coordinateur ai-01** et à toute lane qui touche un sous-module. Source : mandat user 2026-09-02, verbatim :

> « Ca sera une bonne chose de ne pas laisser nos sous-modules sans maintenance, si j'ai souhaité les définir comme sous-modules de CoursIA, c'est pour qu'ils puissent évoluer avec nous et **chacun d'eux a un rôle dans le dépôt principal qui n'est plus à démontrer**. »

La conséquence pratique : un sous-module n'est pas une dépendance qu'on subit, c'est un dépôt **du cluster** dont le backlog est **notre** backlog. Une PR qui dort six semaines chez `MyIntelligenceAgency` est exactement aussi grave qu'une PR qui dort sur `jsboige/CoursIA`.

**État vérifié, mesures datées et incidents** : [docs/reference/submodule-maintenance-detail.md](../../docs/reference/submodule-maintenance-detail.md) — table de statut de gate par sous-module, précondition de jeton, faux positifs mesurés.

## Règle HARD 1 — le périmètre est de cinq dépôts, pas trois

| Chemin dans CoursIA | Remote | Entretien |
|---|---|---|
| `MyIA.AI.Notebooks/Search/MetaGeneticSharp` | `jsboige/MetaGeneticSharp` | coordination ai-01 |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq` | `MyIntelligenceAgency/Z3.Linq` — **fork de `endjin/Z3.Linq`** | coordination ai-01 ; les livraisons partent **en PR upstream** (Epic #1206) |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Automata` | `MyIntelligenceAgency/Automata` | coordination ai-01 |
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum` | `ArgumentumGames/Argumentum` | **agent permanent dédié** — ai-01 ne fait que le bump de pointeur |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/semantic-fleet` | `MyIntelligenceAgency/semantic-fleet` (`branch = stable-from-v0343`) | coordination ai-01 |

**La liste faisant foi est `.gitmodules`, jamais un souvenir** — `Automata` est le cinquième et s'oublie, et `MetaGeneticSharp` vit sous `jsboige/`, **pas** sous `MyIntelligenceAgency/`.

**Le critère tient en une phrase** : un sous-module est un dépôt **qu'on fait vivre**. Une dépendance de build qu'on subit se clone (`forge install --no-git`), elle ne se déclare pas. Retrait des trois `foundry-lib/lib/*` (#14518) et faux négatif `Could not resolve to a Repository` : [detail §1](../../docs/reference/submodule-maintenance-detail.md#1-périmètre--pourquoi-la-liste-se-lit-dans-gitmodules).

## Règle HARD 2 — la dérive de gitlink se mesure, elle ne s'intuitionne pas

Un gitlink en retard rend **invisible depuis CoursIA** du travail déjà mergé en amont. La mesure est mécanique :

```bash
cd <racine CoursIA>
for P in $(git config -f .gitmodules --get-regexp '^submodule\..*\.path$' | awk '{print $2}'); do
  U=$(git config -f .gitmodules --get "submodule.$P.url")
  B=$(git config -f .gitmodules --get "submodule.$P.branch" 2>/dev/null)
  REF=${B:+refs/heads/$B}; REF=${REF:-HEAD}
  L=$(git ls-tree origin/main "$P" | awk '{print substr($3,1,12)}')
  R=$(git ls-remote "$U" "$REF" 2>/dev/null | awk '{print substr($1,1,12)}')
  [ -z "$R" ] && { printf "INJOIGNABLE %-56s (ref %s)\n" "$P" "$REF"; continue; }
  [ "$L" != "$R" ] && printf "DERIVE %-56s %s -> %s (ref %s)\n" "$P" "$L" "$R" "$REF"
done
```

**La référence de comparaison est la branche déclarée** : `refs/heads/<branch>` quand `.gitmodules` porte un `branch =` (explicite, pour ne jamais résoudre un tag homonyme), `HEAD` sinon. Comparer un sous-module épinglé à `HEAD` distant **fabrique une dérive** qui n'existe pas — faux positif permanent mesuré sur `semantic-fleet` (#14872), [detail §2](../../docs/reference/submodule-maintenance-detail.md#2-faux-positif-permanent-head-vs-branche-déclarée-14872). Et un `ls-remote` muet s'affiche `INJOIGNABLE`, **jamais** comme une égalité.

**Ordre obligatoire** (déjà porté par le `CLAUDE.md` global) : commiter **dedans** d'abord, pousser, **puis** bumper le pointeur parent. Jamais l'inverse.

## Règle HARD 3 — l'absence de gate est le défaut, pas les PRs qui dorment

Avant de traiter un backlog de sous-module comme de la négligence, **vérifier qu'un gate existe et se déclenche**. Trois PRs dormantes sous un dépôt sans gate ne sont pas trois oublis : c'est **un** défaut structurel, et le corriger vaut mieux que relancer les auteurs. Le manque de CI se traite en **issue de suivi nommée**, pas en reproche de lane.

**Substitution admise tant que le gate manque** : deux vérifications **firsthand indépendantes** (fresh-clone, build + suite de tests complète, sur **deux lanes distinctes**), avec leurs comptes de tests et leurs SHA **cités dans le body de la PR de bump**. Une seule vérification, ou une vérification par l'auteur seul, ne remplace pas un gate.

**Cinq états de gate** — la substitution R3 s'applique **par défaut**, et ne cesse qu'à l'état 3 :

| # | État | Substitution R3 |
|---|---|---|
| 1 | **Absent** — aucun workflow, aucun run | active |
| 2 | **Câblé, jamais déclenché sur la pile en cours** — le trigger ne couvre pas les PRs visées | active ; c'est le **déclencheur** qui doit être qualifié, pas seulement le câblage |
| 3 | **Câblé, déclenché, vert récent** sur la branche par défaut | **cesse** — A2 est acquis |
| 4 | **Drift / perte de gate** — un état 3 qui perd son workflow | redevient active |
| 5 | **Câblé, déclenché, rouge récent** — le gate existe et tire, mais hors-main ou en régression | active jusqu'au retour au vert |

Le passage d'un état à l'autre est un **geste tracké** : PR dédiée sur le dépôt submod (câblage ou re-câblage), mise à jour de la table d'état dans le detail, et revue coord pour valider la bascule.

**Commande de mesure** (à passer à chaque cycle `/coordinate` et à chaque PR de bump) :

```bash
for R in MyIntelligenceAgency/Z3.Linq MyIntelligenceAgency/Automata \
         jsboige/MetaGeneticSharp MyIntelligenceAgency/semantic-fleet \
         ArgumentumGames/Argumentum; do
  echo "=== $R ==="
  gh api "repos/$R/actions/workflows" --jq '"workflows total=\(.workflows|length), actifs=\([.workflows[]|select(.state=="active")]|length)"'
  gh api "repos/$R/actions/runs?per_page=1" --jq '"  runs total=\(.total_count), dernier=\(.workflow_runs[0]|"\(.created_at) \(.name) -> \(.conclusion // .status)")"'
done
```

**Un `403` est une question, pas une absence mesurée** — ne jamais en conclure « 0 workflow ». L'org `MyIntelligenceAgency` refuse les PAT fine-grained de plus de 366 jours : épingler le jeton **par commande** (`GH_TOKEN=$(gh auth token --user <compte>)`), jamais par `gh auth switch` (état global au process `gh`, cf. R5). [detail §3](../../docs/reference/submodule-maintenance-detail.md#3-précondition-de-jeton-pour-la-mesure-de-gate-mesurée-le-2026-09-05).

**Statut courant par sous-module** : [table du detail §4](../../docs/reference/submodule-maintenance-detail.md#4-table-de-statut-de-gate-par-sous-module). Elle se **relit** avant chaque PR de bump — elle date de sa mesure, pas de sa lecture, et elle ne se mémorise pas.

## Règle HARD 4 — sur un stack, la forme du merge de la base n'est pas neutre

Merger la **base** d'un stack en **squash** réécrit son SHA : les PRs enfants basées sur sa branche deviennent orphelines et exigent un `git rebase --onto`. Merger la base en **commit de merge** préserve les SHA, et les enfants se retargettent alors par un simple `gh pr edit --base main`.

**Vérifier après retarget, avant de merger l'enfant** : son diff doit s'être **réduit à son propre périmètre**, sans fichier de la base qui fuit. C'est cette mesure qui valide le choix de forme — pas l'intention qui l'annonçait.

## Règle HARD 5 — droits `gh` : épingler, ne pas basculer

`myia-ai-01` a `MergePullRequest` sur `jsboige/CoursIA`, **mais pas** sur `jsboige/MetaGeneticSharp` ni sur `MyIntelligenceAgency/*` (`GraphQL: myia-ai-01 does not have the correct permissions`). Épingler le jeton **par commande** :

```bash
GH_TOKEN=$(gh auth token --user jsboige --hostname github.com) gh pr merge <N> --repo <owner>/<repo> --squash
```

Préférer cette forme à `gh auth switch`, qui mute un état **global au process `gh`** et entre en course avec les autres sessions de la machine (cf [coordinator-discipline.md](coordinator-discipline.md) R1, [model-delegation.md](model-delegation.md) R6). Et **jamais `--delete-branch`** : la branche est ce qui permet de rouvrir une PR fermée par erreur.

## Règle HARD 6 — un sous-module compte dans le provisionnement

Une lane sans grain peut être servie par un sous-module : son backlog fait partie du pool. Un cycle `/coordinate` qui ne regarde que `jsboige/CoursIA` laisse structurellement quatre dépôts sans coordinateur — c'est précisément l'état que ce mandat corrige. La mesure de la Règle 2 est à passer **à chaque cycle**, au même titre que la passe de merge.

## Voir aussi

- [docs/reference/submodule-maintenance-detail.md](../../docs/reference/submodule-maintenance-detail.md) — **détail** : table de statut de gate, mesures datées, incidents
- `~/.claude/CLAUDE.md` §Git — commiter dedans, push, puis bump le parent
- [coordinator-discipline.md](coordinator-discipline.md) — R1 (merge actif), R4 (jamais sanctionner l'idle), R5 (steer qui atteint)
- [proactive-coordination.md](proactive-coordination.md) — R5, le pool n'est pas borné à un dépôt
- [git-workflow.md](git-workflow.md) — force push, scan de branche orpheline
- **Epic #1206** — piste Z3.Linq : fork endjin + port + PRs upstream (issue `endjin/Z3.Linq#29` = pivot de provenance)
