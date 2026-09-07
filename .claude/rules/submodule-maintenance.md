# Sous-modules — maintenance active, jamais un dépôt dormant

S'applique au **coordinateur ai-01** et à toute lane qui touche un sous-module. Source : mandat user 2026-09-02, verbatim :

> « Ca sera une bonne chose de ne pas laisser nos sous-modules sans maintenance, si j'ai souhaité les définir comme sous-modules de CoursIA, c'est pour qu'ils puissent évoluer avec nous et **chacun d'eux a un rôle dans le dépôt principal qui n'est plus à démontrer**. »

La conséquence pratique : un sous-module n'est pas une dépendance qu'on subit, c'est un dépôt **du cluster** dont le backlog est **notre** backlog. Une PR qui dort six semaines chez `MyIntelligenceAgency` est exactement aussi grave qu'une PR qui dort sur `jsboige/CoursIA`.

## Règle HARD 1 — le périmètre est de cinq dépôts, pas trois

| Chemin dans CoursIA | Remote | Entretien |
|---|---|---|
| `MyIA.AI.Notebooks/Search/MetaGeneticSharp` | `jsboige/MetaGeneticSharp` | coordination ai-01 |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq` | `MyIntelligenceAgency/Z3.Linq` — **fork de `endjin/Z3.Linq`** | coordination ai-01 ; les livraisons partent **en PR upstream** (Epic #1206) |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Automata` | `MyIntelligenceAgency/Automata` | coordination ai-01 |
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum` | `ArgumentumGames/Argumentum` | **agent permanent dédié** — ai-01 ne fait que le bump de pointeur |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/semantic-fleet` | `MyIntelligenceAgency/semantic-fleet` (`branch = stable-from-v0343`) | coordination ai-01 |

**`Automata` est le cinquième, et il est facile à oublier** : il n'apparaît dans aucun dispatch historique. La liste faisant foi est `.gitmodules`, jamais un souvenir — c'est en la lisant qu'on découvre aussi que `MetaGeneticSharp` vit sous `jsboige/`, **pas** sous `MyIntelligenceAgency/` (un `gh pr list --repo MyIntelligenceAgency/MetaGeneticSharp` rend `Could not resolve to a Repository`, ce qui se lit à tort comme « rien à faire »).

**Le périmètre déclaré est désormais le périmètre maintenu.** `.gitmodules` ne contient plus que ces cinq forks : les trois `foundry-lib/lib/*` (`forge-std`, `openzeppelin-contracts`, `account-abstraction`) en ont été retirés (#14518). C'étaient des upstreams tiers, pas des forks — on ne les faisait pas vivre et on ne le pouvait pas. Ils s'installent via `forge install --no-git`, pinnés sur `foundry-lib/foundry.lock`, et vivent sous `.gitignore` — régénérables comme `node_modules`.

**Le critère tient en une phrase** : un sous-module est un dépôt **qu'on fait vivre**. Une dépendance de build qu'on subit se clone, elle ne se déclare pas — quantité de composants clonent leurs dépendances sans que le dépôt parent s'en encombre.

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

La référence de comparaison est la **branche déclarée** quand `.gitmodules` porte un `branch =` (`refs/heads/` explicite, pour ne jamais résoudre un tag homonyme), `HEAD` sinon — `HEAD` résout la branche par défaut et déclare « DERIVE » un gitlink qui est exactement sur sa branche déclarée (#14872 : faux positif permanent sur `semantic-fleet`). Et un `ls-remote` muet (ref injoignable, 403 d'org, réseau) s'affiche `INJOIGNABLE`, jamais comme une égalité — la même leçon que celle du `403` de la mesure de gate ci-dessous.

**Ordre obligatoire** (déjà porté par le `CLAUDE.md` global) : commiter **dedans** d'abord, pousser, **puis** bumper le pointeur parent. Jamais l'inverse.

**Un `branch =` dans `.gitmodules` n'est pas le gitlink.** `semantic-fleet` déclare `branch = stable-from-v0343` alors que son gitlink pointe ailleurs et que son `main` est ailleurs encore : **trois références divergentes** qui se lisent comme un seul état. Réconcilier explicitement avant de conclure quoi que ce soit sur le retard d'un sous-module.

## Règle HARD 3 — l'absence de gate est le défaut, pas les PRs qui dorment

Avant de traiter un backlog de sous-module comme de la négligence, **vérifier qu'un gate existe et se déclenche** :

- `MetaGeneticSharp` n'a **aucun workflow**.
- `semantic-fleet` en a plusieurs, mais aucun ne s'est déclenché sur les PRs concernées — bases de *stack* hors des branches sur lesquelles ils sont câblés.

Trois PRs dormantes sous un dépôt sans gate ne sont pas trois oublis : c'est **un** défaut structurel, et le corriger vaut mieux que relancer les auteurs. Le manque de CI se traite en **issue de suivi nommée**, pas en reproche de lane.

**Substitution admise tant que le gate manque** : deux vérifications **firsthand indépendantes** (fresh-clone, build + suite de tests complète, sur **deux lanes distinctes**), avec leurs comptes de tests et leurs SHA **cités dans le body de la PR de bump**. Une seule vérification, ou une vérification par l'auteur seul, ne remplace pas un gate.

**Statut de gate par sous-module (mise à jour c.14463 / c.14566)** : l'organe externe à la R3 est la **liste des submod avec un workflow fonctionnel** — la substitution R3 s'applique par défaut, sauf si la liste ci-dessous dit « gate acquis ». Une PR de bump qui omet les deux vérifications et qui ne cite pas un submod à « gate acquis » **manque à R3** ; un submod listé à « gate acquis » qui perd son workflow (drift, suppression) **redevient** soumis à la substitution. Le passage d'un submod d'un état à l'autre est lui-même un **geste tracké** : PR dédiée sur le dépôt submod (câblage ou re-câblage), référence dans le tableau ci-dessous, et revue coord pour valider la bascule. **Cinq états** (cf. tableau) : `Absent`, `Câblé jamais déclenché sur pile`, `Câblé déclenché vert récent`, `Drift / perte de gate`, `Câblé déclenché rouge récent`.

**Cinq états de gate** (mesurés firsthand par la commande de la colonne « vérifié le ») :

1. **Absent** (`MetaGeneticSharp`, `Automata`) — aucun workflow, aucun run. Substitution R3 active par défaut.
2. **Câblé, jamais déclenché sur pile en cours** (`Z3.Linq`) — workflows existent et sont actifs, mais le déclenchement ne couvre pas les PRs/processus visés (base de stack hors-trigger). Substitution R3 **active**, et le **déclencheur** doit être qualifié pour cesser (pas seulement le câblage).
3. **Câblé, déclenché, vert récent** (cas général à viser) — un run vert sur la branche par défaut du submod **satisfait** A2 et la substitution R3 **cesse** de s'appliquer.
4. **Drift / perte de gate** — un submod listé en (3) qui perd son workflow (suppression, mise hors-service) **redevient** soumis à la substitution. Bascule trackée.
5. **Câblé, déclenché, rouge récent** (`semantic-fleet` au 2026-09-04) — run vert manquant, substitution R3 active jusqu'à un retour au vert. **Bascule différente** du (3) car le gate existe et déclenche, juste sur une branche hors-main / avec une régression.

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

**Précondition de jeton (mesurée le 2026-09-05)** : l'org `MyIntelligenceAgency` refuse les fine-grained PATs de plus de 366 jours. Sous un tel jeton la boucle rend `403` sur ses **trois** repos et 3/5 lignes deviennent infetchables. Elle passe sous `jsboige` **et** sous `myia-ai-01` depuis ai-01, et `403` sous le PAT de po-2026 : la précondition n'est donc pas un compte particulier, c'est **un jeton que l'org accepte** -- l'épingler par commande (`GH_TOKEN=$(gh auth token --user <compte>)`), jamais par `gh auth switch` (état global au process `gh`, cf. R5). **Un `403` est une question, pas une absence mesurée** : ne jamais en conclure « 0 workflow » -- c'est exactement la ligne fausse que ce tableau existe pour empêcher.

| Submodule | Workflow CI | Run vert récent | Substitution R3 | Vérifié le (PR) |
|---|---|---|---|---|
| `MyIA.AI.Notebooks/Search/MetaGeneticSharp` | **Absent** (0 workflow, 0 run) | — | OUI | #14566 (#14558, c.14463) |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq` | **Câblé, jamais déclenché sur pile** (3 workflows actifs, 5 runs totaux, dernier build vert 2026-09-04) | n/a sur pile | OUI | #14566 (#14558, c.14463) |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Automata` | **Absent** (0 workflow, 0 run) | — | OUI | #14566 (#14558, c.14463) |
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum` | agent permanent dédié (hors-org) | n/a dédié | OUI (gate hors-org, voir §Argumentum dédiée) | n/a hors-org |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/semantic-fleet` | **Câblé, déclenché, rouge récent** (18 workflows, 15 actifs, 538 runs totaux, 2 failure `dotnet-format` + `dotnet-integration-tests` à 2026-09-04T04:20Z sur `fix/c716-7225-multiconnector-tests-rewrite`) | non-vert | OUI (jusqu'à un run vert) | #14566 (#14558, c.14463) |

**Application concrète** : une PR de bump sur `MetaGeneticSharp` qui se contente de citer un SHA upstream **manque R3** tant que A2 n'est pas acquis (#14408). Une PR de bump qui cite un run vert sur la branche par défaut du submod **satisfait** A2 et la substitution R3 **cesse** de s'appliquer à `MetaGeneticSharp` (les bumps suivants peuvent omettre les deux vérifications). Le passage d'« aucun workflow » à « workflow acquis » est un **commit sur le submod** (câblage `.github/workflows/dotnet-ci.yml` sur `jsboige/MetaGeneticSharp`), suivi d'une **mise à jour du tableau ci-dessus** dans une PR sur CoursIA-2.

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

- `~/.claude/CLAUDE.md` §Git — commiter dedans, push, puis bump le parent
- [coordinator-discipline.md](coordinator-discipline.md) — R1 (merge actif), R4 (jamais sanctionner l'idle), R5 (steer qui atteint)
- [proactive-coordination.md](proactive-coordination.md) — R5, le pool n'est pas borné à un dépôt
- [git-workflow.md](git-workflow.md) — force push, scan de branche orpheline
- **Epic #1206** — piste Z3.Linq : fork endjin + port + PRs upstream (issue `endjin/Z3.Linq#29` = pivot de provenance)
