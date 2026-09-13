# Sous-modules — détail : état vérifié, incidents et mesures datées

Détail déporté de [`.claude/rules/submodule-maintenance.md`](../../.claude/rules/submodule-maintenance.md), qui porte les règles HARD 1 à 6. Ce fichier porte ce qui **date** : la table de statut de gate, les mesures horodatées, les faux positifs mesurés et les incidents fondateurs. La règle référence ce fichier ; elle ne le duplique pas.

Motif du déport (`harness-hygiene`, 3 tiers) : le harnais est auto-chargé à **chaque requête** de **chaque session**, sur les cinq machines. Une table de SHA et de dates de vérification y coûte des tokens en permanence pour une information qui se relit ponctuellement, avant une PR de bump.

---

## 1. Périmètre — pourquoi la liste se lit dans `.gitmodules`

**`Automata` est le cinquième, et il est facile à oublier** : il n'apparaît dans aucun dispatch historique. La liste faisant foi est `.gitmodules`, jamais un souvenir.

**Faux négatif à connaître** : `MetaGeneticSharp` vit sous `jsboige/`, **pas** sous `MyIntelligenceAgency/`. Un `gh pr list --repo MyIntelligenceAgency/MetaGeneticSharp` rend `Could not resolve to a Repository` — ce qui se lit à tort comme « rien à faire ». L'erreur porte sur l'organisation, pas sur le backlog.

### Retrait des trois `foundry-lib/lib/*` (#14518)

`.gitmodules` ne contient plus que les cinq forks. Les trois `foundry-lib/lib/*` (`forge-std`, `openzeppelin-contracts`, `account-abstraction`) en ont été retirés : c'étaient des upstreams tiers, pas des forks — on ne les faisait pas vivre et on ne le pouvait pas. Ils s'installent via `forge install --no-git`, pinnés sur `foundry-lib/foundry.lock`, et vivent sous `.gitignore` — régénérables comme `node_modules`.

Le critère qui a tranché : un sous-module est un dépôt **qu'on fait vivre**. Une dépendance de build qu'on subit se clone, elle ne se déclare pas — quantité de composants clonent leurs dépendances sans que le dépôt parent s'en encombre.

---

## 2. Faux positif permanent `HEAD` vs branche déclarée (#14872)

**Un `branch =` dans `.gitmodules` n'est pas la branche par défaut du dépôt distant.** `semantic-fleet` déclare `branch = stable-from-v0343`, et sa branche par défaut est `main` : **deux** références, pas trois.

Mesure du 2026-09-07 :

| Référence | SHA |
|---|---|
| gitlink sur `origin/main` | `9df360374e1c` |
| tip de la branche déclarée `stable-from-v0343` | `9df360374e1c` — **identique** |
| `HEAD` distant (branche par défaut `main`) | `168fd5d8bef5` |

Le gitlink est **exactement sur sa branche déclarée**. C'est l'état *nominal* d'un sous-module épinglé, pas une dérive à réconcilier.

**Note de rédaction** : une version antérieure de la règle disait l'inverse (« son gitlink pointe ailleurs », « trois références divergentes »). Elle envoyait le lecteur chercher une troisième divergence qui n'existe pas, et lui faisait lire comme un retard ce qui est le fonctionnement attendu. Le seul point à retenir est celui que porte désormais la règle : comparer le gitlink à `HEAD` **fabrique** une dérive ; comparer à `refs/heads/<branche déclarée>` mesure la vraie.

`refs/heads/` est explicite pour ne jamais résoudre un tag homonyme. Un `ls-remote` muet (ref injoignable, 403 d'org, réseau) s'affiche `INJOIGNABLE`, jamais comme une égalité — même leçon que le `403` de la mesure de gate ci-dessous.

---

## 3. Précondition de jeton pour la mesure de gate (mesurée le 2026-09-05)

L'org `MyIntelligenceAgency` refuse les fine-grained PATs de plus de 366 jours. Sous un tel jeton, la boucle de mesure rend `403` sur ses **trois** repos et 3/5 lignes deviennent infetchables.

Elle passe sous `jsboige` **et** sous `myia-ai-01` depuis ai-01, et rend `403` sous le PAT de po-2026 : la précondition n'est donc pas un compte particulier, c'est **un jeton que l'org accepte**. L'épingler par commande :

```bash
GH_TOKEN=$(gh auth token --user <compte>) gh api ...
```

Jamais par `gh auth switch`, qui mute un état **global au process `gh`** (cf. règle HARD 5).

**Un `403` est une question, pas une absence mesurée** : ne jamais en conclure « 0 workflow ». C'est exactement la ligne fausse que la table ci-dessous existe pour empêcher.

---

## 4. Table de statut de gate par sous-module

**À relire avant chaque PR de bump** (mise à jour c.14463 / c.14566) — cet état date de sa mesure, pas de sa lecture. La colonne « Vérifié le » porte le cycle et la PR qui l'ont établi.

| Submodule | Workflow CI | Run vert récent | Substitution R3 | Vérifié le (PR) |
|---|---|---|---|---|
| `MyIA.AI.Notebooks/Search/MetaGeneticSharp` | **Câblé, déclenché, rouge récent** — 1 workflow `dotnet-ci`, 8 runs totaux ; run #7 ubuntu+windows SUCCESS sur PR avant merge ; run `34208179870` post-merge sur `main` SHA `dbcd40473e0fad04505b362276e8d3acf6982926` : ubuntu SUCCESS 2026-09-08T09:07:35Z, **windows FAILURE** 2026-09-08T09:08:40Z | non-vert (job Windows) | **OUI** | c.1003 (#15190, post-DM ai-01 2026-09-08T15:21Z — état corrigé post-`CHANGES_REQUESTED`) |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Z3.Linq` | **Câblé, jamais déclenché sur pile** — 3 workflows actifs, 5 runs totaux, dernier build vert 2026-09-04 | n/a sur pile | OUI | #14566 (#14558, c.14463) |
| `MyIA.AI.Notebooks/SymbolicAI/SMT/Automata` | **Absent** — 0 workflow, 0 run | — | OUI | #14566 (#14558, c.14463) |
| `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argumentum` | **Câblé, déclenché, vert récent** — 5 workflows / 5 actifs, 4479 runs totaux, `Build` success 2026-09-07T04:08:13Z sur `master` SHA `bab289c05bb6` ; master HEAD courant `f5acc7bedd05`, build re-déclenché 2026-09-07T09:21:11Z | vert | **NON** | #15007 (c.956, 2026-09-07) |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/semantic-fleet` | **Câblé, déclenché, rouge récent** — 18 workflows, 17 actifs, 553 runs totaux, dernier `Python Integration Tests` failure 2026-09-07T01:29:00Z sur `main` | non-vert | OUI (jusqu'à un run vert) | #15007 (c.956, 2026-09-07) |

### Le cas `MetaGeneticSharp` — câblé depuis c.990, toujours rouge

`MetaGeneticSharp` porte un workflow `dotnet-ci` depuis c.990 (PR #53 mergée 2026-09-08T09:06:40Z sur `jsboige/MetaGeneticSharp`). Il n'est donc plus dans l'état « Absent ».

Le run post-merge sur `main` reste **FAILURE côté Windows**, sans message d'erreur explicite : NUnit Adapter 4.6.0.0 rapporte « Test Run Successful » 180/180, puis le step de test postérieur sort en exit code 1. Le flaky-Windows s'investigue **à part**, et se démontre par **un second run vert sur le même SHA** — pas par un run vert sur un autre SHA.

**Conséquence** : la substitution R3 reste **OUI** tant qu'aucun run main complet n'est vert. Un bump doit citer le SHA upstream **et** les deux vérifications firsthand.

### Le cas `semantic-fleet` — des workflows qui ne tirent pas sur la pile

`semantic-fleet` en porte plusieurs, mais **aucun ne s'est déclenché sur les PRs concernées** : les bases de *stack* vivent hors des branches sur lesquelles ils sont câblés. L'état 2 (« câblé, jamais déclenché sur la pile ») se superpose donc à l'état 5 mesuré sur `main` — et c'est pourquoi qualifier le **déclencheur** compte autant que constater le câblage.

### Application concrète de la bascule

- Une PR de bump sur `MetaGeneticSharp` qui se contente de citer un SHA upstream **manque R3** tant que A2 n'est pas acquis (#14408).
- Une PR de bump qui cite un **run vert sur la branche par défaut** du submod **satisfait** A2 : la substitution R3 **cesse** de s'appliquer à ce sous-module, et les bumps suivants peuvent omettre les deux vérifications.
- Le passage d'« aucun workflow » à « workflow acquis » est un **commit sur le submod** (câblage `.github/workflows/dotnet-ci.yml`), suivi d'une **mise à jour de la table ci-dessus** dans une PR sur CoursIA-2.

---

## Voir aussi

- [`.claude/rules/submodule-maintenance.md`](../../.claude/rules/submodule-maintenance.md) — les règles HARD 1 à 6
- [`.claude/rules/harness-hygiene.md`](../../.claude/rules/harness-hygiene.md) — les 3 tiers, motif de ce déport
- **Epic #1206** — piste Z3.Linq : fork endjin + port + PRs upstream (issue `endjin/Z3.Linq#29` = pivot de provenance)
