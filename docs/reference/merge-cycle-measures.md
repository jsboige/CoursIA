# Cycle de merge — mesures qui fondent le contrat

Detail de [`.claude/rules/merge-cycle-contract.md`](../../.claude/rules/merge-cycle-contract.md). Le harnais porte les quatre regles ; ce fichier porte les chiffres, pour que le harnais reste succinct ([harness-hygiene](../../.claude/rules/harness-hygiene.md)).

## Le cycle du 2026-09-22 — 30 merges, et ou sont partis les refus

30 PRs mergees sur la fenetre, mesure firsthand (`search/issues is:pr is:merged merged:>=<debut>` = 30), corroborant exactement la somme des trois passes du cycle (2 + 10 + 18). Le mandat user de ~20 merges par cycle est tenu.

Sur **80 candidates** passees au gate d'entree :

| Issue | Compte | Ce que ca dit |
|---|---:|---|
| mergees | 18 | — |
| **pas de dossier digne de confiance** (`rc=1`/`rc=2`) | **32** | la production de dossiers plafonne |
| **rouge CI** | **27** | cause d'infrastructure, pas un defaut de PR |
| `BLOCKED` atteste (`rc=3`) | 3 | dispatchable depuis le motif, sans ouvrir les surfaces |

**Aucune** des 59 refusees ne l'a ete pour un defaut d'elle-meme. C'est le constat qui fonde la regle 3 : renvoyer ces PRs a leurs auteurs leur demande de reparer ce qui n'est pas chez eux.

### Les 32 sans dossier, par motif

| Motif rendu par le gate | Compte |
|---|---:|
| surfaces changees ou non entierement attestees, dont **12** explicitement « changed after dossier » | ~20 |
| `no [ADJOINT PREFLIGHT] dossier comment found` | 11 |
| `rc=2` — snapshot bouge pendant la lecture | 1 |

Le motif dominant n'est pas l'absence de travail : c'est du travail **fait puis perime**. D'ou la regle 2.

## La mesure de conversion — pourquoi le format du rendu est le levier

Trois lots, meme cycle, meme gate, meme coordinateur :

| Lot | Format | Converti | Taux |
|---|---|---:|---:|
| titulaire | liste **nominative** | 10 / 10 | **100 %** |
| secretaire | **cumul** (« 56 OK B.0 frais ») | 15 / 53 | **28 %** |
| coordinateur | auto-tire sur les plus vieilles | 2 / 54 | **4 %** |

Le travail sous-jacent du deuxieme lot etait reel et de qualite : 96 PRs attestees, 56 fraiches. Il a converti a 28 % parce qu'il est arrive en **compte**, forcant une re-decouverte a l'aveugle sur 80 PRs — re-decouverte qui a elle-meme perime une partie des attestations qu'elle traversait.

**Le format de rendu pese davantage que le cout unitaire d'un appel API.** C'est la reponse structurelle a la question du plafond de quota, et elle est gratuite.

## Le cas fondateur de la regle 4 — #17390

Le gate (`scripts/check_adjoint_prevalidation.py`) recupere l'etat des checks **deux fois** par PR :

| Source | Ligne | Transport |
|---|---|---|
| `statusCheckRollup` dans `_pr_metadata` | `:732` | **GraphQL**, le champ le plus cher : il deplie chaque check-run |
| `_head_check_runs(headRefOid)` | `:763` via `:706` | **REST**, et deja la source de verite declaree du projet (`latest_wins_check_runs`, `:396`) |

Le retrait du champ est **juste** et n'a pas ete livre en code : `statusCheckRollup` entre dans `_metadata_identity`, donc dans l'empreinte, donc le retirer perime **toutes** les attestations en vol d'un coup (~92 au moment de la mesure). Le livrable est l'issue #17390, avec sa fenetre et son controle positif obligatoire — un test qui **echoue** si un check conclut pendant la lecture du snapshot.

Et la portee se declare : ce levier reduit le cout **par appel**, pas la peremption, qui est la cause dominante.

## Capacite CI — l'arbitrage user du 2026-09-22

Q34 du registre demandait s'il fallait plafonner la concurrence des runners sur ai-01. **Arbitrage user : non — on ne coupe pas la capacite, on l'equilibre entre GitHub, po-2024 et ai-01, et on monte po-2026 si besoin.**

Le cadrage binaire de la question etait fautif, et la mesure du vivant l'a montre. Sur ai-01 :

```
coursia-runner  : 10 slots x COURSIA_RUNNER_CPUS=2   = 20 vCPU
coursia-waiters : 16 slots x WAITER_CPUS=0.25        =  4 vCPU
                                               total = 24 vCPU
COURSIA_RUNNER_CPU_BUDGET = 24
coursia-ci.slice CPUQuota  = 24 vCPU  (nproc = 32)
```

Le dimensionnement est **coherent et delibere** : 24 demandes contre 24 accordes, au vCPU pres. Il n'y avait ni derive a corriger ni sur-souscription a reduire.

Le defaut est **l'absence de marge**. Un budget exactement sature throttle en permanence des que la charge monte, et chaque slot de calcul lance `pytest -n 4` — jusqu'a 40 workers xdist forkant du `git` sur 20 vCPU de quota. De la sortent les `BlockingIOError: [Errno 11]` sur `_fork_exec` (EAGAIN sur `fork()`) et les runners morts sans logs (`conclusion=null` + `BlobNotFound`).

Repartition du pool `coursia-linux`, cible de **129 des 173** declarations `runs-on` du depot :

| Hote | slots online | busy a la mesure |
|---|---:|---:|
| `myia-ai-01` | 10 | 8 |
| `myia-po-2024` | 8 | 7 |
| `myia-po-2026` | 2 | 2 |
| **total** | **20** | **17** |

Le levier retenu est donc d'**ajouter** des slots sur po-2026 (cible 8, parite avec po-2024), ce qui soulage ai-01 par le tirage de file sans toucher a sa configuration.

**Non etabli, et pas devine** : `docker ps` rend 0 conteneur runner sur ai-01 alors que 28 `Runner.Listener` tournent. La cause n'est pas mesuree. De meme, la corruption d'etiquette `cour sia-linux` signalee par po-2026 n'est pas mesurable depuis ai-01 (`actions/runners` rend 403 sous `myia-ai-01`, readlink sur `/proc/<pid>/cwd` refuse).

### Piege de provisionnement a ne pas rejouer

Deployer une unite systemd declarant N slots **sans** son drop-in de sizing fait retomber `supervise.sh` sur `MEMORY=4g` par defaut ; le garde de budget refuse, `Restart=always` reboucle toutes les 30 s, et le pool ne monte **jamais**. Les deux fichiers partent ensemble ou aucun. Et `assert_cpu_budget()` **sort immediatement sans rien imprimer quand le budget vaut 0** : son silence n'est pas un feu vert, c'est une absence de mesure. Detail : [`persist/README.md`](../../scripts/ci/docker/linux-runner/persist/README.md).
