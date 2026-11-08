# Séparation des lanes de documentation — pérenne / transiente

> REFERENCE — vivante — dernière révision 2026-11-08

L'arbre `docs/` vit deux lanes distinctes (design #14623) : des **documents pérennes**
(références, procédures, règles — vivants, mis à jour sur place) et des **rapports
transients** (mesures datées, figées). La convention complète de la lane transiente
— nom daté, en-tête gelé, les trois destinations, le contrat de distillation — vit
dans le [README de la lane](../transients/README.md). Cette référence pérenne porte
la **méthode de tri** qui alimente la lane et l'**état courant de la resorption**,
deux choses que le README de lane (description de soi) ne porte pas.

## La méthode de tri de l'arbre pérenne

Passe récurrente : on mesure les documents pérennes **intouchés depuis 5+ semaines**
puis on les **classe** — jamais on ne les déplace en masse :

1. **transient** → déplacé vers `docs/transients/` par `git mv` pur (sortie de scan,
   capture d'une issue close, sans consommateur) ;
2. **vivant** → référence stable, rien à faire ;
3. **figé par construction** → artefact régénéré par la CI, registre append-only,
   pré-enregistrement d'expérience : le gel est sa fonction, pas une dérive — reste pérenne ;
4. **daté, à distiller** → contenu durable qui a un foyer pérenne ; extraction par
   document, un grain séparé chacun.

Principe porteur : **intouchés ≠ morts** — une référence stable ne bouge pas par
construction, sa stabilité n'est pas une dérive. Le tri rend visible ce qui, dans
l'arbre pérenne, a fini son office de vivant, sans suppression ni déplacement aveugle.

## État de la resorption — queue de distillation

La passe du 2026-11-02 (56 intouchés sur 316 pérennes) a classé l'arbre et listé
**11 documents datés à distiller** dans les vagues suivantes :
`reference/adk-migration-2-eval` · `reference/backtester-e2-cadrage` ·
`reference/backtester-e2-svm-kernel` · `reference/ci-aggregator-rollout` ·
`reference/dotnet-restore-rfc-17361` · `reference/probas-history` ·
`reference/review-coverage-threshold` · `ml/bdh-evaluation` ·
`lean/life-sat-cost-frontier` · `lean/cluster-junctions-c857` ·
`ci/po2024-topology-baseline`.

Application mesurée de la méthode — classements complets et preuves des 56 intouchés :
[2026-11-02-tri-perennel-stale-56](../transients/2026-11-02-tri-perennel-stale-56.md).

## Vérification

```bash
python scripts/check_docs_transients_lane.py --distillation   # chaque rapport de la lane est cité par un doc pérenne
```

## Voir aussi

- [README de la lane transiente](../transients/README.md) — convention complète (nom, en-tête, destinations, distillation)
- [scripts-reference.md](scripts-reference.md) — organes `check_docs_transients_lane.py` / `check_docs_reference_lane.py`
- Issue [#14623](../../issues/14623) — le design des deux lanes
