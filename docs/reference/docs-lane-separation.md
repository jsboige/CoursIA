# Séparation des lanes de documentation — pérenne / transiente

> REFERENCE — vivante — dernière révision 2026-11-11

> REFERENCE — vivante — dernière révision 2026-11-10

L'arbre `docs/` vit deux lanes distinctes (design #14623) : des **documents pérennes**
(références, procédures, règles — vivants, mis à jour sur place) et des **rapports
transients** (mesures datées, figées). La convention complète de la lane transiente
— nom daté, en-tête gelé, les trois destinations, le contrat de distillation — vit
dans le [README de la lane](../transients/README.md). Cette référence pérenne porte
la **méthode de tri** qui alimente la lane et renvoie le suivi des vagues de
distillation à l'issue #14623, deux choses que le README de lane (description de soi)
ne porte pas.

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

## Application mesurée

La passe du 2026-11-02 a classé 56 documents pérennes intouchés depuis 5+ semaines.
Les classements et les preuves de cette application sont conservés dans le rapport
transient [2026-11-02-tri-perennel-stale-56](../transients/2026-11-02-tri-perennel-stale-56.md) ;
l'état des vagues ultérieures se suit dans l'issue #14623.

## Vérification

```bash
python scripts/check_docs_transients_lane.py --distillation   # chaque rapport de la lane est cité par un doc pérenne
```

## Voir aussi

- [README de la lane transiente](../transients/README.md) — convention complète (nom, en-tête, destinations, distillation)
- [scripts-reference.md](scripts-reference.md) — organes `check_docs_transients_lane.py` / `check_docs_reference_lane.py`
- Issue [#14623](https://github.com/jsboige/CoursIA/issues/14623) — le design des deux lanes
