# Prévalidation — pourquoi l'ordre compte, et ce que la tête vient périmer (#16878)

Détail déporté de la puce « `update-branch` tue AUSSI le dossier de prévalidation » de [`git-workflow.md`](../../.claude/rules/git-workflow.md). Le sujet : **le dossier de prévalidation atteste une tête, pas une PR** — et l'ordre des gestes qui en découle.

**La règle fait foi** pour l'ordre et le gel ; ce document ne les rejoue pas, il donne le **pourquoi** (le mécanisme vérifié à la source, la boucle réelle, et les deux prémisses de l'issue fondatrice qui étaient fausses).

## 1. La mesure fondatrice — 17 candidates sur 17

**Rapporté par l'issue #16878** (2026-09-19), non re-mesuré ici : le gate d'entrée de la passe de merge (`scripts/check_adjoint_prevalidation.py`) a rendu `exit 1` sur **17 candidates sur 17**, et **aucun** de ces refus ne portait sur un défaut de PR. Les trois motifs observés, verbatim de l'issue :

```
- head is stale: dossier=174bf0db..., live=caeec4d9...
- discussion surfaces changed or were not fully attested
- diff-files is stale: dossier=2, live=1
```

Distinction à tenir : le **fait** « 17/17, aucun défaut de PR » est un témoignage daté ; ce qui est **vérifié ici** est le **mécanisme** qui le produit (§2) — et c'est le mécanisme qui justifie la règle. Une règle qui ne s'appuierait que sur le compte serait un argument d'autorité ; elle s'appuie sur le code.

## 2. Le mécanisme, vérifié à la source

`scripts/check_adjoint_prevalidation.py` épingle dans le dossier des **surfaces mesurées à l'instant T**, puis refuse si elles ont bougé.

Surfaces comparées — `diff-files`, `diff-additions`, `diff-deletions` :

```python
# l.548-550
        "diff-files": snapshot["changedFiles"],
        "diff-additions": snapshot["additions"],
        "diff-deletions": snapshot["deletions"],
```

Le refus, générique sur toute surface comptée :

```python
# l.552-554
    for key, live_value in comparisons.items():
        if integers.get(key) is not None and integers[key] != live_value:
            errors.append(f"{key} is stale: dossier={integers[key]}, live={live_value}")
```

Le refus sur la tête — la surface qui décide de tout :

```python
# l.556-558
    if f.get("head") != snapshot["headRefOid"]:
        errors.append(
            f"head is stale: dossier={f.get('head', '?')}, live={snapshot['headRefOid']}"
        )
```

Et la surface des discussions, qui n'est pas un compte :

```python
# l.534
            "discussion surfaces changed or were not fully attested: "
```

**Conséquence** : `gh pr update-branch` crée un commit de fusion, donc **change la tête**. Le dossier écrit avant atteste `caeec4d9…` alors que la PR vit à `174bf0db…` : `head is stale`. Le gate refuse — **à raison**. Le défaut n'est pas dans le gate, il est dans **l'ordre** : le protocole demandait le dossier **avant** la stabilisation de la branche.

## 3. La boucle, et où elle se referme réellement

Le raisonnement de l'issue #16878 était :

1. `main` devient rouge → les lanes doivent `update-branch` pour récupérer le correctif. **C'est le bon geste.**
2. `update-branch` change la tête → le dossier est périmé, les comptes de diff bougent.
3. le même `update-branch` ré-arme le DWELL de 120 min → `PR gate` rouge.
4. DWELL rouge → l'adjoint ne peut pas attester `checks: latest-wins-green` → il **retient** le dossier, à juste titre.
5. pas de dossier → `exit 1` → pas de merge → la PR vieillit → il faut re-`update-branch`.

**L'étape 3 est fausse dans le cas courant, et c'est la correction apportée ici.** Depuis **#16149**, `scripts/ci/merge_dwell.py` mesure le plancher par `last_authoritative_committed_at` : la date de **committer** du dernier commit qui **modifie le côté PR**. Une fusion de rafraîchissement de base **prouvée content-free** (deux parents · second parent ancêtre de la base · arbre identique à l'auto-merge) est **sautée** — le plancher est donc **inchangé** par un `update-branch` **sans conflit**, qui est le cas ordinaire. La règle portait cette affirmation périmée jusqu'à #16962/#17286.

**La boucle se referme donc par l'étape 2, pas par l'étape 3.** C'est suffisant pour la bloquer : la péremption du dossier par changement de tête ne dépend pas du DWELL. Le DWELL reste une raison d'**attendre** (le plancher issu des commits de contenu est toujours là) — jamais une raison de ré-écrire un dossier.

Ce détail compte pour la suite : une issue qui motive un protocole par un mécanisme faux reste dangereuse même quand le protocole est bon, parce que la prochaine personne à toucher le sujet réintroduira l'erreur en toute bonne foi.

## 4. Ce qui était déjà écrit, et où

L'issue écrit : « **L'autre moitié n'est écrite nulle part** ». C'est **inexact** — la péremption par changement de tête/surface est déjà portée par [`coordinate/SKILL.md`](../../.claude/skills/coordinate/SKILL.md) :

> un contrat machine-lisible exact-head, trois surfaces B.0, checks latest-wins, scope, domaine et verdict ; **un changement de head ou de surface le perime**.

Ce qui manquait n'est donc pas le **fait**, c'est **l'ordre** — et le fait qu'il soit nommé comme la condition qui débloque la boucle. La règle **renvoie** au skill pour le fait plutôt que de le redécrire : deux surfaces qui reformulent la même règle finissent par diverger, c'est précisément le défaut de #16962.

## 5. Pourquoi cet ordre — et pas un autre

L'ordre en 4 temps lui-même est porté par la règle (puce « `update-branch` tue AUSSI le dossier de prévalidation ») ; il n'est **pas** recopié ici, pour la raison du §4.

Ce qui mérite d'être explicité, c'est **pourquoi le gel en est la pièce centrale** : c'est la seule qui ne se déduit pas du mécanisme. Un dossier a besoin d'une **branche silencieuse** — sans gel, le travail de prévalidation est détruit par le travail de réparation, et le gel ne peut pas se déduire de « le dossier atteste une tête », il faut le **décider**.

Le blocage est structurel : **chacun fait exactement ce que son rôle prescrit** — la lane rafraîchit (bon geste), l'adjoint atteste à la tête exacte (sa fonction), le coordinateur exige un dossier valide (le gate). Aucun des trois gestes n'est fautif ; le défaut est dans leur **séquence**, donc aucun des trois ne peut en sortir seul. C'est ce qui rend l'ordre — et non le constat — la livraison.

## Voir aussi

- [`.claude/rules/git-workflow.md`](../../.claude/rules/git-workflow.md) — la règle : les deux moitiés du mécanisme `update-branch`, l'ordre, le gel
- [`scripts/check_adjoint_prevalidation.py`](../../scripts/check_adjoint_prevalidation.py) — le gate, et ses trois codes de sortie
- [`.claude/skills/coordinate/SKILL.md`](../../.claude/skills/coordinate/SKILL.md) — la passe de merge, la péremption par tête/surface
- [#16962 / #17286](https://github.com/jsboige/CoursIA/issues/16962) — le prédicat DWELL réel, et pourquoi la règle l'avait périmé
