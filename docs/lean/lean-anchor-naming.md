# Convention de noms d'ancres `native_decide` du gate Lean

**Source :** #21905 (investigation + déplacement de la source de vérité du
matching). **Date de mesure :** 2026-10-24, branche
`fix/21905-anchor-naming-source`.

## Ce que le matching fait

Le gate `proof-integrity` (`.github/workflows/lean-axiom.yml`,
`fail-on-sorry` + `allow-axioms`) compare **exact-string** les noms
d'axiomes que Lean émet au build (`#print axioms`) à la liste d'autorisation
de l'appelant. Il n'y a ni normalisation, ni prefixe, ni wildcard : un nom
qui diffère d'un caractère d'une entrée autorisée est un rouge. Le parsing
de la variable `ALLOW` (liste à virgules, ou `@<chemin>` vers un fichier
source de vérité depuis #21905) vit dans `scripts/lean/allow_list.py`
(unit-testé : `scripts/tests/test_axiom_allow_file.py`).

## La convention observée — mesure, pas supposition

Sous le lake `conway_lean`, **une seule** des 77 entrées du job
`proof-integrity-audit` porte un suffixe non-ASCII :

```
Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1✝
```

Le suffixe est la **croix latine U+271D** (`✝`), pas la daguère U+2020
(`†`) — c'est le codepoint que Lean émet, vérifié :

1. **sur le workflow** : le seul caractère non-ASCII exotique de tout
   `.github/workflows/lean-conway.yml` est U+271D, porté par cette seule
   entrée (grep exhaustif des codepoints > U+007F) ;
2. **sur les logs du run CI vert** `39746855422` : la ligne
   `#print axioms` de `p4_base_exhaustive` émet le nom **avec** le suffixe
   U+271D — le match exact-string contre l'entrée autorisée réussit, d'où le
   vert.

> **Portée de la mesure, dite honnêtement :** le rejeu local
> `lake build` de `conway_lean` est inopérant à froid (`.lake` vide,
> Mathlib à reconstruire — inadapté à un cycle). Les noms émis sont donc
> sourcés des **logs du dernier run CI vert**, pas d'un build local de la
> session. La convention « Lean émet le suffixe de façon systématique pour
> cet ancre » est portée par cette mesure CI, pas par un rejeu local.

Le **grep item 4** de l'issue (autres suffixes exotiques dans le workflow)
renvoie **aucun autre** : les seuls autres caractères non-ASCII du fichier
sont de la prose (`§ · à é ê î — ℕ → ∀ ≤ ≥`), aucun dans un nom d'axiome.

## Pourquoi le suffixe est là et ne se « nettoie » pas

Le nom `p4_base_exhaustive...ax_1_1✝` n'est pas une coquille à corriger :
c'est **l'identifiant que Lean dérive** pour cet ancre, et le gate le
consomme tel quel. Retirer le U+271D d'une entrée de la liste (ou
normaliser côté parsing) sans re-mesurer l'émission au build
**désalignerait le matching** : le gate ferait alors rouge un ancre qui
était vert — c'est l'inverse du but. Toute future modification de
sanitisation (normaliser le suffixe à l'émission côté `#print axioms`, ou
côté parser) est une **décision séparée** qui exige sa propre mesure
d'émission : elle est hors du périmètre de #21905 et part dans la PR de
suivi `lean-axiom-name-sanitization` si le mainteneur la demande.

## Source de vérité de la liste

La liste des 77 noms n'est **plus inline** dans le workflow : elle vit dans
`scripts/lean/allow_axioms_conway.txt` (une entrée par ligne, `#`
commentaires ignorés), pointée par

```yaml
allow-axioms: "@scripts/lean/allow_axioms_conway.txt"
```

Le chemin se résout contre la racine du checkout (`GITHUB_WORKSPACE` en
CI) par `scripts/lean/allow_list.py`, avec repli sur le cwd pour un run
local. Fail-closed : un `@<chemin>` inexistant fait échouer le step — une
allow-list manquante n'est jamais traitée comme une allow-list vide.

Deux dérivs du workflow corrigés au passage du move :

- le commentaire de l'en-tête du job audit disait **81** noms ; la mesure
  au move en trouve **77** (dérive postérieure à #21833 — les twins `_en`
  `_initial_nonempty` perdent leurs ancres, 10 entrées — sans que le compte
  soit suivi). Le commentaire est corrigé.
- la liste inline portait l'entrée `✝` en pleine ligne YAML : l'extraire
  vers un fichier évite de rescrir une ligne de 4 Ko à chaque évolution
  d'ancres du lake.

## Gardes de régression

- `scripts/tests/test_axiom_allow_file.py` — round-trip byte-identique de
  l'entrée U+271D, absence de wildcard, compte 77, cablage workflow→fichier.
- `scripts/lean/tests/test_conway_blocking_gate_whitelist_aligned.py` —
  inchangé, toujours vert (il vise le job **bloquant**, pas l'audit).
