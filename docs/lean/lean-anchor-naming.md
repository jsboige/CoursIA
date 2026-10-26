# Convention de noms d'ancres `native_decide` du gate Lean

## Ce que le matching fait

Dans `LeanVerifier.check_axioms`, le matching est normalisé des deux côtés
par `normalize_axiom_name` : les noms extraits de `#print axioms` et les
entrées de l'allow-list sont transformés, puis comparés par appartenance
à un ensemble
(`MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/lean_server.py:204-215` et
`:901-905`).

La normalisation est exactement celle-ci :

```python
_AXIOM_NAME_DECORATION_RE = re.compile(r"[^\w.'!?]+$")


def normalize_axiom_name(name: str) -> str:
    return _AXIOM_NAME_DECORATION_RE.sub("", name.strip().rstrip("."))
```

Elle applique, dans cet ordre :

1. `.strip()`, qui retire les espaces de bord ;
2. `.rstrip(".")`, qui retire les points terminaux ;
3. la regex `[^\w.'!?]+$`, qui retire la suite terminale de caractères hors
   de l'alphabet conservé : `\w` au sens Unicode de Python, `.`, `'`, `!`
   et `?`.

Elle ne réécrit ni le préfixe ni les caractères internes du nom, et conserve
notamment les suffixes `?` et `!`. Elle retire en revanche une décoration
terminale telle que la croix latine U+271D (`✝`). Deux orthographes qui ont la
même forme normalisée correspondent ; une ancre réellement différente reste
interdite. La comparaison porte sur le nom complet normalisé : il n'y a pas de
correspondance par préfixe ni d'interprétation de wildcard.

Le parsing de `ALLOW` accepte une liste à virgules ou `@<chemin>` vers un
fichier. Il est implémenté par `parse_allow` dans
`scripts/lean/allow_list.py:29-63`.

## Décoration terminale et lecture du fichier

L'allow-list Conway comporte notamment :

```text
Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1✝
```

Le suffixe est la croix latine U+271D (`✝`), distincte de la dague U+2020
(`†`). La forme normalisée de cette entrée est :

```text
Conway.Life.p4_base_exhaustive._native.native_decide.ax_1_1
```

Le parseur du fichier conserve le caractère U+271D à la lecture. La
normalisation intervient uniquement dans la comparaison du gate : la présence
de la décoration dans l'allow-list ou dans le nom extrait ne change donc pas
l'ancre retenue. Elle ne modifie jamais le fichier d'autorisation.

## Source de vérité de la liste

La liste du job `proof-integrity-audit` vit dans
`scripts/lean/allow_axioms_conway.txt`, référencé par :

```yaml
allow-axioms: "@scripts/lean/allow_axioms_conway.txt"
```

`scripts/lean/allow_axioms_conway.txt` contient **77 entrées** : le critère de
compte est celui de `parse_allow`, à savoir les lignes non vides après
suppression du texte de commentaire introduit par `#` et des espaces de bord.
Ces entrées sont uniques, et celle portant U+271D ci-dessus est la seule qui
contient un caractère non-ASCII. Le commentaire `allow-axioms` du job dans
`.github/workflows/lean-conway.yml` indique le même total.

Le chemin `@<chemin>` se résout contre la racine du checkout
(`GITHUB_WORKSPACE` en CI), avec repli sur le répertoire courant pour un run
local. La résolution est fail-closed : un fichier inexistant ou illisible fait
échouer le parsing au lieu de produire une allow-list vide.

## Gardes de régression

`scripts/tests/test_axiom_allow_file.py` vérifie le round-trip byte-identique
de l'entrée U+271D, la normalisation des deux côtés du matching, le refus
d'une ancre distincte, la concordance du compte entre le fichier, cette
documentation et le workflow, ainsi que le câblage workflow vers le fichier.
