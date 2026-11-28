# `myia_nb` — l'aide partagée des carnets Rust

Crate locale, sans dépendance, qui porte ce que chaque carnet Rust du dépôt recopiait : l'affichage « à la Python » des valeurs et la mesure d'un temps d'exécution.

## Pourquoi une crate

Les carnets Rust comparent leurs sorties à celles de leur jumeau Python : `True`/`False`, `[1, 2, 3]`, `['a', 'b']`, `(1, 2)`. Ces fonctions d'affichage étaient recopiées dans chaque carnet, et les copies ont dérivé — la même fonction de booléen s'écrit avec deux types de retour différents selon le carnet, ce qui fait diverger la sortie visible d'un carnet à l'autre. Une version unique, versionnée et testée, remplace les copies.

La crate ne réduit pas le nombre de lignes de chaque carnet, et le `:dep` **coûte** un chargement par exécution (mesuré sur le carnet pilote : quelques secondes, body de la PR de livraison). Ce qu'elle supprime, c'est la dérive des copies — pas le temps de démarrage.

## Utilisation dans un carnet

Le `:dep` se pose **en tête du premier bloc de code**, une seule fois :

```rust
:dep myia_nb = { path = "../Config/rust/myia_nb" }
use myia_nb::py_bool;
```

**Le chemin est relatif au dossier du carnet**, pas à la racine du dépôt : le noyau résout un `path` de dépendance contre son répertoire de travail, qui est celui du carnet. Un carnet un niveau sous `MyIA.AI.Notebooks/` (comme `Sudoku/`) porte `../Config/rust/myia_nb`, deux niveaux `../../Config/rust/myia_nb`. Le chemin se calcule, il ne se recopie pas :

```bash
python scripts/notebook_tools/wire_myia_nb.py --apply <carnet>
```

Un `:dep` ajouté en cours de carnet recompile la session et efface les variables déjà saisies : il ne bouge pas de la tête (le validateur `check_rust_notebook_contract.py` le refuse).

## API

| Fonction | Sortie |
|---|---|
| `py_bool(b)` | `True` / `False`, en `&'static str` |
| `py_bool_string(b)` | même texte, en `String` |
| `py_bool_list(v)` | `[True, False]` |
| `py_list(v)` | `[1, 2, 3]` |
| `py_str_list(v)` | `['a', 'b']` (representation `repr`) |
| `py_tup(v)` | `(1, 2)`, `(1,)` pour un singleton, `()` pour le vide |
| `time_it(f)` | le résultat du calcul et sa `Duration` ; le calcul est exécuté **une fois** |
| `ms(d)` | `12.345 ms`, trois décimales |

## Migrer une définition locale

| Définition locale | Remplacement |
|---|---|
| `fn py_bool(x: bool) -> &'static str { if x { "True" } else { "False" } }` | `use myia_nb::py_bool;` |
| même corps, `.to_string()` sur les deux branches, retour `String` | `use myia_nb::py_bool_string as py_bool;` — le nom appelé est conservé, aucun site d'appel ne bouge |

**Rien d'autre ne se migre à l'aveugle.** Les variantes de `py_list` / `py_tup` mesurées sur `main` diffèrent par le type d'argument et parfois par la sémantique (une fonction homonyme affiche un masque de bits : ce n'est pas un formateur de tranche). Le fixer les **signale** sans les toucher ; une adoption est un geste par carnet, relu.

## Construire et tester

```bash
cargo test --manifest-path MyIA.AI.Notebooks/Config/rust/myia_nb/Cargo.toml
```

Aucune dépendance, aucun réseau : la crate se construit avec la toolchain épinglée du pli 0. Le dossier `target/` et le fichier `Cargo.lock` sont ignorés : une bibliothèque sans dépendance ne publie pas de verrou, dont le format dépend de la version de `cargo` qui l'a produit.

## Référence

- [rust-porting-spec.md](../../../../docs/reference/rust-porting-spec.md) § « L'aide partagée ne se recopie pas » — la règle de `:dep` et de migration
- [kernels-runtime.md](../../../../docs/reference/kernels-runtime.md) § Rust — toolchain, exécution, timings, `:dep` en tête
- Pli 3 de l'Epic [Parité Rust #26510](https://github.com/jsboige/CoursIA/issues/26510) — organe 3 : [#27098](https://github.com/jsboige/CoursIA/issues/27098)
