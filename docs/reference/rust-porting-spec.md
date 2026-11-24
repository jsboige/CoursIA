# Gabarit de spécification de portage Rust — un seul format, deux producteurs

> REFERENCE — vivante — dernière révision 2026-11-21
>
> **Provenance** : [Epic #26510](https://github.com/jsboige/CoursIA/issues/26510) (Parité Rust), **Pli 3** [#27098](https://github.com/jsboige/CoursIA/issues/27098), point 4 (« le gabarit de spécification de portage »). Le pli 1 a livré la table de correspondance : [rust-ecosystem-map.md](rust-ecosystem-map.md). Le pli 0 a livré la chaîne d'outils : [kernels-runtime.md § Rust](kernels-runtime.md#rust-notebooks-rust-via-evcxr).

## 1. Ce que ce gabarit établit

Une **page de spécification par carnet** : un carnet Rust ne s'écrit pas avant que sa page soit remplie. La page décrit ce que le portage doit produire, à partir de quelles crates, avec quelles tolérances, et dans quel temps — de sorte qu'un agent simple puisse implémenter le carnet depuis la page seule, et qu'un vérificateur puisse décider si le carnet livré est conforme à la page.

**Un seul format, deux producteurs.** Le harnais `nb_coder` produit déjà des pages de spécification pour la parité Python/C# (la vague du 17/11 : [#27103](https://github.com/jsboige/CoursIA/issues/27103), [#27112](https://github.com/jsboige/CoursIA/issues/27112), …). Le portage Rust produit les siennes. **Les deux remplissent la même forme** — un gabarit ne se fork pas : une divergence de forme se justifie dans la page elle-même, elle ne se crée pas en silence.

La forme de référence est donc **celle des specs C# en production**, lue sur `#27103` :

| Section de la spec C# | Ce qu'elle porte |
|---|---|
| En-tête + parents | `Grain:`, `Parent :`, `Voir` |
| **Objet** | source, cible, noyau canonique, périmètre |
| **Cellules à porter** | tableau `index source` / `première ligne verbatim` / `équivalent attendu` |
| **Attendus testables** | valeurs, verdicts, propriétés vérifiables |
| **Bibliothèques NuGet** | paquet, version, précédent de série |
| **Notes spécifiques** | désalignements assumés, séries voisines |
| **Interdits** | ce qui est interdit dans le carnet produit |
| **Livraison** | forme de la PR, attestations, citations exigées |

## 2. Les neuf sections, et ce que la version Rust y ajoute

| # | Section | Ce qu'elle porte | Ce que la version Rust ajoute | Source de vérité |
|---|---|---|---|---|
| 1 | En-tête | `Grain:`, `Parent :`, `Voir` | le lot d'origine (`#27129`…) et la page de spec | l'Epic #26510, ses plis et lots |
| 2 | Objet | source, cible, noyau, périmètre | noyau canonique `rust` (evcxr), suffixe `-Rust`, `rust-wsl` **jamais commité** | [kernels-runtime.md](kernels-runtime.md#rust-notebooks-rust-via-evcxr) |
| 3 | Plan des cellules | tableau index / verbatim / équivalent | l'équivalent est **Rust** ; chaque cellule est **autonome** (les fonctions ne persistent pas d'une cellule à l suivante) | kernels-runtime.md, § « Deux pièges de persistance mesurés » |
| 4 | Exercices | ≥ 3 exercices, stubs C.1 | les stubs Rust ne lèvent pas d'erreur ; la valeur neutre est explicite | CLAUDE.md §C.1 |
| 5 | Attendus testables | valeurs et verdicts | **une tolérance par cellule numérique** (absolue ou relative) | registre `scripts/notebook_tools/rust_conformance.d/` (point 2 du pli) |
| 6 | Crates cibles | paquet, version, précédent | crate, version **épinglée**, licence, feature, verdict natif/pont/brut ; `:dep` en **tête** de carnet | carte d'écosystème + crates.io/docs.rs au jour de la spec |
| 7 | Écueils de traduction | (absent de la spec C# : même écosystème) | emprunts et durées de vie, absence de surcharge d'opérateurs, aléatoire **graine par graine**, `ndarray` ≠ `numpy`, cellule autonome | retour d'expérience cité par l'Epic (#26510) |
| 8 | Temps attendus | (porté par `metadata.papermill.duration`) | le carnet Rust **n'a pas** de traducteur papermill : les durées viennent du bloc committé, jamais d'une mesure murale ; timeout : **15 ×** le temps attendu en cache cargo chaud, **300 s au plus** (cette marge couvre aussi le premier run, cache froid) | [kernels-runtime.md](kernels-runtime.md#timings--timeouts) |
| 9 | Interdits + Livraison | interdits, forme de PR | s'ajoutent : pas de `:dep` ailleurs qu'en tête, pas de pont Python (`pyo3`) sans verdict écrit, pas de sortie fabriquée, CI = **validation structurelle seule**, exécution réelle locale obligatoire | pli 0 (décisions écrites) |

## 3. Le gabarit — à copier dans le corps d'une issue de spec

```markdown
Grain: portage-rust/<série> -- lane <machine:workspace>

Parent : #<lot d'origine>      (ex. #27129)
Voir : #<page de spec du carnet jumeau> , #27098 , #26510

## Objet

- Source : `<chemin du carnet Python>` (<n> cellules, <n> code, exécution complète sur `<python3>`)
- Cible : `<chemin du carnet Rust>` (à créer) — suffixe `-Rust`, kernelspec canonique `rust` (evcxr)
- Noyau : `rust` — `:dep` **en tête de carnet**, une seule fois ; aucun `:dep` plus bas
  (un `:dep` tardif recompile tout et efface les variables typées)
- Périmètre : le carnet entier est porté (markdown adapté, même fil pédagogique, interprétations conservées)
- Cellules autonomes : chaque cellule code se suffit à elle-même (les fonctions ne persistent pas
  d'une cellule à la suivante sous evcxr) ; un type opaque en top-level est enclosed dans un bloc `{ ... }`

## Plan des cellules

Le tableau couvre les cellules CODE (index = position dans le carnet source, toutes cellules confondues).

| Index (source) | Première ligne (verbatim) | Équivalent Rust attendu |
|---|---|---|
| 1 | `<ligne source>` | `<crate + API + rôle>` |
| n | `# Exercice 1 -- <sujet>` | Exercice 1 à compléter : stub C.1, valeur neutre explicite |

## Exercices

- <n> exercices, dont <n> corrigés ; mêmes sujets que la source, adaptés au langage
- Verdict attendu cité dans la sortie de la source (le corrigé s'appuie sur la source, il ne la réinvente pas)

## Attendus testables

- <verdict ou valeur> — <précision> — seule combinaison possible : <raison>
- Les instances (données) sont celles du carnet source, reprises telles quelles

## Tolérances (une par cellule numérique)

| Cellule (source) | Grandeur comparée | Tolérance | Comparé à |
|---|---|---|---|
| <index> | <grandeur> | <absolue ou relative> | sortie Python <nom de la cellule> |

Une cellule sans tolérance est une cellule **non comparable** : elle ne figure pas dans le registre
de conformité différentielle (`scripts/notebook_tools/rust_conformance.d/<slug>.yaml`).

## Crates cibles

- `<crate>` `<version épinglée>` — licence `<MIT/Apache-2.0/…>` — feature `<…>` — verdict `<natif/pont/brut>`
- Précédent de série : <autre carnet qui l'utilise, ou « aucun »>
- `:dep` de tête : `:dep <crate> = "<version>"` (+ `:dep <crate> = { version = "…", features = [...] }` si feature)
- **Si le crate lie un moteur natif** (`cp_sat` → OR-Tools) : le prérequis système se **mesure
  avant** d'écrire la page (en-têtes + bibliothèques du moteur, `protoc` si les bindings sont
  générés, `libprotobuf` au link), et la page nomme **l'hôte d'exécution** et les variables
  d'environnement. Recette mesurée le 2026-11-21 sur `cp_sat` 0.4.1 :
  - **hôte** : OR-Tools ne publie **aucun binaire C++ pour Windows** (v9.2 → v9.15 ; le wheel
    Python Windows ne livre que des DLL, sans en-têtes ni `.lib` d'import) → exécution sous
    **WSL**, archive Linux officielle (`or-tools_amd64_ubuntu-22.04_cpp_v9.15.6755.tar.gz`)
    dans `/opt/ortools` ;
  - **variables** : `ORTOOLS_PREFIX=/opt/ortools` — **au pluriel**, c'est le nom que lit le
    `build.rs` du crate (le commentaire de `lib.rs` écrit `ORTOOL_PREFIX` et est **erroné**) —
    puis `RUSTFLAGS='-Clink-arg=-lprotobuf'` ;
  - **noyau** : `evcxr_jupyter` n'est **pas sur PyPI** (404 sur six noms candidats) ; il se
    construit depuis GitHub (`cargo install --git https://github.com/evcxr/evcxr
    evcxr_jupyter`). `cargo install evcxr` n'installe que `testing_runtime` : il n'y a pas de
    binaire `evcxr` à invoquer. `evcxr_jupyter` **écrase le kernelspec `rust`** à chaque
    démarrage : l'environnement est à réappliquer après chaque démarrage ;
  - **sortie parasite** : evcxr évalue la valeur de la dernière expression — une cellule code
    enveloppée dans `{ … }` produit un `execute_result "()"` ; un `;` final après l'accolade
    le supprime.

## Écueils de traduction

- <emprunts / durées de vie> — <ce que cela change dans le plan des cellules>
- <absence de surcharge d'opérateurs> — <contournement choisi, et son coût>
- <aléatoire> — <graine, et pourquoi la graine est portée de la source>
- <numpy → ndarray> — <ce qui change dans les sorties>

## Temps attendus

- Bloc source : <durée mesurée dans `metadata.papermill.duration` du bloc committé>
- Cible : <durée attendue> — timeout d'exécution : **15 ×** la durée attendue en cache cargo chaud, **300 s au plus** (cette marge couvre aussi le premier run, cache froid)
- Le carnet Rust n'a pas de traducteur papermill : aucune valeur de passage n'est injectée

## Interdits

- `panic!` / `unimplemented!()` / `todo!()` / `unreachable!()` à la place d'une valeur : INTERDIT partout, cellules de cours comme exercices
- Stub vide ou affichage de substitution à la place d'une implémentation des cellules de cours
- Sortie fabriquée ou hand-editée : chaque cellule code est exécutée sous le kernelspec `rust`, sorties réelles committées (C.2)
- Carnet committé sans exécution complète ; aucun `execution_count` null
- `:dep` hors de la tête de carnet ; pont `pyo3` sans verdict écrit dans la page
- Aucun appel réseau, aucune clé d'API, aucun GPU

## Livraison

- PR par lot, une série par PR, dans la limite de taille d'une PR du dépôt (attestations comprises)
- Enregistrer le triplet dans `scripts/notebook_tools/twin_pairs.d/` (côté `rust:`) avec audit réel,
  jamais une réattestation aveugle ; déclarer la tolérance dans `scripts/notebook_tools/rust_conformance.d/`
- Citer les durées des blocs committés dans le body de PR, jamais une durée murale locale
- CI = validation structurelle seule ; l'exécution réelle est **locale** (règle F), sur le siège
  qui a la toolchain Rust épinglée
```

## 4. Remplir avant d'implémenter

1. **La page précède le carnet.** Une page remplie après coup n'est pas une spécification : elle devient un compte-rendu, donc un récit de correction — ce que le dépôt refuse dans les carnets.
2. **Une tolérance par cellule numérique, dans la page.** C'est le seul endroit où la tolérance peut être décidée : le registre de conformité différentielle la consomme telle quelle, et une tolérance implicite (arrondi, « à peu près ») n'est pas une tolérance.
3. **Les temps viennent des blocs committés**, pas d'une mesure murale : le carnet Rust n'a pas de traducteur papermill, et la durée de compilation d'evcxr dépend du cache cargo.
4. **Les écueils sont les arguments de la page.** Ils n'expliquent pas une décision, ils la bornent : si la page n'explique pas pourquoi la cellule 7 est réécrite plutôt que traduite, la cellule 7 est une invention.
5. **Le lot, pas le carnet.** Une page est fille d'un carnet du lot ; c'est le lot qui donne son périmètre à la PR.

## 5. Ce qui est vérifié après coup — les validateurs

| Contrôle | Où il vit | Ce qu'il refuse |
|---|---|---|
| `:dep` en tête de carnet | validateur du pli 3 (point 5) | un `:dep` hors de la tête, ou plusieurs `:dep` de tête |
| Pas d'erreur volontaire (C.1) | validateur du pli 3 (point 5) | `panic!`, `unimplemented!()`, `todo!()`, `unreachable!()` dans un stub |
| Exécution complète committée (C.2) | validateur du pli 3 (point 5) | un `execution_count` null, une sortie non exécutée |
| Conformité différentielle | registre `scripts/notebook_tools/rust_conformance.d/` (point 2 du pli) | une sortie Rust qui s'écarte du Python/C# au-delà de la tolérance déclarée |
| Parité à trois côtés | `scripts/notebook_tools/twin_pairs.d/` (point 1 du pli) | un triplet attesté dont l'empreinte ne correspond plus au blob au commit |

## 6. Anti-fork

- Une section de plus ou de moins dans une spec = une **amendement** de la forme : il se justifie dans la page, il ne se crée pas par usage.
- Les specs C# déjà en production ne sont pas réécrites : elles **adoptent** la forme. Une spec C# qui manque une section propre au Rust (tolérances, écueils) est complétée au fil de l'eau, pas convertie.
- Toute divergence de forme entre deux producteurs se tranche dans la page la plus récente, jamais par convention tacite.

## Voir aussi

- [rust-ecosystem-map.md](rust-ecosystem-map.md) — correspondance bibliothèques → crates (pli 1)
- [kernels-runtime.md § Rust](kernels-runtime.md#rust-notebooks-rust-via-evcxr) — toolchain, exécution, papermill, CI, suffixe et kernelspec (pli 0)
- [scripts-reference.md](scripts-reference.md) — les organes de conformité différentielle et de parité
- Epic [Parité Rust #26510](https://github.com/jsboige/CoursIA/issues/26510) · Pli 3 [#27098](https://github.com/jsboige/CoursIA/issues/27098)
