# Pli 5 — verdict d'outil : réécriture d'hypergraphes

Issue #23093 (grain A), Epic #19742. Mesures du 2026-10-29, lane `myia-po-2024:CoursIA`.

## Verdict

**`RECOVERABLE-LOCAL`** — une alternative ouverte, **officielle et MIT**, existe :
`libSetReplace`, le cœur C++ du paquet `SetReplace` de Wolfram Research. Elle se
construit et passe ses propres tests sur cette machine, **sans Wolfram Engine**.

La décision de mainteneur sur le noyau Wolfram Language n'est donc **pas** un
préalable au pli : elle ne conditionne que le confort d'une façade en langage
Wolfram. Le grain B peut avancer.

La checklist 6 axes de `INTRINSIC` ne s'applique pas : le verdict n'est pas
`INTRINSIC`. La branche « réimplémentation pédagogique déclarée » n'est pas
utilisée non plus — elle n'a plus de raison d'être.

## Les trois branches, dans l'ordre exigé par l'issue

| # | Branche | Mesure | Résultat |
|---|---|---|---|
| 1 | `SetReplace` officiel (langage Wolfram) | Paquet vivant : `maxitg/SetReplace`, MIT, 252 étoiles, HEAD `44c868b` (2025-02-03) | Existe. Sa façade WL exige le **Wolfram Engine**, dont l'activation passe par un compte : décision de mainteneur. **Non bloquant** (voir branche 2) |
| 2 | Alternative ouverte | `libSetReplace/` — 16 entrées, C++ pur, MIT, son propre `CMakeLists.txt` | **Construit et teste vert sans Wolfram Engine** → c'est elle qui ferme le verdict |
| 3 | Réimplémentation pédagogique déclarée | — | **Non nécessaire** |

### Détail de la branche 1 — le piège du nom

`pip install setreplace` **n'installe pas** le paquet de Wolfram Research.
PyPI sert une réimplémentation **tierce en Rust** de Kovas Boguta
(`kovasb/setreplace-py`) :

| | Officiel | Tierce (PyPI) |
|---|---|---|
| Dépôt | `maxitg/SetReplace` | `kovasb/setreplace-py` |
| Licence | **MIT** | **MIT** sur PyPI, **`NOASSERTION`** sur GitHub |
| Étoiles | 252 | **2** |
| Activité | vivant (push 2026-07-18) | créé 2026-06-10, **dernier push 2026-06-11** |
| Moteur | C++ + langage Wolfram | Rust |

Un paquet publié puis abandonné en 24 h, à 2 étoiles, dont la licence GitHub et
la licence PyPI ne concordent pas, ne peut pas porter un verdict. Il a donc été
mesuré (`setreplace_pypi_control.py`), pas cru sur son résumé.

**Ce que la mesure en dit** : la sémantique est fidèle. `19/19` cas passent,
y compris les trois propriétés du docstring officiel (`Kernel/SetReplace.m`) —
appariement depuis le début de la liste, sortie ajoutée **en fin** de liste,
doublons **non fondus**. Il reste utilisable comme commodité locale ; il n'est
pas la référence.

### Détail de la branche 2 — la preuve de construction

Environnement : WSL Ubuntu 24.04, `g++ 13.3.0`, 16 cœurs, `cmake 4.4.4`.

`cmake` était absent de la machine et `sudo` réclame un mot de passe : il a été
installé par `pip` dans un venv (outil réel, aucun `sudo`, rien de contourné).

```
cmake .. -DSET_REPLACE_BUILD_TESTING=ON -DCMAKE_BUILD_TYPE=Release
cmake --build . -j 14
```

| Binaire de test | Tests | Résultat |
|---|---|---|
| `HypergraphSubstitutionSystem_test` | 7 | PASSED (405 ms) |
| `profile_tests` | 6 | PASSED (3008 ms) |
| `Parallelism_test` | 4 | PASSED (643 ms) |
| **Total** | **17** | **0 échec, rc=0 pour les trois** |

Sortie verbatim conservée dans `libsetreplace_build_proof.txt`.

### Ce que ce cœur porte déjà pour les grains B et C

Vérifié dans les en-têtes, pas supposé :

- `HypergraphMatcher::allMatches()` — énumération de **toutes** les
  correspondances : c'est le multiway dont le grain B a besoin.
- `TokenEventGraph`, avec `SeparationType { Spacelike, Branchlike }` — la
  séparation spatioïde/branchoïde est exactement la structure causale du projet
  Wolfram, donc le socle du grain C.
- `HypergraphSubstitutionSystem::events()` — la liste complète des événements,
  nœuds du graphe causal.
- `replaceOnce` et `replace(StepSpecification)` — le contrôle du nombre de pas
  pour l'exposant d'échelle.

## Ce qui n'est pas établi

Trois limites, dites plutôt que tues :

1. **Aucune exécution du paquet officiel en langage Wolfram.** Le Wolfram Engine
   n'est pas installé et son activation est une décision de mainteneur. Les
   comparaisons de sémantique s'appuient donc sur le **docstring officiel**, pas
   sur une exécution du WL. C'est suffisant pour le verdict (la branche 2 suffit),
   pas pour affirmer une équivalence bit à bit entre les deux moteurs.
2. **Le harnais de test officiel refuse Windows** — `libSetReplaceTest.sh` teste
   `uname` et sort `Operating System not supported`. La construction a donc été
   faite sous WSL. Un poste sans WSL devra passer par CMake directement.
3. **Aucun binding Python officiel.** La bibliothèque s'invoque en C++ ; la
   conduire depuis Python demande un pont à écrire, ou l'acceptation du paquet
   tiers comme façade (voir branche 1). Ce pont est un choix de grain B, pas un
   préalable au verdict.

## Reproductibilité

```bash
# branche 3 — le paquet tiers, mesuré
python -m pip install setreplace==0.2.0
python scripts/hypergraph/setreplace_pypi_control.py --json /tmp/control.json

# branche 2 — le cœur officiel
git clone --depth 1 https://github.com/maxitg/SetReplace.git
cd SetReplace && mkdir build && cd build
cmake .. -DSET_REPLACE_BUILD_TESTING=ON -DCMAKE_BUILD_TYPE=Release
cmake --build . -j 14
find . -path "*libSetReplace/test*" -type f -executable -exec {} \;
```

## Note de méthode — le témoin peut être le bug

La première version du contrôle rendait **3/12** et accuser le paquet était la
sortie facile. Les neuf échecs venaient tous de mes valeurs attendues :

- `events` compte des **substitutions**, pas des générations — un événement
  réécrit *une* arête, pas toutes les correspondances (`SetReplaceAll` fait cela) ;
- la graine `{{1,1}}` ne porte **qu'un** atome (c'est une boucle), pas deux.

Un quatrième attendu était faux pour la même famille de raison : j'avais supposé
une sémantique d'**ensemble** là où le docstring décrit une **liste** où la
sortie est ajoutée à la fin. Après rédérivation à la main, `19/19`.

Conséquence pour la suite du pli : un contrôle de correction ne vaut que si ses
attendus sont dérivés d'une source citée, jamais d'une intuition sur ce que
« devrait » faire un moteur de réécriture.

## Voir aussi

- #23093 — le pli 5, ses trois grains et ses critères d'acceptation.
- #19742 — l'Epic Origami-Wolfram, registre des plis.
- `scripts/hashlife/` — le précédent de forme : instruments et verdicts d'un pli.
- `sota-not-workaround.md` — les cinq verdicts ; `organ-first-implementation.md`.
