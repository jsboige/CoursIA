# Jonctions Mathlib po-2027 — vérification build du groupe `db584cd6` (suite de #21319)

**Statut** : runs 1-7 (2026-11-09/10) — **22/26 membres verts à travers la jonction** (run 7 `LAKE_JOBS=1`, EXIT=0) ; 4 traînards en suivi. Ce document est le compte-rendu de la tranche « suite ordonnée de #21319 » annoncée sur #4362 (claim c.6734239837).

## Pourquoi cette tranche

Le compte-rendu de l'Apply #21319 ([junctions-apply-po-2027-c1731.md](junctions-apply-po-2027-c1731.md), 2026-10-18) concluait MIXED : 4 SUCCESS / 6 FAILED (rollbackés) / 14 non couverts, avec deux causes d'échec distinctes — (a) artefacts `Blocks.olean` / `.olean.private` signalés manquants dans le cache partagé (kelly_lean, search_lean), (b) cibles requises en échec de compilation (game_theory, learning_theory, decision_theory) et trace sur `Sudoku.Propagation_en`. La suite ordonnée : rebuild/re-verify des artefacts du cache, puis rejeu de `lake build` sur l'ensemble du groupe dans un run unique.

## État mesuré avant le run (2026-11-09, lecture seule)

- **Scan** (`-Mode Scan`, 07:56Z) : le groupe `db584cd6` compte 26 membres jonctionnables ; **21/26 JUNCTIONED** — dont les **6 rollbackés de #21319, re-jonctionnés depuis** (game_theory_lean, learning_theory_lean, decision_theory_lean, kelly_lean, search_lean, sudoku_lean). Sans checkout local : galois, grothendieck, hecke, darksnail/build-evidence, fixtures `stable_marriage/upstream`. Isolés inchangés (mimo, formal_logic, differential, torchlean, discrepancy, kls, peters, conway_cgt).
- **Artefacts du cache** : `Mathlib/GroupTheory/GroupAction/Blocks.olean` (+ `.private`, `.server`, répertoire complet) **présents**, datés du **2026-10-15 15:12** — soit ANTÉRIEURS au run #21319 du 18/10 qui les signalait manquants. L'échec d'alors ne venait donc pas d'une absence de fichier sur le disque actuel ; causes plausibles : hash invalide lu par lake, ou jonction absente au moment du build de ces membres (re-téléchargement incomplet). Le rejeu tranche.
- **Baseline anti-régression** (`count_code_sorry.py --json`, 08:0xZ) : **somme `distinct_code_sorry` = 17** sur 39 lakes — game_theory_lean 4, decision_theory_lean 4, conway_lean 1, knot_lean 8. (La baseline de #21319 était 12 ; l'écart +5 est le travail Lean livré sur `main` depuis le 2026-10-18, sorry-cibles documentés inclus.) L'acceptance de ce run : **17 → 17 inchangés**.

## Premier run (interrompu par un redémarrage)

Commande : `pwsh -NoProfile -File scripts/lean/setup_shared_mathlib.ps1 -Mode Apply -Group db584cd6 -Build`, lancé à 08:03 locale. Sortie (verbatim, tronquée aux faits) :

- `Cache existant valide reutilise (rev db584cd6…)` ; 4 membres à traiter, 22 déjà jonctionnés (l.580 du script = affichage ; la boucle `foreach ($m in @($g.Group))` l.639 couvre **les 26** quand `-Build` est passé).
- `lake build … Compression_lean …` → **FAILED**, rollback du membre :
  - `error: McMillan.lean:1:0: failed to read file '…\Mathlib\Analysis\SpecialFunctions\Pow\Deriv.olean.private'`
  - idem pour `PrefixCodes.lean:1:0` ; `[-8714/8729] Building PrefixCodes (169s)` ; `Built PrefixCodes_en (375s)`
  - `rollback SANS backup -- .lake/packages/mathlib ABSENT, membre a re-approvisionner`
- Puis démarrage de `assignment_lean` — et **arrêt du run (exit 4) au redémarrage de la machine**, sans verdict pour ce membre.

### Diagnostic du symptôme `Deriv.olean.private`

Le message suggère un artefact manquant. La mesure dit l'inverse :

| Mesure (2026-11-09 ~11:00 locale) | Résultat |
| --- | --- |
| `Deriv.olean.private` sur le cache | **présent, 1 181 736 octets, mtime 2026-10-15 15:12:19, lisible** (handle ouvert) |
| Intégrité du cache | **8 322 `.olean` / 8 312 `.olean.private`** — 10 manquants, **tous sous `Cache\*`** (paquet du toolchain, hors Mathlib) |
| `.hash` voisins | présents, datés du 15/10 — le cache **n'a pas été réécrit** depuis |
| Probe Lean (`import Mathlib.Analysis.SpecialFunctions.Pow.Deriv` + `#check deriv_pow`, LEAN_PATH identique au run) | **exit 0** — l'import se charge |
| Durée probe #1 → probe #2 | **261,6 s → 19,9 s** (×13 plus rapide à cache OS chaud) |
| RAM / disque au moment du diagnostic | 63,6 Go (18,5 libres) / 702 Go libres |

**Verdict** : pas d'artefact manquant. La lecture du cache était pathologiquement lente après le redémarrage (cache OS froid + contention I/O — le processus `lake` du run affichait 79 s de CPU pour ~40 min de temps réel, donc ~97 % bloqué sur disque). Un `lean` lisant un `.olean.private` pendant cette contention a échoué ; deux minutes plus tard la même chaîne d'import se charge en 19,9 s. La cause (a) de #21319 n'est donc **pas** une absence d'artefact : c'est au mieux une lecture transitoire en état dégradé, au pire un artefact effacé puis recréé entre-temps — le rejeu tranche.

## Runs de vérification (relance — 2026-11-09)

Lignée (commande identique : `pwsh -NoProfile -File scripts/lean/setup_shared_mathlib.ps1 -Mode Apply -Group db584cd6 -Build`) :

| Run | Heure (locale) | Parallélisme | Issue |
| --- | --- | --- | --- |
| 2 | ~12:1x | défaut (20 cœurs) | exit 4 — arrêt machine (2e redémarrage) |
| 3 | ~18:0x | défaut (20 cœurs) | exit 4 — extinction voyage ; 4 rollbackés persistés dans `share-state.json` |
| 4 | ~19:2x → 20:22 | défaut (20 cœurs) | **EXIT=0 — 20 SUCCESS / 6 FAILED** (log `.tmp/junction_build_run4.log`) |
| 5 | ~21:05 | `LAKE_JOBS=4` | **EXIT=0 — 21 SUCCESS / 5 FAILED** (log `.tmp/junction_build_run5.log`) |
| 6 | 22:1x → 23:1x | `LAKE_JOBS=2` | **EXIT=0 — 21 SUCCESS / 5 FAILED** (log `.tmp/junction_build_run6.log` ; GROTH réduit à 2 cibles) |
| 7 | 00:1x (10/11) | `LAKE_JOBS=1` | **EXIT=0 — 22 SUCCESS / 4 FAILED** (log `.tmp/junction_build_run7.log`) ; GROTH repassé VERT |

### Run 4 (défaut, 20 workers) — 20/26

Les 6 FAILED (game_theory, learning_theory, GOL/conway, GROTH/grothendieck, KNOTS/knot, Tweety/argumentation) nomment **tous le même fichier du cache** : `Mathlib/MeasureTheory/VectorMeasure/SetIntegral.olean.private` (`error: …:1:0: failed to read file`). Mesures sur ce fichier : présent (1 331 384 octets, mtime 2026-10-15, voisins complets), SHA256 OK en lecture intégrale, probe `import` exit 0 depuis un membre vert (mathlib_examples, même jonction), **importé directement par aucun des 6**. La machine a par ailleurs OOM-tué la session de l'agent **pendant** ce run : 20 workers lean × 5-17 Go sur 64 Go — la lecture mmap d'un fichier sain échoue sous pression commit.

### Run 5 (`LAKE_JOBS=4`) — 21/26

- **game_theory_lean repassé VERT** (échec au run 4) : l'échec n'est pas déterministe par membre — le niveau de parallélisme y est pour quelque chose.
- **Fraîcheur (2026-11-10)** : « vert » ci-dessus = build **à travers la jonction, au head de ce run** (reconfirmé aux runs 6 et 7) ; ce n'est pas un état permanent du lake. À un autre head, la review de #25591 (03:24Z) documente le lake game_theory **rouge** (`Bounded_en.lean: unknown namespace 'RepeatedGames'`, suffixage i18n EN) — l'état courant du lake se re-vérifiera après les suffixages #23906 en vol.
- 5 ré-échecs, erreur exacte capturée cette fois : **`error: Lean exited with code 4294967295`** (crash lean.exe, code -1) — signature différente du run 4 (lecture mmap), même famille d'épuisement de ressources. learning_theory, GOL/conway et GROTH échouent sur **tous** leurs modules (échec d'import massif) ; KNOTS/knot sur **deux cibles seulement** (`Knots.AlexanderTrivial` + jumeau `_en`, à 699 s chacun) ; Tweety/argumentation sur 6 (`Fundamental*`, `Grounded*`, `Synthesis*`, à 102 s). Les compteurs `[3032/3054]` / `[8717/8719]` sont les **tailles des closures Mathlib importées**, pas des rebuilds.
- **Drift de manifeste éliminé** : `lake-manifest.json` mesurés rouges comme verts — mathlib `db584cd6` + toolchain `v4.33.0` partout ; lake ne re-build pas Mathlib à travers la jonction.

### Run 6 (`LAKE_JOBS=2`) — 21/26, mêmes traînards, GROTH se rapproche

Terminé 23:09 locale (EXIT=0). Les mêmes 5 membres ré-échouent, mais l'écart se resserre : **GROTH passe de « tous modules en échec » à 2 cibles seulement** (`Grothendieck.CoversEtaleArrow_en`, `Grothendieck.FlasqueRetract_en`) — le module principal `Grothendieck` est **BUILT** (21 s), et le log montre une élaboration réelle (signatures Mathlib `IsDiscreteValuationRing`… résolues). KNOTS échoue toujours sur ses 2 seules cibles `Knots.AlexanderTrivial`(+`_en`), crash `4294967295` à **1494 s** chacun — soit 2× plus long qu'à `LAKE_JOBS=4` (699 s) : plus de mémoire disponible retarde le crash sans l'éviter. Tweety : 6 cibles à 168-169 s, même signature. learning_theory et conway : tous modules, inchangés. La progression GROTH (et le flip game_theory du run 5) confirment la lecture ressources ; le cas KNOTS à 1494 s en parallélisme 2 commence à ressembler à un plafond du module lui-même — le run 7 (`LAKE_JOBS=1`) tranche.

### Run 7 (`LAKE_JOBS=1`) — 22/26, GROTH repasse, le palier parallélisme est épuisé

Terminé EXIT=0 (log `.tmp/junction_build_run7.log`), cache `db584cd6` réutilisé.

- **GROTH/grothendieck_lean repassé VERT** (échec runs 4-6) : à un seul worker, les 2 cibles récalcitrantes (`CoversEtaleArrow_en`, `FlasqueRetract_en`) passent et le membre est re-jonctionné. Troisième flip de la lignée (game_theory au run 5, GROTH au run 7) — la lecture « borné par les ressources » tient pour ce membre.
- **learning_theory** : 16 cibles en échec (`Perceptron.Data`, `PacLearning.{Data,BernoulliMGF}` ± `_en`, `GradientFlow.{Plain,Residual}`, `EffectiveTheory.{CircleOfDays,Grokking,InfoBits,Repons}` ± `_en`, `MathUniverse`, `Generators_en`) — tous modules, inchangé depuis le run 4.
- **GOL/conway** : 14 cibles `Conway.*` en échec (`Life` ± `_en`, `Life.{Torus,GridCanonical,Oscillators,Spaceships,Hashlife,HashlifeDecideMemo,AdversarialBattery}` ± `_en`, `FreeWillTheorem` ± `_en`) — tous modules, inchangé.
- **KNOTS/knot** : seules cibles en échec `Knots.AlexanderTrivial` (+ jumeau `_en`). À `LAKE_JOBS=1` — plus aucun autre worker lean sur la machine — `✖ [3032/3054] Building Knots.AlexanderTrivial (1927s)` puis **`INTERNAL PANIC: out of memory`**, exit 1 ; `_en` exit `4294967295` à 1933 s. **Le levier parallélisme est épuisé : l'OOM survient même à un worker.** Hypothèse de travail : plafond d'élaboration du module (1927 s d'élaboration avant le crash, là où les 21 membres verts tiennent dans la même configuration). Mais la règle [lean-merge-discipline] tranche la suite : un `INTERNAL PANIC: out of memory` sous Windows n'est **pas** un verdict — la migration WSL Ubuntu est le geste requis avant de conclure à un plafond intrinsèque du module.
- **Tweety/argumentation** : 6 cibles (`Grounded`, `Fundamental`, `Synthesis` ± `_en`), exit `4294967295`, `Synthesis` à 84-85 s (`[8717/8719]`) — crash rapide et constant, signature distincte de KNOTS.
- Les 4 membres rollbackés **sans backup** (`.lake/packages/mathlib` absent) : à re-provisionner (~5 Go de Mathlib chacun) pour toute reprise hors jonction.
- Bruit sans effet : un warning linter `defProp` (`ReidemeisterCombinatorial_en.lean:156`) dans la sortie knot — pas une erreur de build.

### Verdict sur les deux causes héritées de #21319

- **(a) artefacts manquants — réfuté.** Le cache (8 322 `.olean` / 8 312 `.private`, les 10 manquants sous `Cache\*` hors Mathlib) est **consommé vert par 21 membres sur 26**, dont **5 des 6 rollbackés de #21319** (game_theory — après `LAKE_JOBS=4`, decision_theory, kelly, search, sudoku) ; seul learning_theory reste en échec, pour des raisons de ressources (b). Les échecs de lecture du run 4 désignaient un fichier sain sous pression mémoire.
- **(b) échecs de compilation — bornés par les ressources, pas par le contenu, jusqu'au palier final.** Le même membre (game_theory) passe de rouge à vert en baissant le parallélisme 20 → 4 ; GROTH suit au run 7 (`LAKE_JOBS=1`). Il reste 4 traînards, dont KNOTS pour lequel le levier parallélisme est **épuisé** (OOM à un worker). Suite : migration WSL Ubuntu (discrimine infra vs plafond de module, règle lean-merge-discipline), provisioning autonome en repli (~5 Go chacun).

## Après le run

- **Sorry après** : `distinct_code_sorry` = 17 (mesuré `count_code_sorry.py --json` post-run 5) — **17 → 17, inchangé** vs baseline du matin. Aucune source `*.lean` touchée par la lignée entière (runs 1-7).
- **État des jonctions** (`share-state.json`, persisté par membre) : **22 membres jonctionnés** ; 4 rollbackés (`needsProvision: true`) : learning_theory, GOL/conway_lean, KNOTS/knot_lean, Tweety/argumentation_lean — GROTH sorti de la liste au run 7.
- **Run 7 (`LAKE_JOBS=1`) terminé, EXIT=0 — 22/26.** Pour les 4 traînards restants : migration WSL en premier geste (tranche la question KNOTS), provisioning autonome (~5 Go de Mathlib chacun) en repli.
- **Purge `520045ab` (11,79 Go)** : reste **interdite** — le build vert n'est pas établi sur les 4 re-pointés restants.

## Garde-fous reconduits de #21319

- Purge du cache orphelin `v4.32.1-520045ab` (11,79 Go) : **interdite** tant que le build vert sur les re-pointés n'est pas établi.
- Tout membre dont le build échoue est rollbacké par le script (backups `.bak-2611` + `share-state.json`, désormais conforme au disque — le défaut #21454 est corrigé dans le script courant).
- Aucune source `*.lean` n'est touchée par ce run : `distinct_code_sorry` ne peut bouger que si un build casse/écrit une preuve, ce que l'instrument détecte.
