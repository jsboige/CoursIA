# Recette de migration Lean — de 4.32/4.33 vers **4.35.0**

**Date de rédaction :** 2026-11-20 · **Lane :** `myia-ai-01:CoursIA-2` · **EPIC :** [#27478](https://github.com/jsboige/CoursIA/issues/27478), Jalon 0
**Statut :** recette **vivante** — chaque jalon ajoute les pièges réellement rencontrés, pas des généralités.

---

## 0. Ce que cette recette est, et ce qu'elle n'est pas

Elle décrit **le geste** « migrer un lac Lean d'un pin 4.3x vers 4.35.0 », vérifié de bout en
bout sur le siège `myia-ai-01` le 2026-11-20.

Elle ne décrit pas :
- la **liste** des 43 pins — elle est dans le body de l'EPIC et se remesure trivially
  (`git ls-files '**/lean-toolchain'`) ;
- la **stratégie** d'ordre des jalons — elle est dans l'EPIC ;
- un **big-bang** : la règle reste *un lac = une PR*, chacune vérifiée isolément.

**Le lemme qui gouverne tout le reste :** un pin de toolchain n'est pas une version de
Mathlib. Les deux se déplacent séparément, et les preuves qui en dépendent (signatures,
axiomes, noms de lemmes) sont indexées sur les deux à la fois.

---

## 1. Les pins de la cible 4.35.0

Source : le **précurseur vivant** `MyIA.AI.Notebooks/SymbolicAI/Lean/torchlean_lean`, déjà
en 4.35.0 sur ce dépôt (`lean-toolchain` + `lake-manifest.json`, lus firsthand le 2026-11-20).

| Paquet | `inputRev` (ce qu'on écrit) | `rev` (ce qui est épinglé) |
|---|---|---|
| Lean | `v4.35.0` | — (elan) |
| `mathlib` | `v4.35.0` | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| `«doc-gen4»` | `v4.35.0` | `0e1ffe2e4ba5ecfdfaf15c65b8d3805dbb7134ae` |
| `floatlib` | (hérité) | `1f5771b3e36a98f17fcac2c6d76aaa024b36aa37` |
| `torchlean` (amont) | — | `b64a6feccbeba9547e19fa902fa878c00b994dd0` |

**Le `rev` est la vérité ; `inputRev` est l'intention.** `lake update` réécrit l'`inputRev`
et résout un `rev` ; si l'on écrit `inputRev` à la main sans réécrire le `rev`, le `lake-manifest.json`
reste sur l'ancien commit et **le build passe quand même** — sur l'ancienne Mathlib. D'où la
règle : **comparer les manifests** avant et après (`scripts/lean/compare_lake_manifests.py`),
ne pas se fier au diff du fichier de pin.

---

## 2. Le paysage : une **ancre** et vingt **sous-lacs**

Recensement firsthand sur `origin/main` au `d1937ebe375fc` (2026-11-20) :
**43 `lean-toolchain` trackés**.

| Pin | Nb | Nature |
|---|---:|---|
| `v4.33.0` | **36** | 35 sous-lacs + **l'ancre de série** `SymbolicAI/Lean/lean-toolchain` |
| `v4.32.1` | 2 | `ANALYSE/kls_lean`, `GameTheory/SocialChoice/social_choice_lean_peters` |
| `v4.33.1` | 2 | `differential_lean`, `formal_logic_lean` |
| `v4.33.0-rc1` | 1 | `GameTheory/conway_cgt_lean` (rc → stable) |
| `v4.25.0` | 1 | `agent_tests/.../stable_marriage/upstream` — **fixture, à ne pas migrer** |
| `v4.35.0` | 1 | `torchlean_lean` — le précurseur |

> **Écart de recensement avec l'EPIC** : l'EPIC annonce 35 lacs en `v4.33.0` ; la mesure
> firsthand donne **36**, parce que **l'ancre de série est elle-même un `lean-toolchain`**.
> Ce n'est pas une erreur de l'EPIC, c'est une catégorie qu'il ne listait pas — et la
> distinction est décisive (voir §3, piège P3).

**L'ancre n'est pas un lac.** `MyIA.AI.Notebooks/SymbolicAI/Lean/` ne contient **ni
`lakefile.lean` ni `lake-manifest.json`** : c'est un répertoire conteneur qui porte les
carnets. Son `lean-toolchain` sert les carnets Lean qui n'ont **pas** de lac au-dessus
d'eux. Les 20 sous-lacs portent **chacun** leur pin et **aucun n'hérite** de l'ancre
(mesuré le 2026-11-20 : 20 pins distincts, aucun `v4.33.0` hérité de l'ancre).

Conséquence directe : `scripts/lean/ci_lakes.json` ne cite **que** des sous-lacs (mesuré :
aucune entrée ne pointe `SymbolicAI/Lean/lean-toolchain`). **Migrer l'ancre ne déclenche
aucun rebuild de la CI des lacs.**

---

## 3. Les pièges, tous mesurés

### P1 — Le REPL apparié : sans lui, le kernel ne démarre pas

Le kernel `lean4-wsl` n'utilise pas `lake env repl` mais un **binaire REPL apparié à la
toolchain du lac** (`~/.elan/bin/repl-<tag>`). `~/.elan/bin/repl` est *stable-locked* : il
embarque une version de Lean arbitrairement plus ancienne.

Table de correspondance : `scripts/lean/setup_native_lean4_import.py` → `REPL_TOOLCHAIN_TAGS`
(et la table inlinée dans `~/.lean4-kernel-wrapper.py`, à garder en sync).

**Mesuré sur ce siège, avant la tranche :** sous l'ancre `v4.33.0`, le wrapper **refuse de
démarrer** —

```
Lean 4 kernel startup failed: REPL/toolchain divergence. The pinned toolchain is
leanprover/lean4:v4.33.0 (tag v4.33.0) but the available REPL binary reports Lean 4.30.0.
Refusing to start: a mismatched REPL renders every cell as a parse error under an exit 0.
```

> **Ce blocage est préexistant** : il existait depuis le bump de l'ancre à `v4.33.0`
> (6/11, PR #24965), sur ce siège. Le message du wrapper est explicite et il a raison :
> un REPL décalé rend **chaque cellule** en erreur de parse **sous un exit 0**.

**Remède :** `python scripts/lean/setup_native_lean4_import.py build-repl <tag>`.

### P2 — Le repo `repl` n'a pas de tag pour chaque patch release

Pour une patch release, le tag source peut manquer. Le script checkout alors le tag
**inférieur** le plus proche et **écrase** le `lean-toolchain` de la copie pour forcer la
version demandée.

**Piège mesuré en amont (incident du 2026-08-21) :** un checkout **silencieusement** raté
laissait `HEAD` sur le tag précédent et produisait un REPL décalé d'une version, dont le
**seul** symptôme est `incompatible header` ou `Unknown identifier` à l'import.

Le script vérifie `HEAD == <tag>^{commit}` **en Python** avant de builder (les guillemets
ne survivent pas à la frontière `wsl.exe` → `bash -lc`). **Ne pas rebuild le REPL à la
main** : passer par l'organe.

### P3 — Un répertoire **sans lac** au-dessus n'a pas de sysroot

C'est le piège propre à **l'ancre**. Le wrapper cherche un lac en remontant depuis le cwd ;
s'il n'en trouve pas, il n'y a pas de `lake env` d'où tirer `LEAN_PATH` → **le REPL démarre
sans sysroot** → le prelude n'est pas chargé.

**Mesuré le 2026-11-20, sous l'ancre `v4.35.0` avec le REPL apparié installé :**

```
chdir /mnt/d/CoursIA-2-wt/lean435/MyIA.AI.Notebooks/SymbolicAI/Lean (lake=None)
```

et la cellule `import Lean` + `#check True.intro` rend :

```
❌ Unknown identifier `True.intro`
```

Le repli `~/lean-projects/notebook_context` **est interdit** (règle #16181 : *no fallback
to any … the unrelated `~/lean-projects/notebook_context` stub*) et il **n'existe pas** sur
ce siège.

**Interprétation juste :** ce n'est pas le bump qui a cassé le kernel, c'est le kernel qui
a **cessé de refuser de démarrer** (P1levait le refus) et a thereby révélé le défaut
suivant. Le kernel `lean4-wsl` **ne peut pas exécuter de cellule** dans un répertoire sans
lac ; il faut soit un lac, soit la voie compilateur (`scripts/lean/lean_exec.py`), soit un
kernelspec par-lac (`lean4-wsl-conway`, `lean4-wsl-groth16200`).

**Ce que cela signifie pour une migration d'ancre :** le bump de l'ancre est **sûr** et
**vérifiable** par `lake env lean --version`, mais il **ne rend pas** les carnets sans lac
exécutables sous `lean4-wsl`. Ne pas le dire comme le contraire.

### P4 — Un build qui s'arrête n'est pas forcément un mismatch de toolchain

`lake build` qui rend **143** (SIGTERM) ou qui reste bloqué sur les modules Mathlib 6000+ /
8498 est un **OOM / kill de parallélisme**, pas une incompatibilité de version.

Procédure : [windows-native-toolchain.md §3](windows-native-toolchain.md#3-quand-lake-build-sigterm-ise-lean-exited-143).
Le build Lean **borné** est obligatoire côté WSL (mandat user du 29/10 : un build Lean non
borné peut vider la VM) :

```bash
wsl -d Ubuntu -u root -- systemd-run --scope -q -p MemoryMax=<borne> -p MemorySwapMax=<borne> \
  --uid=<user> --gid=<user> -- env HOME=/home/<user> bash -lc 'lake build'
```

Côté Windows natif, borner le parallélisme (`lake build -j 1`) et surveiller la charge de
commit de l'hôte.

### P5 — `rfl`, `rw`, `subst` ne suffisent pas sur un constructor polymorphe d'univers

Piège tactic déjà catalogué : [l902_tactic_pitfalls.md](l902_tactic_pitfalls.md). Le `rfl`
direct **ne prouve** rien si l'univers reste non résolu ; les 4 stratégies testées et leurs
verdicts y sont consignés. Il est **indépendant** du pin : il se rencontre à 4.33 comme à
4.35, mais une migration le rend visible parce que le lemme cesse de compiler tel quel.

### P6 — Les mentions en prose des carnets

Un carnet qui écrit en clair « pin `v4.33.0` » devient **faux** si le pin bouge. Mais
attention à **qui** désigne cette mention : beaucoup désignent le pin d'un **sous-lac**
(`conway_lean`, `mathlib_examples`, `sensitivity_lean`, `grothendieck`), pas celui de l'ancre.
**Une mention n'est à corriger que si le lac qu'elle désigne est migré** — sinon on
introduit un mensonge inverse.

### P7 — `grep -c sorry` ne compte pas les preuves

Toujours `python scripts/lean/count_code_sorry.py --json`, champ **`distinct_code_sorry`**
(`grep -c sorry` sur-compte la prose d'un facteur ≥ 20).

---

## 4. Check-list d'une tranche (une PR par lac)

| # | Étape | Commande / preuve | Condition de passage |
|---|---|---|---|
| 1 | Toolchain installé | `elan toolchain install leanprover/lean4:v4.35.0` | les deux élans (Windows natif **et** WSL) portent la version |
| 2 | Pin du lac bumpé | `lean-toolchain` du lac | une seule ligne modifiée |
| 3 | Manifest aux pins 4.35 | `lake update` puis `scripts/lean/compare_lake_manifests.py` | `rev` = `56a00585…` (Mathlib) |
| 4 | REPL apparié | `setup_native_lean4_import.py build-repl v4.35.0` | `INSTALLED-repl-4.35.0` |
| 5 | Build | `lake build` (borné) | **SUCCESS**, log prouvable |
| 6 | Axiomes | `count_code_sorry.py --json` avant/après ; job `lean-axiom` | `distinct_code_sorry` inchangé ou mieux ; **0 `sorryAx`/`native_decide.*`** non whitelisté ; `Classical.choice` whitelisté **par nom** |
| 7 | B.3 | si le job `lean-axiom` n'est pas câblé pour le lac | écrire **« non applicable »** dans le body, explicitement |
| 8 | Carnets re-exécutés | papermill, kernel du lac | `execution_count` non null, **0 erreur** (C.2) |
| 9 | Jumeaux `_en` | attestation twin-parity | parité verte |
| 10 | Anti-régression | diff | aucune preuve remplacée par `sorry`/stub |

**B.3 ne se saute pas en silence** : « non applicable » s'**écrit** dans le body.

---

## 5. Ordre des jalons (EPIC #27478) et état au 2026-11-20

| Jalon | Contenu | État |
|---|---|---|
| 0 | Recette (`docs/lean/migration-4.35.md`) + ancre de série | **cette tranche** |
| 1 | GameTheory (7 lacs, CI Conway câblée #26775) | à faire |
| 2 | SymbolicAI/Lean cœur (GALOIS, GOL, GROTH×2, Geometry, KNOTS, Langlands, Riemann200, Serre100, petits) | à faire |
| 3 | `formal_logic_lean` (4.33.1 → 4.35.0) — **débloque #27477** | à faire |
| 4 | Séries satellites + les deux 4.32.1 | à faire |
| 5 | Consommation : #27477 Greffes A/B en CONSUMER_PINNED | dépend du jalon 3 |

**Règles de coordination :** une lane = un lac à la fois, `[CLAIMED]` avec `paths:` du lac ;
ne pas migrer un lac sous PR ouverte active (le bump rebaserait la PR) ; lister les PRs
ouvertes touchant le lac dans la tranche.

---

## 6. Ce que cette tranche a mesuré (2026-11-20, siège `myia-ai-01`)

| Mesure | Valeur |
|---|---|
| Pins trackés | 43 (36 en `v4.33.0`, dont l'ancre) |
| Sous-lacs sous `SymbolicAI/Lean/` | 20, **aucun** n'héritant de l'ancre |
| `ci_lakes.json` | ne cite **que** des sous-lacs — l'ancre n'y est pas |
| Toolchain 4.35.0 (elan Windows natif) | **installée** (elan 4.2.1 ; la machine portait jusqu'à v4.34.1) |
| Toolchain 4.35.0 (elan WSL `/home/jesse`) | **installée** |
| REPL apparié | `~/.elan/bin/repl-4.35.0` construit depuis le tag source `v4.35.0` (24 jobs) |
| Sélection par le wrapper | « REPL: `/home/jesse/.elan/bin/repl-4.35.0` (Lean 4.35.0) » — log `~/.lean4-wrapper.log` |
| Témoin de l'ancre | `lake env lean --version` → **4.35.0** (commit `eb6cafb7290e`) |
| Témoin négatif (avant) | ancre `v4.33.0` → kernel **mort** (« REPL/toolchain divergence … reports Lean 4.30.0 ») |
| Résiduel mesuré | sous l'ancre, `lake=None` → pas de sysroot → `Unknown identifier` (P3) |

**Ce qui n'est pas prouvé ici :** l'exécution de bout en bout d'un carnet Lean de la série
(la voie WSL sans lac est en défaut, voir P3) ; le build des sous-lacs sur 4.35 (jalons 1-4) ;
le repli `#27477` (jalon 3).

---

## Voir aussi

- [EPIC #27478](https://github.com/jsboige/CoursIA/issues/27478) — le mandat et les jalons
- [windows-native-toolchain.md](windows-native-toolchain.md) — build Windows natif
- [wsl-kernels-detail.md](../reference/wsl-kernels-detail.md) — le kernel `lean4-wsl`
- [l902_tactic_pitfalls.md](l902_tactic_pitfalls.md) — pièges de tactic
- [knot-4.33-investigation.md](knot-4.33-investigation.md) — investigation d'un lac 4.33
- [precedent mesuré](https://github.com/jsboige/CoursIA/pull/24965) — PR #24965 (`9be411ea0898a`), bump de l'ancre v4.30.0 → v4.33.0
