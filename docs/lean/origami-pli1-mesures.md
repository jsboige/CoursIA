# Origami — Pli 1, journal du build hors CI de l'enveloppe `differential_lean`

> **Statut** : Pli 1 (sub-grain 1, « petites fermetures ») de l'EPIC origami géométrie
> différentielle (#18205). Journal d'une mesure de build exécutée **hors CI**.
> **Date du relevé** : 2026-10-08, heures **UTC** (le script estampille en `date -u`).
> **Machine** : `myia-po-2025` — Windows 11, WSL Ubuntu, mémoire plafonnée à ~32 Go,
> arbre sur `/mnt/d` (DrvFS).
> **Source brute** : `pli1-build.log`, produit par `pli1-build.sh` (trois étapes :
> `lake exe cache get`, `lake build`, `lake env lean DifferentialTour.lean`). Les extraits
> cités ci-dessous en sont **littéraux**.

Le lake mesuré est l'enveloppe [`differential_lean/`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/)
livrée par #19636 : un `require` git épinglé sur le tag amont `v0.1.3` de
[`qinz1yang/differential-geometry`](https://github.com/qinz1yang/differential-geometry)
(commit `7a48598d35109aa99d1cc678e2724c213cdf4ff3`), toolchain `leanprover/lean4:v4.33.1`,
fichier de visite `DifferentialTour.lean` et son jumeau anglais (i18n #4980). Aucune source
amont n'est recopiée : le lake **déclare une dépendance**, il ne la forke pas.

## Ce que ce journal couvre — et ce qu'il ne couvre pas

| Sub-grain du Pli 1 | Couvert ici |
|---|---|
| 1. Petites fermetures — build Morse / de Rham / Bonnet–Myers + `#print axioms` | **OUI** — objet de ce journal |
| 2. Build témoin de Poincaré (machine forte, hors CI) | **NON** — reste ouvert ; c'est lui qui décide si Poincaré entre dans un carnet exécuté (ampleur citée dans l'EPIC #18205) |
| 3. Sources tierces (NOTICE, conformité) | non — livré par #18978, [`origami-reconnaissance.md`](origami-reconnaissance.md) |
| 4. Emplacement dans le dépôt | non — livré par #18978 |

Le relevé de reconnaissance du 2026-10-03 avait classé le sub-grain 1
`RECOVERABLE-MACHINE` (« lake trop lourd pour 30 min »). Ce journal est la mesure de la
récupération : elle a eu lieu sur `myia-po-2025`, **hors CI**, et les chiffres ci-dessous
disent pourquoi elle ne peut pas être un job CI.

## Les trois commandes mesurées

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean
lake exe cache get                     # oleans Mathlib
lake build                             # cible par défaut : DifferentialTour + DifferentialTour_en
lake env lean DifferentialTour.lean    # second interrogatoire du témoin, hors du build
```

Relevés avant/après : `free -m`, `sha256sum lake-manifest.json`, `du -sm .lake`.

## Le run, en trois tentatives — la troisième est celle qui compte

| # | Début (UTC) | Déroulement | Fin |
|---|---|---|---|
| 1 | 2026-10-08 03:06:09Z | `cache get` rc=0 (5 239 s, « Decompressing 8689 already-cached file(s) ») puis `lake build` — **mort en vol à `[4094/4223]`** : la VM WSL s'arrête (aucune erreur Lean dans le log, 129 jobs restants) | log figé 06:20:36Z |
| 2 | 2026-10-08 15:43:11Z | **rc=127 immédiat** — `lake: command not found` : shell *non-login*, le PATH d'`elan` n'est pas chargé | 15:43Z |
| 3 | 2026-10-08 15:44:03Z | **run décisif** : `cache get` rc=0, build **repris à `[4095/4223]`**, achevé ; témoin relu | **2026-10-08 19:34:02Z** |

La reprise après la mort n° 1 est **gratuite** : les oleans déjà produits sont dans
`.lake`, et le build repart de lui-même au premier job non construit — mesuré, `[4095]` est
le premier job rebâti. Aucun ménage manuel n'est requis. Du premier `START` à la fin, la
journée a duré **16 h 28**, dont ~9 h 23 d'interruption (VM arrêtée).

## Table des mesures — run décisif (n° 3)

| Étape | rc | Durée | Détail (littéral) |
|---|---:|---:|---|
| `lake exe cache get` | 0 | 3 249 s | « No files to download » — cache déjà en place |
| `lake build` | 0 | **10 039 s (2 h 47)** | « Build completed successfully (4223 jobs). » — cible par défaut, les deux siblings |
| `lake env lean DifferentialTour.lean` | 0 | 329 s | les trois `#print axioms` (section suivante) |
| **Total des trois étapes** | 0 | **13 617 s (3 h 47)** | de 15:44:03Z à 19:34:02Z, relevés compris (3 h 50 de mur) |

Tentative 1, pour mémoire : `cache get` rc=0 en 5 239 s — la **même** étape mesurée une
seconde fois, dans un `.lake` qu'il fallait décompresser ; les deux rendent rc=0.

### Mémoire et disque

```text
--- memoire avant ---                --- memoire apres ---
Mem: total 32095  used 4953          Mem: total 32095  used 5050
     free 25971  available 27141          free 22030  available 27044      (Mo)
```

**La mémoire n'est pas la contrainte de cette visite** : ~5 Go utilisés, ~27 Go disponibles
avant comme après, sous un plafond WSL de ~32 Go. Les pics RSS par module (2,5 à 2,8 Go)
sont relevés dans le README du lake, table « Mesures relevées ».

Empreinte disque de `.lake` : **8 818 Mo** après la tentative 1 (build arrêté à
`[4094/4223]`), **9 379 Mo** à la fin — ~9,2 Gio pour le lake construit, Mathlib décompressée
incluse. C'est le coût de stockage d'une visite rejouée sur un poste.

### L'épinglage n'a pas dérivé

`lake-manifest.json` est **identique avant et après** les trois tentatives :

```text
ef3cb2d9b1635502fa061aa0a6c782aa7383e3a88226a4e97821a439073bef85  lake-manifest.json
```

`lake --version` rend `Lake version 5.0.0-src+819816b (Lean version 4.33.1)` ; le
`lean-toolchain` du lake est `leanprover/lean4:v4.33.1`, l'exception documentée qui le
distingue du parc (v4.33.0). Résolutions relevées au `cache get` : amont `7a48598d…`
(tag `v0.1.3`), Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, et les huit paquets
satellites (plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries,
Cli).

## Le témoin `#print axioms`, lu deux fois

**Pendant le build** — les trois théorèmes-têtes, dans les deux siblings. Les lignes `Built`
sont reprises telles quelles, à cela près que le glyphe d'information qui les préfixe dans la
sortie de Lean est omis (règle de style E du dépôt) :

```text
[4221/4223] Built DifferentialTour (142s)
info: DifferentialTour.lean:31:0: 'DifferentialGeometry.Topology.Morse.exists_quadratic_chart_of_isLocalMin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: DifferentialTour.lean:34:0: 'DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: DifferentialTour.lean:37:0: 'DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_diameter_le_of_complete_metric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[4222/4223] Built DifferentialTour_en (145s)
info: DifferentialTour_en.lean:35:0: 'DifferentialGeometry.Topology.Morse.exists_quadratic_chart_of_isLocalMin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: DifferentialTour_en.lean:38:0: 'DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: DifferentialTour_en.lean:41:0: 'DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_diameter_le_of_complete_metric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Build completed successfully (4223 jobs).
```

**Hors du build** — étape 3, les trois mêmes relus indépendamment (329 s) :

```text
'DifferentialGeometry.Topology.Morse.exists_quadratic_chart_of_isLocalMin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.DifferentialForm.pullbackCohomologyMap_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_diameter_le_of_complete_metric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Verdict : les trois points d'entrée ne dépendent que de `propext`, `Classical.choice` et
`Quot.sound` — **aucun `sorryAx`, aucun `native_decide.*`**. L'annonce de l'amont est
mesurée sur trois points d'entrée, pas reprise sur parole. Pour une dépendance externe,
c'est l'équivalent du comptage de `sorry` sur nos lakes propres, et il est appliqué au bord
de la dépendance.

## Deux pièges de mesure relevés, et consignés

1. **Un shell `non-login` n'a pas `lake` dans le PATH.** La tentative 2, lancée par
   `wsl bash -c` (sans `-l`), rend rc=127 sur chaque étape — le log le dit littéralement :
   `pli1-build.sh: line 14: lake: command not found`. La forme qui marche est
   `wsl -d Ubuntu bash -lc 'cd <dir>; nohup bash pli1-build.sh …'`.
2. **Le `rc` d'une commande pipée est celui du pipe, pas celui de la commande.** L'étape 3
   s'écrit `lake env lean … 2>&1 | tail -60` : le `tour rc=0` publié est le code de sortie
   de `tail`. La tentative 2 le **démontre** — `lake` n'existe pas, et le log affiche
   pourtant `tour rc=0 duree=0s`. Ce que la tentative 3 prouve n'est donc pas son `rc` mais
   sa **sortie** (les trois lignes d'axiomes ci-dessus). Les étapes 1 et 2, elles, relèvent
   leur `rc` directement : ces deux lectures-là sont valides.

## Ce que la mesure décide

- **Budget CI : la visite reste hors CI.** 10 039 s (2 h 47) pour un `lake build` complet à
  partir d'un `.lake` froid — le régime d'un runner CI — et 3 h 47 pour la visite entière,
  là où les jobs CI de ce dépôt meurent vers ~30 min de build (#18100). Même le relevé
  incrémental du 07/10, pourtant fait dans un `.lake` chaud, totalisait ~2 359 s (39 min)
  d'élaboration pour les trois fermetures seules (README du lake). Les deux régimes
  dépassent le plafond : l'arbitrage « hors CI » du README est **confirmé par la mesure**.
  Inscrire ce lake dans la matrice CI partagée reste une décision de budget qui appartient
  au coordinateur, pas à la PR qui livre la visite.
- **La contrainte est le temps, ni la mémoire ni le disque.** ~5 Go de mémoire utilisée,
  ~27 Go disponibles, ~9,2 Gio de `.lake` : rien de tout cela n'est un obstacle ; la durée
  d'élaboration en est un.
- **La reprise après incident est acquise.** Un build tué par l'environnement (VM arrêtée)
  reprend au job suivant sans ménage — propriété utile à toute mesure longue d'un lake, et
  qui rend une interruption coûteuse seulement en heures, jamais en travail perdu.

## Reproduire

```bash
cd MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean
lake exe cache get
lake build
lake env lean DifferentialTour.lean
```

Attendu : rc=0 aux trois étapes, `Build completed successfully (4223 jobs)`, et les trois
théorèmes-têtes dépendant de `[propext, Classical.choice, Quot.sound]`. Sur un `.lake` froid
(décompression Mathlib incluse), compter plusieurs heures ; sur un `.lake` déjà bâti,
quelques minutes.

## Voir aussi

- [#18205](https://github.com/jsboige/CoursIA/issues/18205) — EPIC origami géométrie différentielle
- [`differential_lean/README.md`](../../MyIA.AI.Notebooks/SymbolicAI/Lean/differential_lean/README.md) —
  l'enveloppe, ses mesures du 07/10 et la forme « par dépendance, jamais par copie » (#19636)
- [`origami-reconnaissance.md`](origami-reconnaissance.md) — Pli 1, sub-grains 3 (sources
  tierces) et 4 (emplacement), livrés par #18978
