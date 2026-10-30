# .NET 9 → 10 → 11 — Deltas runtime mesurés sur les bancs et carnets types du dépôt

> **Issue** : #18771 (P1, mesure centrale de l'EPIC #18695). Prérequis satisfaits : pin
> dotnet-interactive canonique 1.0.712001 (#18766, décision ai-01 du 02/10), 3 carnets types
> sélectionnés (#18769), 5 bancs baseline (#18770).
> **Chiffres attendus** : `net11-toub-digest.md` (article Toub, baseline .NET 10.0.12 —
> fichier en approche par la PR #18772, même dossier cible). **Chiffres mesurés ci-dessous** :
> baseline .NET 9.0.20 / 10.0.12 /
> 11.0.0-rc.1.26425.128 sur notre matériel.
> **Mesure** : myia-po-2026, 2026-10-02.
> **Complément** : re-mesure du banc 3 (Automata) par `myia-po-2023` le 2026-10-20 — voir la
> section « Re-mesure du banc 3 ».

## Conditions (reproductibles)

| Paramètre | Valeur |
|---|---|
| CPU | 12th Gen Intel Core i7-12700H (X64 RyuJIT AVX2, 14 cœurs) |
| Runtimes exécutants | .NET **9.0.20** (9.0.2026.41315) · .NET **10.0.12** (10.0.1226.42308) · .NET **11.0.0** RC (11.0.26.42628, build `11.0.100-rc.1.26425.128`) |
| Installation 9 et 11 | `dotnet-install` user-local sans UAC (`~/.dotnet-r9`, `~/.dotnet-r11` — règle F) ; 10 = machine-wide |
| Binaire mesuré | **un seul build** Release par banc (SDK 10.0.204 machine-wide), exécuté tel quel sur les 3 runtimes via `DOTNET_ROLL_FORWARD=Major` + `DOTNET_ROOT` dédié — le delta mesure le JIT/runtime, pas le compilateur |
| Preuve du runtime effectif | header BDN `// Runtime=.NET X.Y.Z` dans chaque log (9.0.20 / 10.0.12 / 11.0.0 vérifiés fichier par fichier) |
| Passes | 3 passes complètes (p1-p3), ordre interleave runtime dans chaque passe ; **médiane des 3 moyennes** par (banc × runtime) |
| Config BDN | InProcess + `Job.ShortRun` (playbook maison Defender, cf #18770) |
| Charge concurrente | runners CI WSL actifs pendant la mesure (sur-souscription documentée #15574) — les benchmarks à variance élevée sont flaggés INCONCLUSIF ci-dessous, pas maquillés |
| Sources | clones depth-1 des branches `feature/benchmarkdotnet-baseline` (PRs amont #18770 : MGS#58, Z3.Linq#34, Automata#8, semantic-fleet#84) |

## Banc 1 — MetaGeneticSharp (unités : ms)

| Benchmark | net9 | net10 | net11 | 9→10 | 9→11 | 10→11 | Alloc 9/10/11 |
|---|---:|---:|---:|---:|---:|---:|---|
| CenterBias_Ackley_5k | 1.563 | 1.447 | 1.426 | **−7.4 %** | −8.8 % | −1.5 % | 3.63 MB (identique) |
| CenterBias_Suite4_5k | 6.677 | 6.274 | 6.514 | −6.0 % | −2.4 % | +3.8 % | 18.85 MB (identique) |
| RandomSearch_Ackley2D_10k | 1.540 | 1.570 | 1.655 | +1.9 % | +7.5 % | +5.4 % | 2.14 MB (identique) |
| RandomSearch_Sphere10D_50k | 12.311 | 9.122 | 10.642 | −25.9 % | −13.6 % | +16.7 % | 25.94 MB (identique) — GC-sensible (Gen0 2000), médiane inter-passes encore volatile : **INCONCLUSIF 10→11** |

## Banc 2 — Z3.Linq (unités : ms ; charge native-dominée, la marge .NET = marshaling du wrapper)

| Benchmark | net9 | net10 | net11 | 9→10 | 9→11 | 10→11 | Alloc 9/10/11 |
|---|---:|---:|---:|---:|---:|---:|---|
| Linear_TechEd | 21.85 | 19.67 | 19.61 | **−10.0 %** | −10.3 % | −0.3 % | 13.14 / 13.23 / 13.8 KB |
| MiniSudoku4x4 | 21.36 | 20.25 | 20.49 | −5.2 % | −4.1 % | +1.2 % | 104.77 / 104.35 / 104.41 KB |
| SendMoreMoney | 25.49 | 25.36 | 23.66 | −0.5 % | −7.2 % | −6.7 % | 49.72 / 49.53 / 49.76 KB |

## Banc 3 — Automata (unités : us)

| Benchmark | net9 | net10 | net11 | 9→10 | 9→11 | 10→11 | Alloc 9/10/11 |
|---|---:|---:|---:|---:|---:|---:|---|
| Matching_DotNetDelegate | 587.1 | 578.8 | 573.3 | −1.4 % | −2.4 % | −1.0 % | 222.32 / 222.33 / 222.48 KB |
| Pipeline_ConvertDeterminizeMinimize | 2290.4 | 2039.7 | 2122.7 | **−10.9 %** | −7.3 % | +4.1 % | 2710.23 / 2709.52 / 2709.59 KB |
| Pipeline_EvilRegex | 1930.8 | 2053.8 | 2462.6 | +6.4 % | +27.5 % | +19.9 % | 2128.37 KB (identique) — StdDev in-passe ≈ mean (1738 de médiane sur 2685 de moyenne en net11) : **INCONCLUSIF**, à re-mesurer fenêtre CI calme — **re-mesuré le 20/10 : le signal +27,5 % ne se reproduit pas (+2,3 % en 9→11), cf. « Re-mesure du banc 3 »** |

> **Banc 3 re-mesuré le 20/10** (fenêtre du 20/10, 3 passes × 3 runtimes, protocole BDN
> identique) : les trois lignes de ce banc sont re-contextualisées dans la section
> « Re-mesure du banc 3 » — le signal fort du 02/10 sur `Pipeline_EvilRegex` n'y est
> **pas reproduit** (le +27,5 % devient +2,3 % en 9→11), la dispersion inter-passes y
> reste grande et les deltas fins du banc y restent **non concluants**. Les valeurs de ce
> tableau restent celles de la session du 02/10.

## Banc 4 — semantic-fleet (unités : us)

| Benchmark | net9 | net10 | net11 | 9→10 | 9→11 | 10→11 | Alloc 9/10/11 |
|---|---:|---:|---:|---:|---:|---:|---|
| JsonSerializer.Serialize (DTO settings) | 68.24 | 39.04 | 33.35 | **−42.8 %** | **−51.1 %** | **−14.6 %** | 35.69 KB / 36.5 KB / 36.9 KB |
| FromRequestSettings (round-trip) | 98.01 | 59.95 | 47.03 | **−38.8 %** | **−52.0 %** | **−21.6 %** | 38.61 KB / 39.5 KB / 39.9 KB |
| PromptSignature.Matches | 2.843 | 3.054 | 2.750 | +7.4 % | −3.3 % | −10.0 % | 2.77 KB (identique) — INCONCLUSIF (µs, variance > delta) |
| PromptTransform.InterpolateKeys (regex) | 16.33 | 22.32 | 18.15 | +36.7 % | +11.1 % | −18.7 % | 22.56 KB / 23.1 KB / 23.4 KB — passes dispersées : **INCONCLUSIF** |

## Banc 5 — Argumentum (unités : us ; AssetConverter, TFM net9.0-windows)

| Benchmark | net9 | net10 | net11 | 9→10 | 9→11 | 10→11 | Alloc 9/10/11 |
|---|---:|---:|---:|---:|---:|---:|---|
| Rule.LoadFromContent (50 règles multilingues) | 1714.1 | 2142.7 | 1806.4 | +25.0 % | +5.4 % | **−15.7 %** | 165.02 / 164.58 / 165.07 KB |
| Rule.LoadFromContent (500 règles multilingues) | 5124.1 | 5314.9 | 4615.0 | +3.7 % | −9.9 % | **−13.2 %** | 855.06 / 854.66 / 854.83 KB |
| Timestamping DateTime.Now ×1000 | 296.8 | 217.8 | 128.5 | **−26.6 %** | **−56.7 %** | **−41.0 %** | 57.66 / 57.66 / 57.98 KB |

Le 9→10 de Rule.LoadFromContent 50 (+25 %) est contre-intuitif et non confirmé par la variante
500 règles (+3,7 %). **Contrôlé le 29/10** : le delta 9→10 de ce banc **n'est pas établi** — sous un
ordre équilibré, net10 et net9 se chevauchent ; sous cet ordre, le biais de position **résiduel**
tombe à **+11,2 %** (moyennes agrégées sur les 18 jambes : 213,6 → 237,5 → 236,1 µs), du même ordre
que l'écart net9→net10 (+6,9 %) ; sur un runtime isolé et à n = 2 par position, l'étendue brute
atteint 38,6 % (net10) — c'est ce que le carré latin neutralise. Ce banc reste interprétable
**en 10→11**, pas en 9→10 — voir « Contrôle du banc 5 ».

> **Banc 5 contrôlé le 29/10.** Les valeurs ci-dessus sont celles de la session du 02/10 (ordre
> **fixe** : net9, net10, net11) et ne sont **pas réécrites**. Le contrôle du 29/10 (18 jambes,
> ordre équilibré, lecture par séparabilité) établit : le **9→10 n'est pas établi** sur les trois
> axes ; le **gain net11 sur le parsing ne se sépare pas** de la dispersion intra-runtime ; le
> **gain net11 sur le timestamping est confirmé** (intervalle disjoint des deux autres). Les
> valeurs absolues **ne sont pas comparables** à celles de la session du 02/10 (machine et
> version RC différentes) : ce sont les **verdicts par axe** qui sont transposés ici, pas les
> chiffres. Détail et limites : « Contrôle du banc 5 ».



**Plafond structurel prouvé** : le kernel canon `dotnet-interactive` **1.0.712001** cible
`Microsoft.NETCore.App 10.0.0` — sous un `DOTNET_ROOT` .NET 9 seul, le kernel refuse de
démarrer (`You must install or update .NET to run this application. Framework:
'Microsoft.NETCore.App', version '10.0.0'`). La mesure « carnet sous runtime 9 » est donc
**impossible avec le canon kernel actuel** (le roll-forward ne descend pas) : le volet
carnets mesure **10 vs 11** seulement.

Mesure = wall-clock du process complet (spawn kernel + compilations Roslyn + exécution),
1 run par (carnet × runtime), kernel `.net-csharp` canon 1.0.712001, copies temporaires
exécutées dans leur dossier de série (chemins de données relatifs), aucune cellule du dépôt modifiée.

| Carnet | net10 | net11 (RC) | Delta | État |
|---|---:|---:|---:|---|
| ML-05-TimeSeries | 16.7 s | 16.2 s | −3 % | **27 OK / 0 erreur des deux côtés** — compat .NET 11 prouvée, delta < bruit wall-clock (n=1) : **nul mesuré** |
| Infer-02-Gaussian-Mixtures | 24.4 s | 23.5 s | −3.7 % | idem — compat prouvée, pas de régression |

Chemins exacts (les noms de fichiers ont été renommés après ces mesures : `ML-5-TimeSeries` →
`ML-05-TimeSeries` le 10/10, `Infer-2-Gaussian-Mixtures` → `Infer-02-Gaussian-Mixtures` le
19/10) : `MyIA.AI.Notebooks/ML/ML.Net/ML-05-TimeSeries.ipynb` et
`MyIA.AI.Notebooks/Probas/Infer/Infer-02-Gaussian-Mixtures.ipynb`.

**Re-mesure calme du 02/10 soir (#18878, artefacts préservés au gist)** : ML-05-TimeSeries 13,0 s (net10) → **9,4 s** (net11) ; Infer-02-Gaussian-Mixtures 21,0 s → 21,2 s. Les deux séries (charge CI du matin : −3 %/−3,7 % ; calme du soir : −28 %/+1 %) divergent plus entre elles qu'entre runtimes — la dispersion inter-séances domine, ce qui **confirme** la lecture ci-dessous : le wall-clock carnet mesure le lancement kernel + Roslyn, pas le delta runtime. Ce que la re-mesure prouve et préserve : compatibilité complète sous 11.0.0-rc.1 (cellules code toutes exécutées, aucune erreur, runtime imprimé dans l'artefact ; comptes exacts au manifeste du gist).

Lecture honnête : le wall-clock carnet est dominé par le démarrage kernel + Roslyn ; un gain
runtime de −10 % sur les seules cellules de calcul serait invisible ici. Les bancs ci-dessus
restent l'instrument de mesure ; les carnets prouvent la **non-régression et la compatibilité**
de la chaîne notebook complète sous .NET 11 RC (kernel, Roslyn scripting, ML.NET, Infer.NET).

## Complément po-2024 (2026-10-13) — franchir le plafond « carnets 10 vs 11 seulement »

La contrainte ci-dessus (« carnet sous runtime 9 impossible ») tient **du canon kernel
1.0.712001** (TFM net10.0). Elle est levable avec un instrument **non-canon documenté** :
dotnet-interactive **1.0.617701**, dernière build mono-TFM **net9.0**, roulant sur les
trois runtimes par `DOTNET_ROLL_FORWARD=LatestMajor` (`+ DOTNET_ROLL_FORWARD_TO_PRERELEASE=1`
pour le RC). Build de kernel identique partout — la seule variable est le runtime.

- **Runtimes isolés** user-local sans UAC : `~/.dotnet-r9` (9.0.20), `~/.dotnet-r10` (10.0.12),
  `~/.dotnet-r11` (11.0.0-rc.1), chacun NETCore + ASP.NET (le host exige les deux).
  **Prérequis restore** : une install runtime-seule fait échouer toute cellule
  `#r "nuget: ..."` — dotnet-interactive restaure via le `dotnet` de son `DOTNET_ROOT`, qui
  sans SDK rend `PackageRestoreResult(succeeded=false, errors=[])` et crashe en
  `ArgumentException` (erreur avalée, constaté sur les builds 617701 ET 712001). Chaque dir
  porte donc aussi un SDK (9.0.318 / 10.0.401), purement au service du restore — le runtime
  hébergé reste fixé par le roll-forward (re-probe post-install : 9.0.20 / 10.0.12 / 11.0.0
  inchangés).
- **Preuve du runtime effectif** : carnet témoin une cellule (`System.Environment.Version`)
  sous chaque kernelspec, avant et après installs SDK — `RUNTIME 9.0.20 / 10.0.12 / 11.0.0`
  (contrôle canon 712001 @ r10 : `10.0.12`).
- **Protocole** : wall-clock papermill par run, **médiane de 3 runs alternés** (jamais 3 runs
  consécutifs du même runtime), chaque run vérifié (0 output `error`, toutes cellules
  `execution_count` rempli) — 21/21 valides, 2026-10-13, i7-11800H.

| Carnet | .NET 9 | .NET 10 | .NET 11 (rc.1) | Contrôle canon* |
|---|---:|---:|---:|---:|
| ML-05-TimeSeries | 11,37 s | 11,65 s (+2,5 %) | 12,48 s (+9,8 %) | 11,14 s |
| Infer-02-Gaussian-Mixtures | 23,98 s | 25,79 s (+7,6 %) | 26,52 s (+10,6 %) | — |

\* contrôle = canon 1.0.712001 sous .NET 10, contre 11,65 s pour l'instrument 617701 même
runtime : écart instrument **4,4 %** — même ordre que les deltas inter-runtime. Dispersion
intra-runtime ±10-15 % (ex. Infer-02 r11 : 24,29-30,66 s).

**Lecture** : aucun delta 9 → 10 → 11 distinguable du bruit au wall-clock carnet —
convergent avec la lecture po-2026 ci-dessus (kernel + Roslyn dominent), et le levier
bancs 9 → 10 (−5 à −43 %) **ne se transfère pas au format carnet** : les médianes r9 sont
égales ou plus courtes que r10/r11 aux bruits près. Ce complément ajoute : la donnée carnet
.NET 9 (absente du volet po-2026), la médiane alternée n=3 (vs n=1/2 séances), et le bornage
de l'écart instrument (4,4 %).

## Volet carnets — axe 1 (awaits profonds / Runtime Async) — ai-01, 2026-10-19

Le volet carnets ci-dessus couvre deux axes : ML.NET numérique et allocations Infer.
L'axe 1 de l'EPIC — **awaits profonds / Runtime Async opt-in**, cas de grep CA2027 — n'y
était pas couvert. La sélection des 3 carnets types est arbitrée sur [#18769] ; ce qu'il en
reste ici est le **volet mesuré** de l'axe 1.

**Les deux porteurs de l'axe 1, et pourquoi ils ne se confondent pas** (mesures first-hand
sur `origin/main` @ `63a8207db`, 2026-10-19) :

| Porteur | Chemin exact | Rôle sur l'axe 1 | Rejouable sur une machine stock ? |
|---|---|---|---|
| Cas de grep CA2027 | `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/CopilotSDK/01-GitHub-Copilot-SDK-Binding.ipynb` | **seul** `Task.WhenAny` des carnets du dépôt (1 hit : `await Task.WhenAny(tcs.Task, Task.Delay(TimeSpan.FromSeconds(180)))` ; hors sous-module `semantic-fleet`, qui en porte un second en cellule 34 de `02-oobabooga-chat-capabilities.ipynb`) ; **23 `await`** — quatrième carnet le plus asynchrone du dépôt (trois carnets Aspire et Semantic-Kernel-MCP le précèdent) | **non** — exige `CopilotAgent.App` construit (`copilot.exe`) **et** un abonnement GitHub Copilot ; sans le binaire, la cellule **dégrade en silence** (« Copilot CLI introuvable », 0 erreur, aucune mesure) |
| Porteur hors ligne | `MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/08-Aspire-AsyncFFI-Dotnet.ipynb` | async **aux frontières natives** (P/Invoke, `UnmanagedCallersOnly`, `TaskCompletionSource`, `GCHandle`) ; sa §4 est l'instrument de la famine du pool étranger — le temps de blocage du thread natif dans `SetResult` (instrumentée par #21479) | **oui** — entièrement hors ligne, **0 erreur** |

**Mesure du porteur hors ligne** — noyau `.net-csharp` canon 1.0.712001, .NET 10 machine-wide,
2026-10-19 : **11,0 s** de wall-clock rapporté par `notebook_tools.py execute`, **0 erreur**.
La même exécution chronométrée par l'exécuteur .NET `dotnet_executor.py` (via son wrapper
`exec_dotnet_persist.py`) donne 7,9 s et 8,9 s sur deux passages : la dispersion du wall-clock
carnet est celle décrite plus haut (kernel + Roslyn dominent).

| Carnet (axe 1) | net10 (canon) | net11 (RC) | Delta | État |
|---|---:|---:|---:|---|
| `08-Aspire-AsyncFFI-Dotnet.ipynb` | 11,0 s | — | **non mesuré** | rejouable hors ligne ; compat .NET 11 **à établir** par l'instrument non-canon `1.0.617701` décrit plus haut (aucun runtime isolé .NET 9/11 sur la machine de mesure) |
| `01-GitHub-Copilot-SDK-Binding.ipynb` | 39,7 s (po-2023, 14/10) | — | **non mesuré** | **non rejouable hors machine équilibrée** ; quand le CLI manque, l'exécution « passe » (0 erreur) sans produire la moindre mesure — un vert qui ne prouve rien |

**Commande de rejeu** (depuis la racine d'un checkout à jour ; le `--cwd` par défaut est le
dossier du carnet, ce qui résout les chemins de données relatifs) :

```bash
python scripts/notebook_tools/notebook_tools.py execute MyIA.AI.Notebooks/GenAI/Integrations-DotNet/Aspire/08-Aspire-AsyncFFI-Dotnet.ipynb --cell-by-cell --dotnet-only --timeout 300
```

## Verdicts par axe (gain net mesuré vs chiffre attendu du digest)

| Axe | Attendu (digest, baseline .NET 10) | Mesuré 10→11 | Mesuré 9→10 (rattrapage) | Verdict |
|---|---|---|---|---|
| JSON serialize/round-trip (semantic-fleet) | Writer escape-heavy 0,26 (×3,9) | **−14,6 % / −21,6 %** | −42,8 % / −38,8 % | **conforme en signe, inférieur en amplitude** — notre DTO n'est pas escape-heavy pur ; le gros morceau est le rattrapage 9→10 |
| DateTime.Now + timestamps (Argumentum) | **0,45 (×2,2)** | **−41,0 %** | −26,6 % — **non établi** (contrôle du 29/10) | **10→11 conforme en signe et confirmé séparable** (intervalle net11 disjoint des deux autres runtimes, contrôle du 29/10) ; amplitude relative −25 % (×1,7 mesuré vs ×2,2 article, sous charge CI) — l'axe le mieux vérifié du digest sur nos charges ; **le 9→10 n'est pas établi** : sous ordre équilibré, net10 et net9 se chevauchent |
| Rule parsing multilingue (Argumentum) | (String.Split via agrégats, hors ratios article) | −13,2 % / −15,7 % — **non séparables** (contrôle du 29/10) | +3,7 % / +25 % — **non établis** (contrôle du 29/10) | **le gain 11 sur le parsing n'est pas établi** : aucune paire de runtimes ne se sépare sur les deux axes de parsing, l'amplitude intra-runtime (jusqu'à ×2,5 pour un même runtime) domine l'écart inter-runtime ; le 9→10 de la variante 50 règles a été **contrôlé** (29/10, sur une autre machine — voir « Contrôle du banc 5 ») et **n'est pas établi** |
| Collections/LINQ (MGS) | FindAll 0,30 · SequenceEqual ×7,7 | ~0 à +17 % (GC-sensible) | −6 à −26 % | **non couvert** (nos bancs n'exercent pas ces API précises) ; côté 11 : nul/inconclusif |
| Charge native-dominée (Z3.Linq) | (rien de spécifique promis) | −0,3 à −6,7 % | −5 à −10 % | **rattrapage 10 réel (marshaling), gain 11 nul** |
| Allocation-heavy pipeline (Automata) | (Stores covariants 0,56 etc.) | +4,1 % / INCONCLUSIF EvilRegex — **signal +27,5 % non reproduit le 20/10** (re-mesure : +2,3 % 9→11, dispersion inter-passes 47–69 %) | −10,9 % | **rattrapage 10 réel ; 11 non prouvé sur cette charge** (allocs identiques au Ko près — cohérent : nos pipelines allouent par design, pas par défaut runtime) |
| Kernel notebooks | — | — | — | **le canon 1.0.712001 exige déjà ≥ .NET 10** : le dépôt ne peut pas rester « runtime 9 » pour les carnets même sans migration |

## Synthèse pour la décision P2 (LTS vs GA, escalade user)

1. **Le vrai levier mesuré est le saut .NET 9 → 10** : −5 à −43 % selon la charge (JSON et
   marshaling sur nos bancs ; `DateTime.Now` **hors banc 5**, dont le 9→10 est non établi — voir
   « Contrôle du banc 5 »). C'est aussi ce que le kernel canon impose déjà.
2. **.NET 11 RC ajoute, sur nos charges réelles, deux gains mesurés** : JSON (−15 à −22 %
   10→11) et DateTime.Now/timestamps (**−41 %** 10→11, l'axe le mieux vérifié du digest — gain
   **confirmé séparable** par le contrôle du 29/10) ; le parsing de règles Argumentum (−13/−16 %)
   **n'est plus compté comme gain établi** (29/10 : aucune paire de runtimes ne s'y sépare) ; les
   autres axes sont plats, non couverts ou inconvissables sous charge CI.
3. Les axes « vedettes » du digest (×3,9 escape, ×7,7 SequenceEqual, BigInteger ×2) ne sont
   pas exercés par nos charges : **si l'EPIC veut les départager, il faut des bancs ciblés
   API** (extension naturelle de #18770), pas nos charges représentatives.
4. Conditions : RC1, machine partagée avec CI — les deltas < ±10 % sur ces bancs ne sont pas
   séparables du bruit ; à re-mesurer fenêtre calme avant toute décision définitive.

## Re-mesure du banc 3 — fenêtre du 20/10 (myia-po-2023)

Objet : le drapeau **INCONCLUSIF** posé le 02/10 sur `Pipeline_EvilRegex` (banc 3) — « StdDev
in-passe ≈ mean (1738 de médiane sur 2685 de moyenne en net11) : à re-mesurer fenêtre CI
calme ». Cette section est la réponse mesurée à ce drapeau.

### Protocole (identique à celui du 02/10, cf. #18770)

| Paramètre | Valeur |
|---|---|
| Machine | `myia-po-2023` — i7-12700H, X64 RyuJIT AVX2 (14 cœurs) — **même modèle de CPU** que la session du 02/10 (`myia-po-2026`) |
| Runtimes | .NET **9.0.21** (9.0.2126.50404) · .NET **10.0.13** (10.0.1326.50504) · .NET **11.0.0** (11.0.26.50505 ; SDK `11.0.100-rc.2.26504.105`, distinct du runtime) |
| Preuve du runtime effectif | header `// Runtime=.NET X.Y.Z` de chaque log, vérifié fichier par fichier (9.0.21 / 10.0.13 / 11.0.0) |
| Config BDN | `InProcessEmitToolchain`, 5 warmup / 15 itérations / 1 invocation / unroll 1 — **le protocole du 02/10** (#18770) ; `ServerGarbageCollection = false` |
| Passes | 3 passes complètes, ordre net9 → net10 → net11 ; **médiane des 3 moyennes** par (banc × runtime) |
| Artefact mesuré | sous-module `Automata` au gitlink épinglé `f0618529fa`, clone depth-1 **hors dépôt** (worktree du sous-module laissé propre) ; build Release `net9.0` unique exécuté tel quel sur les 3 runtimes (`--fx-version`) — les deltas **intra-session** mesurent le runtime, pas le compilateur ; aucun comparatif binaire n'est établi avec le build du 02/10 (les SDK diffèrent : `11.0.100-rc.2` vs `10.0.204`), l'effet éventuel du compilateur n'est pas isolé entre les deux sessions |
| Journaux | gist secret [64353cf9](https://gist.github.com/jsboige/64353cf993eac7c393611a3edaeff6f1) — 9 logs BDN + `SHA256SUMS.txt` (empreinte du manifeste : `9b7644d7589c6161265614e178db4ded8e5df746d3f51a46be3ea8788379d626`) |

### Mesures (médiane des 3 moyennes, en µs)

| Benchmark | net9 | net10 | net11 | 9→10 | 9→11 | 10→11 |
|---|---:|---:|---:|---:|---:|---:|
| Pipeline_EvilRegex | 2829.4 | 2944.0 | 2894.6 | +4.1 % | **+2.3 %** | **−1.7 %** |
| Pipeline_ConvertDeterminizeMinimize | 3080.3 | 3937.0 | 3170.7 | +27.8 % | +2.9 % | −19.5 % |
| Matching_DotNetDelegate | 956.6 | 1058.0 | 815.2 | +10.6 % | −14.8 % | −22.9 % |

### Lecture (quatre points, sans arrondi favorable)

1. **Le signal fort du 02/10 ne se reproduit pas.** Le « .NET 11 pénalise `Pipeline_EvilRegex`
   de +27,5 % » (et le +19,9 % en 10→11) devient **+2,3 %** et **−1,7 %** sur la médiane des 3
   moyennes de la fenêtre du 20/10. C'est le point le plus net de cette re-mesure : aucun
   effet runtime n'y est visible ; la non-reproduction est cohérente avec un artefact de la
   fenêtre du 02/10, sans le prouver.
2. **Le drapeau « StdDev in-passe ≈ mean » ne se reproduit pas non plus** : en net11, le
   rapport StdDev/moyenne vaut 18,1 % sur la passe 1 (19,4 % sur la base médiane), le
   rapport StdDev/médiane de la passe 2 vaut 6,4 %, et la passe 3 vaut 11,8 % en
   StdDev/moyenne (11,9 % en StdDev/médiane) — loin du relevé du
   02/10, où le StdDev in-passe était de l'ordre de la moyenne de la passe (1738 de
   médiane sur 2685 de moyenne). BDN signale une distribution multimodale dans 5 des
   9 logs de la fenêtre — mValue 3,25 (net10) et 3,33 (net9) sur
   `Pipeline_ConvertDeterminizeMinimize`, 3 sur `Pipeline_EvilRegex` (net10 et net11,
   passe 3) et 3,25 (net9) sur `Matching_DotNetDelegate` — cohérent avec une charge très
   allouante (2,13 Mo par opération), pas un défaut propre à un runtime ; la pression
   Gen0 invoquée comme cause n'a **pas** été mesurée dans cette fenêtre.
3. **La fenêtre du 20/10 n'est pas plus calme que celle du 02/10** : la dispersion **entre
   passes** — écart (max − min) rapporté à la **moyenne des deux bornes** — vaut 47 %
   (`Pipeline_ConvertDeterminizeMinimize` en net10 : 2557 → 4135 µs) et 69 %
   (`Matching_DotNetDelegate` en net11 : 603 → 1241 µs). Sur ces deux autres
   benchmarks elle domine les deltas inter-runtime, et les lignes du 02/10 (`−10,9 %` pour
   `Pipeline_ConvertDeterminizeMinimize`) ne sont **pas** reproduites non plus — dans un sens
   ou dans l'autre. Sur ces deux-là, la re-mesure **ne tranche rien**.
4. **Les valeurs absolues ne sont pas comparables entre les deux sessions** : net9
   `Pipeline_EvilRegex` vaut 2829 µs ici contre 1931 µs au 02/10 (+46 %), à protocole BDN
   identique et CPU de même modèle. L'origine probable de l'écart est les versions patch
   des runtimes (9.0.21 vs 9.0.20, 10.0.13 vs 10.0.12, rc.2 vs rc.1) et l'état de charge
   de la machine — hypothèse non isolée : les deux facteurs varient ensemble d'une session
   à l'autre.
   **Seuls les deltas intra-session sont comparables** — d'où la règle de lecture : on compare
   une session à elle-même, jamais une colonne à l'autre.

### Ce que cette re-mesure règle, et ce qu'elle ne règle pas

| Point | État après le 20/10 |
|---|---|
| `Pipeline_EvilRegex` : le runtime .NET 11 est-il plus lent que .NET 9 ? | **non mesuré** — +2,3 % 9→11, −1,7 % 10→11 : aucun écart distinguable du bruit |
| `Pipeline_EvilRegex` : le drapeau INCONCLUSIF du 02/10 | **non reproduit** — le signal +27,5 % et le rapport StdDev élevé du 02/10 n'apparaissent pas dans la fenêtre du 20/10 ; une non-reproduction affaiblit le drapeau, sans le trancher |
| `Pipeline_ConvertDeterminizeMinimize`, `Matching_DotNetDelegate` | **toujours non concluants** — dispersion inter-passes 47–69 % (écart max−min rapporté à la moyenne des deux bornes) |
| Les 3 autres bancs encore marqués INCONCLUSIF (`RandomSearch_Sphere10D_50k` (MGS), `PromptSignature.Matches` et `PromptTransform.InterpolateKeys` (semantic-fleet)) | **non re-mesurés** dans ce cycle : même travail de préparation (clone depth-1 + build Release) sur des sous-modules dont les bancs amont relèvent de la coordination ai-01 |
| Une fenêtre **calme** (runner CI de la machine au repos) avec n ≥ 5 passes | **non obtenue** sur cette machine ; c'est la condition qui reste pour serrer la dispersion inter-passes |

## Contrôle du banc 5 — l'ordre fixe rend le delta 9→10 ininterprétable (myia-ai-01:CoursIA-2, 29/10)

Objet : les **deux** drapeaux que ce document pose sur le banc 5 et laisse ouverts depuis le
02/10 — « le 9→10 de Rule.LoadFromContent 50 (+25 %) est contre-intuitif et non confirmé par la
variante 500 règles (+3,7 %) : à re-mesurer fenêtre calme » (prose du banc 5) et « le 9→10 de la
variante 50 règles à re-mesurer fenêtre calme » (tableau « Verdicts par axe »). Cette section est
la réponse mesurée à ces deux drapeaux.

**Source de la mesure** : PR amont [ArgumentumGames/Argumentum#2056](https://github.com/ArgumentumGames/Argumentum/pull/2056) —
**non mergée à ce jour** ; le fichier de mesures `benchmarks/MULTI-RUNTIME-net9-net10-net11-RECHECK.md`
**n'existe que sur sa branche** (`feature/benchmarkdotnet-multiruntime-recheck`), pas sur
`Argumentum/main`. Les valeurs citées ici sont donc susceptibles de changer si la PR amont évolue.

**Ce que ce contrôle est, et ce qu'il n'est pas.** Ce n'est **pas** une ré-exécution de la
session du 02/10 : il tourne sur une **autre machine**, avec une **autre version RC** et un
protocole de harness légèrement différent (apphost lancé directement, pas le job BDN du 02/10).
Les **valeurs absolues ne sont donc pas comparables** à celles du tableau du banc 5 — seule la
session du 02/10 est comparable à elle-même. Ce que le contrôle apporte à ce document, ce sont
les **verdicts de séparabilité par axe** et l'**amplitude de l'artefact d'ordre**, établis sur les
**mêmes axes de benchmark** que le banc 5.

### Protocole

| Paramètre | Valeur |
|---|---|
| Objet | le **confound d'ordre** du banc 5 : dans un ordre fixe (net9, net10, net11), la position est parfaitement confondue avec le runtime |
| Matrice | **18 jambes** = 6 répétitions × 3 runtimes, en **carré latin** (trois ordres cycliques `9,10,11` / `10,11,9` / `11,9,10`, répétés deux fois) : chaque runtime occupe **chaque position exactement deux fois** |
| Espacement | 60 s entre deux jambes consécutives |
| Warm-up | **écarté** — une jambe `net9` jouée puis jetée avant la première jambe mesurée |
| Attestation | ligne `[Host]` du rapport BDN de chaque jambe lue et comparée au runtime attendu : **18 jambes, 0 écart** |
| Lecture | par **séparabilité** — deux groupes ne sont distinguables que si `max(A) < min(B)` ; deux groupes qui se recouvrent ne sont **pas** séparés (absence de séparation, pas preuve d'égalité) |
| Runtimes | .NET **9.0.22** · **10.0.14** · **11.0.0-rc.3** |
| Machine | i9-14900KF (le document d'origine amont tourne sur i7-13650HX ; la session du 02/10 de ce document sur i7-12700H) — **valeurs absolues non comparables** |

### Mesures — axe timestamping (`DateTime.Now` + `yyyyMMdd-HHmmss` ×1000, en µs)

| Runtime | moyenne | médiane | min – max |
|---|---:|---:|---:|
| net9.0.22 | 273,5 | 272,8 | 171,8 – 384,4 |
| net10.0.14 | 292,4 | 290,1 | 222,7 – 361,7 |
| net11.0.0-rc.3 | **121,2** | 118,3 | 99,7 – 152,6 |

**Séparabilité** :

| Comparaison | Verdict |
|---|---|
| net11 vs net9 | **SÉPARÉS** (max net11 = 152,6 < min net9 = 171,8) |
| net11 vs net10 | **SÉPARÉS** (max net11 = 152,6 < min net10 = 222,7) |
| net10 vs net9 | **CHEVAUCHEMENT** (222,7 – 361,7 et 171,8 – 384,4) |

**Axe parsing** (`Rule.LoadFromContent`, 50 et 500 règles) : **aucune paire de runtimes n'est
séparable**, sur aucun des deux axes. L'amplitude **intra-runtime** atteint ×2,5 sur l'axe
« 50 règles » (1 142 → 2 871 µs pour un **même** runtime).

**Allocations** (50 / 500 / timestamps, en KB) : net9 `162,73 / 854,48 / 57,54` · net10
`162,66 / 854,62 / 57,38` · net11 `162,54 / 854,82 / 57,76` — identiques à moins de 1 KB près,
l'étendue intra-runtime étant elle-même de cet ordre.

### Le confound, mesuré et non supposé

Dans l'ordre fixe du banc 5, la position est confondue avec le runtime. **L'amplitude de cet
artefact est mesurée sur ce banc** : sur un runtime isolé et à n = 2 par position, les moyennes
par position de l'axe timestamping s'étalent de **238,3 µs** (1re position) à **330,2 µs**
(3e position) pour **net10**, soit **+38,6 %** — une **étendue brute**, dans un seul sens
(net10 : 238,3 < 330,2), pas une dispersion symétrique, et **non représentative** : sur net9
l'étendue ne vaut que +3,4 %, sur net11 +27,9 %. C'est précisément ce que le **carré latin
neutralise** : le protocole étant équilibré (chaque runtime occupe chaque position exactement
deux fois), le biais **résiduel** sur les moyennes agrégées des 18 jambes tombe à **+11,2 %**
(213,6 → 237,5 → 236,1 µs, puis plat de p2 à p3), soit **le même ordre que l'écart net9→net10
(+6,9 %)**. Une réplication
« 9,10,11 ×3 » peut donc lire un net10 plus lent que net9 alors que l'ordre équilibré montre
qu'ils sont **indiscernables** : c'est l'artefact de l'ordre, pas un effet de runtime. La suite
monotone du document amont (#2054 : 565 → 381 → 245 µs) **ne se reproduit pas** sous cet ordre
équilibré.

### Lecture (cinq points, sans arrondi favorable)

1. **Le gain net11 sur le timestamping est réel et séparable** : 121,2 µs contre 273,5 (net9) et
   292,4 (net10), intervalle net11 **disjoint** des deux autres — **−55,7 % vs net9**,
   **−58,5 % vs net10**. C'est la seule affirmation de cet axe qui survit au protocole équilibré ;
   elle ne dit rien sur la **taille exacte** du gain, l'intervalle net9 s'étalant sur un facteur
   2,2. **Cette confirmation est indépendante** de la session du 02/10 (autre machine, autre
   protocole) : elle porte sur le **signe et la séparabilité**, pas sur l'amplitude.
2. **Le gain net10 sur net9 n'est pas établi** : les intervalles se recouvrent. Le verdict est
   une **absence de séparation**, pas une preuve d'égalité — un gain net10 plus petit que la
   dispersion du banc resterait indétectable ici. Aucune des trois lignes du banc 5 ne peut donc
   porter un verdict de gain **ou** de régression sur son delta 9→10.
3. **Le gain net11 sur le parsing n'est pas établi** : aucune paire de runtimes ne se sépare sur
   les deux axes de parsing, et l'amplitude intra-runtime (jusqu'à ×2,5) domine l'écart
   inter-runtime. Les **−15,7 % / −13,2 %** (10→11) de la session du 02/10 ne sont donc **pas**
   confirmés — ils ne sont pas infirmés non plus : ils sont **indéterminés** à la précision de ce
   banc.
4. **Les allocations ne discriminent pas** : identiques à moins de 1 KB près sur les trois
   runtimes, l'étendue intra-runtime étant du même ordre. Elles ne portent donc aucun argument
   dans un sens ou dans l'autre.
5. **La variabilité intra-runtime est le fait le plus important** de ce banc : toute affirmation
   d'amplitude doit être exprimée en **séparabilité**, pas en pourcentage de moyenne.

### Ce que ce contrôle règle, et ce qu'il ne règle pas

| Point | État après le 29/10 |
|---|---|
| Banc 5 — le 9→10 est-il une régression de `Rule.LoadFromContent` 50 (+25 %) ? | **non établi** — sous ordre équilibré, net10 et net9 sont indiscernables, et l'écart de position mesuré (±38,6 %) est du même ordre que le +25 % lui-même |
| Banc 5 — le 9→10 est-il un gain ? | **non établi** — même constat, dans l'autre sens : l'absence de séparation n'est pas une preuve d'égalité |
| Banc 5 — le gain net11 sur le timestamping tient-il ? | **confirmé en signe et en séparabilité** par un protocole équilibré indépendant ; amplitude non comparable d'une session à l'autre |
| Banc 5 — le gain net11 sur le parsing de règles (−15,7 % / −13,2 %) tient-il ? | **non établi** — aucune paire de runtimes ne se sépare sur les axes de parsing |
| Les **valeurs absolues** du tableau du banc 5 (session du 02/10) | **inchangées** — elles restent la mesure de cette session, et ne sont pas comparables aux valeurs de ce contrôle |
| Le 9→10 du banc 5 **sur la session du 02/10 elle-même** | **toujours non mesuré** — le contrôle tourne sur une autre machine ; seule une re-session du 02/10 sur cette machine trancherait la question *pour cette session* |
| Une fenêtre **calme** sur la machine du 02/10, avec n ≥ 5 passes | **non obtenue** — c'est la condition qui reste pour trancher la question *dans les conditions d'origine* |

### Origine et reproduction

- **Contrôle amont** : [ArgumentumGames/Argumentum#2056](https://github.com/ArgumentumGames/Argumentum/pull/2056) — **PR ouverte, non mergée à ce jour** ; branche `feature/benchmarkdotnet-multiruntime-recheck`, fichier `benchmarks/MULTI-RUNTIME-net9-net10-net11-RECHECK.md` (présent sur cette branche seule, absent de `Argumentum/main`), scripts versionnés `benchmarks/recheck-multiruntime.ps1` (matrice équilibrée) et `benchmarks/recheck-multiruntime-aggregate.py` (agrégation + test de séparabilité) : la conclusion repose sur une **matrice rejouable**, pas sur une lecture de trois nombres.
- **Nature de la relation avec ce document** : ce contrôle est **produit par la même lane** que la
  présente correction ; il est le relais amont de l'EPIC .NET 11 côté CoursIA (#18770) et de
  l'EPIC #18695. Le document amont d'origine (#2054) **n'est pas réécrit** : ses mesures restent
  telles quelles, et le contrôle s'y **ajoute**.
- **Reproduire** : voir le corps de la PR amont #2056 (build Release `AssetConverter.Benchmarks`,
  `recheck-multiruntime.ps1` puis `recheck-multiruntime-aggregate.py`).

## Provenance des journaux

- **Logs BDN — 45 = 5 bancs × 3 passes × 3 runtimes** : gist [d434d4dc](https://gist.github.com/jsboige/d434d4dc48db03a37bab05259921d4be) (secret, accessible par lien), manifeste `SHA256SUMS.txt` inclus, empreinte SHA-256 du manifeste `47951d824eccec4e0974142405734623c332b2ae79dd74bd9a234bbc3514c052`. Chaque log porte son header `// Runtime=.NET X.Y.Z` (9.0.20 / 10.0.12 / 11.0.0) ; l'interleave des passes se lit sur les timestamps consécutifs — ex. MGS : passe 1 à 12:23:05/08/11, passe 2 à 12:24:18/21/23, passe 3 à 12:24:48/51/53.
- **SHA exacts des bancs mesurés** (branche `feature/benchmarkdotnet-baseline`, clones depth-1) : MetaGeneticSharp `365a4fb2384f` · Z3.Linq `b804c30859e9` · Automata `abaabd1b6518` · semantic-fleet `ff0dfb47c052` · Argumentum `709e6d05f6c2`.
- **Traces carnets (volet wall-clock) — re-mesurées et préservées (#18878, 02/10 soir, machine calme)** : 4 artefacts exécutés versés dans le même gist [d434d4dc](https://gist.github.com/jsboige/d434d4dc48db03a37bab05259921d4be). Chaque artefact porte une **cellule probe** qui imprime le runtime effectif (`.NET 10.0.12` / `.NET 11.0.0-rc.1.26425.128` — les versions exactes des Conditions), toutes ses cellules code exécutées (ML-5 : **17/17** ; Infer-2 : **28/28**) et **0 erreur**. Empreintes SHA-256 : ML-5 net10 `8bf83441ef846b7e` · net11 `acf51fa1c1e4ff81` · Infer-2 net10 `e755acaadb67fe1c` · net11 `fb832217406e6bfa` (complets dans `SHA256SUMS-notebooks.txt` du gist). Les identifiants d'artefact `ML-5` / `Infer-2` sont ceux du dépôt du 02/10, **antérieur** aux renommages de fichiers du 10/10 et du 19/10 : ils désignent les mêmes deux carnets que `ML-05-TimeSeries` et `Infer-02-Gaussian-Mixtures` dans le tableau ci-dessus.

## Reproduire

```powershell
# runtimes
& dotnet-install.ps1 -Channel 9.0 -InstallDir "$env:USERPROFILE\dotnet-r9"
& dotnet-install.ps1 -Version 11.0.100-rc.1.26425.128 -InstallDir "$env:USERPROFILE\dotnet-r11"
# build unique (SDK machine 10.x) puis 3 exécutions par banc :
$env:DOTNET_ROLL_FORWARD="Major"; $env:DOTNET_MULTILEVEL_LOOKUP="0"
& "$env:USERPROFILE\dotnet-r9\dotnet.exe" <Bench.dll> --filter *   # idem r11 ; 10 = machine-wide
```

Voir aussi : [#18770] (bancs, baselines absolues) · [#18769] (sélection carnets) ·
[#18766] (canon kernel) · EPIC [#18695].
