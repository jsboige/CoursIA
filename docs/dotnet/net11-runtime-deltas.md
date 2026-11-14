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
>
> **Banc 3 re-mesuré le 11/10** (session **4 runtimes** × 5 passes entrelacées sur
> `myia-ai-01`, net8.0 y entrant pour la première fois) : les valeurs de ce tableau
> **restent celles de la session du 02/10** — la session du 11/10 est re-contextualisée
> dans la section « Session du 2026-11-10 sur `myia-ai-01` ». Elle n'établit **aucun**
> écart 10→11 sur les six axes du banc.
>
> **Contrôle croisé du 11/10, le même jour** (une seule compilation, trois runtimes) : la
> session du 11/10 comparait **quatre compilations**, une par TFM, là où le protocole de
> référence tient la compilation constante. Rejoué en compilation constante, **aucune des
> 18 paires n'est séparable** et le « rattrapage 9→10 » de −26,8 % **n'est pas établi**
> (−14,0 %, intervalles qui se recouvrent). Les verdicts de la session du 11/10 sont
> donc **retirés** : voir « Contrôle croisé du 2026-11-10 ».

## Banc 4 — semantic-fleet (unités : us)

> « Re-mesure du banc 4 » — les deux drapeaux INCONCLUSIF de ce banc
> (`PromptSignature.Matches`, `PromptTransform.InterpolateKeys`) ont été re-mesurés le 30/10
> sur un modèle de CPU distinct (i7-11800H) : **les deux drapeaux sont maintenus** — une
> session à 5 passes (#23326) mesure sur `Matches` le signe opposé au mien, et le protocole
> du banc (une invocation par itération) rend cette cellule structurellement bruitée ; les
> deux lignes JSON sont en revanche reproduites en signe et en amplitude. Les valeurs de ce
> tableau restent celles de la session du 02/10.

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
| ML-05-TimeSeries-CSharp | 16.7 s | 16.2 s | −3 % | **27 OK / 0 erreur des deux côtés** — compat .NET 11 prouvée, delta < bruit wall-clock (n=1) : **nul mesuré** |
| Infer-02-Gaussian-Mixtures | 24.4 s | 23.5 s | −3.7 % | idem — compat prouvée, pas de régression |

Chemins exacts (les noms de fichiers ont été renommés après ces mesures : `ML-5-TimeSeries` →
`ML-05-TimeSeries-CSharp` le 10/10, `Infer-2-Gaussian-Mixtures` → `Infer-02-Gaussian-Mixtures` le
19/10) : `MyIA.AI.Notebooks/ML/ML.Net/ML-05-TimeSeries-CSharp.ipynb` et
`MyIA.AI.Notebooks/Probas/Infer/Infer-02-Gaussian-Mixtures.ipynb`.

**Re-mesure calme du 02/10 soir (#18878, artefacts préservés au gist)** : ML-05-TimeSeries-CSharp 13,0 s (net10) → **9,4 s** (net11) ; Infer-02-Gaussian-Mixtures 21,0 s → 21,2 s. Les deux séries (charge CI du matin : −3 %/−3,7 % ; calme du soir : −28 %/+1 %) divergent plus entre elles qu'entre runtimes — la dispersion inter-séances domine, ce qui **confirme** la lecture ci-dessous : le wall-clock carnet mesure le lancement kernel + Roslyn, pas le delta runtime. Ce que la re-mesure prouve et préserve : compatibilité complète sous 11.0.0-rc.1 (cellules code toutes exécutées, aucune erreur, runtime imprimé dans l'artefact ; comptes exacts au manifeste du gist).

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
| ML-05-TimeSeries-CSharp | 11,37 s | 11,65 s (+2,5 %) | 12,48 s (+9,8 %) | 11,14 s |
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
| `08-Aspire-AsyncFFI-Dotnet.ipynb` | 11,0 s (mur) ; **80,04 ms [71,82 – 103,48]** (n=25, instrument §4) | **81,45 ms [70,59 – 116,79]** (n=25, instrument §4) | **+1,76 %** — **INCONCLUSIF** (intervalles chevauchants) | rejouable hors ligne ; compat .NET 11 **établie** (RC 11.0.0-rc.3.26522.148, instrument canon de la §4) ; voir `net11-async-ffi-deltas.md` |
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
| Allocation-heavy pipeline (Automata) | (Stores covariants 0,56 etc.) | +4,1 % / INCONCLUSIF EvilRegex — **signal +27,5 % non reproduit le 20/10** (re-mesure : +2,3 % 9→11, dispersion inter-passes 47–69 %) — **le 11/10 n'établit aucun écart 10→11 sur les six axes du banc** (session 4 runtimes × 5 passes, 0 paire séparable) | −10,9 % — **établi le 02/10, NON CONFIRMÉ le 11/10** : la session 4 runtimes du 11/10 donnait −26,8 % (intervalles disjoints), mais le **contrôle croisé du 11/10 en compilation constante ne reproduit pas le verdict** (−14,0 %, intervalles qui se recouvrent) — l'écart établi était donc au moins partiellement un effet de compilation | **rattrapage 10 réel ; 11 non prouvé sur cette charge** (allocs identiques au Ko près — cohérent : nos pipelines allouent par design, pas par défaut runtime) — **l'axe allocation est le seul concluant de la session du 11/10, et il est négatif** (amplitude ≤ 0,92 % sur les charges en Mo) |
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

## Re-mesure du banc 3 — fenêtres du 20/10 (myia-po-2023), du 29/10, du 11/10 et contrôle croisé du 11/10 (myia-ai-01:CoursIA-2)

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
| Les 3 autres bancs encore marqués INCONCLUSIF (`RandomSearch_Sphere10D_50k` (MGS), `PromptSignature.Matches` et `PromptTransform.InterpolateKeys` (semantic-fleet)) | **non re-mesurés** dans ce cycle : même travail de préparation (clone depth-1 + build Release) sur des sous-modules dont les bancs amont relèvent de la coordination ai-01 — **tentative du 29/10 sur `myia-ai-01` : non concluante (fenêtre chargée), cf. « Tentative du 2026-10-29 sur myia-ai-01 »** |
| Une fenêtre **calme** (runner CI de la machine au repos) avec n ≥ 5 passes | **non obtenue** sur cette machine — **non obtenue non plus sur `myia-ai-01` le 29/10 (charge d'hôte mesurée à 62-91 %), cf. la même section**. Elle n'est pas pour autant la condition **suffisante** : le protocole des bancs est une seconde cause, plus fondamentale, cf. « Le protocole du banc, seconde cause » |

### Tentative du 2026-10-29 sur `myia-ai-01` — les 3 bancs restants, et la charge de l'hôte

Les trois bancs encore marqués INCONCLUSIF ont été re-mesurés le **2026-10-29, ~18:05-18:07Z**, sur le poste `myia-ai-01`
(`myia-ai-01:CoursIA-2`). Objet double : tenter de lever le drapeau, et **mesurer si ce siège peut servir de fenêtre calme**.

**Protocole exécuté** (même règle de lecture que ci-dessus : on compare une session à elle-même).

| Paramètre | Valeur |
|---|---|
| Bancs | `RandomSearch_Sphere10D_50k` (MetaGeneticSharp) · `PromptSignature.Matches` et `PromptTransform.InterpolateKeys` (semantic-fleet) |
| Build | Release `net9.0` **unique** par banc (SDK 10.0.114 machine), jamais reconstruit entre les runtimes |
| Exécution | `dotnet exec --fx-version <version exacte>` : 9.0.22 et 10.0.14 (racine machine), 11.0.0-rc.3.26522.148 (racine isolée `~/.dotnet11`, `dotnet-install` user-level, sans UAC) |
| Config BDN | 0.15.8, `InProcessEmitToolchain`, ShortRun 5 warmup / 15 itérations / 1 invocation / unroll 1 (protocole de référence, mode InProcess) |
| Passes | **5** par (banc × runtime), ordre **interleave** (net9 → net10 → net11 dans chaque passe), **médiane des 5 moyennes** par cellule |
| Attestation | chaque journal porte son header `// Runtime=.NET X.Y.Z` — 9.0.22 / 10.0.14 / 11.0.0 relevés sur les 45 journaux (3 bancs × 3 runtimes × 5 passes) |

**Mesures** (médiane des 5 moyennes, en µs ; dispersion = écart max−min rapporté à la moyenne des bornes, par runtime)

| Benchmark | net9 | net10 | net11 (rc.3) | 9→10 | 9→11 | dispersion max |
|---|---:|---:|---:|---:|---:|---:|
| `RandomSearch_Sphere10D_50k` | 13 169 | 14 450 | 13 108 | +9,7 % | −0,5 % | 38 % |
| `PromptSignature.Matches` | 4,77 | 5,83 | 4,85 | +22,2 % | +1,7 % | 102 % |
| `PromptTransform.InterpolateKeys` | 20,92 | 25,23 | 16,36 | +20,6 % | −21,8 % | 123 % |

**Charge de l'hôte pendant la fenêtre** : `myia-ai-01` héberge en permanence le vLLM de la flotte et les runners
CI auto-hébergés — **charge processeur 91 % à 18:05Z, 62 % à 18:15Z, 76 % à 18:16Z**, avec **149 à 150 processus**
`dotnet`/`node`/`Runner` relevés sur les mêmes échantillons.

### Ce que la tentative règle, et ce qu'elle ne règle pas

| Point | État après le 29/10 |
|---|---|
| `RandomSearch_Sphere10D_50k` (MGS) | **toujours non concluant** — 9→11 à −0,5 %, pour une dispersion de 28 à 38 % ; le delta est dans le bruit |
| `PromptSignature.Matches` (semantic-fleet) | **toujours non concluant** — 9→11 à +1,7 %, dispersion 42 à 102 % (le 9→10 apparent de +22 % est un artefact de bruit) |
| `PromptTransform.InterpolateKeys` (semantic-fleet) | **toujours non concluant** — le −21,8 % apparent est **incohérent avec la dispersion de 123 %** sur net9 : la session ne permet pas de le retenir |
| La fenêtre **calme** | **non obtenable sur ce siège** — fait mesuré, pas une hypothèse : la charge de l'hôte (62-91 %) et les 149-150 processus-résidents ne laissent pas de fenêtre de mesure propre. La re-mesure qui doit lever ces trois drapeaux doit se faire sur un **siège sans runners CI** (po-2023 ou po-2026), pas être rejouée ici |
| Comparabilité avec les sessions du 02/10 et du 20/10 | **aucune** — machine différente, versions patch des runtimes différentes, .NET 11 en rc.3 (contre rc.1 puis rc.2). Ces chiffres sont une **troisième session**, pas une prolongation des précédentes ; ils se lisent session par session, comme les deux autres |

Les trois drapeaux INCONCLUSIF **restent donc posés** : cette tentative n'apporte pas de verdict, elle apporte la
preuve que la condition manquante (une fenêtre calme) n'est pas accessible depuis ce poste.

### Session du 2026-11-10 sur `myia-ai-01` — quatre runtimes, cinq passes entrelacées

Quatrième session du banc 3 (après le 02/10, le 20/10 et le 29/10), et
**première session à quatre runtimes** : net8.0 y entre pour la première fois,
et les **deux** classes de banc du sous-module sont mesurées — dont
`AutomatonOpsBench`, qui n'avait jamais été comparé entre runtimes. Objet :
trancher l'axe « rattrapage 9→10 / gain 10→11 » du banc 3 avec un critère de
séparabilité explicite, et publier les baselines net10 / net11 qui manquaient au
dépôt amont du sous-module.

#### Protocole

| Paramètre | Valeur |
|---|---|
| Machine | `myia-ai-01` — i9-14900KF 3,20 GHz, 32 cœurs logiques / 24 physiques, Windows 11 Pro (10.0.26300.9711) |
| Runtimes | .NET **8.0.33** · **9.0.22** · **10.0.14** · **11.0.0** (rc.3.26522.148) |
| Preuve du runtime effectif | en-tête `[Host] : .NET X.Y.Z (...)` de chaque rapport BDN, relevé sur les 20 runs |
| Config BDN | 0.15.8, `InProcessEmitToolchain`, ShortRun 5 warmup / 15 itérations / 1 invocation / unroll 1, `ServerGarbageCollection = false` |
| Passes | **5** passes complètes, ordre **interlacé** (net8 → net9 → net10 → net11 dans chaque passe), **médiane des 5 moyennes** par cellule |
| Build | un build Release **par TFM** (le `<TargetFrameworks>` du banc ne liste que `net8.0;net9.0` : édition temporaire d'une ligne, restaurée après mesure) |
| Artefact mesuré | sous-module `Automata` au gitlink épinglé `e6193d9b0988b7cf9d8023bd3a8291baca4b73f4` — **identique** au commit mesuré (`git ls-tree origin/main`) |
| Bancs | `AutomatonOpsBench` (déterminisation, minimisation Hopcroft, équivalence) **et** `RegexPipelineBenchmarks` (pipeline symbolique, matching SRE, regex piégée) |

Deux écarts de protocole, assumés : (a) contrairement aux sessions du 20/10 et
du 29/10, qui rejouaient un **build unique** `net9.0` via
`dotnet exec --fx-version`, chaque runtime a ici **son** build — c'est le
protocole des baselines amont, qui évite l'artefact du roll-forward, au prix
d'une variante de compilateur par TFM ; (b) `AutomatonOpsBench` n'avait jamais
été comparé entre runtimes. **Ces valeurs ne sont comparables à aucune session
antérieure**, seulement à elles-mêmes.

#### Mesures (médiane des 5 moyennes)

| Benchmark | net8.0 | net9.0 | net10.0 | net11.0 (rc.3) | 8→9 | 9→10 | 10→11 | Allocated (8 / 9 / 10 / 11) |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `Determinize_NFA_L15` (ms) | 12.77 | 13.62 | 14.26 | 11.81 | +6.7 % | +4.7 % | -17.2 % | 11.42 MB / 11.42 MB / 11.42 MB / 11.41 MB |
| `Determinize_plus_MinimizeHopcroft_L15` (ms) | 50.85 | 40.29 | 44.33 | 54.18 | -20.8 % | +10.0 % | +22.2 % | 26.05 MB / 26.06 MB / 26.06 MB / 26.06 MB |
| `IsEquivalent_DFA_Twins_L15` (ms) | 15.58 | 13.24 | 13.86 | 15.45 | -15.0 % | +4.7 % | +11.5 % | 24.08 MB / 24.08 MB / 24.07 MB / 23.86 MB |
| `Matching_DotNetDelegate` (µs) | 616.0 | 536.0 | 705.0 | 562.0 | -13.0 % | +31.5 % | -20.4 % | 219.99 KB / 222.77 KB / 223.48 KB / 223.63 KB |
| `Pipeline_ConvertDeterminizeMinimize` (µs) | 1792.0 | 1730.0 | 1267.0 | 1383.0 | -3.4 % | -26.8 % | +9.1 % | 2709.13 KB / 2712.74 KB / 2705.76 KB / 2704.8 KB |
| `Pipeline_EvilRegex` (µs) | 1328.0 | 1145.0 | 959.0 | 994.0 | -13.8 % | -16.2 % | +3.7 % | 2125.73 KB / 2129.95 KB / 2124.28 KB / 2124.66 KB |

**Critère de séparabilité** : deux runtimes sont séparables sur un axe si
l'intervalle [min, max] des 5 moyennes de passes de l'un **et** de l'autre
**ne se recouvrent pas**. 18 paires testées (6 benchmarks × 3 paires
consécutives), **3 séparables** :

| Benchmark | Paire | Écart | Intervalles | Statut |
|---|---|---:|---|---|
| `Pipeline_ConvertDeterminizeMinimize` | net9 → net10 | **−26,8 %** | [1645..1864] vs [876..1509] µs | **établi** |
| `Determinize_plus_MinimizeHopcroft_L15` | net8 → net9 | **−20,8 %** | [46.43..57.04] vs [38.85..42.08] ms | **établi** |
| `Determinize_plus_MinimizeHopcroft_L15` | net9 → net10 | +10,0 % | [38.85..42.08] vs [43.65..51.61] ms | **non compté** — à la limite exacte du seuil de ±10 % de ce document |

#### Lecture (six points, sans arrondi favorable)

1. **Le rattrapage 9→10 est confirmé, et son amplitude dépasse celle du
   02/10.** `Pipeline_ConvertDeterminizeMinimize` : **−26,8 %** en 9→10
   (intervalles disjoints), contre −10,9 % au 02/10 sur la même charge et dans
   le même sens. C'est le seul écart franchement établi de la session, et il
   porte sur la charge la plus allouante du banc — l'axe que le digest Toub
   vise.
   **Verdict retiré le même jour** : le contrôle croisé (« Contrôle croisé du
   2026-11-10 ») rejoue le banc en compilation constante et ne retrouve pas cet
   écart (−14,0 %, intervalles qui se recouvrent). Le point est conservé ici
   comme le constat de la session, pas comme un verdict du document.
2. **net9 bat net8 sur la minimisation Hopcroft (−20,8 %)** : donnée **nouvelle**
   — net8 n'avait jamais été comparé à net9 sur ce banc.
3. **Aucune paire n'est séparable en 10→11, sur aucun des six axes.** Les
   intervalles de .NET 11 et de .NET 10 se recouvrent partout, y compris sur le
   pipeline symbolique où le gain net10 avait été établi. **Aucun gain .NET 11
   n'est établi sur le banc 3** — et aucun écart négatif net ne l'est non plus :
   le résultat est « rien de séparable », pas « .NET 11 est plus lent ».
4. **Les allocations ne bougent pas** : amplitude maximale de 0,92 % sur les
   charges en Mo, 1,65 % sur la plus petite charge (le matching délégué). C'est
   le **seul axe concluant** de la session — et il conclut à l'absence de gain
   d'allocation attribuable au runtime, .NET 10 comme .NET 11. Cohérent avec le
   reste du document : nos pipelines allouent par design, pas par défaut
   runtime.
5. **La fenêtre n'est toujours pas calme, et c'est mesuré** : CPU 66 % à 93 %
   sur 20 échantillons (un échantillon isolé à 11 %), 1081 à 1098 processus
   résidents dont 104 `dotnet`/`node`/`Runner`. Le poste `myia-ai-01` héberge le
   vLLM de la flotte et les runners CI auto-hébergés. La session **confirme** le
   constat du 29/10 sur ce siège : ce poste n'est pas une fenêtre calme. La
   comparaison intra-session en est d'autant moins affectée que tous les
   runtimes ont subi la même charge — c'est la limite assumée d'une session
   unique.
6. **Cinq passes suffisent à rendre séparables des écarts réels, mais pas à en
   exclure d'autres** : un intervalle de cinq points est large ; une session
   plus longue resserrerait les intervalles et pourrait rendre séparables des
   paires aujourd'hui dans le bruit. Le sens des conclusions de la session
   (10→11 non séparable sur les six axes) est robuste à ce degré de précision,
   mais **une amplification d'axe reste possible** — et le contrôle croisé du
   11/10 montre que le 9→10, lui, ne survit pas au protocole de référence.

#### Ce que cette session règle, et ce qu'elle ne règle pas

| Point | État après le 11/10 |
|---|---|
| `Pipeline_ConvertDeterminizeMinimize`, 9→10 | **établi dans cette session** (−26,8 %, intervalles disjoints) — **verdict retiré le jour même par le contrôle croisé** : en compilation constante, l'écart n'est plus que de −14,0 % et les intervalles se recouvrent. Le « rattrapage 10 » du banc 3 **n'est pas établi** sous le protocole de référence |
| `Pipeline_ConvertDeterminizeMinimize`, 10→11 | **non séparé** — aucun gain .NET 11 établi |
| Les six axes du banc 3, 10→11 | **aucun séparable** — le gain .NET 11 n'est pas établi sur ce banc, et le « signal +27,5 % » du 02/10 sur `Pipeline_EvilRegex` ne réapparaît pas une seconde fois (ici +3,7 % en 10→11) |
| Axe allocation | **concluant, et négatif** — aucun gain d'allocation attribuable au runtime, .NET 10 comme .NET 11 |
| net8 hors des comparaisons antérieures | **entré dans la comparaison** pour la première fois : le banc 3 se lit désormais de net8 à net11 dans une même session |
| Comparabilité avec les sessions du 02/10, du 20/10 et du 29/10 | **aucune** — poste différent, versions patch différentes, build par TFM au lieu d'un build roulé en avant : cette session est une **quatrième session autonome** |
| La fenêtre calme sur ce siège | **toujours non obtenable** — fait mesuré (point 5) |

#### Provenance

Baselines publiées dans le dépôt amont du sous-module (`MyIntelligenceAgency/Automata`) :
PR **#19** (`bench/net10-net11-baselines-4runtimes`) —
`benchmarks/BASELINE-net10.0.md`, `benchmarks/BASELINE-net11.0.md` et
`benchmarks/COMPARISON-net8-net11-2026-11-10.md` (comparaison des quatre
runtimes, matrice des 5 passes, profil de charge d'hôte). **Aucun code de
production modifié** ; `Automata.Benchmarks.csproj` inchangé (l'édition de
`<TargetFrameworks>` était locale et a été restaurée avant livraison). Les 20
rapports BDN (5 passes × 4 runtimes) sont reproductibles par les commandes de la
section « Protocole ».

#### Mesures brutes, cellule par cellule

Chaque runtime a été exécuté 5 fois ; l'intervalle [min, max] ci-dessous est
celui qui sert de critère de séparabilité.

| Benchmark | Runtime | min | max | médiane |
|---|---|---:|---:|---:|
| `Determinize_NFA_L15` | net8.0 | 12.01 | 15.82 | 12.77 |
| `Determinize_NFA_L15` | net9.0 | 12.19 | 15.74 | 13.62 |
| `Determinize_NFA_L15` | net10.0 | 11.68 | 16.41 | 14.26 |
| `Determinize_NFA_L15` | net11.0 | 10.72 | 12.16 | 11.81 |
| `Determinize_plus_MinimizeHopcroft_L15` | net8.0 | 46.43 | 57.04 | 50.85 |
| `Determinize_plus_MinimizeHopcroft_L15` | net9.0 | 38.85 | 42.08 | 40.29 |
| `Determinize_plus_MinimizeHopcroft_L15` | net10.0 | 43.65 | 51.61 | 44.33 |
| `Determinize_plus_MinimizeHopcroft_L15` | net11.0 | 39.98 | 65.88 | 54.18 |
| `IsEquivalent_DFA_Twins_L15` | net8.0 | 13.15 | 20.73 | 15.58 |
| `IsEquivalent_DFA_Twins_L15` | net9.0 | 12.38 | 16.12 | 13.24 |
| `IsEquivalent_DFA_Twins_L15` | net10.0 | 12.76 | 18.59 | 13.86 |
| `IsEquivalent_DFA_Twins_L15` | net11.0 | 11.93 | 23.20 | 15.45 |
| `Matching_DotNetDelegate` | net8.0 | 603.0 | 723.0 | 616.0 |
| `Matching_DotNetDelegate` | net9.0 | 439.0 | 677.0 | 536.0 |
| `Matching_DotNetDelegate` | net10.0 | 521.0 | 795.0 | 705.0 |
| `Matching_DotNetDelegate` | net11.0 | 481.0 | 732.0 | 562.0 |
| `Pipeline_ConvertDeterminizeMinimize` | net8.0 | 1629.0 | 2245.0 | 1792.0 |
| `Pipeline_ConvertDeterminizeMinimize` | net9.0 | 1645.0 | 1864.0 | 1730.0 |
| `Pipeline_ConvertDeterminizeMinimize` | net10.0 | 876.0 | 1509.0 | 1267.0 |
| `Pipeline_ConvertDeterminizeMinimize` | net11.0 | 1240.0 | 1530.0 | 1383.0 |
| `Pipeline_EvilRegex` | net8.0 | 1147.0 | 1521.0 | 1328.0 |
| `Pipeline_EvilRegex` | net9.0 | 1048.0 | 1316.0 | 1145.0 |
| `Pipeline_EvilRegex` | net10.0 | 871.0 | 1144.0 | 959.0 |
| `Pipeline_EvilRegex` | net11.0 | 888.0 | 1117.0 | 994.0 |

### Contrôle croisé du 2026-11-10 — une seule compilation, trois runtimes

**Objet.** La session du 11/10 comparait **quatre compilations**, une par TFM
(`net8.0`, `net9.0`, `net10.0`, `net11.0`). Le protocole de référence de ce
document (« build unique … jamais reconstruit entre les runtimes ») tient au
contraire la **compilation constante** et ne fait varier que le runtime : une
comparaison par TFM melange donc l'effet runtime à l'effet compilation. Ce
contrôle rejoue le banc 3 dans le protocole de référence, pour séparer les deux
effets et dire ce qui survit.

#### Protocole

| Paramètre | Valeur |
|---|---|
| Compilation | **une seule**, `net9.0`, Release — SHA-256 `150be1f2546eb8e5be4401d83b9860490ede13280230be256d35b535db8b34ee` ; le **même fichier** est exécuté sous les trois runtimes |
| Runtimes | net9.0.22 · net10.0.14 · net11.0.0-rc.3.26522.148, sélectionnés par `dotnet exec --fx-version <version exacte>` |
| Preuve du runtime | en-tête `// Runtime=.NET X.Y.Z (build, …)` de chaque journal BDN, relevé sur les 15 journaux : une seule version par runtime, sur les 5 passes |
| Config BDN | 0.15.8, `InProcessEmitToolchain`, `ShortRun` 5 warmup / 15 itérations / 1 invocation / unroll 1 — identique à la session du 11/10 |
| Passes | **5** passes, ordre **interlacé** (net9 → net10 → net11), **médiane des 5 moyennes** |
| Critère | inchangé : deux runtimes sont séparables si leurs intervalles [min, max] des 5 moyennes ne se recouvrent pas |
| Charge d'hôte | CPU 52 % à 91 % sur 15 échantillons, 1079 à 1099 processus résidents (session du 11/10 : 66–93 %, 1081–1098) |

#### Mesures (médiane des 5 moyennes ; intervalle [min, max] des 5 passes ; unités : us)

| Benchmark | net9.0.22 | net10.0.14 | net11.0 (rc.3) | 9→10 | 10→11 | 9→11 |
|---|---|---|---|---:|---:|---:|
| `Determinize_NFA_L15` | 12 510 [11 080 ; 17 500] | 14 830 [14 060 ; 17 660] | 11 530 [10 610 ; 14 120] | +18,5 % | −22,3 % | −7,8 % |
| `Determinize_plus_MinimizeHopcroft_L15` | 47 600 [35 810 ; 54 140] | 40 870 [33 960 ; 48 530] | 48 570 [36 760 ; 57 920] | −14,1 % | +18,8 % | +2,0 % |
| `IsEquivalent_DFA_Twins_L15` | 14 440 [13 420 ; 16 390] | 17 010 [14 810 ; 17 970] | 12 930 [12 270 ; 19 630] | +17,8 % | −24,0 % | −10,5 % |
| `Matching_DotNetDelegate` | 419 [281 ; 702] | 603 [438 ; 753] | 542 [349 ; 718] | +43,9 % | −10,2 % | +29,2 % |
| `Pipeline_ConvertDeterminizeMinimize` | 1 467 [1 061 ; 1 787] | 1 261 [870 ; 1 795] | 1 229 [985 ; 1 403] | **−14,0 %** | −2,6 % | −16,2 % |
| `Pipeline_EvilRegex` | 954 [945 ; 1 249] | 842 [735 ; 1 068] | 1 016 [711 ; 1 084] | −11,7 % | +20,7 % | +6,6 % |

**Aucune des 18 paires testées n'est séparable** : tous les intervalles se
recouvrent. Les allocations restent alignées entre runtimes : 2 712,74 KB
(net9), 2 706,04 KB (net10), 2 705,13 KB (net11) sur
`Pipeline_ConvertDeterminizeMinimize`, soit un écart de 0,25 % et 0,28 %.

#### Lecture (six points, sans arrondi favorable)

1. **Le verdict « établi » sur l'axe 9→10 est retiré.** En compilation
   constante, l'écart tombe de −26,8 % à −14,0 % et les intervalles se
   recouvrent ([1 061 ; 1 787] contre [870 ; 1 795]). Le « rattrapage .NET 10 »
   du banc 3 **n'est pas établi** sous le protocole de référence : l'amplitude
   publiée était donc, au moins pour partie, un effet de compilation.
2. **Le gain .NET 11 reste non établi**, et cette fois par une seconde voie. La
   session du 11/10 l'établissait par l'absence de paire séparable en 10→11 ;
   le contrôle retrouve ce verdict à l'identique, et referme les deux axes
   que la session laissait ouverts (9→10 et 8→9).
3. **L'axe allocation reste le seul axe concluant, et il reste négatif.** Aucun
   gain d'allocation attribuable au runtime n'est établi, .NET 10 comme .NET 11,
   et l'écart entre runtimes (≤ 0,28 % sur le pipeline) est plus faible que
   celui mesuré dans la session du 11/10 (≤ 0,92 %).
4. **Ce contrôle ne teste pas net8.** Une comparaison inter-runtime suppose la
   même IL ; net8 n'y entre pas. Le verdict « net9 bat net8 de 20,8 % » de la
   session du 11/10 **reste donc non vérifié** — ni infirmé, ni confirmé.
5. **Les dispersions du contrôle sont au moins aussi larges** que celles de la
   session du 11/10 (jusqu'à 85,8 % contre 47–69 %) : la charge d'hôte, comparable
   dans les deux sessions, n'a pas été plus favorable. Un verdict qui ne survit
   qu'à un tirage favorable n'est pas un verdict établi — c'est le sens du
   critère retenu.
6. **Ce contrôle établit un point négatif, pas une cause.** Il dit qu'aucun
   écart inter-runtime n'est établi en compilation constante ; il ne dit pas
   pourquoi la dispersion est si large. La fenêtre calme reste non obtenue sur
   ce siège, et le « Protocole du banc, seconde cause » plus bas reste la
   question ouverte.

#### Ce que ce contrôle change dans le document

Les lignes de renvoi du tableau de synthèse du banc 3, la ligne de verdict par
axe et le tableau « ce que cette session règle » sont **corrigées** : le 9→10
n'est plus « établi », il est « non établi en compilation constante ». La
session du 11/10 reste publiée comme session — ses valeurs sont réelles et
reproductibles, avec le protocole qu'elle a suivi (compilations par TFM) — et le
contrôle en montre la limite.

#### Provenance et reproduction

Les 15 rapports BDN du contrôle sont conservés hors dépôt. Reproduction (une
compilation, trois runtimes, 5 passes entrelacées) :

```bash
dotnet build src/Automata.Benchmarks -c Release -f net9.0
dotnet exec --fx-version 9.0.22                 bin/Release/net9.0/Automata.Benchmarks.dll --filter '*'
dotnet exec --fx-version 10.0.14                bin/Release/net9.0/Automata.Benchmarks.dll --filter '*'
dotnet exec --fx-version 11.0.0-rc.3.26522.148  bin/Release/net9.0/Automata.Benchmarks.dll --filter '*'
```

### Le protocole du banc, seconde cause — et elle est plus fondamentale que la fenêtre

Cette section corrige une lecture trop courte de ce document. Jusqu'ici, la dispersion résiduelle
était attribuée à l'hôte : charge CI, fenêtre non calme, dispersion inter-séances. Une mesure
indépendante de la lane `myia-po-2023:CoursIA-2` (dashboard #18695, commentaire `c.6505273899`)
établit qu'une seconde cause, **inscrite dans la configuration des bancs**, suffit à elle seule à
empêcher la conclusion — et qu'un hôte au repos ne la lèverait pas.

Dans la configuration mesurée le 29/10, `InProcessShortConfig` épinglait
`.WithInvocationCount(1).WithUnrollFactor(1)`
(dans `semantic-fleet/benchmarks/SemanticFleet.Benchmarks/PromptSettingsBenchmarks.cs` ; même
choix dans `MetaGeneticSharp.Benchmarks/OptimizerBenchmarks.cs`, justifié au fichier par un
contournement antivirus). Conséquence à cette date : **une itération valait exactement une invocation**, soit
3,7 à 90 µs selon la cellule — deux à quatre ordres de grandeur sous les ~100 ms que BDN
recommande, et qu'il réclame lui-même dans les journaux. À cette granularité, le bruit n'est pas
réduit par une machine calme : il est structurel. Le gitlink `semantic-fleet`
`e675df97c4c5`, présent sur `main` au 09/11, a depuis retiré ce plafond d’invocation et ajouté
des variantes par opération ; voir la campagne Linux ci-dessous. Cette évolution ne modifie pas
les résultats historiques ci-dessus et ne prouve pas, à elle seule, les deltas entre runtimes.

Ce que cette correction ne dit pas — et **deux mécanismes déjà publiés puis réfutés par la mesure**.
La même lane a d'abord avancé deux explications de l'écart entre régimes, puis les a testées et
écartées elle-même (`c.6506079066` sur #18695, après `c.6505273899`) : ni le `UnrollFactor` par
défaut, ni une fusion d'appels purs par le JIT n'en rendent compte. Même job long avec
`.WithUnrollFactor(1)` (6 runs) : `Serialize` 3,6-4,4 µs contre 4,29 avec le défaut 16, `Matches`
13-18 ns contre 14 — le facteur de déroulage ne change rien. Et un benchmark à argument **variable**
sur 8 jobs de contenu distinct, où le hissage est impossible par construction, ne ralentit rien :
rapport variable/constant de 0,9× sur les trois runtimes. Ce qui subsiste est un **fait**, pas une
explication — deux régimes de mesure du même appel diffèrent d'un facteur 13× à près de 300×, et le
mécanisme en est **ouvert**.

Le [test à N croissant rapporté le 29/10 sur #18695](https://github.com/jsboige/CoursIA/issues/18695#issuecomment-6507128099)
a depuis comparé N = 1, 100 et 10 000 appels par invocation, en job long, sur les trois
runtimes (deux passes entrelacées par runtime). Les médianes rapportées pour `Matches` vont de
13,5 à 22,1 ns/opération et celles de `Serialize` de 3 799 à 4 671 ns/opération ; elles ne
chutent pas lorsque N augmente. Cette expérience appuie la lecture du **coût marginal** du job
long, sans établir la nature du résidu du `ShortRun`. Elle porte sur un seul siège et une seule
journée ; ses journaux et CSV sont restés en scratch hors dépôt. Il s'agit ici d'une reprise du
compte rendu, non d'une reproduction indépendante ni d'un nouveau verdict inter-runtimes.

**Ce que cela change pour les chiffres de ce document.** Ni la direction ni les valeurs ne sont
renversées ; c'est leur **solidité** qui n'est pas celle qui était écrite. Les deux régimes
disponibles se contredisent en signe sur `Serialize` 9→10 (ShortRun apparié −27,4 %, job long
+17,0 % puis +19,8 %) et sur `RoundTrip`. Aucun des quatre écarts inter-versions de cette série
n'est donc **établi** : le drapeau INCONCLUSIF est confirmé, mais pour une raison de plus, et la
re-mesure à programmer ne se réduit pas à « trouver une machine calme ».

La correction du banc relève des sous-modules. `semantic-fleet` a depuis retiré le plafond
d'invocation ; l'effet sur le bruit et sur les deltas reste à apprécier par des campagnes
indépendantes. `UnrollFactor(1)` était **déjà** la valeur du dépôt côté `ShortRun` ; le changer
n'expliquait pas l'écart de régimes, pas plus que la variation des arguments à elle seule.

## Banc 4 actualisé — mesure Linux des runtimes 9, 10 et 11 (09/11)

Sur le gitlink `semantic-fleet` **e675df97c4c511681c98d2d60ccd5fd26ce1b899** de `main`,
le banc existant utilise maintenant un nombre automatique d'invocations et propose les variantes
`Signature_Matches_PerOp` (10 000 appels, arguments tournants) et `JsonSerialize_PerOp`
(1 000 appels). Nous avons exécuté ces deux méthodes et leurs variantes à un appel :
BenchmarkDotNet 0.15.8, `InProcessEmitToolchain`, 5 warmups, 15 itérations ciblant 100 ms,
`UnrollFactor=1`. La compilation Release du projet `benchmarks/SemanticFleet.Benchmarks` a réussi
avec SDK 10.0.403 ; `GITHUB_ACTIONS=true` désactive la cible `dotnet format` du sous-module.
Chaque processus a été lancé avec `dotnet exec --fx-version <version> <dll> --filter
'*Signature_Matches*' '*JsonSerialize*' --exporters json`. Le code et les données du banc ne
sont pas modifiés.

Six paires : les trois premières dans l'ordre 10 puis 9, les trois suivantes 9 puis 10.
Hôte Linux Debian 13, Xeon Platinum 8370C, 5 cœurs logiques disponibles ; runtimes 9.0.22 et
10.0.14, même binaire net9.0. Le tableau donne les moyennes BDN en **ns/opération** ; les
variantes par opération divisent déjà par leur nombre d'appels. Les écarts inter-passes ne sont
pas des intervalles de confiance ; les statistiques BDN et mesures d'itérations effectives sont
conservées dans [`scripts/results/net11-semantic-fleet-2026-11-09/`](../../scripts/results/net11-semantic-fleet-2026-11-09/)
(18 exports JSON, étapes hors `Workload/Actual` omises). La première passe exploratoire, hors
protocole équilibré, n'est pas dans le tableau.

| Paire | Matches 9 / 10 | Matches ×10000 9 / 10 | Serialize 9 / 10 | Serialize ×1000 9 / 10 |
|---:|---:|---:|---:|---:|
| 1 | 37,21 / 28,54 | 37,48 / 28,45 | 6 341 / 11 146 | 6 327 / 8 613 |
| 2 | 36,82 / 32,67 | 38,79 / 37,70 | 6 719 / 9 961 | 15 877 / 15 449 |
| 3 | 48,24 / 26,57 | 39,50 / 29,81 | 6 827 / 10 791 | 6 654 / 9 395 |
| 4 | 37,56 / 36,52 | 51,03 / 28,35 | 7 569 / 9 602 | 6 447 / 8 613 |
| 5 | 40,25 / 36,99 | 48,63 / 29,57 | 8 942 / 9 538 | 8 525 / 9 014 |
| 6 | 37,34 / 30,67 | 47,63 / 30,90 | 7 575 / 9 817 | 6 722 / 9 063 |

Pour `Serialize ×1000`, le delta apparié 10/9 varie de −2,7 % à +41,2 %, avec changement de
signe. Pour `Matches ×10000` il varie de −44,4 % à −2,8 %. Les deux tailles d'invocation ne
sont pas une réplication exacte de l'expérience historique N=1/100/10000 : la variante Matches
fait aussi tourner ses entrées.

Le runtime officiel **11.0.0-rc.3.26522.148** a ensuite été installé à part et le même binaire
net9.0 exécuté six fois avec la même commande et configuration BDN. Ces passes suivent toutes
les passes 9/10 : elles ne sont **pas appariées** à elles et ne permettent pas de séparer un
effet du runtime d'une dérive de la machine dans le temps.

| Passe 11 | Matches | Matches ×10000 | Serialize | Serialize ×1000 |
|---:|---:|---:|---:|---:|
| 1 | 36,65 | 40,25 | 9 334 | 10 264 |
| 2 | 30,52 | 27,59 | 12 681 | 7 366 |
| 3 | 32,32 | 28,52 | 8 620 | 7 471 |
| 4 | 27,20 | 29,92 | 8 280 | 7 644 |
| 5 | 29,28 | 29,85 | 9 150 | 8 777 |
| 6 | 29,43 | 29,45 | 7 342 | 7 584 |

Cette campagne est limitée à une VM partagée ; elle ne contrôle ni la charge de l'hôte ni l'ordre
à l'intérieur d'une paire. La série 11 est tardive et la dispersion est visible : elle ne justifie
pas un gain généralisable. **INCONCLUSIF** reste le verdict inter-runtimes. Une campagne isolée
et entrelacée 9/10/11 reste nécessaire.

## Re-mesure du banc 4 (semantic-fleet) — fenêtre du 30/10 (myia-po-2024)

Objet : les deux drapeaux INCONCLUSIF posés le 02/10 sur le banc 4 — `PromptSignature.Matches`
(« µs, variance > delta ») et `PromptTransform.InterpolateKeys` (« passes dispersées »).
Cette section est la réponse mesurée à ces deux drapeaux : première re-mesure d'un banc
semantic-fleet depuis la session du 02/10, sur un modèle de CPU distinct de celles du 02/10
et du 20/10.

### Protocole (config BDN identique à celle du 02/10, portée par la classe de banc)

| Paramètre | Valeur |
|---|---|
| Machine | `myia-po-2024` — i7-11800H (8 cœurs), X64 RyuJIT AVX-512 — **modèle de CPU distinct** des sessions du 02/10 et du 20/10 (i7-12700H toutes deux) |
| Runtimes | .NET **9.0.22** (9.0.2226.52218) · .NET **10.0.14** (10.0.1426.52326) · .NET **11.0.0-rc.1.26425.128** (affiché `11.0.0`, 11.0.26.42628) — patchs plus récents que les sessions précédentes (9.0.21 / 10.0.13) |
| Preuve du runtime effectif | ligne `[Host] : .NET X.Y.Z` de chacun des 9 rapports BDN, vérifiée fichier par fichier (9.0.22 / 10.0.14 / 11.0.0) ; le rc.1 exige le host autonome `~/.dotnet/dotnet.exe` — le host système n'a pas résolu le rc.1 installé côté user (`DOTNET_ROOT` exporté, deux formes de chemin testées : le résolveur ne liste que `C:\Program Files\dotnet`) |
| Config BDN | celle portée par la classe : `[Config(typeof(InProcessShortConfig))]` = `InProcessEmitToolchain`, ShortRun, 1 invocation / unroll 1, 5 warmup / 15 itérations — **lancée sans flags de job CLI** : les flags (`-i -j short --warmupCount…`) ajoutent un second job et exécutent 8 bancs au lieu de 4 |
| Passes | 3 passes complètes, ordre net9 → net10 → net11 ; **médiane des 3 moyennes** par (banc × runtime) |
| Artefact mesuré | clone depth-1 de `feature/benchmarkdotnet-baseline` @ `6f965904854b` — **SHA distinct** de la session du 02/10 (`ff0dfb47c052`) : le fichier de banc est inchangé entre les deux (diff vide sur `benchmarks/`), mais le **code sous test** a bougé (fichiers touchés : 58 ; +1105/−3801 : retrait du connecteur Oobabooga au profit du connecteur OpenAI-compatible, `MultiConnector.Configuration` concerné) — les valeurs absolues ne sont **pas** comparables d'une session à l'autre |
| Journaux | gist secret [8839f288](https://gist.github.com/jsboige/8839f288b803fbe77e5cfd8282dc1e35) — 9 rapports BDN + `SHA256SUMS.txt` (empreinte SHA-256 du manifeste `6d9b8c88fd9a73a5ca04ce8a631354b7c3127663803f75fd9268245a11ce713d`) |

### Mesures (médiane des 3 moyennes, en µs)

| Benchmark | net9 | net10 | net11 | 9→10 | 9→11 | 10→11 | Alloc 9/10/11 |
|---|---:|---:|---:|---:|---:|---:|---|
| JsonSerializer.Serialize (DTO settings) | 186.9 | 130.9 | 124.6 | **−29.9 %** | **−33.3 %** | −4.9 % | 35.7 / 35.7 / 36.0 KB — identiques à ~1 % près |
| FromRequestSettings (round-trip) | 259.6 | 164.9 | 134.5 | **−36.5 %** | **−48.2 %** | **−18.5 %** | 38.6 / 38.6 / 38.9 KB — identiques à ~1 % près |
| PromptSignature.Matches | 11.59 | 9.96 | 8.34 | **−14.1 %** | **−28.1 %** | **−16.3 %** | 2.11–2.77 KB (net9) ; non rendu par MemoryDiagnoser sur 10/11 (tiret BDN) |
| PromptTransform.InterpolateKeys (regex) | 55.0 | 57.4 | 62.5 | +4.4 % | +13.5 % | +8.8 % | 21.6–23.4 KB — dispersion allocs intra-runtime du même ordre que le delta |

### Lecture (quatre points, sans arrondi favorable)

1. **Les deux lignes JSON confirment — signe et amplitude — ce que la session du 02/10 avait
   établi.** À CPU, patchs de runtime et code sous test tous distincts, les deltas
   reproduisent : −33.3 % / −48.2 % en 9→11 ici contre −51.1 % / −52.0 % au 02/10, et le
   rattrapage porte encore l'essentiel du gain (9→10 : −30 % / −36 %, le 10→11 ajoutant
   −5 % / −18 %). Les allocations identiques au Ko près sur les deux lignes confirment que
   le gain est runtime (JIT/writer), pas un effet d'allocation.
2. **`PromptSignature.Matches` : le drapeau du 02/10 n'est pas levé — la première lecture
   de cette session était trop favorable.** Les trois passes net10 (9.84–10.08 µs, écart
   2.4 %) sont toutes sous les trois passes net9 (10.61–13.69 µs) : sur **cette** session,
   le 9→10 à −14.1 % paraît propre, et le 9→11 atteint −28.1 % en médiane. Mais une
   session à 5 passes sur un autre siège (#23326) mesure sur la même cellule un 9→10 à
   **+22.2 %** et un 9→11 à **+1.7 %**, avec une dispersion inter-passes de 42 à 102 % :
   les deux sessions se contredisent **en signe**. Les valeurs ci-dessus restent des
   mesures ; elles ne portent pas de verdict — voir « Contrôle croisé » ci-dessous.
3. **`PromptTransform.InterpolateKeys` : le drapeau tient.** Les deltas (+4.4 % / +13.5 % /
   +8.8 %) sont inférieurs à la dispersion inter-passes de chaque runtime (19 % / 12 % /
   38 %, écart max−min rapporté à la moyenne des deux bornes) et les ranges se chevauchent
   (49.0–72.4 µs sur l'ensemble des passes). Aucun gain n'est mesuré non plus : regex
   compilée + `string.Format` ne profitent pas des gains writer. Le drapeau
   « passes dispersées » du 02/10 est **confirmé par une seconde machine**, et la session à
   5 passes (#23326) conclut de même (dispersion de 123 % sur net9).
4. **Les valeurs absolues restent incomparables entre sessions** — banc inchangé mais code
   sous test distinct (retrait Oobabooga), CPU distinct, patchs distincts. La règle de
   lecture du 20/10 s'applique : on compare une session à elle-même.

### Contrôle croisé — ma session à 3 passes contre la session à 5 passes (#23326)

Une session indépendante, conduite sur un autre siège et avec **cinq** passes entrelacées au
lieu de trois (#23326, `myia-ai-01:CoursIA-2`), a mesuré les mêmes cellules du même fichier
de banc (`semantic-fleet/benchmarks/SemanticFleet.Benchmarks/PromptSettingsBenchmarks.cs`).
Ce qui est comparable est le **signe et l'amplitude des deltas**, pas les valeurs absolues :
le code sous test et le CPU diffèrent des deux côtés.

| Cellule | Cette session (3 passes, i7-11800H) | Session #23326 (5 passes) | Lecture |
|---|---:|---:|---|
| `JsonSerializer.Serialize` | 9→10 −29.9 % · 9→11 −33.3 % | 9→10 −27.4 % (régime apparié) | **accord** — même signe, même amplitude |
| `PromptSignature.Matches` | 9→10 −14.1 % · 9→11 −28.1 % | 9→10 +22.2 % · 9→11 +1.7 % (dispersion 42–102 %) | **opposition de signe** — cellule bruitée, aucun verdict |
| `PromptTransform.InterpolateKeys` | 9→10 +4.4 % · 9→11 +13.5 % (dispersion 19 / 12 / 38 %) | 9→10 +20.6 % · 9→11 −21.8 % (dispersion 123 %) | les deux sessions concluent « non concluant » |

**Pourquoi ce désaccord n'est pas un désaccord de code.** Le fichier de banc porte une config
de classe, `InProcessShortConfig`, qui épingle `.WithInvocationCount(1)` et
`.WithUnrollFactor(1)` : **une itération vaut une invocation**, soit quelques µs à quelques
dizaines de µs selon la cellule — deux à quatre ordres de grandeur sous la durée que
BenchmarkDotNet recommande, et qu'il réclame lui-même dans ses journaux. À ce grain, le bruit
est **structurel** : une machine au repos ne le réduit pas, et une séparation nette sur trois
passes peut n'être que le hasard d'un échantillon — mes propres journaux en montrent la
trace, avec une dispersion de 46 % sur net11 pour `Matches` (7.14 / 8.34 / 11.47 µs).
#23326 mesure cette même granularité par un second canal (job long, argument variable) sans
non plus établir d'écart inter-versions : c'est cette mesure, et non l'absence de fenêtre
calme, qui fonde le verdict « non concluant ».

Ce que ma session apporte malgré tout, et qui tient : les **deux lignes JSON** sont
reproduites en signe et en amplitude par la session à 5 passes (−27.4 % contre −29.9 % en
9→10), et les allocations y sont identiques au Ko près des deux côtés — le gain y est runtime,
pas allocation.

### Ce que cette re-mesure règle, et ce qu'elle ne règle pas

| Point | État après le 30/10 |
|---|---|
| `PromptSignature.Matches` : drapeau INCONCLUSIF du 02/10 | **maintenu** — la lecture « levé en tendance » portée par la première version de cette section est **infirmée** par une session à 5 passes qui mesure le signe opposé sur 9→10 (+22.2 %) avec une dispersion de 42 à 102 % (#23326) ; cause de l'écart au 02/10 non tracée (code sous test distinct) |
| `PromptTransform.InterpolateKeys` : drapeau INCONCLUSIF du 02/10 | **maintenu, confirmé sur seconde machine** — dispersion inter-passes ≥ deltas sur les trois runtimes, aucun gain mesuré |
| Lignes JSON (Serialize / round-trip) | **reproduites en signe et amplitude** sur i7-11800H à patchs plus récents — le rattrapage 9→10 porte l'essentiel, allocations identiques au Ko près |
| `RandomSearch_Sphere10D_50k` (MGS) | **non re-mesuré par cette session** — la session à 5 passes (#23326) l'a mesuré (9→11 à −0.5 % pour une dispersion de 28 à 38 %) et le laisse **non concluant** ; le banc reste donc ouvert |
## Le régime à N croissant — le test nommé « non fait », mesuré (2026-11-10, `myia-ai-01:CoursIA-2`)

La section ci-dessus (« Le protocole du banc, seconde cause ») énonce deux choses : le pin
`.WithInvocationCount(1).WithUnrollFactor(1)` est en place dans le fichier de banc du
sous-module, et le test qui départagerait « coût fixe par itération » de « coût réel » —
`OperationsPerInvoke` croissant sur le même appel — **n'est pas fait**. Les deux affirmations
ont été confrontées à l'amont le 2026-11-10 : la première est **périmée**, la seconde a été
**faite entre-temps**, et le test a été rejoué ici pour fixer l'échelle et le mécanisme.

### Ce que l'amont a fait entre-temps — le pin a été supersédé

| Fait | Source | Date |
|---|---|---|
| Le pin `WithInvocationCount(1)` est **retiré** ; l'invocation count redevient automatique, `IterationTime(100 ms)` est ajouté, `UnrollFactor(1)` est **conservé** | PR amont **#108** (`d53f533`), fusionnée dans `stable-from-v0343` | 2026-10-29T21:15Z |
| Quatre bancs « per-op » sont ajoutés : `OperationsPerInvoke` (1 000 / 10 000) sur **arguments tournants consommés** | PR amont **#108** | 2026-10-29T21:15Z |
| `benchmarks/BASELINE-net9.0.md` est **régénérée** sous l'instrument corrigé ; elle publie la réponse : « le coût/op de référence est celui des lignes per-op, **stable de N=1 à N=10 000** », et le pin sur-estimait le coût/op d'un **×11 à ×152** selon le chemin | PR amont **#109** (`6e642ae`) | 2026-10-31T16:57Z |

Le **gitlink épinglé** dans CoursIA suit `stable-from-v0343` (`.gitmodules`) et pointe
`e675df9`, tête de cette branche — il **contient** donc `d53f533` et l'instrument corrigé
(vérifié : `git ls-tree origin/main …/semantic-fleet` → `e675df9` ;
`git merge-base --is-ancestor d53f533 origin/stable-from-v0343` → vrai).

Mais les sessions de ce document ont mesuré **autre chose** : la session du 30/10
(`myia-po-2024`) et celle du 11/10 (`myia-ai-01`) ont cloné
`feature/benchmarkdotnet-baseline` @ `6f965904854b` — branche **qui n'est pas un descendant
de `d53f533`** (`git merge-base --is-ancestor` → faux), où le fichier de banc **porte encore**
le pin (lignes 135-136 : `.WithInvocationCount(1)` / `.WithUnrollFactor(1)`).

Conséquence, à lire telle quelle : **l'artefact mesuré par les sessions de ce document n'est
pas l'artefact épinglé.** L'état décrit par la section « seconde cause » (le pin en place)
n'existe plus dans le sous-module épinglé — il existe encore dans la branche employée par
les sessions. La phrase « le correctif … relève de la coordination `ai-01` et n'est pas ouvert
par cette PR » ne reste donc vraie que pour **la moitié `MetaGeneticSharp`** : son
`OptimizerBenchmarks.cs` épingle lui aussi `InvocationCount(1)`, et n'a pas été repris par
l'amont.

### Le test, cette fois, mesuré sur ce siège

Protocole — **une seule compilation** (`net9.0`) du fichier de banc `6f96590`, trois runtimes
joués par `dotnet exec --fx-version`, **cinq passes entrelacées**, et une innovation de
protocole par rapport aux sessions précédentes : **une classe de banc par processus BDN**
(les sessions antérieures jouaient les cinq classes dans le même processus).

| Paramètre | Valeur |
|---|---|
| Artefact | `feature/benchmarkdotnet-baseline` @ `6f965904854b` (le même fichier de banc que les sessions du 30/10 et du 11/10) |
| Instrumentation | copie **verbatim** du `Setup` et des quatre méthodes de `PromptSettingsBenchmarks`, plus une échelle de comptage |
| Régimes | `InvocationCount` = 1 / 100 / 10 000 (ShortRun, 5 warmup / 15 itérations / unroll 1), et un job long (10 warmup / 100 itérations / 1 invocation) |
| Runtimes | net9.0.22 · net10.0.14 · net11.0.0 (rc.3.26522.148) — en-tête `// Runtime=` relevé sur les 60 journaux |
| Config BDN | **0.14.0** (version du `csproj` de cette branche), `InProcessEmitToolchain` |
| Passes | 5, entrelacées, **médiane des 5 moyennes** par (classe × runtime × cellule) |
| Charge d'hôte | relevée avant chaque run : 63 % à 88 % de CPU, 1 065 à 1 073 processus résidents |

**Mesures — coût par invocation, en ms (médiane des 5 moyennes)**

| Runtime | Cellule | N = 1 | N = 100 | N = 10 000 | Ratio N=10 000 / N=1 |
|---|---|---:|---:|---:|---:|
| net9 | `FromRequestSettings` (round-trip) | 0,08816 | 0,03537 | 0,00742 | 0,084 |
| net9 | `JsonSerializer.Serialize` (persistance) | 0,07019 | 0,02911 | 0,00314 | 0,045 |
| net9 | `PromptSignature.Matches` | 0,00533 | 0,00011 | 0,00009 | 0,017 |
| net9 | `PromptTransform.InterpolateKeys` | 0,02395 | 0,00484 | 0,00219 | 0,091 |
| net10 | `FromRequestSettings` | 0,05732 | 0,01788 | 0,00740 | 0,129 |
| net10 | `JsonSerializer.Serialize` | 0,03113 | 0,01348 | 0,00415 | 0,133 |
| net10 | `PromptSignature.Matches` | 0,00310 | 0,00012 | 0,00008 | 0,026 |
| net10 | `PromptTransform.InterpolateKeys` | 0,01851 | 0,00374 | 0,00208 | 0,112 |
| net11 | `FromRequestSettings` | 0,06026 | 0,01296 | 0,00758 | 0,126 |
| net11 | `JsonSerializer.Serialize` | 0,04222 | 0,01201 | 0,00333 | 0,079 |
| net11 | `PromptSignature.Matches` | 0,00339 | 0,00011 | 0,00009 | 0,025 |
| net11 | `PromptTransform.InterpolateKeys` | 0,02910 | 0,00262 | 0,00244 | 0,084 |

Job long (100 itérations × 1 invocation), net9 : `FromRequestSettings` 0,09181 ·
`JsonSerializer.Serialize` 0,06467 · `PromptSignature.Matches` 0,00286 ·
`PromptTransform.InterpolateKeys` 0,01460 ms.

### Lecture (sept points, sans arrondi favorable)

1. **Le coût par invocation décroît quand N croît, sur les trois runtimes et sur les quatre
   cellules.** Le rapport N=10 000 / N=1 tombe entre 0,017 et 0,133 : le régime N=1 ne
   mesure **pas** la même chose que le régime N=10 000. C'est la réponse à la question que la
   section « seconde cause » laissait ouverte : **le coût mesuré à N=1 n'est pas le coût réel
   par opération.**
2. **Le job long ne converge pas vers le plateau.** À 110 appels au total (10 warmup + 100
   itérations × 1 invocation), le job long mesure `FromRequestSettings` à 0,09181 ms sur
   net9 — c'est-à-dire **au niveau du régime N=1** (0,08816), et non du plateau (0,00742).
   L'amortissement est donc lié au **nombre d'invocations dans une même région mesurée**, pas
   au nombre total d'appels : c'est le côté « **coût fixe par itération** » de l'alternative.
3. **Le facteur d'inflation se retrouve indépendamment de l'amont.** Rapport N=1 / N=10 000
   mesuré ici : ×11,9 (`FromRequestSettings`), ×22,4 (`Serialize`), ×59 (`Matches`), ×10,9
   (`InterpolateKeys`). Facteurs publiés par l'amont (baseline régénérée #109) : ×14-×15,
   ×22-×23, ×144-×152, ×11-×13. Trois des quatre cellules coïncident à ±15 % près ; le quatrième
   (`Matches`, ×59 contre ×144-×152) est du même ordre de grandeur, la cellule étant la moins
   stable. La mesure de l'amont et celle-ci se corroborent.
4. **Une classe de banc par processus supprime une contamination intra-processus.** Dans la
   grille où les cinq classes jouaient le même processus, la classe du dépôt et sa copie
   verbatim divergeaient de 1,2 à 3×. En processus séparés, elles concordent : sur net9,
   `FromRequestSettings` vaut 0,10209 ms pour la classe du dépôt et 0,08816 ms pour la copie —
   un écart de 14 %, **à l'intérieur** de la dispersion inter-passes (43 % à 72 %). L'écart
   inexpliqué constaté plus tôt était donc un **artefact de protocole** (cinq classes dans un
   même processus), non une différence entre les deux fichiers.
5. **Sous le pin, deux cellules paraissent séparables entre net9 et net11** —
   `FromRequestSettings` −43,4 % et `JsonSerializer.Serialize` −48,7 %, intervalles disjoints
   au sens du critère du document. Ces valeurs appartiennent au **régime gonflé** (point 1) et
   s'accompagnent d'une dispersion de 43 % à 82 % : elles **ne constituent pas** un verdict
   par opération. Elles disent que le protocole épinglé amplifie aussi les écarts.
6. **La correction amont ne change pas ce qui est établi.** Les deux drapeaux INCONCLUSIF du
   banc 4 restent posés ; aucun gain inter-runtime n'est établi par cette session ; la
   question de fond (l'axe .NET 10 / .NET 11) reste ouverte sur les mêmes cellules.
7. **Ce qui n'est pas mesuré ici** : le mécanisme de l'amortissement. La courbe en N
   établit *que* le coût décroît et *à partir de quoi* ; elle n'établit pas *pourquoi*.
   Le contrôle de mécanisme est la sous-section suivante : il établit que **les deux
   mécanismes sont réels et additifs** — un coût fixe par région mesurée (terme `c/N`) et
   la promotion tier-1 du JIT absente aux petits N.

### Contrôle de mécanisme — le tiering du JIT (2026-11-10, suite)

La lecture ci-dessus établit *que* le coût par invocation décroît quand N croît ; elle
n'établit pas *pourquoi*. Deux mécanismes restent candidats, et ils ne se prédisent pas de
la même façon :

- **H1 — coût fixe par région mesurée** (le harnais) : la valeur mesurée suit
  `valeur(N) = w + c/N`, avec `w` le coût réel par opération et `c` un coût fixe amorti sur
  les invocations d'une même région mesurée. Le régime N=1 mesure `w + c`, le régime
  N ≥ 1 000 mesure `w`. **Prédiction** : la courbe doit s'ajuster à ce modèle, et l'écart
  N=1 / plateau doit être **le même** quelle que soit la qualité du code compilé.
- **H2 — tiering du JIT** : la méthode de banc n'est pas assez appelée pour être promue en
  tier-1, elle tourne donc en code **non optimisé** ; l'inflation est alors un facteur
  multiplicatif qui dépend de la cellule, pas de N. **Prédiction** : désactiver le tiering
  (`DOTNET_TieredCompilation=0`) doit faire chuter la valeur à N=1 sans changer la forme
  de la courbe.

**Protocole.** La grille précédente est rejouée **à un seul facteur changé** :
`DOTNET_TieredCompilation=0` dans l'environnement du processus (`dotnet exec`). Tout le
reste est identique : une seule compilation `net9.0`, les mêmes quatre classes, les trois
runtimes, cinq passes entrelacées, une classe par processus (60 runs, `rc=0` sur les 60).
Réserve explicite : ce drapeau désactive **aussi** le PGO dynamique — le plateau n'est donc
pas comparable d'une grille à l'autre (il bouge de ×0,62 à ×2,25 selon la cellule) ; seules
les comparaisons **intra-grille** sont utilisées ci-dessous.

**Résultat — le modèle `w + c/N` s'ajuste à la grille tiering OFF.**

| Runtime | Cellule | N=1 | N=100 | N=10 000 | `w` (plateau) | `c` (fixe) | Modèle à N=100 | Mesuré à N=100 | Part du tiering dans l'inflation à N=1 |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| net9 | `FromRequestSettings` | 0,02578 | 0,00724 | 0,00738 | 0,00724 | 0,01854 | 0,00742 | 0,00724 | **77 %** |
| net9 | `JsonSerializer.Serialize` | 0,01518 | 0,00608 | 0,00504 | 0,00504 | 0,01013 | 0,00514 | 0,00608 | **84 %** |
| net9 | `PromptSignature.Matches` | 0,00221 | 0,00005 | 0,00004 | 0,00004 | 0,00218 | 0,00006 | 0,00005 | **59 %** |
| net9 | `PromptTransform.InterpolateKeys` | 0,01541 | 0,00215 | 0,00170 | 0,00170 | 0,01371 | 0,00184 | 0,00215 | **38 %** |
| net10 | `FromRequestSettings` | 0,03257 | 0,00770 | 0,01222 | 0,00770 | 0,02487 | 0,00795 | 0,00770 | 50 % |
| net11 | `FromRequestSettings` | 0,04863 | 0,00953 | 0,01244 | 0,00953 | 0,03909 | 0,00993 | 0,00953 | 23 % |

(valeurs en ms ; `w` = minimum des mesures à N=100 et N=10 000 ; « part du tiering » =
écart entre la valeur à N=1 tiering ON et tiering OFF, rapporté à l'inflation totale
`valeur(N=1) − w`)

**Lecture.**

1. **H1 est confirmée, et sa forme est mesurée.** Tiering désactivé, la valeur suit
   `w + c/N` : le modèle prédit la valeur à N=100 à 3 % près sur `FromRequestSettings`
   (0,00742 prédit contre 0,00724 mesuré) et à moins de 20 % près sur les trois autres
   cellules — l'écart restant est du même ordre que la dispersion inter-passes de la grille
   OFF (38 % à 105 %). Le « coût fixe par itération » du document n'est donc pas une
   hypothèse : c'est un terme `c/N` mesuré, de 1,6 µs (`Matches`) à 39 µs
   (`FromRequestSettings`, net11) selon la cellule.
2. **H2 est confirmée elle aussi, et elle est d'amplitude variable.** Désactiver le tiering
   fait chuter la valeur à N=1 d'un facteur 1,6 à 4,6 selon la cellule sur net9
   (`Serialize` ×4,6, `FromRequestSettings` ×3,4, `Matches` ×2,4, `InterpolateKeys` ×1,6),
   et laisse le plateau inchangé à 0,5 % près sur `FromRequestSettings` (0,00738 contre
   0,00742). La méthode de banc, appelée 15 fois par itération de mesure, n'atteint jamais
   le seuil de promotion du JIT : elle tourne en code non optimisé, et c'est là que se
   trouve la plus grande part de l'inflation sur les cellules JSON (77 % et 84 % sur net9).
3. **Aucun des deux mécanismes ne suffit seul.** Tiering désactivé, la valeur à N=1 reste
   3× (`FromRequestSettings`, net9) à 55× (`Matches`) au-dessus du plateau : le coût fixe
   du harnais subsiste intégralement. Tiering activé, la valeur à N=1 reste 4× à 12× au-dessus
   de ce que le modèle `w + c/N` prédit pour cette même grille : le tiering s'y ajoute.
   **Les deux sont réels et additifs.**
4. **Ce que cela tranche.** L'alternative ouverte par le document — « coût fixe par itération »
   contre « coût réel » — n'est pas une alternative : la mesure montre que le régime N=1
   mesure **les deux à la fois**, et que le régime à N croissant les sépare. Le « coût réel »
   par opération est `w` — mesuré à 0,0073 ms sur `FromRequestSettings` en net9 — et le
   régime épinglé du dépôt le **sur-estime d'un facteur 3 à 55**, dont la part due au tiering
   du JIT varie de 10 % à 84 % selon la cellule et le runtime.
5. **Ce qui n'est pas établi.** La part du tiering est mesurée par un facteur unique
   (`DOTNET_TieredCompilation=0`), qui désactive simultanément le PGO dynamique : la
   décomposition « tiering / PGO » n'est pas isolée. La dispersion de la grille OFF
   (38 % à 105 %) laisse une marge réelle sur les petites cellules. Le modèle `w + c/N` est
   ajusté sur trois points par cellule : il est **indicatif**, pas démontré.

### Provenance et reproduction

Les 15 rapports BDN de la grille de contrôle (tiering ON) et les 60 de la grille tiering
OFF sont conservés hors dépôt (`D:/CoursIA-2-wt/sf-bench/art2-*` et `art3-*`, journaux
`bench-logs2/` et `bench-logs3/`). Reproduction :

```bash
# grille tiering ON (5 classes x 3 runtimes x 5 passes)
bash D:/CoursIA-2-wt/run-sf-bench-perclass.sh

# grille tiering OFF (meme protocole, un seul facteur change)
DOTNET_TieredCompilation=0 bash D:/CoursIA-2-wt/run-sf-tiering.sh

# lecture (mediane des 5 moyennes, intervalles, dispersions, ajustement w + c/N)
python D:/CoursIA-2-wt/compute-sf-ops3.py art2
python D:/CoursIA-2-wt/compute-sf-ops3.py art3
```

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
- **Traces carnets (volet wall-clock) — re-mesurées et préservées (#18878, 02/10 soir, machine calme)** : 4 artefacts exécutés versés dans le même gist [d434d4dc](https://gist.github.com/jsboige/d434d4dc48db03a37bab05259921d4be). Chaque artefact porte une **cellule probe** qui imprime le runtime effectif (`.NET 10.0.12` / `.NET 11.0.0-rc.1.26425.128` — les versions exactes des Conditions), toutes ses cellules code exécutées (ML-5 : **17/17** ; Infer-2 : **28/28**) et **0 erreur**. Empreintes SHA-256 : ML-5 net10 `8bf83441ef846b7e` · net11 `acf51fa1c1e4ff81` · Infer-2 net10 `e755acaadb67fe1c` · net11 `fb832217406e6bfa` (complets dans `SHA256SUMS-notebooks.txt` du gist). Les identifiants d'artefact `ML-5` / `Infer-2` sont ceux du dépôt du 02/10, **antérieur** aux renommages de fichiers du 10/10 et du 19/10 : ils désignent les mêmes deux carnets que `ML-05-TimeSeries-CSharp` et `Infer-02-Gaussian-Mixtures` dans le tableau ci-dessus.

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

## Contrôle du banc 1 (MetaGeneticSharp) — le régime `InvocationCount(1)` mesure un mélange, et le classement des runtimes en dépend (myia-ai-01:CoursIA-2, 10/11)

### Pourquoi ce contrôle

La section « Le régime à N croissant » établit que, sur le banc `prompt-settings` du
banc 4, le régime épinglé `InvocationCount(1)` **sur-estime** le coût par opération d'un
facteur **×3 à ×55**. Deux causes y sont invoquées : un coût fixe de la région mesurée
amortissable en `c/N`, et le *tiering* du JIT.

Ce contrôle demande si ce facteur **se généralise** aux bancs dont le coût par appel
est de l'ordre de la **milliseconde** — donc au banc 1 (MetaGeneticSharp), dont les
appels coûtent 2 à 8,5 ms (10 000 à 50 000 évaluations de fitness), soit mille fois
plus que ceux du banc 4.

### Protocole

Une compilation unique, **une classe de banc par processus BDN**, 3 passes entrelacées
par configuration, comparaisons **appariées par passe** (les deux membres d'une paire
sont mesurés à quelques secondes d'intervalle). Runtimes .NET 9.0.22, 10.0.14 et
11.0.0-rc.3.26522.148 via `dotnet exec --fx-version` ; BDN 0.15.8 ; hôte Windows 11 Pro
**partagé, charge processeur 62 % à 86 % pendant la session** (mesurée) — d'où le choix
des rapports appariés et de la médiane, et l'impossibilité d'utiliser les valeurs
absolues comme référence.

Trois grilles : (A) `DOTNET_TieredCompilation=1` contre `=0` sur les trois runtimes ;
(B) une échelle de comptage `InvocationCount = N` pour N = 1 / 8 / 64, sur les quatre
charges du banc de référence ; (C) cinq désactivations partielles du tiering pour
tenter d'isoler le mécanisme.

### Résultat 1 — le facteur ×3 à ×55 ne se généralise pas

Coût **par appel** (médiane de 3 passes, en ms), échelle N :

| Charge | N = 1 | N = 8 | N = 64 |
| --- | ---: | ---: | ---: |
| `RandomSearch_Ackley2D_10k` | 2,030 | 1,892 | **0,845** |
| `RandomSearch_Sphere10D_50k` | 16,696 | 9,185 | **10,218** |
| `CenterBias_Ackley_5k` | 1,798 | 1,635 | **1,485** |
| `CenterBias_Suite4_5k` | 8,683 | 6,735 | **6,691** |

Entre N = 8 et N = 64, le coût par appel **bouge encore** : de **−55 %**
(`RandomSearch_Ackley2D_10k` : 1,892 → 0,845) à **+11 %**
(`RandomSearch_Sphere10D_50k` : 9,185 → 10,218) selon la charge. Il n'y a donc **pas**
de plateau, mais l'amplitude résiduelle est faible : le rapport N = 1 / N = 64 vaut
**×1,21 à ×2,40** selon la charge — **très loin** du ×3 à ×55.

### Résultat 2 — de quoi le surcoût est fait

Ce n'est pas un coût de harnais : c'est du **code non optimisé**. Le **profil par
itération** (lignes `WorkloadResult` du journal BDN — absentes du rapport final) montre
une **marche**, le passage du tier0 au tier1, **à l'intérieur** de la fenêtre mesurée :

```text
itération  1..9 :  27,3  29,4  28,9  26,5  27,8  30,4  22,6   9,4   9,1
itération 10..15:   8,9   8,8   9,1   9,1   9,2   7,6
```

La marche est **reproductible** (itérations 8, 7 et 8 sur les trois passes) et les
moyennes de passe s'étalent de 14,578 à 17,614 ms (**21 %**) alors que la charge est
déterministe (seed 7). La variabilité ne vient donc pas de la charge mais de la
**position de la marche** : la moyenne du régime N = 1 est un **mélange**, pas un coût.

Corollaire pour la campagne : **une baseline mesurée en `InvocationCount(1)` n'est pas
un coût établi**, et l'écart au coût établi dépend de la durée de la charge — donc de
la charge elle-même.

### Résultat 3 — le classement des runtimes s'inverse

Charge `RandomSearch_Ackley2D_10k`, .NET 9 / 10 / 11, médiane de 3 passes (ms) :

| Runtime | `default` (régime des baselines) | `off` (tiering désactivé) | `off` / `default` |
| --- | ---: | ---: | ---: |
| .NET 9.0.22 | 1,982 | 1,305 | 0,658 |
| .NET 10.0.14 | 1,956 | **1,052** | 0,538 |
| .NET 11.0.0-rc.3 | 2,261 | 1,185 | **0,524** |

Dans le régime `default` — celui des baselines publiées — **.NET 11 est le plus lent**
des trois. Dans le régime `off`, **.NET 11 est plus rapide que .NET 9** (1,185 contre
1,305, soit 9 %).

L'inversion tient sur les **rapports appariés par passe** : 9 paires sur 9 sont
inférieures à 1, de 0,47 à 0,74, sur les trois runtimes.

La part de tiering **diffère selon le runtime** (×0,52 pour .NET 11 contre ×0,66 pour
.NET 9) : c'est le runtime le plus récent dont la mesure est la plus contaminée.

### Ce que ce contrôle règle, et ce qu'il ne règle pas

**Il règle :**

1. Le facteur ×3 à ×55 du banc `prompt-settings` **ne se généralise pas** aux bancs de
   coût milliseconde : ici ×1,21 à ×2,40 (N = 1 / N = 64) ou ×1,52 à ×1,91
   (`default` / `off`, calculé sur le tableau du résultat 3 : 1,982 / 1,305,
   1,956 / 1,052 et 2,261 / 1,185).
2. Le surcoût du régime épinglé n'est **pas** un coût de harnais amortissable : c'est
   la part de **tier0** restant dans la fenêtre mesurée, et elle se lit **dans le
   profil par itération**, pas dans le rapport BDN.
3. Sur la charge la plus courte du banc 1, **le classement des runtimes dépend du
   régime de tiering**. Toute conclusion de la campagne appuyée sur l'ordre 9 → 10 → 11
   de cette charge doit donc être formulée avec cette réserve.

**Il ne règle pas :**

1. **Le mécanisme exact.** Cinq désactivations partielles (seuil de promotion à 10 et
   à 0, délai de comptage à 0, PGO dynamique coupé, et leurs combinaisons) ne
   reproduisent **pas** l'accélération de la configuration « tiering entièrement
   désactivé ». Ce qui reste ouvert.
2. **Le prédicteur du rapport entre charges** : ×2,40 pour `Ackley2D` contre ×1,21 pour
   `CenterBias_Ackley`, deux charges de durée quasi identique (2,0 et 1,8 ms par
   itération).
3. **La généralisation aux autres bancs.** L'inversion du classement (résultat 3) est
   démontrée sur **une charge sur quatre** : `CenterBias_Ackley` garde le même ordre
   dans les deux régimes, `CenterBias_Suite4` ne montre aucun effet, et
   `Sphere10D_50k` est dominé par le bruit (dispersion jusqu'à 87 %, moyenne bimodale
   du fait de la marche). Le banc 4 (`semantic-fleet`, coûts en µs) **n'a pas été
   recontrôlé** dans ce protocole.
4. **La comparabilité avec les tableaux de ce document.** Les mesures ci-dessus sont
   du 10/11, sur un hôte partagé, en BDN 0.15.8 ; les tableaux « Banc 1 » et « Banc 4 »
   sont du 02/10, sur un portable, en BDN 0.14.0. **Les valeurs absolues ne sont pas
   comparables** — seuls les rapports intra-session le sont.

### Portée pour la campagne

- Les **valeurs absolues** des baselines `InvocationCount(1)` du dépôt contiennent une
  part de tier0 **non quantifiée et dépendante de la charge**. Toute baseline qui
  sert de point de comparaison devrait porter cette réserve.
- Les **deltas inter-runtimes** mesurés sur ces bancs héritent d'une part de tiering
  **qui diffère d'un runtime à l'autre** (ici ×0,52 à ×0,66). Un delta peut donc être
  un artefact de régime plutôt qu'un gain de runtime.
- Le **profil par itération** (journal BDN) est le seul artefact qui rende le mélange
  visible : le rapport final ne le montre pas. C'est le premier réflexe à prendre
  pour un banc qui doit trancher un delta < 20 %.

### Origine et reproduction

- PR amont : `jsboige/MetaGeneticSharp#74` — instrument d'échelle, note de mesure
  complète et **vérificateur indépendant** (il re-derive chaque chiffre cité depuis
  les artefacts BDN et le confronte à la prose ; 63/63 concordants). Il a attrapé une
  erreur réelle pendant la rédaction (un tableau de rapports appariés calculé en
  appariant deux séries **triées** au lieu des paires réelles).
- Artefacts bruts (journaux BDN, rapports CSV et HTML) : **hors dépôt**, volumineux ;
  le protocole et le vérificateur les régénèrent.

