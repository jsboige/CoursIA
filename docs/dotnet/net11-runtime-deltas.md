# .NET 9 → 10 → 11 — Deltas runtime mesurés sur les bancs et carnets types du dépôt

> **Issue** : #18771 (P1, mesure centrale de l'EPIC #18695). Prérequis satisfaits : pin
> dotnet-interactive canonique 1.0.712001 (#18766, décision ai-01 du 02/10), 3 carnets types
> sélectionnés (#18769), 5 bancs baseline (#18770).
> **Chiffres attendus** : `net11-toub-digest.md` (article Toub, baseline .NET 10.0.12 —
> fichier en approche par la PR #18772, même dossier cible). **Chiffres mesurés ci-dessous** :
> baseline .NET 9.0.20 / 10.0.12 /
> 11.0.0-rc.1.26425.128 sur notre matériel.
> **Mesure** : myia-po-2026, 2026-10-02.

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
| Pipeline_EvilRegex | 1930.8 | 2053.8 | 2462.6 | +6.4 % | +27.5 % | +19.9 % | 2128.37 KB (identique) — StdDev in-passe ≈ mean (1738 de médiane sur 2685 de moyenne en net11) : **INCONCLUSIF**, à re-mesurer fenêtre CI calme |

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
500 règles (+3,7 %) : à re-mesurer fenêtre calme avant de le considérer comme une régression.



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
| ML-5-TimeSeries | 16.7 s | 16.2 s | −3 % | **27 OK / 0 erreur des deux côtés** — compat .NET 11 prouvée, delta < bruit wall-clock (n=1) : **nul mesuré** |
| Infer-2-Gaussian-Mixtures | 24.4 s | 23.5 s | −3.7 % | idem — compat prouvée, pas de régression |

**Re-mesure calme du 02/10 soir (#18878, artefacts préservés au gist)** : ML-5-TimeSeries 13,0 s (net10) → **9,4 s** (net11) ; Infer-2-Gaussian-Mixtures 21,0 s → 21,2 s. Les deux séries (charge CI du matin : −3 %/−3,7 % ; calme du soir : −28 %/+1 %) divergent plus entre elles qu'entre runtimes — la dispersion inter-séances domine, ce qui **confirme** la lecture ci-dessous : le wall-clock carnet mesure le lancement kernel + Roslyn, pas le delta runtime. Ce que la re-mesure prouve et préserve : compatibilité complète sous 11.0.0-rc.1 (17/17 et 28/28 cellules code, 0 erreur, runtime imprimé dans l'artefact).

Lecture honnête : le wall-clock carnet est dominé par le démarrage kernel + Roslyn ; un gain
runtime de −10 % sur les seules cellules de calcul serait invisible ici. Les bancs ci-dessus
restent l'instrument de mesure ; les carnets prouvent la **non-régression et la compatibilité**
de la chaîne notebook complète sous .NET 11 RC (kernel, Roslyn scripting, ML.NET, Infer.NET).

## Verdicts par axe (gain net mesuré vs chiffre attendu du digest)

| Axe | Attendu (digest, baseline .NET 10) | Mesuré 10→11 | Mesuré 9→10 (rattrapage) | Verdict |
|---|---|---|---|---|
| JSON serialize/round-trip (semantic-fleet) | Writer escape-heavy 0,26 (×3,9) | **−14,6 % / −21,6 %** | −42,8 % / −38,8 % | **conforme en signe, inférieur en amplitude** — notre DTO n'est pas escape-heavy pur ; le gros morceau est le rattrapage 9→10 |
| DateTime.Now + timestamps (Argumentum) | **0,45 (×2,2)** | **−41,0 %** | −26,6 % | **conforme en signe, amplitude relative −25 %** (×1,7 mesuré vs ×2,2 article, sous charge CI) — l'axe le mieux vérifié du digest sur nos charges |
| Rule parsing multilingue (Argumentum) | (String.Split via agrégats, hors ratios article) | −13,2 % / −15,7 % | +3,7 % / +25 % (anomalie non confirmée, cf banc 5) | gain 11 réel sur le parsing de règles ; le 9→10 de la variante 50 règles à re-mesurer fenêtre calme |
| Collections/LINQ (MGS) | FindAll 0,30 · SequenceEqual ×7,7 | ~0 à +17 % (GC-sensible) | −6 à −26 % | **non couvert** (nos bancs n'exercent pas ces API précises) ; côté 11 : nul/inconclusif |
| Charge native-dominée (Z3.Linq) | (rien de spécifique promis) | −0,3 à −6,7 % | −5 à −10 % | **rattrapage 10 réel (marshaling), gain 11 nul** |
| Allocation-heavy pipeline (Automata) | (Stores covariants 0,56 etc.) | +4,1 % / INCONCLUSIF EvilRegex | −10,9 % | **rattrapage 10 réel ; 11 non prouvé sur cette charge** (allocs identiques au Ko près — cohérent : nos pipelines allouent par design, pas par défaut runtime) |
| Kernel notebooks | — | — | — | **le canon 1.0.712001 exige déjà ≥ .NET 10** : le dépôt ne peut pas rester « runtime 9 » pour les carnets même sans migration |

## Synthèse pour la décision P2 (LTS vs GA, escalade user)

1. **Le vrai levier mesuré est le saut .NET 9 → 10** : −5 à −43 % selon la charge (JSON,
   DateTime.Now et marshaling en tête). C'est aussi ce que le kernel canon impose déjà.
2. **.NET 11 RC ajoute, sur nos charges réelles, deux gains mesurés** : JSON (−15 à −22 %
   10→11) et DateTime.Now/timestamps (**−41 %** 10→11, l'axe le mieux vérifié du digest) ;
   parsing de règles Argumentum −13/−16 % ; les autres axes sont plats, non couverts ou
   inconvissables sous charge CI.
3. Les axes « vedettes » du digest (×3,9 escape, ×7,7 SequenceEqual, BigInteger ×2) ne sont
   pas exercés par nos charges : **si l'EPIC veut les départager, il faut des bancs ciblés
   API** (extension naturelle de #18770), pas nos charges représentatives.
4. Conditions : RC1, machine partagée avec CI — les deltas < ±10 % sur ces bancs ne sont pas
   séparables du bruit ; à re-mesurer fenêtre calme avant toute décision définitive.

## Provenance des journaux

- **Logs BDN — 45 = 5 bancs × 3 passes × 3 runtimes** : gist [d434d4dc](https://gist.github.com/jsboige/d434d4dc48db03a37bab05259921d4be) (secret, accessible par lien), manifeste `SHA256SUMS.txt` inclus, empreinte SHA-256 du manifeste `47951d824eccec4e0974142405734623c332b2ae79dd74bd9a234bbc3514c052`. Chaque log porte son header `// Runtime=.NET X.Y.Z` (9.0.20 / 10.0.12 / 11.0.0) ; l'interleave des passes se lit sur les timestamps consécutifs — ex. MGS : passe 1 à 12:23:05/08/11, passe 2 à 12:24:18/21/23, passe 3 à 12:24:48/51/53.
- **SHA exacts des bancs mesurés** (branche `feature/benchmarkdotnet-baseline`, clones depth-1) : MetaGeneticSharp `365a4fb2384f` · Z3.Linq `b804c30859e9` · Automata `abaabd1b6518` · semantic-fleet `ff0dfb47c052` · Argumentum `709e6d05f6c2`.
- **Traces carnets (volet wall-clock) — re-mesurées et préservées (#18878, 02/10 soir, machine calme)** : 4 artefacts exécutés versés dans le même gist [d434d4dc](https://gist.github.com/jsboige/d434d4dc48db03a37bab05259921d4be). Chaque artefact porte une **cellule probe** qui imprime le runtime effectif (`.NET 10.0.12` / `.NET 11.0.0-rc.1.26425.128` — les versions exactes des Conditions), toutes ses cellules code exécutées (ML-5 : **17/17** ; Infer-2 : **28/28**) et **0 erreur**. Empreintes SHA-256 : ML-5 net10 `8bf83441ef846b7e` · net11 `acf51fa1c1e4ff81` · Infer-2 net10 `e755acaadb67fe1c` · net11 `fb832217406e6bfa` (complets dans `SHA256SUMS-notebooks.txt` du gist).

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
