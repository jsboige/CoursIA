# .NET 11 — Digest de performance (article Toub, 2e moitié récupérée)

> **Source** : Stephen Toub, « Performance Improvements in .NET 11 », .NET Blog, 2026-09-15 —
> <https://devblogs.microsoft.com/dotnet/performance-improvements-in-net-11/>
> **EPIC** : #18695 (mesure progressive des gains runtime async + numérique avant saut hors LTS).
> **Tranche** : récupération des sections inaccessibles au WebFetch classique (plafonné ~50 %) via
> canal alternatif (lecteur SearXNG, constaté intégral le 2026-10-02). La première moitié
> (JIT : Deabstraction, Runtime Async, Bounds Checks, Assertion Propagation, Vectorization,
> Intrinsics, Register Allocation, Startup and Deployment) reste résumée par les points de
> l'EPIC — ce digest couvre ce qui manquait : **GC/write barriers, Threading, Numerics,
> Globalization, Strings/Spans + Regex, Collections/LINQ, I/O, Networking, JSON, Diagnostics**.
>
> **Sémantique des ratios** : colonne Ratio des tables de l'article = temps .NET 11 / temps .NET 10
> (baseline .NET 10.0.12, pas .NET 9) — 0,50 = 2× plus rapide. Le delta .NET 9 → .NET 11 cumule
> donc les gains .NET 10 non mesurés ici ; la mesure locale (EPIC P1) tranchera sur notre matériel.

## Synthèse par section (chiffres de l'article, .NET 10 → .NET 11)

| Section | Gains mesurés (ratio) | Mécanisme principal |
|---|---|---|
| Threading | Monitor Wait/Pulse **0,84** ; thread-pool petits items (batching #122726) | Condition variable stockée sur le lock (suppression du lookup `ConditionalWeakTable`) ; décompte contrôleur une fois par lot |
| GC / write barriers | Store covariant **0,56** ; copie struct mixte **0,74** ; petits structs fusionnés en une écriture vectorielle | Inlining du helper de store tableau (check covariance éliminable) ; analyse de destination heap étendue aux copies de structs |
| Numerics (BigInteger) | Multiply **0,52-0,56** ; Divide **0,51-0,59** ; ShiftLeft **0,46-0,56** ; Parse 100k digits **0,43** ; ToString 100k digits **0,058 (×17 !)** | Limbs `uint` → `nuint` (64 bits/limb) ; Montgomery + fenêtre glissante dans ModPow ; Toom-Cook (PRs kzrnm) ; nouvelles API parse/format **UTF-8 direct** (+ cast double/float rapide ≤ 64 bits) |
| Globalization | ConvertTime From/ToUtc **0,39-0,43** ; **`DateTime.Now` 0,45 (×2,2)** | `TimeZoneInfo` : cache par année des règles de transition ; `DateTime.Now` cache l'offset UTC actif + instant de re-calcul |
| Strings/Spans | UTF8.GetByteCount surrogate-heavy (Arm64) **0,29** ; UTF8.GetCharCount ASCII **0,47** ; Base64 InsertLineBreaks **0,35-0,39** | Comptage/check surrogates vectoriel ; test « vecteur non-ASCII » avant calcul de lane ; cœur Base64 vectorisé aussi pour les sauts de ligne MIME + décodage in-place vectorisé |
| Regex (Searching/Comparing) | Préfixe partagé `[ab]+c[ab]+\|[ab]+` **0,51** ; `(http\|https)` IgnoreCase **0,017 (×59 !)** ; `\b(in)\b` préfixe retrouvé | Passe de cleanup finale sur l'arbre (factorisation du préfixe commun) ; extraction de préfixe `http` complet (pas seulement `htt`) ; captures ne masquent plus le préfixe cherchable |
| Collections/LINQ | ImmutableArray.Create slice **0,50** ; ImmutableArray SequenceEqual **0,13 (×7,7)** ; Array.FindAll (≤4 résultats) **0,30-0,33** et allocations **0,27-0,36** ; Dictionary.Remove clés valeur **0,82** ; HashSet.Contains **0,94** ; OrderedDictionary.Remove (lookup unique) | `Array.Copy` runtime plutôt que boucle manuelle ; chemins optimisés si l'autre séquence est array/list/ICollection ; 4 premiers matchs dans un buffer stack inline |
| I/O | Process stdout/stderr concourants **0,92** (16×8 Mio) | Pipes enfant ouverts en overlapped sur Windows (plus un thread bloqué par pipe) ; astuce `OVERLAPPED.hEvent` low-bit pour `RandomAccess.Read` sync-sur-handle-async |
| Networking | Happy Eyeballs **opt-in** (pas de ratio — réduit la longue traîne de connexion) | Nouvel overload `Socket.ConnectAsync(..., ConnectAlgorithm.Parallel)` : IPv4/IPv6 en parallèle, première connexion gagnante |
| JSON | Writer escape 2 kio **0,26 (×3,9)** ; Reader (indenté) **0,80** | `SearchValues` précalculés pour l'échappement par défaut ; `SkipWhiteSpace` en `IndexOfAnyExcept` vectoriel |
| Diagnostics | Validation `traceparent` W3C en `SearchValues` (pas de table de ratio publiée) ; baggage : append du bloc entier si aucun caractère à échapper | « Pay for play » : `ContainsAnyExcept` multi-caractères au lieu de boucles scalaires |

Nouveauté transversale à noter pour l'audit de code : l'analyseur **CA2027** (dotnet/sdk#51452) signale
le pattern `Task.WhenAny(t, Task.Delay(timeout))` — fuite de timers — et recommande `Task.WaitAsync`.

## Résonance CoursIA (mise à jour du tableau de l'EPIC avec les chiffres de l'article)

| Cible | Gain article pertinent | Commentaire |
|---|---|---|
| `MyIA.AI.Notebooks.csproj` (awaits SK) | Runtime Async (1re moitié) + **CA2027** | L'analyseur s'applique à nos notebooks/services SK avec timeouts — vérifier qu'aucun `WhenAny+Delay` ne traîne (grep) |
| `MyIA.Trading.Backtester` (numérique) | Stores covariants 0,56 ; copie structs 0,74 ; CEA (1re moitié) | Structs `Vector`-like et tableaux `double[]`/`object[]` des moteurs Accord/ML.NET |
| Argumentum | **`DateTime.Now` ×2,2** (l'EPIC citait ×1,9 via devdigest — l'article mesure 0,45) ; TimeZoneInfo 0,39-0,43 | Timestamps événementiels + parsing (cf. String.Split via agrégats, hors article) |
| MetaGeneticSharp | Collections/LINQ (FindAll 0,30, SequenceEqual ×7,7) ; thread-pool batching | Boucles fitness + évaluations parallèles ; LINQ Min/Max bytes/shorts (devdigest, −70-75 %) reste à mesurer localement |
| Z3.Linq / Automata | Guid.Parse (devdigest −20-25 %, hors article) ; BigInteger ×2 si arithmétique arbitrary-precision exposée | À qualifier au banc (P1) |
| semantic-fleet | JSON writer/reader (0,26/0,80) ; **Happy Eyeballs opt-in** pour la latence de connexion ; Diagnostics traceparent | DTOs sérialisés en boucle ; services multi-famille d'adresses |

## Datapoint pin kernel (P0 n°1 de l'EPIC, mesuré 2026-10-02)

`dotnet tool list -g` sur **po-2026** : `microsoft.dotnet-interactive` **1.0.712001** — la machine
n'est **pas** sur le canon `1.0.617701` (kernels-runtime.md). La divergence documentée de po-204
n'est pas seule : po-2026 est **en avance** sur le pin. Toute mesure BenchmarkDotNet en cellule
doit d'abord aligner le pin (règle F : réparer, pas contourner) — sinon les chiffres comparent des
environnements différents d'une machine à l'autre.

## Récupération — méthode (reproductible)

Le lecteur SearXNG (`mcp__searxng__web_url_read` + `section:"<heading>"`) expose l'article **intégral**
(y compris les tables de benchmarks et les listings) là où le WebFetch de l'article s'arrête vers la
moitié (limite de taille de réponse). Les headings accessibles confirment la couverture complète :
Benchmarking Setup, JIT (11 sous-sections), Startup, Threading, Numerics, Globalization,
Strings and Spans (+ Searching and Comparing), Collections and LINQ, I/O, Networking, JSON,
Diagnostics, Cryptography, What's Next. Les PRs `dotnet/runtime#` citées section par section
permettent l'approfondissement arbitraire.

## Suivi

- EPIC #18695 — plan P0-P3 et table des cibles.
- Sous-issues filles créées par la même tranche (P0 ×4, P1 ×3) — voir l'EPIC.
- Ce digest est le document de référence des **chiffres attendus** ; les bancs locaux (P1)
  produiront les chiffres **mesurés** sur notre matériel (docs/dotnet/ à suivre).
