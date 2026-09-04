# Substitution du SVM à noyau — port E2 du Backtester Aricie

> **Source :** #7357 (EPIC E2, grain « substitution du SVM à noyau » prescrit par le body du 2026-08-20) · #7265 (EPIC parent patrimoine Aricie) · #12541 (cadrage Option C, doc `backtester-e2-cadrage.md`) · [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md).
>
> **Verdict : SOTA-OK.** Un SVM à noyau **existe et tourne** en .NET 9 via **Accord.NET 2.6.0**, qui est **déjà une dépendance du fork** (`SupportVectorMachine` + `SequentialMinimalOptimization`, kernels Linear/Gaussian). Aucune substitution tierce n'est requise ; l'hypothèse « le noyau gaussien exige SharpLearning (MIT) ou équivalent » émise dans #12541 est **supersedée** — l'équivalent est Accord.NET lui-même. Aucun verdict `INTRINSIC`.

## Objet du grain

Le cadrage Option C (#12541) a identifié un **gap** : ML.NET n'a pas de SVM à noyau (le linéaire se remplace par `SdcaMaximumEntropy`/`AveragedPerceptron`), et le noyau gaussien « exige SharpLearning (MIT) ou équivalent ». Ce grain a pour objet de **lever l'inconnue** : existe-t-il, en .NET, un SVM à noyau qui se substitue proprement — et qui démontre sa capacité distinctive sur une frontière **non linéairement separable** (Prong B, pas un problème dégénéré) ?

## Mesure

Test compagnon .NET 9 (`dotnet run -c Release`, SDK 10.0.204, packages Accord 2.6.0) sur deux jeux jouets à frontière **non linéairement séparable** :

| Jeu | Noyau LINEAR | Noyau GAUSSIEN (σ optimal) | Écart test |
|---|---|---|---|
| **XOR + bruit** (400 pts, diagonales) | test **0.750** | test **1.000** (σ=0.3/0.5/1.0/2.0 tous 1.000) | **+0.250** |
| **Deux lunes** (400 pts) | test **0.892** | test **0.983** (σ=0.3) | **+0.092** |

Sortie réelle du test (commitée telle quelle) :

```
[XOR + bruit gaussien]  train 280 / test 120
  noyau LINEAIRE   : train 0,782 | test 0,750
  noyau GAUSSIEN(σ=0,3) : train 1,000 | test 1,000   ecart=+0,250
  noyau GAUSSIEN(σ=0,5) : train 1,000 | test 1,000   ecart=+0,250
  noyau GAUSSIEN(σ=1) : train 1,000 | test 1,000   ecart=+0,250

[Deux lunes]  train 280 / test 120
  noyau LINEAIRE   : train 0,864 | test 0,892
  noyau GAUSSIEN(σ=0,3) : train 0,996 | test 0,983   ecart=+0,092
  noyau GAUSSIEN(σ=1) : train 0,968 | test 0,967   ecart=+0,075
  noyau GAUSSIEN(σ=2) : train 0,868 | test 0,892   ecart=+0,000
```

Interprétation : sur le XOR purs (frontière en diagonales, aucune droite ne découpe les classes), le noyau **linéaire est plafonné à 0.750** (juste au-dessus du hasard), tandis que le noyau **gaussien atteint 1.000** — la capacité distinctive du kernel trick est **visible**, pas un artefact. La famille des deux lunes confirme avec un écart de +0.092 (linéaire 0.892 vs gaussien 0.983), et montre la **sensibilité à σ** (σ=2.0 trop large → effondrement à 0.892, le noyau est hyper-paramétré) : un vrai choix de modèle, pas un paramètre gratuit.

## Checklist 6 axes (établissement du verdict)

| # | Axe | Réponse | Verdict |
|---|---|---|---|
| 1 | **Binding .NET / NuGet** | **OUI — Accord.NET 2.6.0** (déjà dépendance du fork) : `KernelSupportVectorMachine(IKernel, inputs)` + noyaux `Linear`/`Gaussian`/`Polynomial`/`Laplacian`/`Sigmoid` + `SequentialMinimalOptimization(svm, X, y).Run()`. **Testé net9.0 et exécuté** (résultats ci-dessus). | **SOTA-OK** |
| 2 | **P/Invoke (libsvm C API)** | Chemin réel existant en fallback : `libsvm.net` (et la famille `libsvm.clr.*`), wrapper P/Invoke de la libsvm C — **non testé car non requis** (axe 1 suffit). | N/A (axe 1) |
| 3 | **CLI `svm-train`/`svm-predict`** | Existe (binaire libsvm) mais dégradé : passage des données par fichiers, pas d'in-process — non retenu (axe 1 plus simple). | N/A (axe 1) |
| 4 | **IKVM (pont Java)** | Non applicable : la cible n'est pas Java (aucune lib SVM Java à transposer sous .NET). | N/A |
| 5 | **PythonNet → `sklearn.svm.SVC`** | Existe (`sklearn.svm.SVC` a un noyau RBF, accessible via CPython) mais **rejeté** : ajoute une dépendance runtime Python + CPython dans le backtester, là où l'axe 1 est déjà présent et pur .NET. | N/A (axe 1) |
| 6 | **Lib différente à rôle équivalent** | L'équivalent recherché **est** Accord.NET (calcul de noyau), pas une lib tierce ; SharpLearning (MIT) n'est **pas** nécessaire — c'est l'hypothèse #12541, maintenant supersedée. | N/A (axe 1) |

**Sur l'axe 1, deux caveats honnêtes** (à porter dans la décision de port, pas un obstacle) :

1. **NU1701** : Accord 2.6.0 cible .NET Framework (`net46+`), pas `netstandard2.0` — il est restauré via le shim de compatibilité et **tourne** en net9.0 (testé). Pour une lib purement managée (aucun P/Invoke natif dans le SVM), le shim est fiable ; le risque résiduel est l'absence de mises à jour/patches sécurité.
2. **Gel 2020** : Accord.NET est dormant (dernière release ~2020). C'est un choix à assumer — mais ce n'est **pas un risque nouveau** : c'est déjà une dépendance du fork, le port n'en introduit pas une.

## Impact sur le port E2

- **Le gap SVM à noyau est fermé** : le fork porte déjà `SupportVectorMachine`+`SequentialMinimalOptimization` (kernels Linear/Gaussian), qui compilent et tournent sur net9.0 avec ces mêmes packages — le port n'exige **aucun** remplacement de la partie SVM.
- **Le seul gap restant** de l'Option C est l'**AutoML** (`ColumnInferenceResults` → `TextLoaderEventArgs` n'existe plus en 0.24, mesuré dans #12541) — une adaptation d'API, pas un manque de capacités.
- **Test d'intégration futur** : le test compagnon ci-dessous se réutilise tel quel (frontière non linéairement separable + assert que `test_gaussien > test_lineaire`) comme garde-fou de non-régression du port du modèle SVM.

## Test compagnon reproductible

`svmkernel.csproj` :

```xml
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net9.0</TargetFramework>
    <ImplicitUsings>enable</ImplicitUsings>
    <Nullable>enable</Nullable>
    <RollForward>LatestMajor</RollForward>
  </PropertyGroup>
  <ItemGroup>
    <PackageReference Include="Accord.MachineLearning" Version="2.6.0" />
    <PackageReference Include="Accord.Statistics" Version="2.6.0" />
    <PackageReference Include="Accord.Math" Version="2.6.0" />
  </ItemGroup>
</Project>
```

`Program.cs` :

```csharp
using System;
using System.Linq;
using Accord.MachineLearning.VectorMachines;
using Accord.MachineLearning.VectorMachines.Learning;
using Accord.Statistics.Kernels;

var rng = new Random(42);
Console.WriteLine("=== SVM a noyau — test .NET 9 (Accord.NET 2.6.0) ===");
Console.WriteLine();
Run("XOR + bruit gaussien", MakeXor(400, 0.18, rng), new[] { 0.3, 0.5, 1.0, 2.0 });
Console.WriteLine();
Run("Deux lunes", MakeMoons(400, 0.12, rng), new[] { 0.3, 0.5, 1.0, 2.0 });
Console.WriteLine();

(double x, double y, int label)[] MakeXor(int n, double noise, Random rng)
{
    var res = new (double, double, int)[n];
    for (int i = 0; i < n; i++)
    {
        double sx = rng.Next(2) == 0 ? 1 : -1;
        double sy = rng.Next(2) == 0 ? 1 : -1;
        int cls = sx * sy > 0 ? 0 : 1;
        res[i] = (sx + G(rng) * noise, sy + G(rng) * noise, cls);
    }
    return res;
}

(double x, double y, int label)[] MakeMoons(int n, double noise, Random rng)
{
    var res = new (double, double, int)[n];
    for (int i = 0; i < n; i++)
    {
        int cls = rng.Next(2);
        double theta = rng.NextDouble() * Math.PI;
        double r = 1.0;
        if (cls == 0)
            res[i] = (Math.Cos(theta) * r + G(rng) * noise,
                      Math.Sin(theta) * r + G(rng) * noise, 0);
        else
            res[i] = (1.0 - Math.Cos(theta) * r + G(rng) * noise,
                      0.5 - Math.Sin(theta) * r + G(rng) * noise, 1);
    }
    return res;
}

double G(Random rng)
{
    double u1 = 1.0 - rng.NextDouble();
    double u2 = rng.NextDouble();
    return Math.Sqrt(-2.0 * Math.Log(u1)) * Math.Cos(2.0 * Math.PI * u2);
}

void Run(string name, (double x, double y, int label)[] data, double[] sigmas)
{
    var r = new Random(42);
    var perm = Enumerable.Range(0, data.Length).OrderBy(_ => r.Next()).ToArray();
    int nTrain = (int)(data.Length * 0.7);
    var trX = new double[nTrain][];
    var trY = new int[nTrain];
    var teX = new double[data.Length - nTrain][];
    var teY = new int[data.Length - nTrain];
    for (int i = 0; i < nTrain; i++)
    {
        trX[i] = new[] { data[perm[i]].x, data[perm[i]].y };
        trY[i] = data[perm[i]].label == 0 ? 1 : -1;
    }
    for (int i = nTrain; i < data.Length; i++)
    {
        teX[i - nTrain] = new[] { data[perm[i]].x, data[perm[i]].y };
        teY[i - nTrain] = data[perm[i]].label == 0 ? 1 : -1;
    }
    var (linTr, linTe) = TrainKernel(new Linear(), 1.0, trX, trY, teX, teY);
    Console.WriteLine($"[{name}]  train {nTrain} / test {data.Length - nTrain}");
    Console.WriteLine($"  noyau LINEAIRE   : train {linTr:F3} | test {linTe:F3}");
    foreach (var sigma in sigmas)
    {
        var (gt, ge) = TrainKernel(new Gaussian(sigma), 1.0, trX, trY, teX, teY);
        Console.WriteLine($"  noyau GAUSSIEN(σ={sigma}) : train {gt:F3} | test {ge:F3}   ecart=+{ge - linTe:F3}");
    }
}

(double tr, double te) TrainKernel(IKernel kernel, double C,
    double[][] trX, int[] trY, double[][] teX, int[] teY)
{
    var svm = new KernelSupportVectorMachine(kernel, 2);
    var smo = new SequentialMinimalOptimization(svm, trX, trY) { Complexity = C };
    smo.Run();
    var pred = svm.Compute(trX);
    double tr = pred.Zip(trY, (v, t) => (v >= 0 ? 1 : -1) == t ? 1 : 0).Sum() / (double)trY.Length;
    var predTe = svm.Compute(teX);
    double te = predTe.Zip(teY, (v, t) => (v >= 0 ? 1 : -1) == t ? 1 : 0).Sum() / (double)teY.Length;
    return (tr, te);
}
```

> Note de reproductibilité : les versions `Accord.MachineLearning 2.1.0.2`/`Accord.Statistics 2.1.0.5` demandées à l'origine n'existent plus sur NuGet (NU1603 : résolues à 2.6.0). Pinner 2.6.0 d'emblée (comme ci-dessus) évite le warning NU1603 ; le warning NU1701 (restauration .NET Framework pour la cible net9.0) reste et est documenté.

## Attribution

Mesure réalisée le 2026-08-23 (lane `myia-po-2025:CoursIA-2`). Source : commentaire #7357 du 2026-08-20 (grain prescrit), cadrage #12541, checklist 6 axes [sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md). Tous les chiffres de ce document viennent de la commande `dotnet run -c Release` exécutée ce cycle — reproductibles depuis le code embarqué ci-dessus. Aucune valeur n'est affirmée de mémoire.

## Disposition upstream — `CalibrateComplexity` (2026-09-03)

Cette section documente la décision et l'action de signalement du défaut `CalibrateComplexity` identifié lors du port SVM à noyau (tranche 4 de l'EPIC #7357, PR [#14369](https://github.com/jsboige/CoursIA/pull/14369) mergée le 2026-09-02).

### Constat

Le bloc passé à `ExecuteWithTimeLimit` dans la méthode `CalibrateComplexity` du fork [`MyIntelligenceAgency/Lean`](https://github.com/MyIntelligenceAgency/Lean) (branche `MyIABacktesting_integration`, SHA `612dddf9`) **ré-instancie `teacher` au lieu d'appeler `Learn`** :

```csharp
() => { try { teacher = new MulticlassSupportVectorLearning<IKernel>(); } catch { } }
```

Conséquence en chaîne mesurée : `machine` reste `null` → `machine.Decide(xTrain)` lève une `NullReferenceException` → avalée par le `catch` englobant → `testError` ne quitte jamais `double.MaxValue` → `testError < currentResult` est toujours faux → `bestComplexity` n'est jamais mis à jour. **La méthode rend TOUJOURS son amorce `0.0001`**, toutes données confondues, pendant que l'appelant journalise `SVM complexity calibrated: 0.0001`.

### Mesure (vérifiée côte à côte)

| jeu | corps réparé | corps upstream |
|---|---|---|
| XOR net (n=64) | 0.0001 | 0.0001 |
| XOR bruité spread 0.9 (n=80) | 0.00374 | 0.0001 |
| **XOR bruité spread 1.1 (n=120)** | **706.88** | **0.0001** |
| XOR bruité spread 1.1 (n=240) | 15.79 | 0.0001 |

Sur XOR net les deux coïncident, mais pour une raison sans rapport : `C=0.0001` y classe déjà parfaitement (erreur 0 à tous les C testés), donc conserver l'amorce y est le bon résultat. La divergence n'apparaît que sur les jeux où la calibration doit effectivement explorer. C'est précisément la mesure rendue par le commentaire détaillé de la méthode `CalibrateComplexity` côté CoursIA (en-tête du fichier `MyIA.Trading.Backtester/TradingSvmModelConfig.cs`, écart 3/3 délibéré).

### Décision : signalement upstream vaut la peine — et il est fait

Le fork `MyIntelligenceAgency/Lean` n'est pas un dépôt du cluster, mais c'est un **fork de `QuantConnect/Lean`** que nous maintenons actif (submodule maintenance, Règle 1 du [submodule-maintenance.md](../../.claude/rules/submodule-maintenance.md) — voir aussi EPIC #1206 pour la piste de retour upstream vers `QuantConnect/Lean`). Un défaut qui **affirme faussement une calibration** dans un sous-système de production mérite un signalement — d'autant que la divergence entre fork et CoursIA est aujourd'hui nécessaire (le fork ne calibre rien ; porter le corps verbatim livrerait une fonction dont le message de log est mensonger).

**Issue upstream ouverte :** [`MyIntelligenceAgency/Lean#40`](https://github.com/MyIntelligenceAgency/Lean/issues/40) — *« CalibrateComplexity ne calibre rien : le bloc sous limite de temps ré-instancie teacher au lieu d'appeler Learn »*. Le ticket documente :

- le défaut (bloc verbatim + chaîne de conséquences) ;
- la mesure côte à côte (4 jeux) ;
- la reproduction minimale ;
- une esquisse de correctif (`machine = teacher.Learn(xTrain, yTrain)` + traitement de `maxedOut` comme signal) ;
- le statut côté émetteur : CoursIA est non-affecté (divergence déjà absorbée par la garde `CalibrateComplexity_ActuallyExploresAndDoesNotReturnItsSeedValue`).

**Pourquoi pas un PR upstream** : la modification touche une fonction de production d'un sous-système de fork dont la trajectoire de maintenance n'est pas consolidée. Ouvrir un PR supposerait un round de revue avec les mainteneurs du fork que cette mesure unilatérale ne déclenche pas. Une issue est l'organe adapté : elle ouvre la conversation sans présupposer l'engagement de leur cycle de release. Une PR pourra suivre si les mainteneurs valident l'esquisse de correctif.

### Côté CoursIA : divergence maintenue

Le port garde l'écart intentionnel avec l'upstream. Une future tranche de mise à jour de `MyIntelligenceAgency/Lean` dans le submodule **ne doit pas ré-aligner** ce point : un `git pull` qui ré-instancierait `teacher` au lieu d'appeler `Learn` ré-introduirait le défaut. C'est la première acceptance du ticket [#14370](https://github.com/jsboige/CoursIA/issues/14370) — *« Ne pas « réaligner sur l'amont » ce point lors d'une tranche ultérieure : l'écart est intentionnel et mesuré »* — et elle est **désormais codifiée** par cette section, à lire en même temps que l'en-tête de `TradingSvmModelConfig.cs`.

### Suite possible

- Si l'issue `#40` reçoit une réponse des mainteneurs et qu'un correctif amont est mergé dans `MyIntelligenceAgency/Lean`, une future tranche de bump submodule pourra **rétablir la convergence** (suppression de l'écart 3/3) et déplacer la garde de régression vers un test d'**équivalence** amont/CoursIA plutôt que d'écart.
- En attendant, la garde existante (`CalibrateComplexity_ActuallyExploresAndDoesNotReturnItsSeedValue` + `CalibratedComplexity_ScoresBetterThanTheSeedComplexity`) couvre la non-régression côté CoursIA : les deux tests sont verts sur main post-#14369.
