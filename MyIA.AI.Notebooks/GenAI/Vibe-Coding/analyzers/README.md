# `MyIA.AgentSafetyAnalyzer` — sous-série Roslyn comme garde-fous d'agent

> **Axe Roslyn de l'Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473)** —
> *The Unexpected AI Stack: C#/.NET, Part 1* (Charles Chen, 08/2026).
> Sub-grain [#10500b](https://github.com/jsboige/CoursIA/issues/10500) — packaging
> `.csproj` standalone des analyseurs prototypés dans
> [`Roslyn-Code-Guardrails.ipynb`](../docs/Roslyn-Code-Guardrails.ipynb) (PR #10502).
> Sub-grain #10500c — extension `AGSEC004` (HttpClient non-constant URL).
> Sub-grain #10500d — registry de suppressions `#pragma warning disable AGSECxxx`.

## Pourquoi ce dossier

Le notebook [`docs/Roslyn-Code-Guardrails.ipynb`](../docs/Roslyn-Code-Guardrails.ipynb)
a prototypé trois analyseurs Roslyn en cellules .NET Interactive (cell 4) et un
`CodeFixProvider` (cell 10) — c'est la **démonstration pédagogique** de l'axe.

Cette sous-série `analyzers/` est la **forme production-ready** des mêmes
analyseurs : un projet .NET `netstandard2.0` qui peut être packagé en
`MyIA.AgentSafetyAnalyzer` (NuGet-ready, prêt à être référencé comme
`ProjectReference` ou `PackageReference` dans n'importe quel `.csproj`).

## Quatre règles

| ID | Règle | Exemple (snippet d'agent dangereux) |
|----|-------|------------------------------------|
| `AGSEC001` | `Process.Start` dont le premier argument n'est **pas** une constante de compilation | `Process.Start(userInput)` |
| `AGSEC002` | Concaténation de chaîne SQL (`"SELECT …" + variable`) | `"SELECT * FROM users WHERE name='" + userInput` |
| `AGSEC003` | Opération `File.Read/Write/Delete` sur un chemin non-constant | `File.ReadAllText(name)` |
| `AGSEC004` | `HttpClient.Get*/Post*/Put*/Delete*/Send*` avec URL non-constante (SSRF) | `httpClient.GetAsync(userInput)` |

Le pivot sémantique (`SemanticModel.GetConstantValue`) est ce qu'un `grep` naïf ne
peut pas distinguer : une **littérale littérale** est sûre (l'agent a écrit
`"notepad.exe"`), une **variable contrôlée par l'attaquant** ne se replie pas en
constante et déclenche le diagnostic avec localisation précise. C'est exactement
la capacité distinctive que l'axe Roslyn de l'Epic met en avant : la vérification
se fait **dans la compilation**, pas en post-processing.

## Registry de suppressions par `#pragma warning` (sub-grain #10500d)

Quand un appel **délibéré et audité** doit malgré tout passer un argument
non-constant (par exemple un `Path.Combine(baseDir, userInput)` validé par une
allow-list en amont), le développeur peut silencer la règle localement avec
la directive standard du compilateur C# :

```csharp
#pragma warning disable AGSEC001
Process.Start("/usr/bin/safe-tool", "--safe-flag", userInput);  // reviewed: whitelisted exe + safe args
#pragma warning restore AGSEC001
```

Le contrat est **per-rule** : `disable AGSEC001` n'affecte que AGSEC001. Une
directive **sans** identifiant (`#pragma warning disable`) éteint toutes les
règles AGSEC* à ce site. Les séquences `disable … restore …` à l'intérieur
d'un même bloc sont honorées (la dernière directive qui couvre la règle
l'emporte). C'est exactement la sémantique que le compilateur applique aux
CS-warnings ; la cohérence entre diagnostics compilateur et diagnostics
analyzer est volontaire.

L'implémentation (méthode `IsSuppressedByPragma`) marche les *leading trivia*
du `SyntaxNode` suspect et cherche les `PragmaWarningDirectiveTrivia`
correspondantes. C'est le pattern recommandé dans la doc Roslyn pour les
`DiagnosticSuppressor`.

## Structure

```
analyzers/
├── AgentSafetyAnalyzer/                  # netstandard2.0, IsPackable=true
│   ├── AgentSafetyAnalyzer.csproj
│   ├── AgentSafetyAnalyzer.cs            # 4 règles + IsSuppressedByPragma
│   └── SqlConcatCodeFixProvider.cs       # Correctif auto pour AGSEC002
└── AgentSafetyAnalyzer.Tests/            # net8.0, xUnit
    ├── AgentSafetyAnalyzer.Tests.csproj
    └── AgentSafetyAnalyzerTests.cs       # 17 tests (6 analyseur + 5 AGSEC004 + 1 codefix + 5 pragma)
```

## Build & test (CPU-only, pas d'Aspire requis)

```bash
cd analyzers/AgentSafetyAnalyzer && dotnet build
cd ../AgentSafetyAnalyzer.Tests && dotnet test
```

Résultat attendu : **17 tests verts**, dont
- 6 tests analyzer (3 règles × 2 — discriminant littéral littéral vs variable attaquant-contrôlée) ;
- 5 tests AGSEC004 (HttpClient no-diagnostic + 4 variants `GetAsync`/`PostAsync`/`SendAsync`/`GetStringAsync`) ;
- 1 test codefix (`AGSEC002_CodeFix_TransformsConcatToInterpolatedString`) ;
- 5 tests suppression par pragma (`AGSEC001_NoDiagnostic_OnPragmaDisable_ForSameRule`,
  `…StillDiagnostic_OnPragmaDisable_ForOtherRule`, `…NoDiagnostic_OnBarePragmaDisable`,
  `…Diagnostic_OnPragmaRestoreAfterDisable`, `AGSEC002_NoDiagnostic_OnPragmaDisable_ForSqlConcat`).

## Comparaison avec le notebook

| Aspect | Notebook (`docs/Roslyn-Code-Guardrails.ipynb`) | Cette sous-série (`analyzers/`) |
|--------|------------------------------------------------|--------------------------------|
| **Forme** | Cellules .NET Interactive, classes définies en cellule | Projet .NET standard, classes en fichiers `.cs` |
| **Réutilisable** | Non (le notebook est un parcours linéaire) | Oui (NuGet-ready) |
| **Tests** | Cellule qui appelle l'analyzer sur un snippet | xUnit + `Microsoft.CodeAnalysis.CSharp.Analyzer.Testing` |
| **CI** | Exécuté dans le kernel du notebook | `dotnet build` + `dotnet test` |
| **Verdict Prong-A** | SOTA-OK (vrai `Microsoft.CodeAnalysis` 4.13) | SOTA-OK (vrai `Microsoft.CodeAnalysis` 4.12, compatible `netstandard2.0`) |

Les deux formes **ne se doublonnent pas** : le notebook enseigne le *pourquoi*
(discrimination sémantique vs grep, localisation précise, `CodeAction` vs
`CodeFixProvider`), la sous-série fournit le *livrable prêt à intégrer*. Le
reader apprend avec l'un et embarque l'autre.

## Sub-grains du ticket parent [#10500](https://github.com/jsboige/CoursIA/issues/10500)

- `10500b` (PR #10559) : packaging `.csproj` standalone — **livré**.
- `10500c` (ce grain, PR #10563) : `HttpClient.Get*/Post*/Put*/Delete*/Send*` URL non-constante (SSRF, AGSEC004) — **livré**.
- `10500d` (PR #10571) : registry de suppressions `#pragma warning disable
  AGSECxxx` pour les faux positifs assumés — **livré**.
- `10500e` : analyzer `==` sur secrets hardcodés (BinaryExpressionSyntax sur
  string littéraux avec préfixes `sk-`, `ghp_`, etc.).

## Garde-fous respectés

- **Prong A** : vrai `Microsoft.CodeAnalysis` 4.12 (`netstandard2.0` compatible),
  verdict **SOTA-OK** (cf. infra de test `Microsoft.CodeAnalysis.CSharp.Analyzer.Testing`
  et `CSharpCodeFixTest`).
- **Prong B** : discrimination sémantique sur les 4 règles (chaque règle a son
  test « no diagnostic sur littéral littéral » ET « diagnostic sur variable
  attaquant-contrôlée ») + discrimination de la suppression (per-rule vs all,
  disable vs restore).
- **C.1** : pas d'erreur volontaire, `Build` et `Test` Successful attendus.
- **C.2** : n/a (pas de notebook ici — `.cs` + `.csproj`).
- **three-exercises-per-notebook** : n/a (pas un notebook).
- **prose FR d'abord** : README en français (cf. `[readme-french-first.md]`).
