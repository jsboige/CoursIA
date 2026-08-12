# `MyIA.AgentSafetyAnalyzer` — sous-série Roslyn comme garde-fous d'agent

> **Axe Roslyn de l'Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473)** —
> *The Unexpected AI Stack: C#/.NET, Part 1* (Charles Chen, 08/2026).
> Sub-grain [#10500b](https://github.com/jsboige/CoursIA/issues/10500) — packaging
> `.csproj` standalone des analyseurs prototypés dans
> [`Roslyn-Code-Guardrails.ipynb`](../docs/Roslyn-Code-Guardrails.ipynb) (PR #10502).

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
| `AGSEC005` | Littéral string dont la valeur commence par un **préfixe credential connu** (`sk-`, `ghp_`, `AKIA`, `AIza`, …) | `const string KEY = "sk-proj-AbCdEf…"` |

Trois pivots sémantiques distincts :

- **AGSEC001/003** — `SemanticModel.GetConstantValue(expr).HasValue` distingue
  une littérale littérale (sûre) d'une variable attaquant-contrôlée (voulue).
- **AGSEC002** — pattern matching SQL sur le littéral gauche d'un `+`
  (sémantique de *position*).
- **AGSEC005** — discrimination par **préfixe lexical** sur le littéral
  (sémantique de *forme* — pour une constante hardcodée, le danger EST la
  constance ; `GetConstantValue` n'aiderait pas).

La table `CredentialPrefixes` est ordonnée *most-specific-first* (`sk-ant-` avant
`sk-`) pour que le diagnostic nomme le bon provider. Le message tronque la
valeur à 12 caractères + `…` (CWE-798 interdit l'affichage du secret complet).

Le pivot sémantique (`SemanticModel.GetConstantValue`) est ce qu'un `grep` naïf ne
peut pas distinguer : une **littérale littérale** est sûre (l'agent a écrit
`"notepad.exe"`), une **variable contrôlée par l'attaquant** ne se replie pas en
constante et déclenche le diagnostic avec localisation précise. C'est exactement
la capacité distinctive que l'axe Roslyn de l'Epic met en avant : la vérification
se fait **dans la compilation**, pas en post-processing.

## Structure

```
analyzers/
├── AgentSafetyAnalyzer/                  # netstandard2.0, IsPackable=true
│   ├── AgentSafetyAnalyzer.csproj
│   ├── AgentSafetyAnalyzer.cs            # 4 règles (AGSEC001/002/003/005)
│   ├── SqlConcatCodeFixProvider.cs       # Correctif auto pour AGSEC002
│   └── HardcodedCredentialCodeFixProvider.cs  # Correctif auto pour AGSEC005
└── AgentSafetyAnalyzer.Tests/            # net8.0, xUnit
    ├── AgentSafetyAnalyzer.Tests.csproj
    └── AgentSafetyAnalyzerTests.cs       # 16 tests (analyseur + codefix)
```

## Build & test (CPU-only, pas d'Aspire requis)

```bash
cd analyzers/AgentSafetyAnalyzer && dotnet build
cd ../AgentSafetyAnalyzer.Tests && dotnet test
```

Résultat attendu : **16 tests verts**, dont le `AGSEC002_CodeFix_TransformsConcatToInterpolatedString`
qui prouve la transformation automatique `"SELECT …" + var` → `$"SELECT … {var}"`,
et `AGSEC005_CodeFix_ReplacesOpenAIKeyWithEnvVarLookup` qui remplace un littéral
`"sk-proj-…"` par `System.Environment.GetEnvironmentVariable("OPENAI_API_KEY") ?? ""`.

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

## Sub-grains restants du ticket parent [#10500](https://github.com/jsboige/CoursIA/issues/10500)

- `10500b` (sub-grain fondateur de cette sous-série) : packaging `.csproj`
  standalone — **livré**.
- `10500c` : ajouter `HttpClient.GetAsync(url)` à la liste des targets AGSEC001.
- `10500d` : registry de suppressions `#pragma warning disable AGSEC001` pour les
  faux positifs assumés.
- `10500e` : analyzer `AGSEC005` sur secrets hardcodés (littéraux string avec
  préfixes `sk-`, `ghp_`, `AKIA`, etc.) — **livré**.
- `10500f` : `CodeFixProvider` `HardcodedCredentialCodeFixProvider` qui remplace
  un littéral credential par `Environment.GetEnvironmentVariable("PROVIDER_API_KEY") ?? ""`
  — **livré** (cette PR).

## Garde-fous respectés

- **Prong A** : vrai `Microsoft.CodeAnalysis` 4.12 (`netstandard2.0` compatible),
  verdict **SOTA-OK** (cf. infra de test `Microsoft.CodeAnalysis.CSharp.Analyzer.Testing`
  et `CSharpCodeFixTest`).
- **Prong B** : discrimination sémantique sur les 3 règles (chaque règle a son
  test « no diagnostic sur littéral littéral » ET « diagnostic sur variable
  attaquant-contrôlée »).
- **C.1** : pas d'erreur volontaire, `Build` et `Test` Successful attendus.
- **C.2** : n/a (pas de notebook ici — `.cs` + `.csproj`).
- **three-exercises-per-notebook** : n/a (pas un notebook).
- **prose FR d'abord** : README en français (cf. `[readme-french-first.md]`).
