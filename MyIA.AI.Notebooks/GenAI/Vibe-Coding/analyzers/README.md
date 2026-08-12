# `MyIA.AgentSafetyAnalyzer` — sous-série Roslyn comme garde-fous d'agent

> **Axe Roslyn de l'Epic [#10473](https://github.com/jsboige/CoursIA/issues/10473)** —
> *The Unexpected AI Stack: C#/.NET, Part 1* (Charles Chen, 08/2026).
> Sub-grain [#10500b](https://github.com/jsboige/CoursIA/issues/10500) — packaging
> `.csproj` standalone des analyseurs prototypés dans
> [`Roslyn-Code-Guardrails.ipynb`](../docs/Roslyn-Code-Guardrails.ipynb) (PR #10502).
> Sub-grain #10500e — AGSEC005 détection de credentials hardcodés (CWE-798).

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
| `AGSEC005` | Littéral string démarrant par un préfixe credential connu (`sk-…`, `ghp_…`, `AKIA…`, `AIza…`, `hf_…`, etc.) — CWE-798 | `const string key = "sk-AbCd…"` |

Les trois premières règles utilisent le pivot sémantique `SemanticModel.GetConstantValue` :
une **littérale littérale** est sûre (l'agent a écrit `"notepad.exe"`), une
**variable contrôlée par l'attaquant** ne se replie pas en constante et
déclenche le diagnostic avec localisation précise. C'est exactement la capacité
distinctive que l'axe Roslyn de l'Epic met en avant : la vérification se fait
**dans la compilation**, pas en post-processing.

**AGSEC005** utilise un pivot différent — la **discrimination par préfixe**.
Un secret hardcodé EST une constante de compilation (par opposition à AGSEC001/003
où la constante est sûre), donc `GetConstantValue` n'aide pas. À la place, on
regarde la *forme* du littéral : un préfixe credential bien connu (OpenAI `sk-`,
GitHub `ghp_`, AWS `AKIA`, Google `AIza`, HuggingFace `hf_`, etc.) indique
quasi-certainement une vraie clé leakée. La table des préfixes est ordonnée
*most-specific-first* (`sk-ant-` avant `sk-`) pour que le message diagnostique
nomme le bon provider.

## Structure

```
analyzers/
├── AgentSafetyAnalyzer/                  # netstandard2.0, IsPackable=true
│   ├── AgentSafetyAnalyzer.csproj
│   ├── AgentSafetyAnalyzer.cs            # 4 règles (AGSEC001/002/003/005)
│   └── SqlConcatCodeFixProvider.cs       # Correctif auto pour AGSEC002
└── AgentSafetyAnalyzer.Tests/            # net8.0, xUnit
    ├── AgentSafetyAnalyzer.Tests.csproj
    └── AgentSafetyAnalyzerTests.cs       # 13 tests (12 analyseur + 1 codefix)
```

## Build & test (CPU-only, pas d'Aspire requis)

```bash
cd analyzers/AgentSafetyAnalyzer && dotnet build
cd ../AgentSafetyAnalyzer.Tests && dotnet test
```

Résultat attendu : **13 tests verts**, dont
- 6 tests analyzer (3 règles sémantiques × 2 — discriminant littéral littéral vs variable attaquant-contrôlée) ;
- 6 tests AGSEC005 (`sk-`, `sk-ant-`, `ghp_`, `AKIA`, plain literal no-match, empty literal no-match) ;
- 1 test codefix (`AGSEC002_CodeFix_TransformsConcatToInterpolatedString`).

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

- `10500b` : packaging `.csproj` standalone — **livré** (PR #10559 MERGED).
- `10500c` : `HttpClient.GetAsync(url)` à la liste des targets (extension
  d'AGSEC001 ou nouvelle règle AGSEC004) — **en vol** (PR #10563 OPEN).
- `10500d` : registry de suppressions `#pragma warning disable AGSECxxx` pour
  les faux positifs assumés — **en vol** (PR #10571 OPEN).
- `10500e` (ce grain) : AGSEC005 détection de credentials hardcodés
  (préfixes `sk-`/`sk-ant-`/`ghp_`/`AKIA`/`AIza`/`hf_`/etc.) — **livré**.

## Garde-fous respectés

- **Prong A** : vrai `Microsoft.CodeAnalysis` 4.12 (`netstandard2.0` compatible),
  verdict **SOTA-OK** (cf. infra de test `CSharpCompilation.WithAnalyzers` direct
  en `AdhocWorkspace`, pattern recommandé dans la doc Roslyn).
- **Prong B** : discrimination sémantique sur les 3 règles sémantiques (chaque
  règle a son test « no diagnostic sur littéral littéral » ET « diagnostic sur
  variable attaquant-contrôlée ») + discrimination par préfixe pour AGSEC005
  (préfixe credential ⇒ diagnostic, littéral neutre ⇒ no diagnostic).
- **C.1** : pas d'erreur volontaire, `Build` et `Test` Successful attendus.
- **C.2** : n/a (pas de notebook ici — `.cs` + `.csproj`).
- **three-exercises-per-notebook** : n/a (pas un notebook).
- **prose FR d'abord** : README en français (cf. `[readme-french-first.md]`).
