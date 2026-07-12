# SemanticFleet.Radix

Standalone .NET module extracted from
[semantic-fleet](https://github.com/SemanticFlow/SemanticFlow) v0.34.3 to
implement **Axis 4 (radix-tree signature matching)** of
[Epic #1210](https://github.com/jsboige/CoursIA/issues/1210).

## Why this module exists

`semantic-fleet`'s `MultiTextCompletionSettings.cs` ships a TODO at lines
266-273 (verbatim in the issue body) describing a planned radix-tree / trie
matcher to replace the linear `SimpleMatchPromptSettings` stub at lines
283-292:

```csharp
public static PromptMultiConnectorSettings? SimpleMatchPromptSettings(
    CompletionJob completionJob,
    IEnumerable<PromptMultiConnectorSettings> promptMultiConnectorSettings)
{
    return promptMultiConnectorSettings.FirstOrDefault(p =>
        completionJob.Prompt.StartsWith(p.Signature.PromptStart));
}
```

This linear scan is fine for a handful of registered signatures but becomes
the dominant cost as the catalogue of `PromptMultiConnectorSettings` grows.
This module drops in a **radix-tree** implementation behind the same delegate
signature, so consumers can swap implementations without forking
`semantic-fleet`.

## How it plugs in

`MultiTextCompletionSettings.PromptMatcher` is a delegate hook:

```csharp
public Func<CompletionJob, IEnumerable<PromptMultiConnectorSettings>, PromptMultiConnectorSettings?>
    PromptMatcher { get; set; } = SimpleMatchPromptSettings;
```

To use the radix-tree matcher:

```csharp
using SemanticFleet.Radix;

settings.PromptMatcher = RadixTreePromptMatcher.Match;
```

No fork of `semantic-fleet` is required.

## API

| Entry point | Purpose |
|-------------|---------|
| `RadixTreePromptMatcher.Match(job, settings)` | Build-then-lookup, single call. Convenience for small catalogues. |
| `RadixTreePromptMatcher.BuildTree(settings)` | Build a reusable tree once. |
| `RadixTreePromptMatcher.MatchWithTree(job, tree)` | Lookup against a pre-built tree. Recommended for hot paths. |
| `RadixTree<TValue>` | Generic radix tree — usable beyond `PromptMatcher` for any prefix-lookup workload. |

## Complexity

| Matcher | Build | Lookup |
|---------|-------|--------|
| `SimpleMatchPromptSettings` (linear) | O(1) | O(n × average-prefix-length) |
| `RadixTreePromptMatcher.Match` | O(total signature length) | O(matched-prefix-length) |
| `RadixTreePromptMatcher.MatchWithTree` | O(total signature length) once | O(matched-prefix-length) |

`n` = number of registered signatures, `matched-prefix-length` ≤ `query.Length`.

For the typical semantic-fleet workload (a few hundred to a few thousand
signatures, dominated by repeated lookups on the same catalogue), prefer the
**two-step `BuildTree` + `MatchWithTree`** pattern.

## Behavioural parity

Tests in
[`tests/RadixTreePromptMatcherTests.cs`](tests/RadixTreePromptMatcherTests.cs)
exercise parity with `SimpleMatchPromptSettings` on disjoint signature sets
where both algorithms pick the same entry. Where prefixes overlap, the
radix-tree matcher returns the entry with the **longest matching prefix** —
matching the literal TODO's "longest prefix" language.

When multiple settings share the same `SignaturePrefix.PromptStart`, the
radix-tree matcher keeps the **most recently inserted** value (last-writer
wins, analogous to `Dictionary<string, TValue>`). The linear baseline returns
the **first** matching entry (`FirstOrDefault`). The test suite avoids this
ambiguity by exercising disjoint signature sets.

Empty `PromptStart` values are **skipped silently** at `BuildTree` time: registering
an empty prefix is a degenerate case the baseline never refuses, so we narrow
the matcher contract rather than introducing a hard failure for behaviour nobody
should rely on. At the lower level, `RadixTree<TValue>.Insert` itself refuses
empty keys outright via `ArgumentException.ThrowIfNullOrEmpty` — the skip is
the matcher's accommodation of the baseline's lax behaviour.

## Building & testing

```bash
dotnet build tools/semantic-fleet-radix
dotnet test  tools/semantic-fleet-radix/tests
```

The `BenchmarkRadixVsLinear` xUnit fact is marked `[Fact(Skip = ...)]` — it
is a micro-benchmark (not a unit test) and is excluded from `dotnet test`.
Run it manually with:

```bash
dotnet test tools/semantic-fleet-radix/tests \
    --filter "FullyQualifiedName~BenchmarkRadixVsLinear" \
    --logger "console;verbosity=detailed"
```

## Scope of this PR

This module is **Axis 4 only**. Axes 1-3 of Epic #1210 (signature sampling,
hybrid dictionary, and upstream merge of this back-port) are out of scope
for this PR. The standalone-module shape was chosen deliberately: jsboige's
note on the epic explains that `PromptMatcher` is a delegate hook, so an
external library can be injected without touching the semantic-fleet core.

## License

MIT — extracted verbatim surface types from semantic-fleet v0.34.3 are
referenced for compatibility only; all new code (the radix tree and matcher)
is original to this module.
