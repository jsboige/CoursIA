# kelly_lean — optimalité du critère de Kelly (log-croissance)

Mini-projet Lean 4 (avec Mathlib, toolchain `v4.31.0-rc1`) prouvant l'**optimalité du
critère de Kelly** pour le *position sizing*. Pour un pari de Bernoulli (probabilité
`p` de gain, cote nette `b`, `q = 1 − p`), la fraction optimale du capital à risquer
est

> **f\* = (b·p − q) / b**

qui **maximise de façon unique** le taux de croissance espéré du capital composé

> g(f) = p·log(1 + b·f) + q·log(1 − f).

Tout sur-pari (`f > f*`) ou sous-pari (`f < f*`) est **strictement sous-optimal**.

Ce résultat fonde le **position sizing** au cœur de la série trading QuantConnect, et
relie cette série à un théorème propre et entièrement démontré. Référence : J. L.
Kelly Jr., *A New Interpretation of Information Rate*, BSTJ (1956). Voir l'issue
[#4052](https://github.com/jsboige/CoursIA/issues/4052) (roadmap Lean
[#4038](https://github.com/jsboige/CoursIA/issues/4038), Tier 2).

## Stratégie de preuve

On évite la concavité abstraite (`StrictConcaveOn`) et l'on prouve `g(f) ≤ g(f*)`
**directement** via la tangente du logarithme en 1 :

> log t ≤ t − 1, avec égalité ssi t = 1 (version stricte : log t < t − 1 pour t ≠ 1).

En écrivant la différence de croissance comme

> g(f) − g(f*) = p·log(W_win(f) / W_win(f*)) + q·log(W_lose(f) / W_lose(f*))

où `W_win(f) = 1 + b·f` et `W_lose(f) = 1 − f` sont les multiplicateurs de richesse,
et en appliquant `log t ≤ t − 1` à chaque rapport, on obtient la **majoration clé**

> g(f) − g(f*) ≤ (f − f*)·g'(f*)

où `g'(f) = p·b/(1+bf) − q/(1−f)` est la pente du log-croissance. Or la condition du
premier ordre donne `g'(f*) = 0` (vérifiée par calcul), donc `g(f) ≤ g(f*)`.

L'**unicité** suit de la version stricte `log t < t − 1` : si `f ≠ f*`, les
multiplicateurs de richesse diffèrent (injectivité de `f ↦ 1 + b·f` et
`f ↦ 1 − f`), donc au moins un rapport diffère de 1, l'inégalité est stricte, et
`g(f) < g(f*)`.

## Modules

| Module | Contenu |
|--------|---------|
| [`Kelly/Bet.lean`](Kelly/Bet.lean) | Pari de Bernoulli `Bet` (p, b), fraction `f`, multiplicateurs de richesse `winWealth`/`loseWealth`, zone admissible `Feasible` = `(−1/b, 1)`. |
| [`Kelly/Growth.lean`](Kelly/Growth.lean) | Taux de croissance espéré `growth` et sa pente `growthGrad`. |
| [`Kelly/Kelly.lean`](Kelly/Kelly.lean) | Fraction de Kelly `kellyFrac`, condition du premier ordre `growthGrad_kelly_zero`, majoration clé `growth_diff_le`, théorèmes phares `kelly_optimal` + `kelly_unique`. |

## Théorèmes prouvés (0 sorry)

- `kelly_optimal : Feasible β f → growth β f ≤ growth β (kellyFrac β)` — `f*` maximise
  le taux de croissance espéré.
- `kelly_unique : Feasible β f → f ≠ kellyFrac β → growth β f < growth β (kellyFrac β)`
  — sur-pari et sous-pari strictement sous-optimaux (unicité du maximiseur).
- Lemmes supports : `kellyFrac_feasible` (f* ∈ (−1/b, 1)), `winWealth_kelly` /
  `loseWealth_kelly` (multiplicateurs en f*), `growthGrad_kelly_zero` (condition du
  premier ordre), `growth_diff_le` (majoration clé).

## Build

```bash
lake build Kelly          # 8496 jobs, 0 sorry, exit 0
```

Vérifié localement : `lake build Kelly` SUCCESS, `grep -rn '\bsorry\b' Kelly/` = 0,
CI `lean-kelly.yml` (`sorry-baseline: "0"`, `sorry-filter-mode: standalone-tactic`).

## Jalon ouvert (non sorry-backed)

La **concavité stricte abstraite** de `g` via `StrictConcaveOn` (vue calcul
`g''(f) < 0`) puis application du théorème du maximiseur unique de Mathlib est un
jalonn alternatif **non livré ici** : la preuve directe via la tangente `log t ≤ t − 1`
atteint le même résultat de façon plus élémentaire et 0 sorry. Généralisation aux
**distributions non-Bernoulli** (gain/perte continus, multi-issues) : ouvert, hors
périmètre du cadre canonique de Kelly (pari de Bernoulli).

## Notebook compagnon

Présentation pédagogique du position sizing / critère de Kelly (Python, paire Lean +
Python côte à côte) à venir dans la série QuantConnect. Le câblage du notebook
revient au propriétaire de la série QuantConnect (convention des lakes frères : le
lake est le livrable formel, le `lake build` est la preuve d'exécution).
