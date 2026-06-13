# Mon Premier Projet Foundry — Counter

Projet Foundry créé dans le cadre du notebook [SC-1-Setup-Foundry](../00-Foundations/SC-1-Setup-Foundry.ipynb). Premier contrat Solidity avec tests unitaires.

## Contrat : Counter.sol

Compteur simple en Solidity 0.8.28 avec protection contre l'underflow.

| Fonction | Type | Description |
|----------|------|-------------|
| `increment()` | `public` | Augmente `count` de 1 |
| `decrement()` | `public` | Diminue `count` de 1 (revert si `count == 0`) |
| `getCount()` | `public view` | Retourne la valeur de `count` |
| `count()` | `public view` | Getter automatique (variable `public`) |

**Protection underflow** : `require(count > 0, "Cannot decrement below zero")` empêche le décrément en dessous de zéro. Solidity 0.8+ a des checks natifs pour l'underflow arithmétique, mais le require explicite fournit un message d'erreur clair.

## Tests : Counter.t.sol

4 tests Foundry couvrant les cas nominal et edge :

| Test | Cas de test |
|------|-------------|
| `testIncrement` | Incrémentation successive (0 -> 1 -> 2) |
| `testDecrement` | Décrémentation (2 -> 1) |
| `testDecrementZero` | Revert attendu quand `count == 0` |
| `testPublicGetter` | Cohérence entre `count()` (auto) et `getCount()` (explicite) |

## Utilisation

```bash
# Compiler
forge build

# Lancer les tests
forge test -vv

# Formater
forge fmt
```

## Structure

```
mon-premier-projet/
├── src/
│   └── Counter.sol          # Contrat Counter
├── test/
│   └── Counter.t.sol        # Tests Foundry
├── script/
│   └── Counter.s.sol        # Script de déploiement
├── foundry.toml              # Configuration Foundry
└── README.md
```

## Documentation Foundry

- [Foundry Book](https://book.getfoundry.sh/) — documentation officielle
- [Forge CLI](https://book.getfoundry.sh/reference/forge/) — commandes forge
- [Testing](https://book.getfoundry.sh/forge/tests) — guide de test Foundry

## Auteurs

Nabil Chartouni, Lucas Majerczyk, Wilfrid Wangon Zekou — TP Smart Contracts 2026.
