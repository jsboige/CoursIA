# MyIA.Trading.Converter (E1 #7265)

Port verbatim du convertisseur **TradeConverter** depuis le fork public
[`MyIntelligenceAgency/Lean`](https://github.com/MyIntelligenceAgency/Lean),
branche `MyIABacktesting_integration` (sha `612dddf9`).

## Scope E1

**Objectif** : démontrer la conversion d'un CSV OHLCV local (Stooq, EODHD, ou
toute source quotidienne gratuite) vers le format dossier Lean officiel, sans
dépendre du paywall **Security Master** de QuantConnect (≈ 600 USD/an).

**Démo incluse** : `Demo.ConvertOhlcvCsvToLeanZip(inputCsv, outputZip, resolution)`
utilise l'API publique `TradeConverter.SaveTradingData<Tickbar>` pour produire
un `.zip` au format Lean daily OU hourly (même format `yyyyMMdd HH:mm` pour
les deux résolutions — la différence daily/hourly est dans le **dossier de
destination** côté Lean Engine, pas dans le format interne du CSV) :

```
yyyyMMdd HH:mm,Open,High,Low,Close,Volume
```

Le format de référence (10 colonnes avec bid/ask) est documenté dans :

- daily → [`partner-course-quant-trading/lean-workspace/data/cfd/oanda/daily/xauusd.zip`](../../MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/data/cfd/oanda/daily/xauusd.zip)
- hourly → [`partner-course-quant-trading/lean-workspace/data/cfd/oanda/hour/xauusd.zip`](../../MyIA.AI.Notebooks/QuantConnect/partner-course-quant-trading/lean-workspace/data/cfd/oanda/hour/xauusd.zip)

La démo produit les 6 premières colonnes (OHLCV), suffisant pour les
stratégies OHLCV-only de l'EPIC #6891.

## Usage

```bash
# Build
dotnet build MyIA.AI.Shared/MyIA.Trading.Converter

# Démo : CSV OHLCV local -> Lean daily zip
dotnet run --project MyIA.AI.Shared/MyIA.Trading.Converter -- ohlcv2lean \
    <input.csv> <output.zip> [daily|hourly]
```

L'argument `[daily|hourly]` est **optionnel** : s'il est omis, la résolution
est déduite du nom de fichier (`*_hourly*` → hourly, sinon daily).

Format CSV OHLCV attendu (header ligne 1) :

```csv
Date,Open,High,Low,Close,Volume[,Spread,BidOpen,...]
2020-01-02,1.12150,1.12250,1.12000,1.12200,12345[,0.00012,1.12140,...]
```

Colonnes 6+ (spread, bid/ask, etc.) sont **ignorées** par `Demo.LoadOhlcvCsv`.

## Mode legacy upstream

Le mode CLI historique (`Process()`) reste accessible via
`dotnet run --project MyIA.AI.Shared/MyIA.Trading.Converter` sans argument —
il charge `ConverterConfig.json` et exécute la pipeline verbatim. Voir
[`exemples/ConverterConfig.daily.json`](exemples/ConverterConfig.daily.json)
pour une config typique.

## Limites & dette technique honnête

| Limite | Cause | Solution future |
|--------|-------|-----------------|
| Démo produit **6 colonnes** (OHLCV) vs **10 colonnes** Lean daily complètes (avec bid/ask) | `Demo` mappe directement `Tickbar` 6 props sur CSV OHLCV ; pas de source bid/ask gratuite | Étendre `Demo` pour consommer 14 colonnes source (eurusd_daily.csv les fournit) |
| `CompressionLibrary.SevenZipSharp` nécessite `7z-x64.dll` runtime chargé correctement | Native lib path resolution Windows | Démo utilise `SharpCompress` (managed pure) par défaut ; SevenZipSharp reste pour usage avancé |
| TradeConverter upstream attend `Trade` (UnixTime+Price+Amount), pas OHLCV | Conçu pour data haute fréquence | Démo utilise `SaveTradingData<Tickbar>` (autre overload) qui accepte OHLCV directement |
| Factor files / map files non gérés | Hors scope convertisseur original | Ref. Lean Engine : `Data/<mkt>/<sym>/factor_files/factor_file.csv` |

## Diff vs upstream

| Aspect | Upstream (fork public) | CoursIA port |
|--------|------------------------|---------------|
| TargetFramework | `net6.0` | `net9.0` (convention repo) |
| HintPaths ZeroFormatter.dll | HintPath local | PackageReference `ZeroFormatter` 1.6.4 |
| HintPaths Admin (`.nuget\packages\sevenzipextractor\`) | Présents | Retirés (PackageReference suffit) |
| Nullable | enable (contexte) | disable (verbatim upstream) |
| ImplicitUsings | enable | disable (verbatim upstream) |
| Code source | Verbatim | Verbatim (pas de modification de la logique) |

**License** : MIT (cf upstream).

## Validation

```bash
# Test démo avec dataset interne CoursIA — daily (3 487 tickbars, 2007-03-30 → 2024-...)
dotnet run -- ohlcv2lean \
    MyIA.AI.Notebooks/QuantConnect/datasets/forex/eurusd_daily.csv \
    DemoOutput/eurusd_trade.zip
# Sortie : Wrote 3487 tickbars to .../eurusd_trade.zip (Lean daily format)

# Test démo hourly (69 928 tickbars — résolu auto depuis le nom *_hourly.csv)
dotnet run -- ohlcv2lean \
    MyIA.AI.Notebooks/QuantConnect/datasets/forex/eurusd_hourly.csv \
    DemoOutput/eurusd_hourly_trade.zip
# Sortie : Wrote 69928 tickbars to .../eurusd_hourly_trade.zip (Lean hourly format)

# Vérif format Lean daily (no header, 6 colonnes OHLCV+vol)
unzip -p DemoOutput/eurusd_trade.zip eurusd_trade | head -3
# Attendu : 20070330 00:00,1.33145,1.34005,1.3288,1.3357999999999999,...

# Vérif format Lean hourly (variable hour, même format de colonnes)
unzip -p DemoOutput/eurusd_hourly_trade.zip eurusd_hourly_trade | head -3
# Attendu : 20070330 00:00,1.33145,1.33235,1.33135,1.3319999999999999,...
```

**Benchmarks mesurés** (SharpCompress, .NET 9.0, Windows 11) :

| CSV | Lignes | Load | Serialize | Compress | Total |
|-----|--------|------|-----------|----------|-------|
| `eurusd_daily.csv` | 3 487 | 0.46 s | 0.08 s | 0.07 s | ~0.6 s |
| `eurusd_hourly.csv` | 69 928 | 4.19 s | 0.45 s | 0.43 s | ~5.1 s |

Le format interne est **identique** daily/hourly (les zips Lean de référence
le confirment). Le différentiateur daily/hourly est le dossier de destination
côté Lean Engine (`data/cfd/oanda/daily/` vs `data/cfd/oanda/hour/`).

## Liens

- Source upstream : https://github.com/MyIntelligenceAgency/Lean/tree/MyIABacktesting_integration
- EPIC parent #7265 : ordre A→E d'atterrissage des modules Aricie dans `MyIA.AI.Shared/`
- EPIC débloqué : #6891 (stratégies QC OHLCV-only sans Security Master paywall)
- Format cible : cf `partner-course-quant-trading/lean-workspace/data/cfd/oanda/daily/`