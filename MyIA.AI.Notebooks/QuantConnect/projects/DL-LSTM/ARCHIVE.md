# ARCHIVE - DL-LSTM (Deep Learning LSTM pour prédiction prix)

**Status** : ARCHIVED (substance pédagogique préservée)
**Date d'archive** : 2026-07-21
**Sharpe** : Aucun backtest QC Cloud exécuté
**Issue de reference** : #7575 (bug-class `PREEXISTING_UNEXEC` quantbooks sans `config.json`)

## Strategy Summary

Stratégie de deep learning basée sur un réseau LSTM bidirectionnel
(`torch.nn.LSTM`, 2 couches de 50 unités) pour la prédiction de prix
d'actifs US equities/ETF.

Architecture :
- Input : séquence de prix normalisés (seq_length, 1)
- Hidden : 2 couches LSTM bidirectionnelles de 50 unités
- Output : prix prédit normalisé (régression, pas classification)

Mécanisme : entraînement sur une fenêtre glissante, prédiction du prix
suivant, position long/short selon le signe de la variation prédite.

## Notes d'infrastructure

- **QC Cloud** : jamais déployé. Le `config.json` est absent du repo,
  le README confirme "Not yet deployed. Copy files to a new QC Cloud
  project to run."
- **Dépendance `torch`** : LSTM bidirectionnel PyTorch. **Hors scope
  QC Cloud** (lean engine ne supporte pas PyTorch GPU/CPU arbitraire
  via `main.py` standard). Le `main.py` peut être exécuté en local
  pour prototypage, mais n'a pas de backtest QuantConnect intégré.
- **`lstm_results.png`** (76 KB) : figure de résultat d'entraînement
  local — confirme que le modèle a été entraîné en local sur
  données de prix, mais pas backtest QC.
- **quantbook.ipynb** : 2/12 cellules non-exécutées — substance
  pédagogique préservée dans `main.py` + `lstm_results.png` + `README.md`.

## Verdict

**INTRINSIC** (limitation infrastructure QC Cloud + Lean engine) :
- Le LSTM bidirectionnel PyTorch n'est pas exécutable via le
  pipeline standard QC Cloud / Lean CLI.
- Le scaffolding est pédagogique : montre comment construire un
  LSTM pour la prédiction de séries temporelles, mais ne produit
  pas de backtest reproductible.
- L'absence de `config.json` confirme que le projet n'a jamais été
  promu en projet QC Cloud opérationnel.

À conserver comme **référence pédagogique** pour l'architecture
LSTM (input/hidden/output, bidirectionnel, normalisation) — **pas
comme source d'alpha live** (pas de backtest QC, pas de Sharpe
documenté).

## Leçons retenues

1. **Lean engine vs PyTorch arbitraire** : le moteur de backtest
   QuantConnect ne supporte pas l'import arbitraire de modèles
   PyTorch dans `main.py`. Pour backtester un LSTM, deux options :
   (a) exporter les poids en format `ONNX` et utiliser `ONNXRuntime`
   via l'API `Self.OnnxModel()`, ou (b) intégrer dans Lean via
   `AddData` + prédiction in-line sans réseau neuronal.
2. **Le scaffolding LSTM sans backtest est pédagogique seulement** :
   montrer l'architecture (bidirectionnel, normalisation, hidden size)
   est utile en cours, mais le `main.py` n'est pas une stratégie
   déployable.
3. **Le `lstm_results.png` est une preuve d'exécution locale**, mais
   pas une preuve d'edge. Aucune métrique Sharpe n'est disponible.

## Fichiers

- `main.py` (6.7 KB) — `LSTMModel` + driver `MyLstmStrategy`
- `lstm_results.png` (76 KB) — figure entraînement local
- `quantbook.ipynb` (87 KB) — exploration QuantBook (2/12 cells unexec)
- `README.md` — Description minimale (jamais déployé)

## References

- #7575 (issue parent) — bug-class `PREEXISTING_UNEXEC` quantbooks
- `scripts/quantconnect/audit_quantbooks_unexec.py` — détecteur
- ONNXRuntime QuantConnect integration : `https://www.quantconnect.com/docs/v2/cloud-platform/ide-features/importing-models`
