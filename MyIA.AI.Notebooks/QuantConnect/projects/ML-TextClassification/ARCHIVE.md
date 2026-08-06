# ARCHIVE - ML-TextClassification (Naive Bayes sentiment simulé)

**Status** : ARCHIVED (substance pédagogique préservée)
**Date d'archive** : 2026-07-21
**Sharpe** : Aucun backtest QC Cloud exécuté
**Issue de reference** : #7575 (bug-class `PREEXISTING_UNEXEC` quantbooks sans `config.json`)

## Strategy Summary

Stratégie de classification de texte (NLP) sur actualités financières
via `sklearn.naive_bayes.MultinomialNB` (Naive Bayes multinomial) pour
prédire le sentiment de marché (positif/négatif/neutre) et générer un
signal de trading directionnel sur actions US.

Architecture :
- Input : corpus de news sentiment (NLP features)
- Hidden : TF-IDF vectorizer + MultinomialNB classifier
- Output : sentiment prédit (3-classes) → position directionnelle
- Univers : actions US large-cap (secteur tech/finance)
- Rebalance : Daily sur signal news

Mécanisme : TF-IDF sur corpus news → classifieur Naive Bayes →
probabilités sentiment → agrégation signal → position long/short/cash.

## Notes d'infrastructure

- **QC Cloud** : jamais déployé. Le `config.json` est absent du repo,
  le README confirme "Not yet deployed. Copy files to a new QC Cloud
  project to run."
- **Dépendance NLP** : le `main.py` documente l'usage de news via
  Quandl (`Quandl()`) ou une source interne simulée. Le module de
  sentiment simulé dans `quantbook.ipynb` (10/14 cells unexec) n'a
  pas de source NLP réelle branchée.
- **quantbook.ipynb** : 10/14 cellules non-exécutées — substance
  pédagogique préservée dans `main.py` (8.5 KB, `MLTextClassificationAlgorithm`)
  + `README.md`.

## Verdict

**INTRINSIC** (substance pédagogique, jamais déployé) :
- Le projet est un **squelette fonctionnel** du pattern "ML
  NLP-sentiment sur actualité financière".
- Le sentiment simulé (placeholder dans `quantbook.ipynb`) n'est
  pas une vraie source NLP — c'est un **abus pédagogique** qu'il
  faut signaler clairement aux étudiants : *"naive Bayes sur
  sentiment simulé != naïve Bayes sur news réelles"*.
- Pas de backtest QC, pas de Sharpe documenté.
- L'absence de `config.json` confirme que le projet n'a jamais
  été promu en projet QC Cloud opérationnel.

À conserver comme **référence pédagogique** pour le pattern ML
NLP-sentiment appliqué au trading — **pas comme source d'alpha
live** (sentiment simulé, pas déployé, pas backtesté).

## Leçons retenues

1. **Sentiment simulé ≠ sentiment réel** : le scaffolding Naive
   Bayes + TF-IDF est valide en soi, mais appliqué à un corpus
   simulé (placeholder), il **n'apprend rien d'utilisable**. C'est
   un contre-exemple pédagogique utile : montre que le pipeline
   ML peut s'exécuter proprement sans produire d'edge.
2. **Naive Bayes sur features TF-IDF** : choix classique pour
   classification de texte, mais limité sur séries temporelles
   financières (bruit de fond élevé, classes déséquilibrées).
3. **Le scaffolding sentiment sans source NLP est une promesse
   vide** : pour passer à un vrai déploiement, il faudrait
   brancher une source NLP réelle (news API payante, Tiingo
   News, Alpha Vantage News, etc.), ce qui constitue un
   `RECOVERABLE-USER-HAND` (API key, coûts).

## Fichiers

- `main.py` (8.5 KB) — `MLTextClassificationAlgorithm`
- `quantbook.ipynb` (38 KB) — exploration QuantBook (10/14 cells unexec)
- `README.md` — Description + avertissement "Not yet deployed"

## References

- #7575 (issue parent) — bug-class `PREEXISTING_UNEXEC` quantbooks
- `scripts/quantconnect/audit_quantbooks_unexec.py` — détecteur
- `.claude/rules/sota-not-workaround.md` — Prong-A vrai outil SOTA,
  pas un placeholder maquillé en résultat