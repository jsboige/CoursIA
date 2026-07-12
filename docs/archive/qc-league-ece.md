# QC League / Strategies — Mobilisation ECE

## Contexte

QuantConnect a annonce fin 2025 que la **Quant League** classique (competitions trimestrielles) devient **Strategies** — une plateforme permanente de partage et decouverte de strategies quantitatives. Q4-2025 etait la derniere edition League au format traditionnel.

**Impact pour les etudiants** : le format Strategies est en fait plus avantageux :
- URLs permanentes pour chaque entree (portfolio employeur)
- Suivi out-of-sample automatique
- Pas de deadline trimestrielle — publication quand la strategy est prete
- Visibilite aupres des recruteurs du secteur

## Communication de mobilisation (brouillon)

> **Sujet :** QuantConnect Strategies — Valorisez vos projets de trading algorithmique
>
> Bonjour a tous,
>
> Vous avez developpe des strategies quantitatives cette annee dans le cadre du Projet 2. Plusieurs d'entre vous ont obtenu des resultats remarquables (Sharpe > 0.5 out-of-sample) sur des approches originales : HMM + K-Means, ML multi-feature, Causal ML, VAE-HMM.
>
> **QuantConnect lance "Strategies"**, une plateforme ou vous pouvez publier vos algorithmes avec un suivi permanent des performances. Contrairement a l'ancien format competition, Strategies vous donne :
> - Une **URL permanente** que vous pouvez mettre sur votre CV et LinkedIn
> - Un **suivi out-of-sample** automatique (vos resultats sont verifies)
> - Une **visibilite aupres des recruteurs** du secteur financier et tech
>
> **Comment participer :**
> 1. Creez un compte gratuit sur [quantconnect.com](https://www.quantconnect.com)
> 2. Importez votre strategy (Python ou C#)
> 3. Lancez un backtest et verifiez les metriques (Sharpe, max drawdown, CAGR)
> 4. Publiez sur Strategies quand vous etes satisfait du resultat
>
> **Ressources disponibles :**
> - 27 notebooks progressifs (QC-Py-01 a QC-Py-Cloud-XX) dans le depot du cours
> - 50+ strategies de reference avec code source et research notebooks
> - Consultations possibles sur rendez-vous
>
> Les etudiants interessee peuvent me contacter directement.
>
> Cordialement,

## Projets etudiants prometteurs (Projet 2)

Source : issue #238

| Groupe | Approche | Points forts | Sharpe OOS |
|--------|----------|-------------|------------|
| Brusset | HMM + K-Means voting regime detection | Originalite du regime detection par vote | A verifier |
| Balssa | 23-feature ML stock selection (RF+GB ensemble) | Feature engineering ambitieux | 0.553 |
| ErwanSi | Causal ML event alpha by sector (DML+CausalForest+DoWhy) | Approche causale rare en quant | A verifier |
| Maisonnave | VAE-HMM forward-filter + feature engineering | Architecture neurale originale | A verifier |

**Action** : inviter ces groupes en priorite a publier sur Strategies, avec accompagnement si necessaire.

## Guide rapide — Publier sur QuantConnect Strategies

### 1. Creer un compte

- Aller sur [quantconnect.com](https://www.quantconnect.com) > Sign Up
- Compte gratuit, 2h de backtest/jour
- Verifier l'email pour activer le compte

### 2. Premiere strategy

```
Organisation → Create Project → Algorithm (Python ou C#)
```

Le template de base genere un skeleton fonctionnel. Modifier le fichier `main.py` avec votre strategy.

### 3. Lancer un backtest

- Cliquer "Build" (verification syntaxe)
- Puis "Backtest" (execution sur donnees historiques)
- Verifier les metriques dans le rapport :
  - **Sharpe Ratio** > 0.5 = bon depart
  - **Max Drawdown** < 30% = risque acceptable
  - **CAGR** > 10% = performance solide

### 4. Publier sur Strategies

Depuis le backtest reussi → "Share to Strategies" (ou equivalent dans la nouvelle interface).

### 5. Ressources du cours

| Ressource | Chemin | Description |
|-----------|--------|-------------|
| Notebooks progressifs | `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-01` a `QC-Py-32` | Debutant a avance |
| Strategies de reference | `MyIA.AI.Notebooks/QuantConnect/projects/` | 50+ strategies avec research |
| Livre de reference | *Hands-On AI Trading* (Jared Broad) | Support du cours |
| Documentation QC | [docs.quantconnect.com](https://www.quantconnect.com/docs) | API, Lean engine |

### Metriques a surveiller

| Metrique | Seuil | Signification |
|----------|-------|---------------|
| Sharpe Ratio | > 0.5 | Ratio rendement/risque acceptable |
| Max Drawdown | < 30% | Perte maximale tolerable |
| CAGR | > 10% | Rendement annuel compose |
| Win Rate | > 50% | Pourcentage de trades gagnants |
| Beta | < 1.0 | Correlation avec le marche |
| Alpha | > 0 | Rendement excendentaire vs benchmark |

## Actions pending

- [ ] Confirmer le format exact de publication Strategies (interface peut avoir evolue)
- [ ] Identifier les etudiants Projet 2 avec les meilleurs resultats OOS
- [ ] Envoyer la communication via Teams/email
- [ ] Organiser une session pratique (1-2h) pour les etudiants interesses
- [ ] Suivi : nombre de strategies publiees par les etudiants ECE
