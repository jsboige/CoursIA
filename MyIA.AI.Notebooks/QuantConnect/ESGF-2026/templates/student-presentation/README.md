# Template Presentation Soutenance ESGF

## Utilisation

1. Copier `slides.md` dans votre repertoire de projet
2. Remplacer les sections `[entre crochets]` avec votre contenu
3. Ajouter vos graphiques (equity_curve.png, etc.) dans le meme repertoire
4. Lancer la presentation :

```bash
npx slidev slides.md
```

## Sections obligatoires

| Slide | Section | Contenu attendu |
|-------|---------|-----------------|
| 1 | Titre | Nom strategie, equipe |
| 2 | Plan | Sommaire |
| 3 | Introduction | Motivation, hypothese |
| 4 | Donnees | Actifs, periode, preprocessing |
| 5 | Modele alpha | Indicateurs, signaux, risk management |
| 6-7 | Resultats | Equity curve + metriques |
| 8 | Analyse | Points forts/faibles, vs benchmark |
| 9 | Robustesse | Sous-periodes, sensibilite |
| 10 | Conclusion | Bilan,改进 |

## Timing

- Objectif : 10 minutes +/- 1 minute
- ~1 minute par slide (10 slides de contenu)
- Ne pas lire les slides : utiliser des mots-cles et parler

## Conseils

- Graphiques : toujours avec legende, axes labels, et titre
- Metriques : tableau comparatif avec benchmark
- Equity curve : avec drawdown en dessous
- Ne pas montrer de code dans les slides (sauf snippet court pour illustration)
