# Modèle de Présentation Étudiant

## Utilisation

1. Copier `slides.md` dans le répertoire de votre projet
2. Remplacer les `[sections entre crochets]` par votre contenu
3. Ajouter vos graphiques (`equity_curve.png`, etc.) dans le même répertoire
4. Lancer la présentation :

```bash
npx slidev slides.md
```

## Sections requises

| Diapositive | Section | Contenu attendu |
|-------------|---------|-----------------|
| 1 | Titre | Nom de la stratégie, équipe |
| 2 | Plan | Table des matières |
| 3 | Introduction | Motivation, hypothèse |
| 4 | Données | Actifs, période, prétraitement |
| 5 | Modèle alpha | Indicateurs, signaux, gestion du risque |
| 6-7 | Résultats | Courbe d'équité + métriques |
| 8 | Analyse | Forces/faiblesses, vs référence |
| 9 | Robustesse | Sous-périodes, sensibilité |
| 10 | Conclusion | Résumé, améliorations |

## Gestion du temps

- Objectif : 10 minutes +/- 1 minute
- environ 1 minute par diapositive (10 diapositives de contenu)
- Ne pas lire les diapositives : utiliser des mots-clés et parler naturellement

## Conseils

- Graphiques : toujours avec légende, étiquettes d'axes et titre
- Métriques : tableau comparatif avec la référence
- Courbe d'équité : avec le drawdown en dessous
- Ne pas montrer de code dans les diapositives (sauf court extrait pour illustration)

---

*Version anglaise (snapshot) : [`README.en.md`](README.en.md).*
