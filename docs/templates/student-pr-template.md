# Template de Pull Request - TP Search

Instructions pour les etudiants lors des seances de TP.

---

## Format de PR attendu

### Titre de la PR

```
TP Search-<N>: Exercice <X> - <Votre Nom>
```

Exemples valides :
- `TP Search-2: Exercice 3 - Jean Dupont`
- `TP Search-3: Exercice 1 - Marie Martin`
- `TP Search-3: Exercice 4 - Pierre Durand`

### Corps de la PR (body)

Copier-coller le modele ci-dessous et remplir les champs :

```markdown
## Exercice resolu

- **Notebook**: Search-<N>-<Titre>.ipynb
- **Exercice**: Ex<numero> - <titre court de l'exercice>
- **Etudiant**: <Prenom Nom>

## Ce que j'ai fait

<Decrivez brievement votre approche en 2-3 phrases>

## Difficultes rencontrees

<Optionnel - si vous avez eu des difficultes, expliquez ici>
```

### Exemple complet

**Titre**: `TP Search-3: Exercice 1 - Jean Dupont`

**Body**:
```markdown
## Exercice resolu

- **Notebook**: Search-3-Informed.ipynb
- **Exercice**: Ex1 - Verification d'admissibilite
- **Etudiant**: Jean Dupont

## Ce que j'ai fait

J'ai implemente la fonction check_admissibility qui parcourt toutes
les paires de villes connectees et verifie que la distance a vol
d'oiseau (heuristique) est inferieure ou egale au cout reel du trajet.

## Difficultes rencontrees

J'ai eu un moment de confusion sur la direction de la comparaison
(h doit etre <= cout reel, pas l'inverse).
```

---

## Regles

1. **Un exercice par PR** - Ne pas regrouper plusieurs exercices dans la meme PR
2. **Ne modifier que les cellules d'exercice** - Les cellules de cours et les solutions cachees ne doivent pas etre modifiees
3. **Resoudre les conflits si necessaire** - Si votre branche est en conflit avec main, faites un rebase
4. **Creer la PR depuis votre fork** - Fork le repo, créez une branche, poussez, puis ouvrez la PR

## Exercices disponibles

| Notebook | Exercices | Statut |
|----------|-----------|--------|
| Search-2-Uninformed | Ex3: BFS bidirectionnel | Ouvert |
| Search-3-Informed | Ex1: Admissibilite, Ex2: Heuristique non-admissible, Ex3: MST/TSP, Ex4: Pathfinding grille | Ouvert |

## Bonus

Chaque exercice valide (+0.5 point) sera ajoute a votre note de TP.
