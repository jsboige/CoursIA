# IIT - Integrated Information Theory

Introduction a la Theorie de l'Information Integree (IIT) avec PyPhi, une bibliotheque Python pour le calcul de Phi et l'analyse de la conscience computationnelle.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 1 |
| Kernel | Python 3 |
| Duree estimee | ~60-90 min |

## Notebook

| Notebook | Contenu | Duree |
|----------|---------|-------|
| [Intro_to_PyPhi](Intro_to_PyPhi.ipynb) | Introduction complete a PyPhi et IIT | 60-90 min |

## Contenu detaille

### Intro_to_PyPhi.ipynb

| Section | Contenu |
|---------|---------|
| Installation | Configuration PyPhi, environnement conda |
| Reseaux | Creation de circuits/graphes, noeuds binaires |
| TPM | Transition Probability Matrices, regles d'evolution |
| Subsystemes | Definition, calcul de Phi |
| CES | Cause-Effect Structures, mecanismes |
| Causation actuelle | Liens causaux entre elements |
| Macro-subsystemes | Coarse-graining, blackboxing |

## Concepts cles

| Concept | Explication | Analogie |
|---------|-------------|----------|
| **TPM** | Regles d'evolution du systeme | Lois de la physique |
| **Etat** | Configuration binaire des noeuds (0 ou 1) | Instantane cerebral |
| **Phi (Big Phi)** | Niveau d'integration du systeme | Force d'un noeud de corde |
| **MIP** | Point faible du systeme (Minimum Information Partition) | Maillon le plus faible |
| **CES** | Geometrie informationnelle | Forme d'une pensee |

## Prerequis

### Connaissances requises

- Python de base (imports, fonctions, tableaux)
- Logique booleenne (etats binaires 0, 1)
- Notions de theorie des graphes (noeuds, connexions)

### Environnement Python

```bash
# Environnement conda recommande (Python 3.7-3.9)
conda create --name pyphi python=3.9 -y
conda activate pyphi
pip install pyphi numpy scipy
```

### Dependances

| Package | Version | Utilisation |
|---------|---------|-------------|
| pyphi | 1.2.0+ | Calculs IIT |
| numpy | 1.21.6+ | Calcul numerique |
| scipy | 0.13.3+ | Fonctions scientifiques |

## Limitations connues

| Probleme | Cause | Solution |
|----------|-------|----------|
| Conflits numpy/scipy | Python 3.10+ incompatible | Utiliser Python 3.7-3.9 |
| StateUnreachableError | Etats inaccessibles | Configuration `VALIDATE_SUBSYSTEM_STATES` |
| Performance | Phi calcul intensif pour grands reseaux | Limiter taille des reseaux |

## Theorie IIT

La Theorie de l'Information Integree (IIT) propose une approche mathematique de la conscience :

1. **Information** : Un systeme conscient doit specifier un grand nombre d'etats possibles
2. **Integration** : L'information doit etre integree (non decomposable)
3. **Exclusion** : Un seul niveau de Phi domine a tout moment

**Phi** mesure le degre d'integration informationnelle d'un systeme. Un Phi > 0 indique une integration irreductible, suggerant une forme de conscience.

## Ressources

### Documentation PyPhi

- [PyPhi Documentation officielle](https://pyphi.readthedocs.io/en/stable/)
- [PyPhi GitHub](https://github.com/wmayner/pyphi)
- [Exemples PyPhi](https://github.com/wmayner/pyphi/tree/master/examples)

### Fondements theoriques

- Tononi, G. (2008) - *Consciousness as Integrated Information*
- Oizumi, M., Albantakis, L., Tononi, G. (2014) - *From the Phenomenology to the Mechanisms of Consciousness*

## Structure des fichiers

```
IIT/
├── Intro_to_PyPhi.ipynb    # Notebook principal
└── README.md               # Cette documentation
```

## Licence

Voir la licence du repository principal.
