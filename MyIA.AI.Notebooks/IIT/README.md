# IIT - Integrated Information Theory

<!-- CATALOG-STATUS
series: IIT
pedagogical_count: 2
breakdown: root=2
maturity: PRODUCTION=2
-->

La conscience est-elle mesurable ? La Théorie de l'Information Intégrée (IIT), proposée par Giulio Tononi, répond oui : un système est conscient dans la mesure où il intègre de l'information de manière non réductible. Plus formellement, la quantité de conscience d'un système correspond à la valeur **Phi** (big Phi), qui mesure le degré d'intégration causale irréductible. Cette série vous apprend à calculer cette mesure avec **PyPhi**, la bibliothèque de référence du laboratoire Tononi, et à explorer la géométrie informationnelle des systèmes complexes.

Le premier notebook couvre le spectre fondamental : construction de graphes causaux binaires, calcul des Transition Probability Matrices (TPM), définition des sous-systèmes, extraction des Cause-Effect Structures (CES), et exploration des macro-subsystemes. Le second approfondit les aspects avancés : partitionnement MIP, repertoires cause-effet, MICE, comparaison big Phi vs small phi, reseaux elargis a 4+ noeuds, coarse-graining et apercu IIT 4.0.

**À qui s'adresse cette série** : étudiants en sciences cognitives, neuroscience computationnelle, et philosophie de l'esprit. Les notebooks (~60-90 min chacun) nécessitent Python 3.9 avec `pyphi` (installé via conda env dédié). Une familiarité avec les graphes et la logique booléenne suffit. Il constitue un complément théorique aux séries [Probas](../Probas/README.md) (modèles probabilistes) et [GameTheory](../GameTheory/README.md) (systèmes multi-agents), avec lesquelles il partage les concepts de causalité et d'interaction.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 2 |
| Kernel | Python 3 (PyPhi/IIT) |
| Duree estimee | ~120-180 min |
| Version | PyPhi 1.2.0+ |

## Notebook

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 1 | [Intro_to_PyPhi](Intro_to_PyPhi.ipynb) | Introduction complète à PyPhi et IIT | 60-90 min |
| 2 | [IIT-2-AdvancedTopics](IIT-2-AdvancedTopics.ipynb) | Partitionnement MIP, repertoires, MICE, reseaux elargis | 60-90 min |

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

### IIT-2-AdvancedTopics.ipynb

| Section | Contenu |
|---------|---------|
| Rappels | Reprise des concepts du notebook 1 |
| Partitionnement MIP | Coupes minimales d'information, bipartitions |
| Repertoires cause-effet | Distributions cause, effet, non-perturbees |
| MICE et concepts | Mechanismes maximalement irreductibles |
| Big Phi vs Small Phi | Comparaison niveau systeme vs mecanisme |
| Reseaux elargis | Systemes 4+ noeuds, interpretation |
| Performance | Coarse-graining, timing, complexite |
| IIT 4.0 | Concept-style, evolutions recentes, debats |

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
# Automated setup (creates conda env + registers kernel)
powershell -File scripts/setup_pyphi_env.ps1

# Manual setup (Python 3.9 required for PyPhi 1.2.0)
conda create --name pyphi python=3.9 -y
conda activate pyphi
pip install pyphi==1.2.0 numpy scipy ipykernel
python -m ipykernel install --user --name pyphi --display-name "Python 3 (PyPhi/IIT)"
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
| `ImportError: cannot import name 'Iterable'` | PyPhi 1.2.0 utilise `collections.Iterable` (supprime Python 3.10+) | Utiliser Python 3.9 (`conda create -n pyphi python=3.9`) |
| StateUnreachableError | Etats inaccessibles | Configuration `VALIDATE_SUBSYSTEM_STATES` |
| Performance | Phi calcul intensif pour grands reseaux | Limiter taille des reseaux |

## Theorie IIT

La Theorie de l'Information Integree (IIT) propose une approche mathematique de la conscience :

1. **Information** : Un systeme conscient doit specifier un grand nombre d'etats possibles
2. **Integration** : L'information doit etre integree (non decomposable)
3. **Exclusion** : Un seul niveau de Phi domine a tout moment

**Phi** mesure le degre d'integration informationnelle d'un systeme. Un Phi > 0 indique une integration irreductible, suggerant une forme de conscience.

## Portee scientifique et debats

L'IIT n'est pas qu'une speculation philosophique : elle a engendre des outils utilises en clinique et alimente l'un des debats les plus vifs des neurosciences.

- **Mesure clinique de la conscience.** Le *Perturbational Complexity Index* (PCI), inspire des principes de l'IIT, est utilise pour evaluer la conscience chez des patients non communicants (coma, etat vegetatif, anesthesie). Le protocole « zap-and-zip » (stimulation TMS + EEG, compression de la reponse) distingue empiriquement les etats conscients des etats inconscients — une retombee concrete et reproductible d'une theorie de la conscience.
- **Une theorie concurrente.** L'IIT s'oppose frontalement aux theories de type *Global Workspace* (Dehaene, Baars), qui font de la conscience une diffusion globale de l'information plutot qu'une integration causale locale. Des programmes de tests adversariaux (collaboration Templeton) confrontent leurs predictions sur des donnees reelles.
- **Enjeu pour l'IA.** L'IIT predit qu'un reseau purement *feed-forward* (comme l'inference d'un LLM classique) a un Phi nul : il calcule sans « etre » conscient, faute de boucles causales integrees. Cette these est centrale dans les discussions sur la conscience artificielle.
- **Controverse.** Le calcul exact de Phi est computationnellement intractable au-dela de petits reseaux (d'ou le coarse-graining du notebook), et la theorie a fait l'objet d'une critique publique retentissante (lettre ouverte de 2023 la qualifiant de « pseudoscience ») — un cas d'ecole pour discuter des criteres de scientificite d'une theorie de l'esprit.

Ces tensions font de l'IIT un excellent terrain pour exercer l'esprit critique : on y manipule un formalisme precis (calculable avec PyPhi) tout en gardant a l'esprit les limites de son interpretation.

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
├── Intro_to_PyPhi.ipynb        # Notebook 1 : introduction
├── IIT-2-AdvancedTopics.ipynb  # Notebook 2 : sujets avances
├── scripts/
│   ├── setup_pyphi_env.ps1     # Setup conda env + kernel
│   └── build_notebook.py       # Script de construction notebook 2
└── README.md                   # Cette documentation
```

## Licence

Voir la licence du repository principal.

## Cross-series Bridges

| Serie | Lien | Connection |
|-------|------|-------------|
| [Probas](../Probas/README.md) | Infer.NET / Pyro | Modeles probabilistes partagent les memes fondements que la mesure d'integration (phi) |
| [GameTheory](../GameTheory/README.md) | OpenSpiel | Jeux cooperatifs et choix social eclairent la complexite de l'interaction multi-agent |
| [SymbolicAI/Lean](../SymbolicAI/Lean/README.md) | Preuves formelles | Preuves Arrow/Sen montrent comment formaliser des proprietes structurelles |
