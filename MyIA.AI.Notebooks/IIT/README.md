# IIT - Integrated Information Theory

<!-- CATALOG-STATUS
series: IIT
pedagogical_count: 2
breakdown: root=2
maturity: PRODUCTION=2
-->

La conscience est-elle mesurable ? La Theorie de l'Information Integree (IIT), proposee par Giulio Tononi, repond oui : un systeme est conscient dans la mesure ou il integre de l'information de maniere non reductible. Plus formellement, la quantite de conscience d'un systeme correspond a la valeur **Phi** (big Phi), qui mesure le degre d'integration causale irreductible. Cette serie vous apprend a calculer cette mesure avec **PyPhi**, la bibliotheque de reference du laboratoire Tononi, et a explorer la geometrie informationnelle des systemes complexes.

Le premier notebook couvre le spectre fondamental : construction de graphes causaux binaires, calcul des Transition Probability Matrices (TPM), definition des sous-systemes, extraction des Cause-Effect Structures (CES), et exploration des macro-subsystemes. Le second approfondit les aspects avances : partitionnement MIP, repertoires cause-effet, MICE, comparaison big Phi vs small phi, reseaux elargis a 4+ noeuds, coarse-graining et apercu IIT 4.0.

**A qui s'adresse cette serie** : etudiants en sciences cognitives, neuroscience computationnelle, et philosophie de l'esprit. Les notebooks (~60-90 min chacun) necessitent Python 3.9 avec `pyphi` (installe via conda env dedie). Une familiarite avec les graphes et la logique booleenne suffit. Il constitue un complement theorique aux series [Probas](../Probas/README.md) (modeles probabilistes) et [GameTheory](../GameTheory/README.md) (systemes multi-agents), avec lesquelles il partage les concepts de causalite et d'interaction.

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Construire et manipuler des reseaux causaux** binaires avec PyPhi (TPM, noeuds, connexions)
2. **Calculer Phi** pour un sous-systeme et interpreter sa valeur (integration vs separabilite)
3. **Analyser une Cause-Effect Structure (CES)** : identifier les concepts, mecanismes et purviews
4. **Appliquer le partitionnement MIP** pour localiser le "maillon faible" d'un systeme
5. **Differencier big Phi et small phi** et comprendre leur roles respectifs dans la theorie
6. **Evaluer les limites computationnelles** de l'IIT et les strategies de coarse-graining
7. **Discuter les implications philosophiques** de l'IIT pour la conscience artificielle

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 2 |
| Kernel | Python 3 (PyPhi/IIT) |
| Duree estimee | ~120-180 min |
| Version | PyPhi 1.2.0+ |

## Notebooks

| # | Notebook | Contenu | Duree |
|---|----------|---------|-------|
| 1 | [Intro_to_PyPhi](Intro_to_PyPhi.ipynb) | Introduction complete a PyPhi et IIT | 60-90 min |
| 2 | [IIT-2-AdvancedTopics](IIT-2-AdvancedTopics.ipynb) | Partitionnement MIP, repertoires, MICE, reseaux elargis | 60-90 min |

## Parcours recommandes

```
Notebook 1 (Fondements)
    |
    v
Notebook 2 (Sujets avances)
```

| Objectif | Parcours |
|----------|----------|
| Decouverte rapide | Notebook 1 seul |
| Maitrise complete | Notebook 1 puis 2 |
| Focus philosophie | Notebook 1 (sections CES + debats) + Notebook 2 (section IIT 4.0) |

### Parcours d'apprentissage

**Phase 1 : Fondements (~90 min, notebook 1)**

Vous installez PyPhi dans un environnement conda dedie (Python 3.9 obligatoire), puis construisez votre premier reseau causal binaire. Le calcul de Phi sur un reseau XOR a 3 noeuds illustre concretement la notion d'integration irreductible. L'exploration de la CES revele comment un systeme "specifie" sa propre geometrie informationnelle. Les 4 exercices vous font varier les sous-systemes, les topologies de reseau et les parametres pour developper une intuition sur ce qui fait monter ou baisser Phi.

**Phase 2 : Approfondissement (~90 min, notebook 2)**

Le deuxieme notebook deconstruit le calcul de Phi : vous manipulez les bipartitions (MIP), les repertoires cause-effet, et les MICE (Maximally Irreducible Cause or Effect). La comparaison big Phi vs small phi clarifie les deux niveaux d'analyse. L'extension a des reseaux a 4+ noeuds montre l'explosion combinatoire et justifie le coarse-graining. L'apercu IIT 4.0 ouvre sur les evolutions recentes de la theorie. Les 3 exercices testent votre comprehension des repertoires, du Phi multi-etats et des reseaux feed-forward (Phi = 0 attendu).

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
| **Small phi** | Integration d'un mecanisme individuel | Tension d'un fil du noeud |
| **MIP** | Point faible du systeme (Minimum Information Partition) | Maillon le plus faible |
| **CES** | Geometrie informationnelle (Cause-Effect Structure) | Forme d'une pensee |
| **MICE** | Mechanisme maximalement irreductible | Brique elementaire de conscience |
| **Purview** | Ensemble de noeuds sur lesquels un mecanisme specifie de l'information | Champ d'influence |

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

- **Mesure clinique de la conscience.** Le *Perturbational Complexity Index* (PCI), inspire des principes de l'IIT, est utilise pour evaluer la conscience chez des patients non communicants (coma, etat vegetatif, anesthesie). Le protocole "zap-and-zip" (stimulation TMS + EEG, compression de la reponse) distingue empiriquement les etats conscients des etats inconscients — une retombee concrete et reproductible d'une theorie de la conscience.
- **Une theorie concurrente.** L'IIT s'oppose frontalement aux theories de type *Global Workspace* (Dehaene, Baars), qui font de la conscience une diffusion globale de l'information plutot qu'une integration causale locale. Des programmes de tests adversariaux (collaboration Templeton) confrontent leurs predictions sur des donnees reelles.
- **Enjeu pour l'IA.** L'IIT predit qu'un reseau purement *feed-forward* (comme l'inference d'un LLM classique) a un Phi nul : il calcule sans "etre" conscient, faute de boucles causales integrees. Cette these est centrale dans les discussions sur la conscience artificielle.
- **Controverse.** Le calcul exact de Phi est computationnellement intractable au-dela de petits reseaux (d'ou le coarse-graining du notebook), et la theorie a fait l'objet d'une critique publique retentissante (lettre ouverte de 2023 la qualifiant de "pseudoscience") — un cas d'ecole pour discuter des criteres de scientificite d'une theorie de l'esprit.

Ces tensions font de l'IIT un excellent terrain pour exercer l'esprit critique : on y manipule un formalisme precis (calculable avec PyPhi) tout en gardant a l'esprit les limites de son interpretation.

## FAQ

### Pourquoi Python 3.9 est-il obligatoire ?

PyPhi 1.2.0 utilise `collections.Iterable`, qui a ete supprime dans Python 3.10 (PEP 585). Tenter d'installer PyPhi sur Python 3.10+ provoque une `ImportError` des le `import pyphi`. L'environnement conda dedie isole cette contrainte sans affecter vos autres projets.

### L'IIT est-elle acceptee par la communaute scientifique ?

L'IIT est une theorie **controversée**. Elle a des retombees cliniques reelles (PCI pour mesurer la conscience chez les patients comateux) mais reste debattue : certains chercheurs la considerent comme le meilleur cadre theorique existant, d'autres la critiquent comme pseudoscience. Les notebooks presentent le formalisme et ses outils sans prendre position — c'est un excellent terrain pour exercer l'esprit critique.

### Quelle est la difference entre big Phi et small phi ?

**Big Phi** ($\Phi$) mesure l'integration au niveau du systeme complet : il quantifie a quel point le systeme est "plus que la somme de ses parties". **Small phi** ($\varphi$) mesure l'integration d'un mecanisme individuel (un sous-ensemble de noeuds) : chaque concept dans la CES a son propre small phi. La CES est l'ensemble des concepts dont le small phi > 0, et le big Phi aggrege ces contributions.

### Un reseau feed-forward peut-il etre conscient selon l'IIT ?

Non. L'IIT predit qu'un reseau purement feed-forward (A -> B -> C, sans boucle de retroaction) a un Phi de zero. L'information transite mais n'est pas "integree" — il n'y a pas de causalite bidirectionnelle. C'est un resultat fondamental pour le debat sur la conscience des LLMs, dont l'inference est essentiellement feed-forward.

### Le calcul de Phi est-il tractable en pratique ?

Pas au-dela de ~5-7 noeuds en pratique. Le nombre de bipartitions a evaluer croit super-exponentiellement avec la taille du systeme. Le notebook 2 (section 7) demontre cette explosion et introduit le coarse-graining comme strategie d'approximation. Pour les systemes reels (cerveau humain : ~86 milliards de neurones), seul le PCI (mesure clinique indirecte) est applicable.

### Peut-on utiliser PyPhi pour un projet de recherche ?

Oui, mais avec caveats. PyPhi est la reference pour IIT 3.0, mais IIT 4.0 (2024+) introduit des changements fondamentaux dans le calcul de Phi. Pour un projet de recherche, verifier la version de la theorie que vous suivez et consulter la [documentation PyPhi](https://pyphi.readthedocs.io/en/stable/) pour les limitations actuelles.

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
| [Probas](../Probas/README.md) | Infer.NET / PyMC | Modeles probabilistes et inference bayesienne partagent les fondements de la mesure d'integration |
| [GameTheory](../GameTheory/README.md) | OpenSpiel / Nashpy | Interactions strategiques multi-agents eclairent la complexite des systemes distribues |
| [SymbolicAI/Lean](../SymbolicAI/Lean/README.md) | Preuves formelles | Formalisation Arrow/Sen montre comment prouver des proprietes structurelles impossibles |
| [RL](../RL/README.md) | Stable Baselines3 | La distinction feed-forward vs recurrent (Phi = 0 vs > 0) eclaire le choix d'architecture RL |
