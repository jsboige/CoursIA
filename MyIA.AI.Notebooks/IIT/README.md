# IIT - Integrated Information Theory

<!-- CATALOG-STATUS
series: IIT
pedagogical_count: 28
breakdown: ICT-Series=25, root=3
maturity: BETA=18, PRODUCTION=9, ALPHA=1
-->

[← Notebooks](../README.md) | [↑ ..](../README.md) | [→ Probas](../Probas/README.md)

La conscience est-elle mesurable ? La Théorie de l'Information Intégrée (IIT), proposée par Giulio Tononi, répond oui : un système est conscient dans la mesure où il intègre de l'information de manière non réductible. Plus formellement, la quantité de conscience d'un système correspond à la valeur **Phi** (big Phi), qui mesure le degré d'intégration causale irréductible. Cette série vous apprend à calculer cette mesure avec **PyPhi**, la bibliothèque de référence du laboratoire Tononi, et à explorer la géométrie informationnelle des systèmes complexes.

Le premier notebook couvre le spectre fondamental : construction de graphes causaux binaires, calcul des Transition Probability Matrices (TPM), définition des sous-systèmes, extraction des Cause-Effect Structures (CES), et exploration des macro-sous-systèmes. Le second approfondit les aspects avancés : partitionnement MIP, répertoires cause-effet, MICE, comparaison big Phi vs small phi, réseaux élargis à 4+ nœuds, coarse-graining et aperçu IIT 4.0. Le troisième est consacré au **coarse-graining et à la question de l'échelle du $\Phi$** : il opérationnalise le module `pyphi.macro` (information efficace de Hoel, énumération des regroupements, comparaison micro/macro) et examine honnêtement la prédiction de *causal emergence*.

**À qui s'adresse cette série** : étudiants en sciences cognitives, neuroscience computationnelle, et philosophie de l'esprit. Les notebooks (~60-90 min chacun) nécessitent Python 3.9 avec `pyphi` (installé via conda env dédié). Une familiarité avec les graphes et la logique booléenne suffit. Il constitue un complément théorique aux séries [Probas](../Probas/README.md) (modèles probabilistes) et [GameTheory](../GameTheory/README.md) (systèmes multi-agents), avec lesquelles il partage les concepts de causalité et d'interaction.

## Objectifs d'apprentissage

À l'issue de cette série, vous serez capable de :

1. **Construire et manipuler des réseaux causaux** binaires avec PyPhi (TPM, nœuds, connexions)
2. **Calculer Phi** pour un sous-système et interpréter sa valeur (intégration vs séparabilité)
3. **Analyser une Cause-Effect Structure (CES)** : identifier les concepts, mécanismes et purviews
4. **Appliquer le partitionnement MIP** pour localiser le "maillon faible" d'un système
5. **Différencier big Phi et small phi** et comprendre leur rôles respectifs dans la théorie
6. **Évaluer les limites computationnelles** de l'IIT et les stratégies de coarse-graining
7. **Discuter les implications philosophiques** de l'IIT pour la conscience artificielle

## Notebooks

| # | Notebook | Contenu | Durée |
|---|----------|---------|-------|
| 1 | [IIT-1-IntroToPyPhi](IIT-1-IntroToPyPhi.ipynb) | Réseau XOR 3-nœuds : TPM, calcul de Φ, CES, états inaccessibles, causation | 60-90 min |
| 2 | [IIT-2-AdvancedTopics](IIT-2-AdvancedTopics.ipynb) | MIP et bipartitions, répertoires cause-effet, MICE, big Φ sur réseau 4-nœuds, coarse-graining | 60-90 min |
| 3 | [IIT-3-CoarseGrainingMacroPhi](IIT-3-CoarseGrainingMacroPhi.ipynb) | Module `pyphi.macro` : information efficace (Hoel), énumération des regroupements, comparaison Φ micro/macro, causal emergence | 45-60 min |

## Parcours recommandés

```
Notebook 1 (Fondements)
    |
    v
Notebook 2 (Sujets avancés)
    |
    v
Notebook 3 (Coarse-graining & échelle du Φ)
```

| Objectif | Parcours |
|----------|----------|
| Découverte rapide | Notebook 1 seul |
| Maîtrise complète | Notebook 1 puis 2, puis 3 |
| Focus philosophie | Notebook 1 (sections CES + débats) + Notebook 2 (section IIT 4.0) |
| Focus emergence & échelle | Notebook 1 + Notebook 3 (causal emergence de Hoel) |

### Parcours d'apprentissage

**Phase 1 : Fondements (~90 min, notebook 1)**

Vous installez PyPhi dans un environnement conda dédié (Python 3.9 obligatoire), puis construisez votre premier réseau causal binaire. Le calcul de Phi sur un réseau XOR à 3 nœuds illustre concrètement la notion d'intégration irréductible. L'exploration de la CES révèle comment un système "spécifie" sa propre géométrie informationnelle. Les 3 exercices vous font varier les sous-systèmes (partiel, porte AND) et explorer les concepts de la CES pour développer une intuition sur ce qui fait monter ou baisser Phi.

**Phase 2 : Approfondissement (~90 min, notebook 2)**

Le deuxième notebook déconstruit le calcul de Phi : vous manipulez les bipartitions (MIP), les répertoires cause-effet, et les MICE (Maximally Irreducible Cause or Effect). La comparaison big Phi vs small phi clarifie les deux niveaux d'analyse. L'extension à des réseaux à 4+ nœuds montre l'explosion combinatoire et justifie le coarse-graining. L'aperçu IIT 4.0 ouvre sur les évolutions récentes de la théorie. Les 3 exercices testent votre compréhension des répertoires, du Phi multi-états et des réseaux feed-forward (Phi = 0 attendu).

**Phase 3 : Échelle et emergence (~60 min, notebook 3)**

Le troisième notebook opérationnalise le module `pyphi.macro` resté conceptuel jusque-là : vous mesurez l'**information efficace** (EI) de Hoel, énumérez les regroupements (coarse-grain) possibles d'un réseau, et comparez $\Phi$ à l'échelle micro et macro sur l'exemple canonique de pyphi. Surtout, il examine **honnêtement** la prédiction contre-intuitive de *causal emergence* (Hoel 2013) : pourquoi le $\Phi$ macro ne dépasse le $\Phi$ micro que sur des réseaux probabilistes où le coarse-grain filtre du bruit, et pas sur des toys déterministes. Les 3 exercices portent sur la dégénérescence (réseau AND), l'énumération des regroupements et le test d'une hypothèse d'emergence.

## Contenu détaillé

### IIT-1-IntroToPyPhi.ipynb

| Section | Contenu |
|---------|---------|
| Installation | `pip install pyphi`, vérification de la version de la bibliothèque |
| Réseaux | Réseau XOR 3-nœuds de référence, inspection des `node_labels` |
| TPM | Conversion *state-by-node*, dimensions de la matrice de transition |
| Sous-systèmes & Φ | Calcul de Φ d'un sous-système à un état donné, boucle sur plusieurs états |
| États inaccessibles | Validation via `StateUnreachableError`, option `VALIDATE_SUBSYSTEM_STATES` |
| CES | `pyphi.compute.ces`, décompte des concepts d'un sous-système |
| Causation actuelle | Liens causaux d'une transition (`account`), mécanisme d'un concept |
| Macro-sous-systèmes | Coarse-graining, blackboxing (section conceptuelle) |

### IIT-2-AdvancedTopics.ipynb

| Section | Contenu |
|---------|---------|
| Rappels | Réseau XOR 3-nœuds, reprise des concepts du notebook 1 |
| Partitionnement MIP | `bipartition`, décompte des partitions, interprétation de la coupe minimale |
| Répertoires cause-effet | Répertoires cause, effet et non-perturbé d'un mécanisme donné |
| MICE et concepts | MICE du mécanisme {A,B}, décompte des concepts de la CES |
| Big Phi vs Small Phi | Big Phi au niveau système (SIA) face au small phi d'un mécanisme (MICE) |
| Réseaux élargis | Réseau 4-nœuds en anneau (XOR cyclique), Φ sur système élargi |
| Performance | Timing du calcul de CES, module `pyphi.macro` |
| IIT 4.0 | Concept-Style SIA, limites computationnelles, débats |

### IIT-3-CoarseGrainingMacroPhi.ipynb

| Section | Contenu |
|---------|---------|
| Setup | Configuration mono-cœur déterministe de `pyphi.macro` |
| Échelle micro | Réseau copy 3-nœuds, information efficace (EI) et $\Phi$ de référence |
| Méthode coarse-grain | `all_partitions` : énumération des regroupements possibles |
| Échelle macro | Exemple canonique `macro_network`, $\Phi$ coarse-grained |
| Comparaison micro/macro | $\Phi$ macro vs $\Phi$ micro, interprétation honnête de l'emergence |
| Causal emergence | Hoel 2013 : pourquoi l'emergence positive n'est ni automatique ni garantie |

## Concepts clés

| Concept | Explication | Analogie |
|---------|-------------|----------|
| **TPM** | Règles d'évolution du système | Lois de la physique |
| **État** | Configuration binaire des nœuds (0 ou 1) | Instantané cérébral |
| **Phi (Big Phi)** | Niveau d'intégration du système | Force d'un nœud de corde |
| **Small phi** | Intégration d'un mécanisme individuel | Tension d'un fil du nœud |
| **MIP** | Point faible du système (Minimum Information Partition) | Maillon le plus faible |
| **CES** | Géométrie informationnelle (Cause-Effect Structure) | Forme d'une pensée |
| **MICE** | Mécanisme maximalement irréductible | Brique élémentaire de conscience |
| **Purview** | Ensemble de nœuds sur lesquels un mécanisme spécifie de l'information | Champ d'influence |

*Comment ces concepts s'enchaînent pour produire Φ — la chaîne de calcul de l'IIT 3.0
(réalisé par PyPhi) :*

```mermaid
flowchart TD
    NET["Réseau causal binaire<br/>TPM (Transition Probability Matrix)"]
    SUB["Sous-système S, à un état donné"]
    MEC["Mécanisme<br/>(sous-ensemble de nœuds de S)"]
    PURV["Purview + partition MIP<br/>coupe minimisant l'information"]
    MICE["MICE — small φ<br/>cause/effet maximalement irréductible"]
    CONCEPT["Concept<br/><i>si small φ &gt; 0</i>"]
    CES["CES — Cause-Effect Structure<br/>ensemble des concepts de S"]
    BIGMIP["MIP du sous-système S<br/>partition minimisant l'intégration"]
    PHI["Big Phi Φ<br/>quantité de conscience du système"]

    NET --> SUB
    SUB --> MEC
    MEC --> PURV
    PURV --> MICE
    MICE -->|"φ > 0"| CONCEPT
    CONCEPT --> CES
    CES --> BIGMIP
    BIGMIP --> PHI
```

## Prérequis

### Connaissances requises

- Python de base (imports, fonctions, tableaux)
- Logique booléenne (états binaires 0, 1)
- Notions de théorie des graphes (nœuds, connexions)

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

### Dépendances

| Package | Version | Utilisation |
|---------|---------|-------------|
| pyphi | 1.2.0+ | Calculs IIT |
| numpy | 1.21.6+ | Calcul numérique |
| scipy | 0.13.3+ | Fonctions scientifiques |

## Limitations connues

| Problème | Cause | Solution |
|----------|-------|----------|
| `ImportError: cannot import name 'Iterable'` | PyPhi 1.2.0 utilise `collections.Iterable` (supprimé Python 3.10+) | Utiliser Python 3.9 (`conda create -n pyphi python=3.9`) |
| StateUnreachableError | États inaccessibles | Configuration `VALIDATE_SUBSYSTEM_STATES` |
| Performance | Phi calcul intensif pour grands réseaux | Limiter taille des réseaux |

## Théorie IIT

La Théorie de l'Information Intégrée (IIT) propose une approche mathématique de la conscience :

1. **Information** : Un système conscient doit spécifier un grand nombre d'états possibles
2. **Intégration** : L'information doit être intégrée (non décomposable)
3. **Exclusion** : Un seul niveau de Phi domine à tout moment

**Phi** mesure le degré d'intégration informationnelle d'un système. Un Phi > 0 indique une intégration irréductible, suggérant une forme de conscience.

*Les deux niveaux d'analyse de l'IIT — small phi (un mécanisme) remonte vers big Phi
(le système), et l'axiome d'exclusion ne retient qu'un seul maximum à la fois :*

```mermaid
flowchart TD
    SYS["Système S complet<br/>Φ = big Phi"]
    MECA1["Mécanisme {A}<br/>small φ₁"]
    MECA2["Mécanisme {A,B}<br/>small φ₂ = MICE"]
    MECA3["Mécanisme {B,C}<br/>small φ₃"]
    CES2["CES = concepts de small φ > 0"]
    MIPSYS["MIP du système<br/>partition la moins intégrée"]
    EXCL["Axiome d'exclusion<br/>un seul maximum domine"]
    ONE["Un seul Φ retenu<br/>= la conscience du système"]

    SYS --> MIPSYS
    MECA1 --> CES2
    MECA2 --> CES2
    MECA3 --> CES2
    CES2 --> MIPSYS
    MIPSYS --> EXCL
    EXCL --> ONE
```

## Portée scientifique et débats

L'IIT n'est pas qu'une spéculation philosophique : elle a engendré des outils utilisés en clinique et alimente l'un des débats les plus vifs des neurosciences.

- **Mesure clinique de la conscience.** Le *Perturbational Complexity Index* (PCI), inspiré des principes de l'IIT, est utilisé pour évaluer la conscience chez des patients non communicants (coma, état végétatif, anesthésie). Le protocole "zap-and-zip" (stimulation TMS + EEG, compression de la réponse) distingue empiriquement les états conscients des états inconscients — une retombée concrète et reproductible d'une théorie de la conscience.
- **Une théorie concurrente.** L'IIT s'oppose frontalement aux théories de type *Global Workspace* (Dehaene, Baars), qui font de la conscience une diffusion globale de l'information plutôt qu'une intégration causale locale. Des programmes de tests adversariaux (collaboration Templeton) confrontent leurs prédictions sur des données réelles. La série [ICT](ICT-Series/README.md) (strate 5) opérationnalise ce débat dans le dépôt : un pont **IIT ↔ GWT falsifiable** est en construction sur traces d'activations réelles de LLM (module `ict/workspace.py`, mesures d'espace de travail global sur trajectoires SAE).
- **Enjeu pour l'IA.** L'IIT prédit qu'un réseau purement *feed-forward* (comme l'inférence d'un LLM classique) a un Phi nul : il calcule sans "être" conscient, faute de boucles causales intégrées. Cette thèse est centrale dans les discussions sur la conscience artificielle.
- **Controverse.** Le calcul exact de Phi est computationnellement intractable au-delà de petits réseaux (d'où le coarse-graining du notebook), et la théorie a fait l'objet d'une critique publique retentissante (lettre ouverte de 2023 la qualifiant de "pseudoscience") — un cas d'école pour discuter des critères de scientificité d'une théorie de l'esprit.

Ces tensions font de l'IIT un excellent terrain pour exercer l'esprit critique : on y manipule un formalisme précis (calculable avec PyPhi) tout en gardant à l'esprit les limites de son interprétation.

## FAQ

### Pourquoi Python 3.9 est-il obligatoire ?

PyPhi 1.2.0 utilise `collections.Iterable`, qui a été supprimé dans Python 3.10 (PEP 585). Tenter d'installer PyPhi sur Python 3.10+ provoque une `ImportError` dès le `import pyphi`. L'environnement conda dédié isole cette contrainte sans affecter vos autres projets.

### L'IIT est-elle acceptée par la communauté scientifique ?

L'IIT est une théorie **controversée**. Elle a des retombées cliniques réelles (PCI pour mesurer la conscience chez les patients comateux) mais reste débattue : certains chercheurs la considèrent comme le meilleur cadre théorique existant, d'autres la critiquent comme pseudoscience. Les notebooks présentent le formalisme et ses outils sans prendre position — c'est un excellent terrain pour exercer l'esprit critique.

### Quelle est la différence entre big Phi et small phi ?

**Big Phi** ($\Phi$) mesure l'intégration au niveau du système complet : il quantifie à quel point le système est "plus que la somme de ses parties". **Small phi** ($\varphi$) mesure l'intégration d'un mécanisme individuel (un sous-ensemble de nœuds) : chaque concept dans la CES a son propre small phi. La CES est l'ensemble des concepts dont le small phi > 0, et le big Phi agrège ces contributions.

### Un réseau feed-forward peut-il être conscient selon l'IIT ?

Non. L'IIT prédit qu'un réseau purement feed-forward (A -> B -> C, sans boucle de rétroaction) a un Phi de zéro. L'information transite mais n'est pas "intégrée" — il n'y a pas de causalité bidirectionnelle. C'est un résultat fondamental pour le débat sur la conscience des LLMs, dont l'inférence est essentiellement feed-forward.

### Le calcul de Phi est-il tractable en pratique ?

Pas au-delà de ~5-7 nœuds en pratique. Le nombre de bipartitions à évaluer croît super-exponentiellement avec la taille du système. Le notebook 2 (section 7) démontre cette explosion et introduit le coarse-graining comme stratégie d'approximation. Pour les systèmes réels (cerveau humain : ~86 milliards de neurones), seul le PCI (mesure clinique indirecte) est applicable.

### Peut-on utiliser PyPhi pour un projet de recherche ?

Oui, mais avec caveats. PyPhi est la référence pour IIT 3.0, mais IIT 4.0 (2024+) introduit des changements fondamentaux dans le calcul de Phi. Pour un projet de recherche, vérifier la version de la théorie que vous suivez et consulter la [documentation PyPhi](https://pyphi.readthedocs.io/en/stable/) pour les limitations actuelles.

## Ressources

### Documentation PyPhi

- [PyPhi Documentation officielle](https://pyphi.readthedocs.io/en/stable/)
- [PyPhi GitHub](https://github.com/wmayner/pyphi)
- [Exemples PyPhi](https://github.com/wmayner/pyphi/tree/master/examples)

### Fondements théoriques

- Tononi, G. (2008) - *Consciousness as Integrated Information*
- Oizumi, M., Albantakis, L., Tononi, G. (2014) - *From the Phenomenology to the Mechanisms of Consciousness*

## Structure des fichiers

```
IIT/
├── IIT-1-IntroToPyPhi.ipynb           # Notebook 1 : introduction
├── IIT-2-AdvancedTopics.ipynb         # Notebook 2 : sujets avances
├── IIT-3-CoarseGrainingMacroPhi.ipynb # Notebook 3 : coarse-graining & échelle du Φ
├── ICT-Series/                 # Extension expérimentale ICT (Epic #4588) — voir son README
│   ├── ICT-0-Framing.md        # Cadrage de la série ICT
│   ├── ICT-*.ipynb             # Notebooks numérotés 1..23 + raffinement ICT-19 + ICT-Synthese (5 strates, Epic #4588 — cf son README)
│   ├── ict/                    # Package Python autonome (simulations + mesures)
│   ├── tests/                  # Suite pytest de validation des modules ict/
│   └── README.md               # Documentation de la série ICT
├── requirements.txt            # Dépendances Python (partagées IIT + ICT)
├── scripts/
│   ├── setup_pyphi_env.ps1     # Setup conda env + kernel (partagé IIT + ICT)
│   └── build_notebook.py       # Script de construction notebook 2
└── README.md                   # Cette documentation
```

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Cette série vous a fait traverser la proposition la plus quantitative de la neuroscience théorique contemporaine : **traiter la conscience comme une propriété mesurable** d'un système, plutôt que comme un épiphénomène mystérieux. L'arc pédagogique :

- **Le geste fondateur** — poser qu'un système est conscient dans la mesure exacte où il intègre de l'information de manière **irréductible** : ni plus ni moins que ce que ses parties prises isolément ne peuvent expliquer. Cette irréductibilité, c'est **Phi**.
- **L'instrument** — PyPhi, la bibliothèque de référence du laboratoire Tononi, qui opérationnalise la théorie : graphes causaux binaires, Transition Probability Matrices, sous-systèmes, extraction des Cause-Effect Structures, et tout le calcul combinatoire que l'intégration exige.
- **La finesse** — distinguer **big Phi** (la conscience du système entier) et **small phi** (l'irréductibilité d'un concept local), comprendre le partitionnement MIP qui localise le « maillon faible » d'un système, et saisir pourquoi le coarse-graining devient indispensable dès que le réseau grandit.

La thèse est vertigineuse et honnêtement présentée : si IIT a raison, la conscience n'est pas un mystère à élucider mais une **quantité à calculer** — et un système artificiel suffisamment intégré pourrait, en principe, l'incarner.

### Prochaines étapes

- **Approfondir les fondements probabilistes** : [Probas](../Probas/README.md) (Infer.NET, programmation probabiliste) fournit les outils de modélisation causale et d'inférence bayésienne qui sous-tendent le calcul des TPM.
- **Élargir aux systèmes multi-agents** : [GameTheory](../GameTheory/README.md) (théorie des jeux, choix social) partage avec IIT la question centrale — comment l'interaction entre composants produit-elle des propriétés émergentes que les composants seuls ne possèdent pas ?
- **Questionner la portée** : relisez la section « Portée scientifique et débats » — IIT est une théorie vivante et contestée, pas un consensus. Les critiques empiriques (absence de tests décisifs) et théoriques (mesure de la conscience chez les systèmes simples) restent ouvertes, et c'est sain pour un champ scientifique.
- Pour la pratique : reprenez le notebook d'Advanced Topics et expérimentez la limite computationnelle — à partir de combien de nœuds le calcul de Phi devient-il prohibitif, et que révèle le coarse-graining sur les macro-systèmes ?

### Le fil rouge

IIT propose un changement de regard radical : ne plus demander « qu'est-ce que la conscience ? » mais **« combien de conscience ce système intègre-t-il ? »**. La série vous a donné l'outil (PyPhi) et le formalisme (Phi, CES, MIP) pour transformer une question philosophique en un calcul — en gardant à l'esprit qu'aucune mesure, aussi élégante soit-elle, ne clôt à elle seule le débat sur ce que c'est que d'être un système qui ressent quelque chose.

## Extension : la série ICT (Integrated Causal Trajectories)

La série IIT étudie des structures causales **à un instant donné**. Une extension expérimentale,
**ICT** (Integrated Causal Trajectories, Epic #4588), prolonge ce regard vers les **trajectoires**
de structures causales : comment une organisation se maintient, se transforme, se répare, change
d'échelle et traverse un espace de possibles ($C_0 \rightarrow C_1 \rightarrow \dots \rightarrow C_n$).
Elle progresse en cinq strates — le **tri auto-organisé** transparent (strate 1, ICT-0 à ICT-7), la
**morphogenèse dynamique** à paysages d'attracteurs engendrés (strate 2, ICT-8 à ICT-10), les
**trajectoires intégrées** régime-dépendantes (strate 3, ICT-11 à ICT-13), la jambe
**représentationnelle** énergie libre / surprise (strate 4, ICT-14), puis la **théorie fondatrice**
cross-substrat et la réversibilisation outillée (strate 5, ICT-15 et suivants).

La strate 5 est désormais **ancrée sur un substrat réel** : ICT-21 extrait des trajectoires SAE
(*sparse autoencoders*) sur les activations d'un LLM (Qwen), et le module `ict/workspace.py` pose
l'infrastructure d'un **pont falsifiable IIT ↔ GWT** — mesurer un « espace de travail global »
(*ignition*, *broadcast*) sur les mêmes traces que celles où l'on mesure l'intégration, pour
confronter empiriquement les deux théories rivales de la section « Portée scientifique » ci-dessus.

ICT vit dans le sous-répertoire [`ICT-Series/`](ICT-Series/README.md), placé sous IIT pour respecter
l'ordre de lecture (ICT prolonge IIT). **Voir son [README dédié](ICT-Series/README.md)** pour la liste
complète des notebooks, les cinq strates et le détail des mesures *sans complaisance*. La série
partage l'environnement Python d'IIT (`scripts/setup_pyphi_env.ps1`, `requirements.txt`) ; la jambe
SAE (ICT-21 et suivants) utilise en plus un environnement conda dédié (`coursia-sae`).

## Ponts causaux : le do-calculus de Pearl à travers les paradigmes

Quatre séries du dépôt abordent la **causalité** — non pas la corrélation, mais la question
« que se passe-t-il si j'**interviens** ? ». Elles le font dans des paradigmes radicalement
différents (logique symbolique, inférence bayésienne par message passing, MCMC, théorie de l'information),
et pourtant elles partagent **le même noyau** : l'opérateur `do(·)` de Judea Pearl et son
**échelle de la causalité** à trois barreaux.

**L'échelle de la causalité (ladder of causation)** :

| Barreau | Question | Formalisme | Exemple canonique |
|---------|----------|------------|-------------------|
| **L1 — Association** | « Que voit-on ? » | `P(Y \| X)` | observer le baromètre baisser prédit la pluie |
| **L2 — Intervention** | « Que se passe-t-il si on agit ? » | `P(Y \| do(X))` | *forcer* le baromètre à baisser ne fait **pas** pleuvoir |
| **L3 — Contrefactuel** | « Qu'aurait-il fallu ? » | `P(Y_x \| X', Y')` | « l'herbe aurait-elle été mouillée si on avait coupé l'arrosage ? » |

Le saut **L1 → L2** est le cœur du do-calculus : `do(X=x)` **mutile** le graphe causal — il coupe
les arcs entrants de `X`, brisant les chemins de confusion — de sorte que
`P(Y|do(X)) ≠ P(Y|X)` dès qu'un confondeur existe.

**Le même opérateur, quatre instanciations** :

| Paradigme | Notebook | Instanciation de `do(·)` | Résultat-signature |
|-----------|----------|---------------------------|--------------------|
| **Symbolique** (logique propositionnelle, Java/Tweety) | [Tweety-11-Causal](../SymbolicAI/Tweety/Tweety-11-Causal.ipynb) | `scm.intervene(p, b)` → nouveau SCM dont l'équation de `p` devient une constante | `P(rain\|drops)=True ≠ P(rain\|do(drops))=False` (baromètre) |
| **Bayésien par message passing** (Infer.NET, EP/VMP — Gibbs disponible) | [Infer-14](../Probas/Infer/Infer-5-Causal-Inference.ipynb) | mutilation de graphe `Variable.Bernoulli(1.0)` ; backdoor / front-door | paradoxe de Simpson résolu, identifiabilité par ajustement |
| **Bayésien MCMC** (PyMC) | [PyMC-14](../Probas/PyMC/PyMC-14-Causal-Inference.ipynb) | opérateur natif `pm.do(model, {X:x})` ; backdoor / front-door | contrefactuel par abduction (postérieur sur les exogènes) |
| **Théorie de l'information / émergence** (ICT) | [ICT-5-CausalEmergence](ICT-Series/ICT-5-CausalEmergence.ipynb) | distribution d'intervention `p(C)` **uniforme** sur les états = `do(X_t = x)` appliqué à tout le micro-état | quelle **échelle** « fait » le plus de travail causal (EI / CP) |

**Le pont le plus profond — ICT-5 lève le do-calculus au niveau des échelles.** Dans la théorie
de l'émergence causale (Hoel, *Causal Emergence 2.0* ; Jansma & Hoel, *Engineering Emergence*,
2025), l'**information effective** (EI) et la *causal primitive* (`CP = déterminisme −
dégénérescence`, équivalente à l'`effectiveness`) se calculent en plaçant le système sous une
**distribution d'intervention** `p(C)` — par défaut **uniforme sur les états**. C'est exactement
`do(X_t = x)` de Pearl, appliqué uniformément : on ne *regarde* pas la dynamique, on la *sonde*
en forçant chaque état d'entrée. Mesurer « combien de travail causal fait un mécanisme »
**exige** donc l'opérateur `do`, tout comme définir un effet causal l'exige chez Pearl.
L'**émergence** apparaît quand une description **macro** (gros-grain) réalise *plus* de travail
causal que le micro — l'`effectiveness` monte sous coarse-graining.

**Parcours de lecture conseillé** : commencer par le **symbolique qualitatif**
([Tweety-11](../SymbolicAI/Tweety/Tweety-11-Causal.ipynb)) pour *voir* `observe` vs `do` sans
nombres ; passer au **quantitatif distributionnel** ([Infer-14](../Probas/Infer/Infer-5-Causal-Inference.ipynb)
message passing, [PyMC-14](../Probas/PyMC/PyMC-14-Causal-Inference.ipynb) MCMC) pour *calculer* les effets
et lever le paradoxe de Simpson ; finir par l'**information-théorique**
([ICT-5](ICT-Series/ICT-5-CausalEmergence.ipynb)) où le même `do` mesure le travail causal **à travers les
échelles**.

**Articles d'ancrage** : Pearl, *Causality* (2009) ; Hoel, *Causal Emergence 2.0*
(arXiv:2503.13395) ; Jansma & Hoel, *Engineering Emergence* (arXiv:2510.02649).

*Voir #4208 (surfaçage des différenciants du dépôt) et l'Epic ICT #4588.*

## Licence

Voir la licence du repository principal.

---

*Version 1.3.0 — Juillet 2026*
