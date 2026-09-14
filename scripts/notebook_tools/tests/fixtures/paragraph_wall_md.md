# Fixture — paragraphes markdown pour `detect_paragraph_length`

Ce fichier sert de **fixture externe** au détecteur
[scripts/notebook_tools/detect_paragraph_length.py](../../../../scripts/notebook_tools/detect_paragraph_length.py),
en complément du `--self-test` embarqué. Les cas vivent dans des sections
distinctes pour qu'un test puisse viser une section par `path` + `start_line`.

## Section 1 — paragraphe-mur fondateur (DOIT tirer)

Cette serie couvre trois stacks complementaires : Infer.NET, PyMC, et des applications standalone comme RSA, identification causale avec DoWhy, ou encore la percolation de liens sur tore fini. Elle totalise 69 notebooks -- 28 en C#/.NET Interactive, 38 en Python, 3 en Lean 4 -- repartis entre le corpus bayesien Infer.NET (21 notebooks, socle 1-20 sans le numero 6 qui vit en accretion Infer-2b, plus les accretions Infer-1b premier modele et Infer-20 quotients et fibres en kernel Python), l'arc theorie de la decision (8 notebooks C# DecInfer plus 2 notebooks Lean pour la certification formelle des lemmes d'escompte geometrique et de l'indice de Gittins, le tout certifie par le lake companion decision_theory_lean), le versant PyMC en parite 1:1 (19 notebooks corpus plus 12 miroirs de l'arc decision, dont la jambe actuarielle 8-12 specialisee en frequence x severite hierarchique et le notebook DecPyMC-11 sur la valeur de l'information en souscription), la percolation (1 notebook Python trois regimes mesures sur un tore fini par Diskin-Easo-Radhakrishnan-Sudakov-Tassion, plus 1 notebook Lean compagnon du lake percolation_lean qui demontre sans sorry le noyau fini), et le pont causal DecisionTheory/Causal-Bridges qui federe les quatre traitements de la causalite dissemines dans le depot (Tweety logique formelle, Infer.NET message passing via le notebook Infer-5-Causal-Inference, PyMC echantillonnage MCMC via PyMC-05-Causal-Inference, et emergence causale PyPhi via ICT-5 et ICT-6 du dossier IIT) autour de l'echelle de Pearl et des trois regles du do-calculus -- identifie l'estimande par backdoor/front-door/variable instrumentale, l'estime par regression ou modele causal, puis le refute par placebo et randomisation. L'outil de reference dowhy (pywhy.org) est execute reel sur chaque notebook, jamais une reimplementation jouet, et la documentation detaillee de chaque segment pedagogique vit dans les README specialises (Infer/, PyMC/, DecisionTheory/DecInfer/, DecisionTheory/PyMC/, DecisionTheory/Causal-Bridges/, Applications/Percolation/).

## Section 2 — paragraphe normal (NE DOIT PAS tirer)

Six paragraphes distincts, courts. Chaque bloc est separe par une ligne vide. Aucun ne depasse les 500 caracteres. La calibration confirme : p50 = 79 c, p75 = 274 c.

Le corpus bayesien compte 21 notebooks, socle numéroté 1 à 20.

L'arc décision en extrait 8 notebooks C# via DecInfer.

Le versant PyMC porte 19 corpus + 12 miroirs de l'arc décision.

La percolation complète ce trio Lean avec son duo Python/Lean.

Le pont causal fédère les quatre séries autour de l'échelle de Pearl.

## Section 3 — paragraphe avec une fence code longue (NE DOIT PAS tirer)

Texte court avant la fence.

```python
# 5000 caractères de code dans une fence -- ne doit pas être compté
def wall_of_code():
    s = "a" * 5000
    return s
```

Texte court après la fence.

## Section 4 — paragraphe avec CATALOG-STATUS (NE DOIT PAS tirer)

<!--
CATALOG-STATUS
series: Fixture
pedagogical_count: 1
breakdown: test=1
maturity: BETA=1
-->

Paragraphe normal apres le marqueur CATALOG-STATUS. Court.

## Section 5 — titre + ligne de tableau longue (NE DOIT PAS tirer)

# Titre H1

## Titre H2 avec une table dont une ligne fait 5000 chars

| Col1 | Col2 |
|------|------|
| aaaa (5000 chars) | y |

Paragraphe normal apres le tableau.