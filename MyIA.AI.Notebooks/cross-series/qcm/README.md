# Banque de QCM (`cross-series/qcm/`)

Banque de questions à choix multiple convertie des exports XML Moodle du
mainteneur (issue #18223). Source : `G:\Mon Drive\MyIA\IA\Rattrapages\` — les
XML bruts (1,8 Mo, images base64) restent sur le Drive, seul le produit
converti vit ici.

## Contenu

147 questions publiées, par thème (décision mainteneur 28/09) :

| Fichier | Thème | Questions |
|---|---|---:|
| `ia-1-introduction-agents.yaml` | IA — Introduction, agents | 15 |
| `ia-2-resolution-problemes.yaml` | IA — Résolution de problèmes | 36 |
| `ia-3-logique-bases-connaissances.yaml` | IA — Logique et bases de connaissances | 19 |
| `ia-4-systemes-probabilistes.yaml` | IA — Systèmes probabilistes | 24 |
| `ia-5-apprentissage.yaml` | IA — Apprentissage | 21 |
| `dl-evaluation-seance.yaml` | Apprentissage profond (évaluation de séance) | 32 |

Non publiés : 63 questions C#/.NET (exclues — pas de cours d'accueil) et 29
Big Data (différées jusqu'à une série Big Data, réimportables par le
convertisseur sans reconversion du reste).

## Format

Un fichier par thème, une liste YAML de questions. Chaque question porte :

```yaml
- id: ia4-001            # identifiant stable (préfixe thème + séquence)
  theme: ia-4-systemes-probabilistes
  type: multichoice      # multichoice | truefalse | matching
  source: INGPA-FIN4000 2020   # quiz d'origine, sans chemin personnel
  enonce: En théorie de l'utilité, quel est le nom de ...
  choix_unique: true     # absent pour matching
  options:               # appariements pour matching (gauche/droite)
  - texte: Continuité
    correcte: true
  - texte: Transitivité
    correcte: false
  explication: ...       # seulement quand Moodle en fournissait une
```

Les images embarquées vivent dans `images/` (référencées depuis l'énoncé par `[figure: images/…]` ; `check`
signale comme orphelin tout fichier non référencé). Une question dont la figure n'est pas
embarquée — cas de ia2-010, dont l'export ne porte qu'une URL externe — est signalée en
`ATTENTION`, cf [RELECTURE-2026-09.md](RELECTURE-2026-09.md).

Trois figures des exports ne sont **pas** republiables en l'état (photographie d'une page de
manuel, captures d'écran de la même page, URL de partage personnelle) : le convertisseur
porte leur traitement dans `PUBLICATION_POLICY` — redessinées à partir de leurs valeurs
(`redraw_qcm_figures.py`), restituées en tableau markdown dans l'énoncé, ou remplacées par un
marqueur neutre. La politique vit dans le convertisseur pour qu'une re-conversion **réapplique**
ces décisions au lieu de réintroduire les figures d'origine.

## Outils

```bash
# conversion (source Drive -> banque) ; XML bruts jamais commis
python scripts/notebook_tools/moodle_bank.py convert \
    --src "G:/Mon Drive/MyIA/IA/Rattrapages" --out MyIA.AI.Notebooks/cross-series/qcm

# validation de la banque commise (identifiants, options, appariements, images)
python scripts/notebook_tools/moodle_bank.py check --bank MyIA.AI.Notebooks/cross-series/qcm

# regeneration de la figure redessinee (deja appelee par `convert`, matplotlib requis)
python scripts/notebook_tools/redraw_qcm_figures.py --out MyIA.AI.Notebooks/cross-series/qcm/images

# passe de test (comptes figés par la décision mainteneur + invariants)
npx pytest scripts/tests/test_moodle_bank.py
```

Le format vise le dispositif d'auto-évaluation de #18207 : chaque question
doit pouvoir nourrir la fonction `verifier(...)` sans conversion supplémentaire.

## Rattachement aux séries

Chaque thème pointe vers les notebooks qui enseignent la notion :

| Thème | Série d'accueil | Notebooks d'ancrage |
|---|---|---|
| `ia-1-introduction-agents` | [`Search/`](../../Search/) | [`Search-01-StateSpace.ipynb`](../../Search/Part1-Foundations/Search-01-StateSpace.ipynb) (agents, environnements) |
| `ia-2-resolution-problemes` | [`Search/`](../../Search/) | [`Search-02-Uninformed.ipynb`](../../Search/Part1-Foundations/Search-02-Uninformed.ipynb) ; CSP : [`Part2-CSP/`](../../Search/Part2-CSP/) et [`Applications/CSP/`](../../Search/Applications/CSP/) |
| `ia-3-logique-bases-connaissances` | [`SymbolicAI/`](../../SymbolicAI/) | [`SMT/`](../../SymbolicAI/SMT/), [`Tweety/`](../../SymbolicAI/Tweety/), [`SemanticWeb/`](../../SymbolicAI/SemanticWeb/) |
| `ia-4-systemes-probabilistes` | [`Probas/`](../../Probas/) | [`DecInfer-01-Utility-Foundations.ipynb`](../../Probas/DecisionTheory/DecInfer/DecInfer-01-Utility-Foundations.ipynb) (utilité, axiomes) ; réseaux bayésiens Infer.NET de la série |
| `ia-5-apprentissage` | [`ML/`](../../ML/) | [`2.1-Workflow-ML.ipynb`](../../ML/DataScienceWithAgents/02-ML-Cours/2.1-Workflow-ML.ipynb) |
| `dl-evaluation-seance` | [`ML/`](../../ML/) | [`03-DeepLearning/`](../../ML/DataScienceWithAgents/03-DeepLearning/) (rétropropagation, attention) et [`04-Vision/`](../../ML/DataScienceWithAgents/04-Vision/) (CNN) |

Questions sans notebook d'accueil : la passe de relecture prévue par #18223
(tranche 4) les énumère par identifiant au fil de la lecture — une question
sans ancrage se signale, elle ne s'invente pas de place. Cette relecture est
livrée : [RELECTURE-2026-09.md](RELECTURE-2026-09.md) registre daté des constats
(coquilles de source, clés contestables, doublons attribués à la source Moodle).
Les sujets de rattrapage Trading, distincts de cette banque, vivent dans la série
QuantConnect (`examens/`, même issue #18223) avec leur propre rattachement.

