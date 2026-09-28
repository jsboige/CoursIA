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

Les images embarquées vivent dans `images/` (référencées depuis l'énoncé).

## Outils

```bash
# conversion (source Drive -> banque) ; XML bruts jamais commis
python scripts/notebook_tools/moodle_bank.py convert \
    --src "G:/Mon Drive/MyIA/IA/Rattrapages" --out MyIA.AI.Notebooks/cross-series/qcm

# validation de la banque commise (identifiants, options, appariements, images)
python scripts/notebook_tools/moodle_bank.py check --bank MyIA.AI.Notebooks/cross-series/qcm

# passe de test (comptes figés par la décision mainteneur + invariants)
npx pytest scripts/tests/test_moodle_bank.py
```

Le format vise le dispositif d'auto-évaluation de #18207 : chaque question
doit pouvoir nourrir la fonction `verifier(...)` sans conversion supplémentaire.
