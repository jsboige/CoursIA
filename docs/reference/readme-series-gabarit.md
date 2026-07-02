# Gabarit de reference -- READMEs de series (MyIA.AI.Notebooks/)

Canevas commun pour l'harmonisation des READMEs de series (niveau 1) et de sous-series (niveau 2), Partie 2 de l'issue #2651. Chaque element du gabarit est **derive d'un exemplaire existant** du depot (recensement des 37 READMEs, commentaire #2651) : rien n'est invente, on generalise ce qui marche deja.

Le README principal du depot donne le ton de reference (registre sobre, ouverture par une question, pas de jugement de valeur editorial) ; les READMEs de series emmenent le lecteur **plus loin**, au plus pres du contenu réel des notebooks.

---

## Ordre canonique des sections

| # | Section | Exemplaire de reference | Obligatoire |
|---|---------|-------------------------|-------------|
| 0 | Marqueur CATALOG-STATUS | (bot-owned, cf. regles ci-dessous) | niveau 1 : oui |
| 1 | Titre + pitch (fil rouge en 1-3 phrases) | `Sudoku/README.md:1-10` | oui |
| 2 | Barre de navigation (parent / precedent / suivant) | `GenAI/Image/README.md:3` | oui |
| 3 | Introduction pedagogique (le pourquoi avant le combien) | `Sudoku/README.md`, `Search/README.md` | oui |
| 4 | Objectifs d'apprentissage (verbes d'action, 3 categories) | `CaseStudies/README.md:81-105` | oui |
| 5 | Table des notebooks | `GameTheory/README.md:64-105` | oui |
| 6 | Parcours de progression / « Pourquoi cet ordre ? » | `GenAI/README.md:117-133` ; `Sudoku/README.md:170-231` | niveau 1 : oui |
| 7 | Prerequis & environnement | `SymbolicAI/README.md:72-84` | oui |
| 8 | Exercices (couverture) | `SymbolicAI/README.md:497-512` | si exercices |
| 9 | Ponts cross-series (spécifiques) | cf. anti-pattern 3 | optionnel |
| 10 | References | `GameTheory/README.md:421-459` | recommande |
| 11 | FAQ (bornee) | cf. anti-pattern 4 | optionnel |

## Format des elements

### 1. Pitch

Le fil rouge de la serie pose en une phrase, puis 1-2 phrases de cadrage. Modèle : `Sudoku/README.md:1-10` (equilibre concision/information). Pas de bandeau de chiffres en ouverture : les decomptes exacts vivent dans le catalogue genere.

### 2. Navigation

Une seule barre, en tete de fichier, sous le titre : lien parent + precedent + suivant. Seul exemplaire actuel du depot : `GenAI/Image/README.md:3` (runner-up : `ML/README.md:275-276`, liens en pied). A generaliser : c'est l'element le plus absent (2 READMEs niveau 1 sur 12, 1 niveau 2 sur 25).

### 4. Objectifs d'apprentissage

Numerotes, verbes d'action, en trois categories : techniques / methodologiques / applicatifs. Modèle : `CaseStudies/README.md:81-105` (competences verifiables). Present dans 8 series sur 12 ; a creer pour RL, a normaliser pour GenAI et QuantConnect.

### 5. Table des notebooks

Colonnes normalisees : `# | Notebook | Kernel | Contenu | Duree`. Modèle : `GameTheory/README.md:64-105` (fil principal et side-tracks separes). Colonne optionnelle « Apport conceptuel » par notebook, differenciateur majeur de `Search/README.md:82-113` -- a generaliser quand la serie s'y prete. Les miroirs C#/Python (Sudoku) ou les phases (QuantConnect) restent des specificites legitimes : adapter les colonnes, pas les supprimer.

### 6. Parcours de progression

Profils de progression chiffres en heures (modèle : `GenAI/README.md:117-133`, 4 profils 20h -> 120h+) ou encart « Pourquoi cet ordre ? » justifiant la sequence (modèle : `Sudoku/README.md:170-231`).

### 7. Prerequis & environnement

Tableau : Kernel / Env special / Packages / Cles API. Modèle : `SymbolicAI/README.md:72-84`. Renvoyer au notebook de setup de la serie plutot que dupliquer les instructions d'installation du README principal.

### 9. Ponts cross-series

Un pont doit nommer le notebook ou le concept precis **des deux cotes** (ex. : « le solveur Z3 de Sudoku-7 reprend l'automate symbolique de Search-Part2-X »). Une ligne generique « voir aussi la serie ML » n'apporte rien : la retirer plutot que la garder.

### 10. References

References academiques avec couverture par notebook + bibliotheques + formalisations le cas echeant. Modèle : `GameTheory/README.md:421-459`.

---

## Anti-patterns a corriger (releves dans l'existant)

1. **Decompte avant le pourquoi** -- bandeau de chiffres en gras en ouverture (`GenAI/README.md:12`). Les chiffres font foi dans `COURSE_CATALOG.generated.md` ; le README ouvre sur la pedagogie.
2. **Duplication parent/enfant quasi-verbatim** -- ex. « l'audio, parent pauvre » present dans `GenAI/README.md:58` ET `GenAI/Audio/README.md:12`. Regle : le parent resume en un paragraphe + lien ; le detail appartient a l'enfant.
3. **Ponts copies-colles** -- bloc « Cross-series bridges » au format identique dans 9 READMEs sur 12, connexions generiques d'une ligne (`ML/README.md:264-269`). Cf. format section 9.
4. **FAQ hypertrophiees** -- souvent le plus gros bloc du fichier (`Sudoku/README.md:606-668` : 63 lignes ; `GameTheory/README.md:354-420` : 67 lignes). Borner a ~6 questions ; le surplus remonte dans l'intro ou part en doc dediee.
5. **Navigation absente** -- generaliser la barre de `GenAI/Image/README.md:3` (cf. section 2).

## Regles de redaction (heritees de la passe Partie 1)

- **Ton sobre et neutre** : pas de jugement de valeur sur des decisions editoriales internes, pas d'auto-celebration (« est assume », « volontairement severe » sans information pour le lecteur).
- **Pas de vocabulaire de conventions internes** : les noms de regles du depot (« C.1 », « stubs conformes », « anti-regression ») n'ont pas leur place dans un README public ; decrire l'effet utile pour le lecteur (« le notebook s'execute de bout en bout meme exercices non faits »).
- **Superlatifs coherents inter-series** : un seul « la plus grande serie » dans le depot (GenAI) ; les autres se qualifient (« l'une des plus vastes »). Pas de revendications concurrentes.
- **Fidelite aux notebooks** : ne promettre que ce que les notebooks demontrent reellement ; verifier avant d'ecrire (lecture des notebooks, pas du seul titre).
- **Chiffres** : pas de decomptes manuels (notebooks, heures totales) qui rouilleront -- renvoyer au catalogue genere.

## Marqueurs CATALOG-STATUS (regle dure)

Les blocs CATALOG-STATUS et `COURSE_CATALOG.generated.*` sont **bot-owned** : jamais d'edition manuelle, jamais de regeneration sur branche (cron only, cf. `docs/reference/catalog_markers.md`). Pour les READMEs ou le marqueur manque (sous-series Search, Probas/Infer, Probas/PyMC, ML/DataScienceWithAgents, GenAI/Image, QuantConnect/Python, QuantConnect/projects) : le **signaler dans le body de la PR**, l'ajout passe par le cycle bot.

## Application (Partie 2)

- **1 livrable par PR** : une serie, ou un petit lot coherent de 4-6 sous-series. Pas de composite.
- **Conserver les specificites legitimes** de chaque serie (miroirs C#/Python, phases, sous-series) : le gabarit normalise la structure, pas le contenu.
- **Cibles prioritaires (bimodalite niveau 2)** : remonter les stubs (`GenAI/CaseStudies` 61 lignes, `QuantConnect/projects` 86, `Search/Part1` 111) vers le gabarit ; reequilibrer les tres longs (`Probas/Infer` 1069 lignes) sans perte de contenu réel.
- **Enrichissement** : rapprocher chaque entrée de table du contenu réel du notebook (ce qu'il demontre, point cle), pour prolonger les intros du README principal.
