## Note de conception — tranche ICT-14 « FreeEnergySurprise » (ICT-14 + ICT-14b) — phase 2

Lane `myia-po-2027:CoursIA-2`, tranche de la consolidation par escaliers (#20298), après le palier 10 (ICT-15/, #22289) et le palier 14 (ICT-19/, #22780).

### Plateau mesure (origin/main = `7d83cceded22`)
- Famille ICT-14 : **2 carnets** — `ICT-14-FreeEnergySurprise-Python.ipynb` (tête) et `ICT-14b-ActiveInferenceEFE-Python.ipynb` (membre) — aucun asset PNG propre.
- Aucune PR ouverte ne touche `ICT-14*` (vérifié via l'API search) ; aucun claim actif d'une autre lane sur ces chemins. Les claims spécifiques du fil #20298 sont ICT-15/ICT-19 (cette lane) et ICT-20 (ai-01) ; le seul claim ICT large est un claim **épique** de 15 jours (stale >48 h) — les tranches à scope de chemin précis procèdent (précédents paliers 10 et 14, même situation).

### Argument pédagogique (règle notebook-accretion-numbering)
La doctrine « escalier » de la carte #20298 : les expériences dans l'ordre où l'on s'est rendu compte qu'on entrait dans le sujet naivement. L'escalier ICT-14 :
- **ICT-14 (tête)** : l'énergie libre `F` attachée au représentant interne `p̂` d'ICT-10 — la *jambe énergie-libre* du triplet fondateur (Φ, F, K). Verdict honnête de la strate : à précision fixe, `F` n'est qu'un habillage du MSE ; la free energy formelle n'y était pas tracée.
- **ICT-14b (membre)** : raffinement — l'*expected free energy* (EFE) passe d'une quantité **observée** à un **pilote** de l'action (inférence active) ; le banc transforme la strate-formule en strate-banc (gate non-stationnaire CONFIRMED, null adverse tient).
Le maintien des deux carnets ordonnés dans une sous-série `ICT-14/` préserve le récit de la jambe F puis de sa montée en mécanisme prospectif.

### Nommage du dossier de sous-série
Le dossier porte le numéro du palier (`ICT-14/`) : c'est le pattern établi par les paliers précédents de la consolidation (#22289 `ICT-15/`, #22780 `ICT-19/`). Le sujet éclairé n'est pas dans le nom du dossier mais dans les noms des carnets (`FreeEnergySurprise`, `ActiveInferenceEFE`) et dans l'escalier de `ICT-Series/README.md`, qui reste l'index de lecture de la série. Si l'auteur veut un nom de dossier descriptif, c'est une décision qui s'applique uniformément à toutes les sous-séries de la consolidation, en PR dédiée — pas palier par palier.

### Mouvement
1. `git mv` des 2 carnets vers `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14/` (même pattern que `ICT-15/` #22289 et `ICT-19/` #22780). **Aucun renommage de fichier** : les noms `ICT-14*` sont conservés, seul le dossier regroupe.
2. Réparation des liens entrants (préfixe `ICT-14/`) : **liens entrants réparés** — `ICT-Series/README.md`, `thom-synthese-distillation.md`, le carnet frère `ICT-40b`, le cross-série `SymbolicAI/Lean/ANALYSE/ANALYSE-03-PFR-Lean.ipynb`, et les docs (`curriculum/recherche`, `ict/feuille-de-route-notebooks`, `ict/tresse-cartographie`, `ict/genealogy-representation-interne`, `ict/dissolution-scalaires`, `cadrage/grothendieckian-lens`, `notebook-metadata/scientific-review-registry`).
   - **Le lien frère intra-dossier** `ICT-14b → ICT-14` reste **sans préfixe** : les deux carnets deviennent *siblings* dans `ICT-14/`, leur lien relatif ne change pas.
3. `docs/reference/rename-ledger.tsv` : 2 entrées append (ancien → nouveau chemin).
4. `pedagogy_density_baseline.json` : 2 clés déportées + `baseline_nb_nav_chain.json` : 1 clé (la tête) — valeurs préservées (garde LOST_KEY/ORPHAN_KEY #13815/#16122).
5. Note de conception committée dans `docs/ict/ict14-freenergy-note-de-conception.md`.

### Non-touché (délibéré)
- `COURSE_CATALOG.generated.*` : byte-identique à `main` (règle catalog-pr-hygiene).
- `_quarto.yml`, `translations/iit/iit.csv`, `translations/symbolicai-lean/symbolicai-lean.csv` : non touchés — l'automatisation les régénérera.
- `ICT-Series/assets/readme/MANIFEST.md` : la mention `ICT-14-FreeEnergySurprise-Python.ipynb` y est une **citation de source** en basename (cellule d'origine d'un asset), pas un lien de navigation — non cassante, laissée telle quelle.
- Les **mentions de sujet** nues (`ICT-14 (free energy)`, `ICT-14 → ICT-20`, tables de cartographie) : le **nom** du carnet ne change pas, seule sa position de dossier change — non cassantes, non touchées.
- Le carnet `ICT-15` (dans le PR #22289 de cette lane) : ses 2 mentions d'ICT-14 sont des **mentions nues**, non cassantes — non touchées, donc **aucune collision** avec #22289.

### Ré-exécution
Aucune cellule **source** n'est modifiée : déplacement pur + liens dans d'autres fichiers ; les seules cellules touchées dans les carnets frères (`ICT-40b`, `ANALYSE-03`) sont des cellules **markdown** (règle C.2, exception markdown). Pas de re-exec due — les outputs committés restent les preuves d'exécution. Précédents : #22289 et #22780, mêmes conditions.

### Validation
- `git mv` : 2 renames à **100 % de similarité** (0 insertion / 0 suppression).
- Fixes de liens : substitutions vérifiées par dry-run avant application.
- `pedagogy_density.py --check-orphans` : **0 ORPHAN_KEY / 0 LOST_KEY pour ICT-14** — 2 clés déportées vers le nouveau chemin (vérifiées présentes), 0 clé ancien-chemin résiduelle. Les 33 `ORPHAN_KEY` que l'organe rapporte sont en `GameTheory`/`GenAI`/`ML` : dette de baseline **pré-existante sur `main`**, hors du périmètre de cette PR (le diff ne touche que des chemins `ICT-14`).

### Questions ouvertes : aucune
Le mouvement est mécaniquement et pédagogiquement non ambigu (2 carnets, tête + membre, sous-dossier du même nom `ICT-14/`, namespace neuf — aucun `ICT-14/` préexistant).
