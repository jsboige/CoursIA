## Note de conception — tranche ICT-12 « Valence / Animats » (ICT-12 + 12b + 12c + 12d + 12e) — phase 2

Lane `myia-po-2027:CoursIA-2`, tranche de la consolidation par escaliers (#20298), après le palier 10 (ICT-15/, #22289), le palier 14 (ICT-19/, #22780) et la tranche ICT-14 (ICT-14/, #22798).

### Plateau mesure (origin/main = `a9bfa41b15e1`)
- Famille ICT-12 : **5 carnets** — `ICT-12-ValenceFieldsAndAnimats` (tête), `ICT-12b-LearnedValence`, `ICT-12c-PregnanceAnimat`, `ICT-12d-InhibitedActionAnimat`, `ICT-12e-Value-of-Information-Animat` — aucun asset PNG propre.
- Aucune PR ouverte de consolidation ne touche `ICT-12*` (vérifié via l'API search) ; aucun claim actif d'une autre lane sur ces chemins. Les claims du fil #20298 sont ICT-15/ICT-19/ICT-14 (cette lane) et ICT-20 (ai-01) ; le seul claim ICT large est un claim **épique** stale >48 h — les tranches à scope de chemin précis procèdent (précédents paliers 10, 14, 19, même situation).

### Argument pédagogique (règle notebook-accretion-numbering)
La doctrine « escalier » de la carte #20298 : les expériences dans l'ordre où l'on s'est rendu compte qu'on entrait dans le sujet naivement. L'escalier ICT-12 (5 carnets, arc Valence → Animat) :
- **ICT-12 (tête)** : premier toy model **actantiel spatial** — des animats dans un champ de valence ; les rôles actantiels de Thom deviennent des **grandeurs mesurées** (capture, évasion, irréversibilité, switching). Verdict honnête : l'anticipateur `p̂` **gagne** en balistique, **perd** en erratique — le modèle interne paie son coût où la source échappe au réactif *et* reste prévisible (régime-dépendant).
- **ICT-12b (membre)** : l'expérience manquante (#7740) — la valence n'est plus *programmée*, elle est **apprise** (Rescorla-Wagner), **transférable** et **réversible**, et surtout **distincte de la prédiction** (π vs `p̂`) — sur banc désincarné.
- **ICT-12c (membre)** : la dissociation `p̂`/π **incarnée** (#7740, jambe C1) — l'animat porte la valence apprise dans l'arène ; la matrice de dissociation montre que prégnance et représentation restent deux grandeurs distinctes, même incarnées.
- **ICT-12d (membre)** : le pendant négatif (#7741, jambe C2) — **inhibition de l'action** (Laborit) : l'opérateur de workspace `W` qui *s'effondre* sous inhibition (rigidification, dette d'irréversibilité).
- **ICT-12e (membre)** : la **valeur de l'information** pour l'animat décisionnel (#13569, greffe 3) — le carnet *pose* le problème et *laisse les organes natifs du dépôt calculer* (`ict.voi` + `Probas/DecisionTheory/voi`, Infer.NET × PyMC en contrôle croisé).

Le regroupement dans `ICT-12/` préserve ce récit ordonné (mesure → apprentissage → incarnation → inhibition → décision).

### Mouvement (6 étapes)
1. `git mv` des 5 carnets vers `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12/` (5 renames, **100 % de similarité**). **Aucun renommage de fichier** : les noms `ICT-12*` sont conservés, seul le dossier regroupe.
2. **Réparation des liens** — ce qui distingue cette tranche des paliers 10/14/19 : les 5 carnets portent **26 liens relatifs sortants** vers le reste de la série (`../../Probas/…`, `../../../docs/…`, `ict/…`, les siblings `ICT-13/18/30`, `../README.md`, `ICT-0-Framing.md`). Descendre d'un niveau les casse tous : **26 liens sortants des cellules markdown** re-préfixés d'un `../` (les **14 liens intra-famille** `ICT-12*` restent sans préfixe — les 5 carnets sont désormais *siblings*). Côté entrant : **32 refs de chemin** préfixées d'`ICT-12/`, réparties sur les fichiers porteurs — `ICT-Series/README.md`, `thom-synthese-distillation.md`, le carnet frère `ICT-Synthese-CrossSubstrat`, et 7 docs (`cadrage/grothendieckian-lens`, `cadrage/magnifica-humanitas-dialogue`, `curriculum/recherche`, `ict/feuille-de-route-notebooks`, `ict/genealogy-representation-interne`, `ict/tresse-cartographie`, `notebook-metadata/scientific-review-registry`).
3. `docs/reference/rename-ledger.tsv` : 5 entrées append (ancien → nouveau chemin).
4. `pedagogy_density_baseline.json` : 5 clés déportées (valeurs préservées) + `baseline_nb_nav_chain.json` : 1 clé (garde LOST_KEY/ORPHAN_KEY #13815/#16122).
5. Note de conception committée.

### Non-touché (délibéré)
- `COURSE_CATALOG.generated.*` : byte-identique à `main` (règle catalog-pr-hygiene) ; `_quarto.yml`, `translations/iit/iit.csv` : non touchés — l'automatisation les régénérera.
- `docs/ledgers/11690-ict-consolidation.md` : les 5 occurrences `### \`ICT-12…ipynb\`` sont des **mentions nues** en backticks (l'en-tête de lecture du carnet), pas des liens de chemin — non cassantes, non touchées.
- Les **5 entrées historiques** du `rename-ledger.tsv` (2026-10-01, ajout du suffixe `-Python`) : conservées telles quelles ; les 5 nouvelles entrées sont en append.
- `scripts/tests/test_detect_organ_duplication.py` : la mention `ICT-12e-…ipynb` y est une **donnée synthétique de test** (un diff factice pour l'organe de détection de duplication d'organe), pas un chemin de navigation — non cassante, non touchée.
- Les **mentions de sujet** nues (`ICT-12 (valence)`, cellules de tables) : le **nom** du carnet ne change pas, seule sa position de dossier change — non cassantes, non touchées.
- Les carnets `ICT-14`/`ICT-15`/`ICT-19` (PRs #22798/#22289/#22780 de cette lane) : leurs mentions d'ICT-12 sont **nues** (nom, pas chemin) — **aucune collision** avec ces PRs.

### Ré-exécution
Aucune cellule **code** n'est modifiée : le seul contenu de cellule touché dans les 5 carnets déplacés est des **cellules markdown** (réparation des liens sortants, 26 liens), plus des liens dans d'autres fichiers. Règle C.2, exception markdown. Pas de re-exec due — les outputs committés restent les preuves d'exécution. Précédents : #22289, #22780, #22798.

### Validation
- `git mv` : 5 renames à **100 % de similarité** (0 insertion / 0 suppression sur le contenu de rename).
- Liens sortants : 26 réécritures, appliquées **uniquement sur les cellules markdown** (script à vérification par cellule : le compte de chaque token dans le fichier brut == son compte dans les cellules markdown → aucun token dans un `outputs`/code n'est touché).
- Liens entrants : 32 préfixations, réparties sur les fichiers porteurs (garde anti-double-prefixe).
- `pedagogy_density.py --check-orphans` : **0 ORPHAN_KEY / 0 LOST_KEY pour ICT-12** (6 clés déportées présentes à l'ancien chemin vidé). Les `ORPHAN_KEY` restants sont en `GameTheory`/`GenAI`/`ML` : dette de baseline **pré-existante sur `main`**, hors périmètre (le diff ne touche que des chemins `ICT-12`).

### Questions ouvertes : aucune
Le mouvement est mécaniquement et pédagogiquement non ambigu (5 carnets, tête + 4 membres, sous-dossier du même nom `ICT-12/`, namespace neuf — aucun `ICT-12/` préexistant).
