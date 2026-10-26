## Note de conception — palier 14 « Enjeu » (ICT-19 + ICT-19b) — phase 2

Lane `myia-po-2027:CoursIA-2`, tranche suivante de la consolidation par escaliers après #22289 (palier 10, en attente de merge). Dispatch ai-01 du 26/10 12:33Z.

### Plateau mesure (origin/main = `be9979b42413`)
- Famille ICT-19 : **2 carnets** (`ICT-19-EnjeuBattery-Python.ipynb`, `ICT-19b-EnjeuBattery-Raffinement-Python.ipynb`), aucun asset PNG.
- Aucune PR ouverte ne touche `ICT-19*` (L898 verifie). Aucun claim actif d'une autre lane sur ces chemins (`check_lane_claim.py 20298` : `blocking_lanes: []`).
- Choix du palier : la carte fixe l'arrivee 14 = Enjeu (tete ICT-19). Parmi les escaliers disponibles apres le palier 10, le palier 14 est le **plus petit scope** (14 refs de chemin contre 19 au palier 13 et 29 au palier 12) et son theme (Enjeu/batterie Gray-Scott) ne recouvre **aucun fichier du bloc lentilles** (palier 15, actif chez ai-01) — le risque de collision inter-lanes est minimal. Les paliers 11-13 restent a servir ; aucun n'est saute pour cause de difficulte, seulement d'ordre de service.

### Argument pedagogique (regle notebook-accretion-numbering)
La carte (strand 3) : « echec scalaire et reparation 19b a preserver ». L'escalier ICT-19 montre le cheminement naif->maturé :
- **ICT-19 (tete, arrivee 14)** : batterie de l'ENJEU — auto-maintien vs pur dissipateur, retour-au-bassin apres `do(·)` sur Gray-Scott S4 (#5489, spec #5483).
- **ICT-19b (membre)** : raffinement — mesure S4 **en espace de champ** qui resout le **faux nul** de la version scalaire (#5728, `repair_gain` +0.82±0.27).
Le maintien des deux carnets ordonnes dans une sous-serie `ICT-19/` preserve le recit de l'echec et de sa reparation — exactement la doctrine « escalier » de la carte (point 3) : les experiences dans l'ordre ou l'on s'est rendu compte qu'on etait entre dans le sujet naivement.

### Mouvement
1. `git mv` des 2 carnets vers `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-19/` (meme pattern que `ICT-15/` en #22289). **Aucun renommage de fichier** : les noms `ICT-19*` sont conserves, seul le dossier regroupe.
2. Reparation des liens entrants (prefix `ICT-19/`) : `ICT-Series/README.md` (l.181 lien ICT-19b + l.210 rangee de table ICT-19/19b), `docs/curriculum/recherche.md`, `docs/ict/feuille-de-route-notebooks.md`, `docs/notebook-metadata/scientific-review-registry.md`.
3. `docs/reference/rename-ledger.tsv` : 2 entrees append (ancien->nouveau chemin).
4. `pedagogy_density_baseline.json` : deplacement des 2 cles vers les nouveaux chemins (garde LOST_KEY/ORPHAN_KEY #13815/#16122).
5. Note de conception commitee dans `docs/ict/palier14-ict19-note-de-conception.md`.

### Non-touched (deliberes)
- `COURSE_CATALOG.generated.*` : byte-identique a main (regle catalog-pr-hygiene).
- `_quarto.yml`, `translations/iit/iit.csv` : non touches par le precedent #22289 — l'automatisation les regenerera.
- `scripts/tests/baseline_nb_nav_chain.json` : aucune cle ICT-19 (verifie).

### Re-execution
Aucune cellule source n'est modifiee (deplacement pur + liens dans d'autres fichiers) — C.2/C.3 : pas de re-exec due, les outputs committes restent les preuves d'execution. Precedent : #22289, deplacement pur, memes conditions.

### Questions ouvertes : aucune
Le mouvement est mecaniquement et pedagogiquement non ambigu (2 carnets, tete + membre, sous-dossier du meme nom). Aucune des questions du type Q1-Q8 de la note palier 10 ne se pose ici : pas de double fil, pas de module `ict/` non expose, pas de collision de numerotation (le dossier `ICT-19/` est un namespace neuf, aucun `ICT-19/` preexistant).
