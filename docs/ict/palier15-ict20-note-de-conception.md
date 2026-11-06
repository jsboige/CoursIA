# Palier 15 « Lentilles et représentations ICT » — note de conception (tête ICT-20)

Lane `myia-po-2023:CoursIA`. Note rendue sur l'issue (#20298, c.6607814524) et
arbitrée par le coordinateur (c.6609950982, 03/11) **avant la première PR** :
Q1 (capstone déplacé tel quel, construit dans un grain séparé), Q2 (seul
`Dissociation-DehaeneF2-SelfReport` rejoindra le bloc observateur en T2) et
Q3 (tranches étalées sur plusieurs cycles) sont accordées telles quelles.

## Plateau mesuré (`origin/main` = `1596350104dd`, 03/11)

- 80 carnets à plat dans `MyIA.AI.Notebooks/IIT/ICT-Series/`, 4 sous-séries
  déjà constituées (`ICT-12`, `ICT-14`, `ICT-15`, `ICT-19`). Le palier 15 est
  le cinquième.
- L898 : seule PR ouverte touchant le périmètre = #24452 (`ICT-36d/36e`), qui
  contraint T3 à attendre son merge ; aucun conflit avec T1.
- Claims : `CLEAR` pour la lane (2 claims périmés contournés).

## Périmètre et tranches

27 carnets sur `main`, découpés en 4 tranches pour rester sous la borne G.4.
Le dossier porte le sujet de la tête (`ICT-20-FeatureCatastrophes/`), comme
les quatre existants — pas un numéro de palier.

| Tranche | Carnets | État |
|---|---|---|
| **T1 — Substrat** | 20, 21, 21b, 21c, 22, 22b | livrée (cette PR) |
| T2 — Observateur | 23, 24, Dissociation-DehaeneF2 | suit T1 mergé |
| T3 — Lentilles | 36, 36b-f, 37, 38, 39, 40a | attend le merge de #24452 |
| T4 — Inoculation / axe douleur | 42, 42b-f, 43, 47, 47b | suit T1 mergé |

L'argument pédagogique est la **chaîne de lecture** : ICT-20 pose ce qu'est
une représentation qui casse ; les SAE (21) la rendent lisible ; le substrat
LLM (22) la rend intervenable ; les lentilles (36-40a) sont les instruments ;
l'inoculation (42-43) et l'axe douleur (47) mesurent ce que coûte de changer
d'instrument.

## Mouvement (identique à chaque tranche — celui du palier 14)

1. `git mv` des carnets de la tranche dans `ICT-20-FeatureCatastrophes/`.
2. Réparer les liens entrants et sortants (voir addendum pour l'étendue
   mesurée de T1, plus large que le palier 14).
3. Append à `docs/reference/rename-ledger.tsv` (une ligne par carnet).
4. Déplacer les clés dans `scripts/notebook_tools/pedagogy_density_baseline.json`
   (garde `LOST_KEY`/`ORPHAN_KEY` #13815/#16122).
5. Rangée du palier dans la table de `docs/ict/README.md`.

Non touché : `COURSE_CATALOG.generated.*` (byte-identique, #9377),
`translations/iit/iit.csv` (purge par le pipeline de sync, précédent palier
14). `scripts/tests/baseline_nb_nav_chain.json` : re-clé chirurgical en T1
(voir addendum), le palier 14 ayant été neutre seulement parce que sa
sous-série avait une seule entrée de chaîne.

## Addendum T1 — ce que la PR a fait de plus que le geste minimal

- **`_quarto.yml` mis à jour** : la note disait « non touché » en
  calquant le diff du palier 14, mais le palier 14 avait laissé la liste
  Quarto périmée et #23295 l'a réparée après coup. L'invariant sur `main`
  est un `_quarto.yml` cohérent avec le disque ; la réparation est pliée
  dans la PR qui déplace (précédent #23295).
- **ICT-22 ré-exécuté** : deux accès `Path("traces/…")` cwd-relatifs et un
  `sys.path.insert(0, os.getcwd())` cassaient depuis la profondeur +1
  (lecture `p.stat()` à l'impression). Source réparée +
  re-exécution Papermill complète (C.2) : 0 erreur,
  chiffres identiques (509/484 Kio, ec_gain 3.438…) ; deux nouveaux flux
  `UserWarning` de `sae_traces.py:131` (évolution du module depuis la
  dernière exécution — traces legacy sans champ `instrument`).
- **Environnement de la ré-exécution, remonté au-dessus du run précédent.**
  La ré-exécution du 03/11 avait tourné sur `numpy 2.3.5` / `python 3.13.3`,
  sous l'exécution antérieure (2026-09-25, `numpy 2.4.6` / `python 3.13.15`).
  Le kernel `python3` canon de po-2023 a été réparé entre-temps (env conda
  dédiée) et la série re-ré-exécutée le 06/11 sous `numpy 2.5.2` /
  `python 3.13.16` : la ligne de version de l'artefact **remonte** au-dessus
  des deux runs précédents, et le smoke GPU d'ICT-21 est rejoué en direct
  (`SMOKE OK`, pipeline Qwen3.5-9B + SAE sur RTX 3090) au lieu du message
  de repli.
- **Liens croisés hors série réparés** : `2.9-Grokking` et
  `3.5-Phenomenes-de-Generalisation` (ML) pointaient vers ICT-21 à plat ;
  `docs/ict/cadrage-trajectoires-representations.md` et
  `docs/ict/dissolution-scalaires.md` aussi. Les mentions en prose sans lien
  (barest noms de fichiers) restent, conformément au précédent du palier 14.
- **Chaîne de navigation interne complétée + baseline nav-chain re-clé.**
  L'organe `check_notebook_nav_chain.py` juge désormais le dossier comme sa
  propre série, et la descente d'un niveau a cassé ce qu'il mesure : la
  chaîne de lecture 20 → 21 → 21b → 21c → 22 → 22b n'existait physiquement
  qu'en liens *retour* (21b → 21, 21c → 21/21b) — rien ne menait *vers* 21c,
  22 ni 22b (4 `orphan_entry`), puis la marche depuis l'entrée ICT-20
  s'arrêtait à 21 (`independent_chain`). Cinq lignes `**Navigation**` posées
  ou complétées (20, 21, 21b, 21c ×2, 22 — markdown seul, pas de
  ré-exécution due) rendent la chaîne marchable de bout en bout depuis sa
  tête ; la sous-série expose désormais l'argument de chaîne que la note
  revendique. Le baseline est re-clé en conséquence : 2 clés plates périmées
  (21c, 22) retirées, 1 entrée transitoire `ICT-23` ajoutée (son seul lien
  entrant intra-série était celui d'ICT-22b, désormais externe ; T2
  descend ICT-23 dans la sous-série et l'entrée disparaît d'elle même). Les
  18 autres findings résolus que l'organe signale sont le drift de `main`
  depuis le 2026-10-23 (GameTheory, MGS, Sudoku — hors périmètre), à
  absorber par la prochaine régénération du baseline sur `main` propre.
