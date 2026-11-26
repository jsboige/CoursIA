# Chantier 1 — tranche A9 : seconde attestation in-repo de l'op 2 « Abstraire à dette bornée »

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2027:CoursIA` · **date de mesure** 2026-10-15
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (op 1) · [A3](12204-ict-chantier-1-a3.md) (ops 3, 9) · [A4](12204-ict-chantier-1-a4.md) (op 4) · [A5](12204-ict-chantier-1-a5.md) (ops 2, 6, 10) · [A6](12204-ict-chantier-1-a6.md) (statuation 11-13 + file d'attente) · [A7](12204-ict-chantier-1-a7.md) (statuations ops 2, 6, quatrième loi) · A8 (conditions de rétrogradation, PR [#20814](https://github.com/jsboige/CoursIA/pull/20814) en attente) · [audit froid](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md) (les 14 opérations, trois axes)

## Ce que cette tranche fait

La statuation A7 avait laissé l'op 2 en FILE D'ATTENTE avec une voie de promotion explicite : *« une seconde instantiation in-repo sur autre série (Search, par exemple) qui abstrait à perte bornée mesurée sans citer Kroer-Sandholm — le patron exact de l'op 6 vient d'en faire la démonstration »*. Cette tranche livre cette seconde attestation : [`Search/Part5-Frontieres/Frontieres-11-Abstraction-Dette-ShortestPath-Python.ipynb`](../../MyIA.AI.Notebooks/Search/Part5-Frontieres/Frontieres-11-Abstraction-Dette-ShortestPath-Python.ipynb), instantiation sur plus court chemin pondéré, construite sans citation de Kroer-Sandholm (sources d'hommage : Culberson & Schaeffer 1998, Holte et al. 2005 — la lignée pattern databases, indépendante de la littérature jeux). *(Annoté le 2026-10-21 : la voie citée est celle d'**avant** le [Correctif A7](12204-ict-chantier-1-a7.md#correctif-du-2026-10-21--la-preuve-dindépendance-requalifiée-revue-externe-dispatch-ai-01), qui refonde la promotion sur l'**origine** ; ce dossier la satisfait déjà sur ses éléments positifs — littérature propre citée, algorithme distinct — voir la statuation ci-dessous.)*

## Statuation — Opération 2 « Abstraire à dette bornée » : promotion PROPOSÉE

Les deux attestations in-repo, indépendantes par le domaine :

| Attestation | Substrat | Témoin |
|---|---|---|
| `GameTheory-19-Abstraction-a-Dette-Python.ipynb` (#12208, exécutée) | jeux à somme nulle (fusion d'états) | courbe de dette mesurée P6→P2, garantie transportée |
| `Search/Part5-Frontieres/Frontieres-11-Abstraction-Dette-ShortestPath-Python.ipynb` (cette tranche, exécutée) | recherche de chemin (partition de la carte, agrégation des traversées) | borne admissible auditée 0/400, contre-témoin moyenne, courbe de dette non monotone |

**Re-mesures firsthand de ce cycle** (une statuation ne s'appuie pas sur la mesure d'un autre sans relire — G.1) :

- Frontieres-11 : **cellules code toutes exécutées (`execution_count` contigu dès 1), 0 erreur, sorties présentes** (lecture JSON du carnet post-papermill, kernel python3) ;
- **Indépendance par construction confirmée : 0 occurrence de `Sandholm`/`Kroer` dans Frontieres-11** (grep insensible à la casse), contre **5 occurrences dans GT-19** — le contraste exact qui avait fondé la promotion de l'op 6 par Search-03f. L'indépendance n'est pas une allégation, elle est mesurée dans le texte de l'artefact. *(Requalifié le 2026-10-21 : ce contraste de grep est un **indice documentaire**, pas la preuve — le critère d'omission est déclassé par le [Correctif A7](12204-ict-chantier-1-a7.md#correctif-du-2026-10-21--la-preuve-dindépendance-requalifiée-revue-externe-dispatch-ai-01) ; ce qui porte l'indépendance de Frontieres-11 est sa **preuve positive d'origine** — sources d'hommage citées Culberson & Schaeffer 1998 / Holte et al. 2005, lignée pattern databases distincte de la littérature jeux, algorithme de bornage admissible distinct du cadre Kroer-Sandholm.)*

**Témoins de la loi « le relèvement transporte une garantie » dans Frontieres-11** (valeurs déterministes, graine 20261015, toutes imprimées par le carnet exécuté) :

| Témoin | Mesure imprimée |
|---|---|
| Borne min admissible (k=6) | **0 violation / 400 requêtes** (200 longues + 200 courtes), contre l'oracle Dijkstra |
| Contre-témoin agrégation moyenne (k=3) | **5 / 200 violations sur les courtes**, 0/200 sur les longues ; premier contre-témoin (20,2)→(21,3) : borne 6.67 > optimum 4 |
| Borne resserrée (interne minimal payé) | **39.0** (vs borne simple 12, optimum 130), admissible **0/400** |
| Relevé par couloir | bracket **[39.0, 138]** contenant l'optimum 130, couloir 252/576 sommets (43 %), **dette 8** |
| Courbe de dette (k=12→2) | non monotone mesurée : dette 0 (4 classes) → 34 (64 classes) → 8 (144 classes) — la dette se mesure, ne se prédit pas |

**Verdict : promotion PROPOSÉE.** Les trois conditions de la voie A7 sont réunies : (1) seconde instantiation in-repo, (2) autre série que GameTheory, (3) perte bornée **mesurée** sans citer Kroer-Sandholm. La statuation formelle dans la table revient à la relecture du chantier (comme A7 avait statué sur les dossiers d'A5) ; ce ledger en est le dossier. *(Annoté le 2026-10-21 : la condition (3) doit se lire sous la voie **refondée** par le [Correctif A7](12204-ict-chantier-1-a7.md#correctif-du-2026-10-21--la-preuve-dindépendance-requalifiée-revue-externe-dispatch-ai-01) — origine documentairement établie (littérature propre citée, algorithme distinct du cadre Kroer-Sandholm, perte bornée mesurée), l'omission n'étant ni nécessaire ni suffisante. Le dossier la satisfait sur ces éléments : la statuation devra peser l'**origine**, non le contraste de grep.)*

## Ce que le carnet ajoute au-delà du critère

La LOI IV d'A7 (« la mesure met au prix les hypothèses de la preuve ») y trouve une occurrence de plus, d'une forme non recensée : l'**admissibilité comme propriété toute-requête**. La borne min ne ment sur aucune des 400 requêtes mesurées ; l'agrégation moyenne — « plus représentative », donc plausible — ment sur les courtes (5/200) et pas sur les longues (0/200) : l'erreur se cache derrière la dette interne quand le trajet est long. Le carnet en tire la leçon de certification : une borne certifie des requêtes, pas des moyennes — l'admissibilité « en général » est déjà mensongère quelque part.

La non-monotonie de la courbe de dette (34 à 64 classes, 8 à 144) est assumée comme contenu : le couloir désigné par le plus court chemin abstrait suit les traversées les moins chères, pas les trajets les plus sages — c'est précisément pourquoi la loi exige une dette *chiffrée à chaque usage* et non estimée a priori.

## Portée de ce qui n'a pas été vérifié

- La statuation formelle (édition de la table dans le body de l'EPIC) n'est pas faite par cette tranche — elle revient à la relecture du chantier.
- Les ops 3 et 5, également en file d'attente, sont couvertes par le claim `myia-ai-01:CoursIA-2` (Search-14a/03g/03h) ; cette tranche ne les touche pas.
