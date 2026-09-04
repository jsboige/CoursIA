# Chantier 1 — tranche A4 : l'opération 4 (*Décomposer localement — poser un recouvrement*) passe de `RAPPORTE` à `FIRSTHAND`

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2027:CoursIA` · **date de mesure** 2026-09-03
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (opération 1) · [A3](12204-ict-chantier-1-a3.md) (opérations 3, 9) · [audit froid](12204-ict-chantier-1-audit-froid.md) (les 14 opérations, trois axes)

## Ce que cette tranche fait, et ce qu'elle ne fait pas

L'audit froid avait laissé l'opération 4 en `TABLE` avec la provenance `RAPPORTE` et **une dette ouverte assumée** (« qui décide où sont les bords ? »). La tranche ne **re-décide** donc rien : elle **relit les trois attestations dans le dépôt** et rapporte ce que la lecture change.

Elle ne touche à aucune autre opération (l'opération 5 est tombée — Tombée 3 de l'audit froid — et n'est pas reprise ici). Elle **corrige en revanche l'identification d'une attestation** : l'« orchestration EPITA » citée par l'audit froid, d'abord déclarée introuvable par un grep trop étroit, **est retrouvée dans le dépôt** (trois témoins committés, Attestation 3) et reste dans la liste des témoins attestables — le compte `2+` (critère d'admission de l'EPIC) tient de toute façon par les Attestations 1 et 2. Le vrai apport, comme en A2, est la **précision de la dette** : la lecture montre que la question « qui décide des bords » reçoit une réponse différente selon la strate — **prouvée** côté Hashlife, **laissée au choix de l'expérimentateur** côté ICT-15d.

## Rappel de l'énoncé mesuré

> **4 — Décomposer localement — poser un recouvrement** : les bords doivent être définis avant les sections.
> Témoin : le recouvrement lui-même, non-jouet.
> Dette déclarée : **qui décide où sont les bords ?** (ouverte)

## Attestation 1 — Hashlife, *la marge prouvée avant la correction de la section* (Lean-formel, non-jouet)

`MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/Life/HashlifeCorrectness/Foundation.lean`
Companion : `HashlifeMarginFragment.lean` (même lake) ; notebook `Lean-16j-Conway-Hashlife-Correctness-Native.ipynb` (**43 cellules, 15 code, `execution_count` 1..15, 0 erreur**).

C'est l'attestation la plus littérale de l'énoncé, et c'est le **témoin non-jouet** que l'EPIC demandait : la preuve de correction de l'algorithme Hashlife réel, où la décomposition en macro-cellules **ne commence qu'après** que les bords (les marges) sont prouvés assez larges. La chaîne, dans l'ordre où le lake la construit :

| Étape | Théorème | Rôle dans « les bords avant les sections » |
|---|---|---|
| Le bord est défini d'abord | `cellMargin` (Foundation.lean:47), `cellMargin_true_iff` (:53) | la marge d'une macro-cellule est **définie avant** toute correction de section centrale |
| Le pas local borne l'information | `step_local` (:899), `step_light_cone` (:929) | l'information ne progresse pas plus vite qu'une cellule par pas de temps — le cône de lumière borne ce qu'une cellule « voit » |
| Le bord est prouvé suffisant | `padCenter2_margin_ge_jumpReach` (:1322), `padCenter2_margin_strictly_gt_jumpReach` (:1334) | la marge **couvre le rayon de saut** de la macro-cellule : ce qui est hors marge ne peut pas influencer la fenêtre centrale |
| La section est correcte | `padCenter2_correct` (:1154), `hashlife_correct_margin` (HashlifeMarginFragment.lean:158) | la correction de la section centrale est prouvée **une fois la couverture établie** |

L'ordre d'implication est la preuve de l'énoncé : `padCenter2_margin_ge_jumpReach` est un théorème qui **décide du bord** — la marge n'est pas une constante choisie par goût, c'est le rayon minimum qui rend la correction locale prouvable. Lean-16j section 4 (« Les quatre murs ») formalise la charnière : `isAlive_true_iff_mem` est « le théorème-charnière : une cellule vivante à l'instant $t$ si et seulement si elle appartient au cône de lumière des cellules initiales … le socle sur lequel Hashlife peut découper l'espace en macro-cellules sans jamais consulter l'extérieur du cône ».

**Ce que la lecture firsthand ajoute.** L'audit froid comptait Hashlife comme attestation « empirique » réputée forte ; la lecture la qualifie plus précisément : la décomposition locale de Hashlife n'est pas un découpage **jouet** — c'est un découpage dont les bords **se chevauchent** (chaque macro-cellule calcule sur cellule + marge, les marges des voisines se recouvrent) et dont la correction est **prouvée** sous la seule condition que la marge couvre le saut. Au sens de l'énoncé, le « recouvrement » est réel : les domaines de calcul se recouvrent par leurs marges, et les bords sont définis (et prouvés) **avant** les sections.

Hygiène d'instrument (cf. A2) : `python scripts/lean/count_code_sorry.py --json` → `conway_lean` **`distinct_code_sorry: 1`** (naive 169, code 2) — l'attestation est portée par des preuves réelles, pas par du `sorry`.

## Attestation 2 — ICT-15d, *l'obstruction de Čech par fenêtres contiguës* (empirique, jouet assumé)

`MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15d-CechObstruction.ipynb` (**16 cellules, 9 code, `execution_count` 1..9, 0 erreur**)
Module : `ict/cech_obstruction.py` (`proxy_sections` :63-89).

Le notebook détecte l'obstruction de cochaînes de Čech sur des **trajectoires synthétiques** (« Banc expérimental : 4 substrats ICT-15c », `window_size` adapté « pour avoir 20–40 fenêtres contiguës par substrat »). La décomposition y est réelle et mesurée — `proxy_sections` découpe la trajectoire en **fenêtres** et évalue chaque proxy par fenêtre — mais le statut « jouet » de l'audit froid est **confirmé avec une nuance qui le durcit** :

- Le vocabulaire cochaîne de Čech est **nominal**. Les « sections » de `proxy_sections` sont des fenêtres **contiguës disjointes** — la docstring le dit noir sur blanc (cech_obstruction.py:86-88) : *« Les fenêtres sont non-recouvrantes (découpage contigu) : c'est le choix le plus sobre pour un « candidat » -- un découpage glissant produirait des sections corrélées par construction, masquant l'obstruction »*. Or l'obstruction de Čech se définit sur des **intersections** de recouvrement — sur une partition il n'y a pas d'intersections, et la « cochaîne » y est calculée sur un complexe trivial. Le choix est honnête et documenté (anti-corrélation), mais il fait du « recouvrement » de ICT-15d un **homonyme** de celui de l'énoncé : une partition, pas un recouvrement au sens topologique.
- C'est l'inverse exact du choix de Hashlife : Hashlife **recouvre par marges** (nécessité de correction), ICT-15d **désigne délibérément des fenêtres non-recouvrantes** (anti-corrélation statistique). Les deux sont des stratégies défendables — pour des objets différents.

**Ce que la lecture firsthand ajoute.** L'exercice 1 du notebook (stub `TODO` étudiant, conforme C.1) demande explicitement de **tester la stabilité du verdict selon `window_size`** : la dette « qui décide où sont les bords » n'y est pas seulement déclarée, elle est **instrumentalisée** — le notebook sait que son verdict dépend du choix des bords et en fait l'exercice. C'est le comportement attendu d'un candidat honnête, et c'est exactement la trace que la table doit porter.

## Attestation 3 — « orchestration EPITA » — **retrouvée dans le dépôt (première identification trop étroite)**

L'audit froid listait une troisième attestation : l'« orchestration EPITA ». Une première passe de cette tranche l'avait déclarée introuvable — **identification fausse, rétractée le 2026-09-03** : le grep était borné aux docs du harnais (`docs/reference/teaching-context.md`, `cluster-agents.md`) et ne couvrait ni les notebooks des séries ni les manifestes de vendoring. Témoins vérifiés firsthand, tous committés dans le dépôt :

- `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-3-orchestration.ipynb` — un notebook **entièrement dédié** à l'orchestration (deux paradigmes de composition), référencé depuis le rung 0-init ;
- `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/Argument_Analysis_Agentic-0-init_agent.ipynb` — ses outputs committés portent **11 occurrences** des logs `[Orchestration.Setup]` (dépendances `jpype` + `semantic_kernel`, configuration LLM). Les trois autres notebooks `_agent` de la série n'en portent aucune : le témoin est ce notebook-là, pas la série ;
- `MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/NOTICE-EPITA` — le manifeste qui épingle fichier par fichier le code vendré du projet `argumentation_analysis` **Epita 2025** (l'objet de #14026).

Identification : le **moteur d'orchestration agentique d'analyse argumentative du projet Epita 2025** (cf #14026).

Verdict de cette tranche sur cette attestation : elle **reste dans la comptabilité du dépôt**, avec ses trois témoins committés. Le critère d'admission de l'EPIC — **≥ 2 attestations indépendantes + témoin connu** — reste satisfait par Attestation 1 + Attestation 2 ; le retour d'EPITA ne change donc pas le compte `2+`, il **restaure l'inventaire** : la table cite de nouveau EPITA parmi les témoins du dépôt, avec sa force exacte (empirique, la moins forte des trois).

**Leçon methodologique** : conclure à l'absence d'un témoin depuis un grep borné aux docs du harnais (`docs/reference/`) est une identification fausse par construction — le code vendré et les notebooks des séries vivent sous `MyIA.AI.Notebooks/**`, avec leurs manifestes de vendoring (`NOTICE-*`). Toute recherche de témoin couvre ces arborescences avant de conclure à l'absence.

## Verdict de la tranche

| Axe | Avant (audit froid) | Après (cette tranche) |
|---|---|---|
| provenance | `RAPPORTE` | **`FIRSTHAND`** |
| attestations | `2+` (ICT-15d jouet, Hashlife, EPITA) | `2+` — **recensées précisément** : Hashlife (Lean-formel, non-jouet) + ICT-15d (empirique jouet, partition avouée) + EPITA (empirique, trois témoins committés, identification restaurée) |
| force | empirique | Lean-formel (bords prouvés avant sections) **+** empirique (verdict à bords explicites, exercice d'invariance) |
| statut | `TABLE` | **`TABLE`** — confirmée |

## La dette, reformulée par la lecture

Le corps de l'EPIC demandait : « **qui décide où sont les bords ?** ». La lecture firsthand ne lève pas la dette — elle montre qu'elle a **deux régimes**, et que c'est cette bipartition qui est le vrai énoncé :

> **Côté Hashlife, la preuve décide des bords** : la marge n'est pas un choix — c'est le plus petit rayon qui rend la correction locale prouvable, et ce rayon est l'énoncé d'un théorème (`padCenter2_margin_ge_jumpReach`). Un découpage Hashlife n'a pas de « qui décide » : le bord est déterminé par la condition de correction, il est prouvé avant les sections, et le recouvrement des marges est une conséquence, pas une décision.
>
> **Côté ICT-15d, l'expérimentateur décide des bords, sans théorie** : `window_size` est un paramètre choisi (20–40 fenêtres), dont la seule contrainte est l'**invariance du verdict** (exercice 1). La dette y est entière : aucune théorie ne dit combien de fenêtres (ni lesquelles) suffisent pour qu'un verdict d'obstruction témoigne — l'invariance se **teste**, elle ne se **dérive** pas.

En A2, la dette de l'opération 1 était « nos attestations sont trois post-mortems ». La dette de l'opération 4 se précise de la même façon : **le cas prouvé (Hashlife) montre que la question a une réponse formelle — c'est le cas empirique (ICT-15d) qui ne la connaît pas**. La table doit porter cette bipartition : la dette n'est pas « qui décide des bords » en général, mais « **quel critère garantit qu'un découpage empirique témoigne, en l'absence de théorème de correction** ».

## Suites ouvertes par cette tranche

- **Inventaire restauré** : l'attestation « orchestration EPITA » **reste** dans la liste des témoins du dépôt — trois fichiers committés la portent (notebook dédié, logs `[Orchestration.Setup]` dans les outputs, `NOTICE-EPITA`) ; la table de l'EPIC la conserve lors de la consolidation, avec la précision de force (empirique, la moins forte des trois).
- **Les bords d'un découpage empirique n'ont pas de critère** : la question « invariance du verdict vs. choix des bords » pourrait devenir un grain de recherche propre (une strate qui **dériverait** un critère de choix de `window_size` au lieu de le tester) — hors périmètre A4, proposé comme suite naturelle.
- **A2 → A4** : la chaîne de vérification du chantier progresse (op 1 en A2, op 4 ici) ; les opérations 3/9 (A3) et les opérations 7/8/10/12 (déjà `FIRSTHAND` dans l'audit froid) sont les autres grains de vérification restants.