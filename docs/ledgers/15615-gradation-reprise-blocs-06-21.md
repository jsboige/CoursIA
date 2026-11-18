# Ledger — Issue #15615 (gradation GameTheory, reprise : re-mesure des blocs 06-20 + entrées post-snapshot + bloc 21)

> **Bornage strict** : ce ledger couvre les **carnets des blocs 06 à 20** de la série GameTheory sur `origin/main` au **2026-10-26**, tête `7eff951f33b` — re-mesure à tête commune des périmètres des fournées B (`15615-gradation-fournee-b.md`, bornage `a492cda2b33` du 2026-10-10), C (`15615-gradation-fournee-c.md`, bornage `5e96ffec4cb` du 2026-10-10) et D (`15615-gradation-fournee-d.md`, bornage `cfa6bbaea4ca` du 2026-10-11) — **plus le bloc 21**, jamais couvert. Il **remplace comme source de vérité** les tables des fournées B-D pour les blocs 06-21, qui restent en place comme **mesures datées** de leur arbre respectif (même convention que le [tableau consolidé 01-05](15615-gradation-blocs-01-05-consolide.md) envers les strates Fondations et A).

## Origine

[NOT-DELIVERED] d'ai-01 du 2026-10-25T12:44Z sur #15615 : « re-mesurer les blocs 06 à 20, mesures à des têtes antérieures ; grader le bloc 21, jamais couvert, alors que l'arbre porte 111 carnets ». Les trois fournées B-D étaient mesurées à trois têtes distinctes (10-10, 10-10, 10-11) ; treize carnets arrivés depuis sont non gradés ; le capstone 21 n'a jamais eu de ligne de gradation. Le 16g, déclaré « non gradé, grain séparé » par l'addendum de la fournée D, n'a pas été gradé non plus : #20366 (fermée) n'a livré que le rebornage comptable 24→25 / 99→100, pas l'entrée de gradation — vérifié au fil de l'issue fermée avant ce travail.

## Méthode

Identique aux fournées : extraction JSON scriptée (kernelspec, comptes code/markdown, headers, sections Prérequis) sur `git show origin/main:<carnet>` à la tête courante ; provenance de chaque entrée post-snapshot par `git log --diff-filter=A` ; lecture firsthand de la section 1 et de la navigation pour les concepts et prérequis.

## Re-mesure des carnets couverts (blocs 06-20)

**71 carnets couverts par les fournées B-D sont toujours présents dans le dossier** (B 27, C 22, D 22 après exclusion de 20d/20e partis en GOL ; le 16g de l'addendum est gradé parmi les 12 post-snapshot ci-dessous). Re-mesurés à `7eff951f33b` : **48 stables, 23 dont les comptes ont dérivé**. Les dérives sont toutes des **prose/densité ou navigation** (grains #13410 « densité », escaliers #20381, ancres biblio #21544, réalignement de prose #20826, fusion de lectures jumelles #21377) — **aucune ne change les concepts ni la difficulté des lignes existantes** ; seule la colonne Cells des fournées a vieilli.

| Fournée | Carnet (dérive de comptes) | Au bornage | À `7eff951f33b` |
|---|---|---|---|
| B | 06-EvolutionTrust-Python | 63 (23) | 65 (23) |
| B | 06j-Bounded-Proofs-Reasoning-Costs-Python | 24 (11) | 32 (11) — densité #21386 |
| B | 07-ExtensiveForm-Python | 35 (15) | 36 (15) |
| B | 08-CombinatorialGames-Python | 34 (11) | 35 (11) |
| B | 08c-CombinatorialGames-Python | 40 (14) | 36 (14) — fusion 4 paires de lectures #21377 |
| B | 10-ForwardInduction-SPE-Python | 37 (15) | 38 (15) |
| C | 13-ImperfectInfo-CFR-Python | 64 (26) | 65 (26) |
| C | 14-DifferentialGames-Python | 51 (19) | 52 (19) |
| C | 15-CooperativeGames-CSharp | 65 (24) | 66 (24) |
| C | 15-CooperativeGames-Python | 69 (30) | 73 (30) — prose réalignée #20826, références #21185 |
| C | 15d-Mobius-Coalitions-Lean-Python | 26 (9) | 27 (9) |
| C | 15e-Coalition-Power-SMT-Python | 33 (11) | 34 (11) |
| C | 15g-AssistanceGames-2026-Python | 15 (8) | 16 (8) |
| D | 16-MechanismDesign-CSharp | 24 (9) | 25 (9) |
| D | 16b-Automated-Mechanism-Design-Python | 17 (7) | 18 (7) |
| D | 16c-Extraction-de-Revenu-DSIC-IR-Python | 23 (7) | 24 (7) |
| D | 17-MultiAgent-RL-CSharp | 26 (12) | 27 (12) |
| D | 17-MultiAgent-RL-Python | 38 (12) | 39 (12) |
| D | 18-Open-Games-et-Lentilles-Python | 27 (11) | 28 (11) |
| D | 18b-Casser-la-Composition-Python | 25 (8) | 26 (8) |
| D | 18c-Humour-Banc-Python | 65 (33) | 66 (33) |
| D | 19-Abstraction-a-Dette-Python | 17 (7) | 18 (7) |
| D | 20-Chemin-Minimal-Robinson-Goforth-Python | 44 (17) | 46 (17) — densité #21375 |

Comptes au format `total (code)`.

## Gradation des entrées post-snapshot (12 carnets) et du bloc 21

| # | Carnet | Prérequis déclarés | Concepts introduits | Cells | Diff. | Jumeau |
|---|---|---|---|---:|---|---|
| 06k | [GameTheory-06k-FairBot-Loeb-Lean](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-06k-FairBot-Loeb-Lean.ipynb) | Aucune déclarée — compagnon natif du module `ProgramGames.FairBot` (#20636) | **FairBot par le théorème de Löb** : interface `ModalProvability` (box + D1/D2/D3, Löb postulé), témoin d'indépendance du champ, faille du sondage de surface L1/L2, duel FairBot×FairBot à point fixe coordonné | 35 (12 code) | **Très haute** | Non |
| 09d | [GameTheory-09d-Stackelberg-PPO-Co-Design-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-09d-Stackelberg-PPO-Co-Design-Python.ipynb) | Aucune déclarée — nav vers 09b/09c (lignée Stackelberg) | **Stackelberg PPO** (Dai et al., ICLR 2026) : terme indirect du gradient sur un duopole, dérivée croisée sans dériver à travers l'interface, co-design concepteur-contrôleur | 26 (10 code) | Haute | Non |
| 11d | [GameTheory-11d-Raffinements-Sequentiels-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-11d-Raffinements-Sequentiels-Python.ipynb) | Aucune déclarée — nav 11/11b/12 (#19461, #22087) | **Raffinements séquentiels calculés** : assessment et rationalité séquentielle, WSE (weak sequential equilibrium), SE, PBE — l'arbre pivot, ce que le WSE accepte et refuse | 35 (15 code) | Haute | Non |
| 13f | [GameTheory-13f-Ataraxos-Patron-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13f-Ataraxos-Patron-Python.ipynb) | Aucune déclarée — « sous-série autour de 13 » | **Ataraxos, patron en trois briques** sur Kuhn Poker (#20408 grain A) : réseau politique-valeur et auto-jeu amorti, réseau de croyances, exploitabilité | 22 (9 code) | Haute | Non (famille 13g/13h) |
| 13g | [GameTheory-13g-Ataraxos-Organe-Natif](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13g-Ataraxos-Organe-Natif.ipynb) | Aucune déclarée — deuxième temps de l'EPIC #20408 | **L'organe natif à budget réduit** : installation réelle, entraînement à budget réduit, mesure centrale recherche contre politique directe, ce qui survit et ne survit pas | 16 (8 code) | Haute | Non (famille 13f/13h) |
| 13h | [GameTheory-13h-Ataraxos-DynamicDamping-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-13h-Ataraxos-DynamicDamping-Python.ipynb) | Aucune déclarée — compagnon de 13f, jouet à équilibre connu | **Coordination temporelle mesurée** (#20408 grain C) : arbre et information sets vérifiés, exploitabilité exacte, ablation du damping dynamique | 20 (9 code) | Haute | Non (famille 13f/13g) |
| 16g | [GameTheory-16g-Populations-Othman-Sandholm-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16g-Populations-Othman-Sandholm-Python.ipynb) | Aucune déclarée — « étend le pilote 16e » (#19888) | **Populations Othman-Sandholm** : pré-enregistrement du protocole gelé avant tout appel, population = distribution sur (θ, r), driver multi-seed, agrégation du welfare, modèle nul | 36 (12 code) | **Très haute** | Non (lignée 16e) |
| 16h | [GameTheory-16h-Cooperation-LLM-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16h-Cooperation-LLM-Python.ipynb) | Aucune déclarée — side-car de la sous-série 16 (#20884, #21021) | **Coopération LLM multi-seed** (Vallinder-Hughes 2024, Payne-Alloui-Cros 2025) : hétérogénéité = distribution sur les stratégies, IPD à proxy scripté, protocole gelé, agrégation par (hétérogénéité, seed) | 36 (12 code) | **Très haute** | Non (lignée 16e/16g) |
| 16i | [GameTheory-16i-Appariage-Stable-Gale-Shapley-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16i-Appariage-Stable-Gale-Shapley-Python.ipynb) | Aucune déclarée — approfondissement du 16 §5 (#21841, #21847) | **Qui peut tricher dans Gale-Shapley** : deferred acceptance, existence, avantage du proposeur, non-stratégicité et manipulation | 17 (9 code) | Haute | Non |
| 16j | [GameTheory-16j-Screening-Loyer-Information-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16j-Screening-Loyer-Information-Python.ipynb) | Aucune déclarée — nav 16c/16k (#21903, #21906) | **Screening et loyer d'information** : benchmark principal informé vs screening sous asymétrie, coût mesuré de l'asymétrie et sa décomposition | 23 (8 code) | Haute | Non |
| 16k | [GameTheory-16k-Theorie-des-Encheres-Myerson-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-16k-Theorie-des-Encheres-Myerson-Python.ipynb) | Aucune déclarée — nav 16c (#21914, #21918) | **Théorie des enchères (Myerson/Vickrey)** : véracité de l'enchère d'ordre 2, revenu sans réserve, réserve de Myerson — le prix mesuré de l'information | 26 (9 code) | Haute | Non |
| 19b | [GameTheory-19b-Bilevel-PPO-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-19b-Bilevel-PPO-Python.ipynb) | Aucune déclarée — nav 19/20 (#21221, #21236, kernel `coursia-ml-training`) | **Co-design bilevel morphologie-contrôle par Stackelberg PPO** : simulateur nageur deux segments testé, suiveur PPO depuis zéro, leader gaussien sur l'espace des morphologies | 30 (12 code) | **Très haute** | Non |
| 21 | [GameTheory-21-Capstone-Choix-Social-Python](https://github.com/jsboige/CoursIA/blob/main/MyIA.AI.Notebooks/GameTheory/GameTheory-21-Capstone-Choix-Social-Python.ipynb) | **« Ce que ce notebook suppose »** (section dédiée — le seul carnet de la série à la règle 1 de la doctrine #5081) | **Capstone de la sous-série SocialChoice** (#20663) : Arrow par la simulation, cycle de Condorcet, Gale-Shapley, ce que le lake Lean prouve et que la simulation ne prouve pas — l'escalier depuis la série mère | 24 (10 code) | Moyenne | Non |

## Totaux à `7eff951f33b`

L'arbre porte **116 carnets** dans `MyIA.AI.Notebooks/GameTheory/` :

| Périmètre | Carnets | Couverture |
|---|---:|---|
| Blocs 01-05 | 32 | tableau consolidé #22316 (bornage 2026-10-24, `8957d81ad44`, 29 carnets à sa date) — re-mesure hors du périmètre nommé par le [NOT-DELIVERED] |
| Blocs 06-20 | 83 | 71 couverts (fournées B-D, re-mesurés ici) + 12 post-snapshot gradés ici |
| Bloc  21 | 1 | gradé ici |
| **Total** | **116** | |

Le capstone 21 referme le périmètre vers le haut : **la série ne s'arrête plus au bloc 20** (l'affirmation de clôture de la fournée D est périmée). Répartition de difficulté des 13 entrées nouvelles : 4 Très haute (06k, 16g, 16h, 19b), 8 Haute, 1 Moyenne (21).

## Observations

### Un seul carnet sur 116 déclare ses prérequis à la règle 1
Le capstone 21, livré **sous la doctrine #5081** (il est né de la table « État et prochain geste par série »), porte la seule section « Ce que ce notebook suppose » de la série. Les 12 autres entrées post-snapshot suivent le pattern historique (navigation/compagnon autodéclaré), robuste à la lecture humaine mais invisible pour un auditeur automatisé — le constat des fournées B-D tient toujours, et s'étend au bloc 21 pour tout futur carnet.

### Le bloc 16 devient le plus dense de la série (13 carnets)
Les arrivées 16g-16k prolongent le continent « mécanismes » : lignée Othman-Sandholm (16e→16g), protocoles LLM multi-seed (16h), matching (16i), screening (16j), enchères (16k). La lignée screening/enchères (16j, 16k) recoupe la famille 17b (information asymétrique) — candidat à l'arbitrage de l'ordre cible (scope 2).

### Le 13g est le seul carnet de la série sans suffixe de langue
`GameTheory-13g-Ataraxos-Organe-Natif` (kernel Python 3) ne porte ni `-Python` ni `-CSharp` — écart au canon « 2 chiffres + suffixe noyau + langue » (#11840) à faire valoir à l'arbitrage.

### Fichier fournée B non réédité — collision vivante
Deux PR ouvertes touchent `15615-gradation-fournee-b.md` (#20442 po-2027:CoursIA-2, #22193 po-2023:CoursIA-2) : les 2 nouveaux du périmètre B (06k, 09d) et les 6 dérives B sont consignés **ici**, le fichier fournée reste une mesure datée de son bornage. Les fichiers fournée C et D restent également intacts — ce ledger est la source de vérité unique des blocs 06-21 à `7eff951f33b`.

## Hors périmètre

- **Ordre cible (scope 2)** : sa consolidation était conditionnée au périmètre complet de l'audit — condition maintenant remplie (tous les carnets 06-21 gradés à une tête commune). Sa proposition reste une étape séparée, pour arbitrage user/coordinateur conformément à l'acceptance de #15615.
- **Blocs 01-05** : périmètre du consolidé #22316 ; un éventuel écart 29↔32 relève d'une passe dédiée.
- **Exécution (scope 3)** : gated sur la validation de l'ordre cible.

## Source des données

- Extraction JSON scriptée (kernelspec, comptes code/markdown, headers, sections Prérequis) sur `git show origin/main:<carnet>` à `7eff951f33b` — script de session, sortie archivée au scratchpad.
- Provenance des entrées post-snapshot : `git log --diff-filter=A -1` par carnet (cités dans les lignes du tableau).
- Comptage de périmètre : `git ls-tree origin/main MyIA.AI.Notebooks/GameTheory/` (116 `.ipynb`).

## Voir aussi

- #15615 — issue pivot (plan en fournées A-D, [NOT-DELIVERED] du 2026-10-25)
- `15615-gradation-fournee-b.md` / `-c.md` / `-d.md` — mesures datées des bornages 2026-10-10/11
- [15615-gradation-blocs-01-05-consolide.md](15615-gradation-blocs-01-05-consolide.md) — source de vérité des blocs 01-05
- #5081 — doctrine de gradation (mandat user 2026-09-23), table « État et prochain geste par série »
- #20366 — rebornage comptable du 16g (fermée sans gradation, vérifié)
