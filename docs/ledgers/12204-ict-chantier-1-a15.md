# Chantier 1 — tranche A15 : statuation de l'opération `institutionnaliser` (définition écrite, deux candidats pesés, condition de promotion mesurable)

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2028:CoursIA` · **date de mesure** 2026-11-26
**Base** : `81e16ebf1c` (`origin/main`)
**Tranche précédente** : [A14](12204-ict-chantier-1-a14.md) (statuation de `inhiber`, §7 nomme ce grain)
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) · [A3](12204-ict-chantier-1-a3.md) · [A4](12204-ict-chantier-1-a4.md) · [A5](12204-ict-chantier-1-a5.md) · [A6](12204-ict-chantier-1-a6.md) · [A7](12204-ict-chantier-1-a7.md) · [A8](12204-ict-chantier-1-a8.md) · [A9](12204-ict-chantier-1-a9.md) · [A10](12204-ict-chantier-1-a10.md) · [A11](12204-ict-chantier-1-a11.md) · [A12](12204-ict-chantier-1-a12.md) · [A13](12204-ict-chantier-1-a13.md)

## Ce que cette tranche fait

Depuis A6, la file d'attente porte **une seule** entrée non numérotée : `institutionnaliser`, avec le motif « **DAO seulement** ». A14 §7 a nommé ce grain et laissé deux candidats mesurés sans être pesés : `SC-02b-Bac-ASable-Institutionnel-Python.ipynb` et `SC-09-DAO-Governance-Python.ipynb`.

La tranche fait trois choses, et **n'en fait pas une quatrième** :

1. elle écrit la **définition de l'opération** — comme pour `inhiber` en A14, elle n'existait nulle part (voir §1) ;
2. elle **pèse les deux candidats** sur les trois axes du Correctif A7, à partir de leurs sorties committées et d'une re-mesure d'exécution de ce cycle ;
3. elle rend un verdict qui **corrige le motif** : « DAO seulement » est faux, et le vrai manque est nommé, chiffré, avec la condition qui le lèverait.

Elle **ne promeut pas** l'entrée. C'est le résultat, pas un renoncement : promouvoir sur la base mesurée ci-dessous serait admettre une loi dont le contraste est nul.

## 1. Le défaut de méthode, constaté avant de statuer

`grep -rn "institutionnaliser" docs/ledgers/` ne rend, comme pour `inhiber` en A14, que la **ligne d'état** recopiée de tranche en tranche (« `institutionnaliser` (DAO seulement) ») et les constats « aucune attestation nouvelle ». Ni loi, ni forme de témoin, ni dette n'est écrite pour cette opération : la table des 14 opérations numérotées vit dans [`docs/transients/2026-08-24-12204-ict-chantier-1-audit-froid.md`](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md) et ne la contient pas.

La définition est donc écrite **ici**, dérivée de ce que les deux candidats mesurent réellement. Si le chantier la juge mal calibrée, c'est elle qu'il amende — et la promotion tombe avec elle.

> **`institutionnaliser`** — faire adopter à un agent une règle **qu'il ne peut pas contourner**, et observer ce que la règle fait à son comportement.
> **Loi** : une règle non contournable **déplace** le comportement de façon mesurable — et ce déplacement n'est pas réductible à « l'agent obéit » : l'institution peut produire des issues **conformes aux règles et pourtant non légitimes**. Le témoin doit donc porter sur les **deux** faces : conformité (les règles tiennent) et légitimité (ce que la règle laisse faire).
> **Témoin** : un dispositif où (a) la règle est **effectivement incontournable** (un double-vote ou un vote hors quorum est **rejeté**, pas seulement découragé), (b) l'issue est **reproductible** (rejouer la séquence rend le même journal), et (c) un **contrôle négatif** montre que l'observation n'est pas un artefact de l'observateur (sur un agenda où il n'y a rien à capturer, on ne capture rien).
> **Dette** : aucune théorie du taux d'institutionnalisation « juste » — quelle densité de règles produit la légitimité n'est pas dérivée d'autre chose que du banc.

Deux propriétés distinguent cette définition de celle d'`inhiber` : ici l'agent **ne perd pas** le moyen d'agir (il vote, il propose) — c'est la règle qui décide ; et le témoin exige une **double face** (conformité + légitimité), ce qui est plus fort qu'un simple contraste d'activité.

## 2. Re-mesures firsthand de ce cycle

Une statuation ne reprend pas la mesure d'autrui sans relire (G.1). Tout ce qui suit est lu le **2026-11-26** sur `origin/main` (`81e16ebf1c`), par lecture JSON des carnets committés.

| Candidat | Cellules code | `execution_count` | Erreurs | Sorties |
|---|---|---|---|---|
| `SymbolicAI/SmartContracts/00-Foundations/SC-02b-Bac-ASable-Institutionnel-Python.ipynb` | 18 | `1..18` contigus | 0 | 18 sur 18 |
| `SymbolicAI/SmartContracts/02-Solidity-Advanced/SC-09-DAO-Governance-Python.ipynb` | 8 | `1..8` contigus | 0 | 8 sur 8 |

Les deux carnets sont donc **exécutés** au sens de C.2. L'exécution ne dit rien de la valeur probante — c'est l'objet des §3 et §4.

## 3. Candidat 1 — `SC-02b` : un banc complet, dont le contraste quantitatif est nul

`SC-02b` est bien davantage qu'un tutoriel : c'est un **dispositif**. Chaîne Anvil locale, contrat `Deliberation` compilé et déployé (cellule 5), trois acteurs à clé dérivée d'un même mnemonic (cellule 3), journal on-chain converti en `pandas` puis empreinté (cellules 9-10).

**Ce que le dispositif prouve, et qui est le plus dur à obtenir** :

| Propriété de la définition §1 | Où elle est mesurée | Sortie committée |
|---|---|---|
| (a) règle **incontournable** | cellule 7 | `double-vote rejete par le contrat : ('execution reverted: deja-vote', ...)` — le rejet vient du contrat, pas du carnet |
| (b) issue **reproductible** | cellules 10-11 | empreinte ronde 1 `449bbd6b781e55af`, ronde 2 `449bbd6b781e55af`, `REJOUABLE : True` — chaîne détruite puis relancée |
| (c) **contrôle négatif** | cellule 17 | `controle anti-recit : 0 capture(s) sur agenda trivial -> PASS (observateur sain)` |
| double face : légitimité | conclusion du carnet | `P1 « Exclure Carole du registre »` **adoptée sans qu'aucune règle ne soit violée** — conformité et légitimité divergent sur la même décision |

**Ce qu'il ne prouve pas, et qui décide du verdict** — le contraste des bras est **nul** :

| Série | n | captures | taux | appels |
|---|---|---|---|---|
| bras1 homogene | 20 | 0 | 0.00 | 122 |
| bras1 heterogene | 20 | 0 | 0.00 | 120 |
| controle homogene | 2 | 0 | 0.00 | 25 |
| controle heterogene | 2 | 0 | 0.00 | 13 |
| bras2 C4 | 12 | 0 | 0.00 | 84 |
| bras2 C5 (v1, transfert-dominant) | 12 | 0 | 0.00 | 84 |
| bras2 C5 (v2, vote-puis-transfert) | 1 | 0 | 0.00 | 9 |

et les deux hypothèses du carnet tombent d'elles-mêmes :

- `H1 heterogene vs homogene (bras 1) : 0.00 vs 0.00 | diff +0.0 pp | IC95 [+0.0 ; +0.0] pp -> NON DETECTEE (IC couvre 0)` ;
- `H2 C5-v2 vs C4 (bras 2) : 0.00 vs 0.00 -> NON_TESTABLE (n_a=1, n_b=12 < SEUIL=5 ; pas d'IC95 sur echantillon insuffisant)` ;
- `2x2 : non lance (aucun signal, protocole)`.

**Lecture honnête.** Deux choses sont vraies en même temps et ne doivent pas être confondues. Le **dispositif** satisfait la définition terme par terme : règle incontournable, rejouabilité, contrôle anti-récit, et même la double face (la capture de coalition est observée qualitativement, et c'est le résultat le plus intéressant du carnet). L'**effet quantifié**, lui, est nul partout, et l'hypothèse qui portait le contraste est **non testable par construction** (`n_a = 1`). Un taux de 0/20 dans les deux bras n'est pas « pas d'effet » : c'est *le dispositif n'a pas encore assez de puissance pour distinguer les deux*.

## 4. Candidat 2 — `SC-09` : un tutoriel, pas un témoin

`SC-09` s'exécute proprement (toutes ses cellules, 0 erreur) mais ses sorties ne portent aucun contraste :

- cellule 5 : `Votes au bloc 5 : 0 | Votes au bloc 10 : 0 | Votes au bloc 30 : 0 | Votes au bloc 55 : 0 | Votes au bloc 70 : 0` — la mesure de pouvoir de vote ne mesure rien ;
- cellule 8 : `Future (eta+1j) : PENDING | Passe (eta-1j) : PENDING | Expired (eta-16j): PENDING` — les trois cas du timelock rendent la même valeur, donc le test ne sépare pas ce qu'il prétend séparer ;
- cellule 6 : `Exercice a completer : quadratic_vote` — **stub conforme C.1**, ce qui est correct pédagogiquement et disqualifiant comme témoin.

Aucune des trois propriétés de §1 n'y est réunie : pas de rejet effectif observé, pas de rejouabilité éprouvée, pas de contrôle négatif. **`SC-09` ne compte pas comme attestation.** Le motif « DAO seulement » est donc doublement faux : il suppose que le seul matériau disponible est un carnet de DAO, alors que ce carnet-là n'atteste rien et que le banc qui atteste n'est pas un carnet de DAO.

## 5. Pesée de l'indépendance — trois axes du Correctif A7

La pesée porte sur **la paire de candidats**, et elle est rapide parce qu'un des deux n'entre pas :

| Axe | Verdict | Preuve |
|---|---|---|
| **(iii) témoin mesuré** | **réuni d'un seul côté** | `SC-02b` porte les trois propriétés de §1 dont le contrôle anti-récit ; `SC-09` n'en porte aucune (§4) |
| **(ii) algorithme identifiable et distinct** | **non réuni — et il n'y a rien à séparer** | les deux candidats reposent sur le même substratum : `web3.py` + Anvil + Solidity, dans la même série `SmartContracts`. Avec un seul témoin, l'axe n'a pas d'objet : il mesure l'écart **entre** deux attestations |
| **(i) littérature propre** | **partagé** | gouvernance on-chain / économie institutionnelle, commune à la série |

**Ce que cette pesée ne peut pas faire.** A14 a pu promouvoir `inhiber` en consignant une limite d'axe (i), parce que **deux** mécanismes disjoints existaient (aucun import croisé). Ici, l'axe (ii) n'est pas « partagé mais acceptable » : il est **vide**, faute d'un second témoin. La différence n'est pas de degré, elle est de nature — et c'est précisément ce que le Correctif A7 devait attraper.

## 6. Verdict

**`institutionnaliser` reste en FILE D'ATTENTE.** Aucune promotion, et le motif change :

| | Motif porté depuis A6 | Motif mesuré au 2026-11-26 |
|---|---|---|
| Énoncé | « DAO seulement » | **une seule attestation, et son contraste quantitatif est nul ; il manque un second témoin indépendant, et le premier n'a pas la puissance de distinguer ses bras** |
| Ce que ça implique | rien de vérifiable | deux gestes, chacun mesurable (§7) |

**Condition de promotion** (format [A8](12204-ict-chantier-1-a8.md)), deux voies, une seule suffit :

- **(a) donner de la puissance au banc existant** — porter le bras `C5 (v2, vote-puis-transfert)` de `n_a = 1` à `n_a ≥ 5` (le `SEUIL` que le carnet s'est lui-même fixé), et obtenir un `IC95` qui **exclut 0** sur `H2`. Tant que `n_a = 1`, `H2` est non testable et aucun verdict ne peut être rendu. **La participation précède la puissance** : contre un comparateur qui ne capture jamais, exclure 0 à l'`IC95` demande 3 captures sur 5, 4 sur 12 ou 4 sur 20 (bootstrap du carnet, graine 42, 10 000 rééchantillonnages) ; or le comparateur `C4` n'est atteignable — au moins deux membres distincts votant sur `P1` — sur **aucun** de ses 12 épisodes, si bien que son zéro est un zéro de non-participation, non un refus (SC-02b, section « Portée de l'observateur », et sa cellule de mesure dont la sortie donne `bras2 C4 : n=12, P1 atteignable 0, captures 0` ; mesure post-hoc du 2026-11-27, issue #28925, committée dans le carnet par #28926). La condition demande donc, dans le même geste, des épisodes où `C4` **et** `C5-v2` réunissent au moins deux votants : sans cela, un écart mesuré mêlerait participation et préférence ;
- **(b) un second témoin sur un substratum indépendant** — ni `web3.py`, ni Anvil, ni Solidity : la règle doit être rendue incontournable par un autre mécanisme (un interpréteur qui rejette, un typage qui interdit, un consensus simulé), avec ses trois propriétés et son propre contrôle négatif.

**Ce qui n'est pas une condition.** Une réécriture pédagogique de `SC-09`, la complétion de ses exercices, ou l'ajout d'un troisième carnet de DAO : ce sont des progrès de série, pas des attestations. Le verdict se lit sur des sorties, jamais sur la prose d'un carnet.

## 7. Ce que cette tranche ne fait pas

- **Elle n'exécute pas la condition (a).** Monter `n_a` de 1 à 5 demande de relancer la génération d'épisodes du bras 2 et de réécrire les sorties de `SC-02b` — un geste de série (`notebook-python`), pas de ledger. Il est nommé ici pour être pris, pas contourné. Depuis le 2026-11-27, la condition porte en outre sa clause de participation (§6) : `C4` n'était atteignable sur aucun de ses 12 épisodes. Cette mesure-là est désormais prise **dans le carnet** : la section « Portée de l'observateur » et sa cellule de mesure sont committées (issue #28925, PR #28926, fusionnée le 2026-11-28), la clause ne repose donc plus sur le corps d'une issue ouverte.
- **Elle ne corrige pas le lien mort du corps de l'EPIC** vers `docs/ledgers/12204-ict-chantier-1-audit-froid.md` : le fichier vit à [`docs/transients/2026-08-24-12204-ict-chantier-1-audit-froid.md`](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md). Déjà signalé en A14 §7, non corrigé ici : deux tranches le nomment, aucune ne l'a fait — c'est un défaut à réparer par une édition séparée du body.
- **Elle ne relit pas** les mesures des tranches antérieures (témoins d'A9, verdicts d'A11) : citées comme contexte, jamais comme preuve.

## 8. État de la table après A15

**TABLE** : opérations numérotées **1 à 14** (14) + `point fixe` + `réviser une croyance` + `inhiber` (A14) = **17 entrées**, inchangé.
**FILE D'ATTENTE** : `institutionnaliser` (**1** entrée) — motif corrigé, condition de promotion écrite en deux voies (§6).

La file ne se vide pas par une promotion : elle se vide par la mesure qui la rend statuable. A15 a établi que cette mesure n'existe pas encore, et où elle se prend.
