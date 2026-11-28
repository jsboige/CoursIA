# Chantier 1 — tranche A14 : statuation de l'opération `inhiber` au format d'admission (deux témoins + condition de rétrogradation)

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2028:CoursIA` · **date de mesure** 2026-11-26
**Base** : `81e16ebf1c` (`origin/main`)
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (op 1) · [A3](12204-ict-chantier-1-a3.md) (ops 3, 9) · [A4](12204-ict-chantier-1-a4.md) (op 4) · [A5](12204-ict-chantier-1-a5.md) (ops 2, 6, 10) · [A6](12204-ict-chantier-1-a6.md) (statuation 11-13 + file d'attente) · [A7](12204-ict-chantier-1-a7.md) (Correctif du 2026-10-21) · [A8](12204-ict-chantier-1-a8.md) (conditions de rétrogradation) · [A9](12204-ict-chantier-1-a9.md) (seconde attestation op 2) · [A10](12204-ict-chantier-1-a10.md) (statuation op 2) · [A11](12204-ict-chantier-1-a11.md) (statuation ops 3 et 5) · [A12](12204-ict-chantier-1-a12.md) (statuation `réviser une croyance`) · [A13](12204-ict-chantier-1-a13.md) (dossier `Argumentation-06c`)

## Ce que cette tranche fait

Depuis [A6](12204-ict-chantier-1-a6.md), la file d'attente porte `inhiber` avec ce motif, recopié tel quel de tranche en tranche : **« pas de banc »**. A6, A11, A12 et A13 ont toutes écrit qu'aucune attestation nouvelle n'avait été mesurée sur cette entrée — sans jamais la mesurer.

La mesure du 2026-11-26 dit autre chose : **deux bancs d'inhibition existent sur `main`**, dans deux modules distincts qui ne partagent aucune ligne d'import, chacun avec ses témoins chiffrés et son **contrôle négatif**. L'annotation « pas de banc » n'est pas incomplète, elle est **fausse**.

La tranche produit donc trois pièces :

1. la **réfutation mesurée** de l'annotation, avec l'état d'exécution réel des deux carnets ;
2. la **définition écrite de l'opération** — que le dépôt n'avait nulle part (voir §1) : sans loi ni forme de témoin écrites, aucune statuation n'était possible, et A6 pouvait légitimement écrire « aucune seconde attestation » sans qu'aucun critère n'existe ;
3. la **pesée de l'indépendance sur les trois axes du Correctif A7**, puis la statuation au format d'admission (deux témoins + condition de rétrogradation).

## 1. Un défaut structurel constaté avant de statuer : l'entrée n'était définie nulle part

`grep -rn "institutionnaliser\|inhiber" docs/ledgers/` ne rend, pour `inhiber`, que la **ligne d'état** recopiée de tranche en tranche (« `inhiber` (pas de banc) ») et les constats « aucune seconde attestation repérée / aucune attestation nouvelle ». Aucune loi, aucune forme de témoin, aucune dette n'est écrite pour cette opération, ni dans le corps de l'EPIC (§2 ne numérote que 1 à 14), ni dans les ledgers du chantier, ni dans [`docs/transients/2026-08-24-12204-ict-chantier-1-audit-froid.md`](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md) qui porte la table des 14 opérations numérotées.

Conséquence : A6 a pu déclarer « aucune seconde attestation repérée » sur une entrée dont **aucun critère n'était écrit** — la déclaration était invérifiable par construction. La définition ci-dessous est donc écrite **par cette tranche**, dérivée des deux bancs mesurés. Si le chantier la juge trop étroite ou trop large, c'est la définition qu'il amende, et la promotion tombe avec elle.

> **`inhiber`** — supprimer une action (ou une invention) que l'agent **pourrait** produire, sans lui retirer le moyen de la produire.
> **Loi** : la suppression se paie. L'entropie d'action chute, l'efficacité de but chute, et le piège **survit à un budget de calcul accru** — donc ce n'est pas un manque de calcul, c'est un mécanisme structurel.
> **Témoin** : le **contraste** libre/inhibé *et* son **contrôle négatif** (sans inhibition, l'agent s'échappe), plus un **balayage dose-réponse** qui montre que le retournement dépend de la dose et pas du bruit.
> **Dette** : aucune théorie du « bon » taux d'inhibition — la dose qui piège n'est pas dérivée d'autre chose que du banc.

Les deux bancs qui suivent satisfont cette définition **terme par terme**, chacun avec son contrôle négatif. C'est ce qui les rend attestants : un banc qui ne montrerait que l'effet, sans le contrôle, ne prouverait pas que c'est bien l'inhibition qui piège.

## 2. Re-mesures firsthand de ce cycle

Une statuation ne s'appuie pas sur la mesure d'un autre sans relire (G.1). Tout ce qui suit est lu le **2026-11-26** sur `origin/main` (`81e16ebf1c`), par lecture JSON des carnets committés et par exécution des tests.

**État d'exécution** :

| Témoin | Cellules code | `execution_count` | Erreurs | Sorties |
|---|---|---|---|---|
| `IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats/ICT-12d-InhibitedActionAnimat-Python.ipynb` | 9 | `1..9` contigus | 0 | toutes les cellules sauf une ont une sortie ; la dernière est une cellule sans sortie (aucune erreur), pas une cellule non exécutée |
| `IIT/ICT-Series/ICT-30-InhibitedInvention-Python.ipynb` | 8 | `1..8` contigus | 0 | 8 sur 8 |

**Tests des deux modules** — `python -m pytest tests/test_inhibited_action.py tests/test_inhibited_invention.py -q` depuis `MyIA.AI.Notebooks/IIT/ICT-Series/` : **35 passed en 38,24 s**, 0 échec.

## 3. Attestation 1 — `ICT-12d` : l'action qu'on peut produire et qu'on s'interdit

**Sources** : `ict/inhibited_action.py` — `InhibitedEnvironment` (l. 50), `adaptive_animat` (l. 166), `action_entropy` (l. 218), `rigidification_test` (l. 243), `goal_seeking_efficacy_test` (l. 279, avec `greedy_toward` l. 300 et `target_fraction` l. 307), `controllability_estimation_test` (l. 330), `irreversibility_debt_bridge` (l. 373). Le module **n'importe que `numpy` et `typing`** (l. 40-42) : il ne dépend d'aucun autre module du paquet.

**Ce que le carnet imprime** (sorties committées, cellules 2 à 14) :

| Mesure | Valeur | Lecture |
|---|---|---|
| couverture d'états, `alpha=1` / `alpha=0` | `3 / 9` vs `8 / 9` | l'inhibition fige l'exploration |
| entropie d'action, contrôlée / inhibée | `1.097` → `0.268` | — |
| **chute d'entropie** | **`0.830`** | verdict `rigidified` (seuil 0,3) |
| **perte d'efficacité** | **`0.706`** | verdict `lost_control` |
| erreur d'estimation de `alpha` sur 3 régimes | `max err = 0.028` | verdict `detected` (seuil 0,1) |
| contrat de la cellule 19 | chaque clause du contrat tient | — |

**Robustesse sur 5 seeds** : `detected 5/5`, `rigidified 5/5`, `lost_control 5/5` ; `entropy_drop` moyenne `0.8678`, écart-type `0.0841`, plage `[0.7407, 0.9423]` contre un seuil de `0.3` ; `efficacy_drop` moyenne `0.6813`, écart-type `0.0428`, plage `[0.6088, 0.7125]`. La dispersion est très en dessous des marges : ce n'est pas un franchissement de seuil par chance.

**Contrôle négatif** : `goal_seeking_efficacy_test` compare `alpha=1` à `alpha=0` — la fraction-cible est plus haute **sans** inhibition, et l'effet de l'action est **nul** sous `alpha=0` alors qu'il opère à contrôle partiel. Sans le contraste, la chute d'entropie serait indistinguable d'un agent simplement moins actif.

## 4. Attestation 2 — `ICT-30` : l'invention qu'on peut produire et qu'on s'interdit

**Sources** : `ict/inhibited_invention.py` — `InhibitedInventingGame(InventingSignalingGame)` (l. 48), `_invent` (l. 89), `play_round` (l. 103), `final_inhibition` (l. 119), `inhibition_traps_rigidification_test` (l. 134), `learned_helplessness_test` (l. 180), `trap_persists_under_more_compute_test` (l. 223), `no_inhibition_escapes_control_test` (l. 260). Le module **s'appuie sur** `ict.symbol_invention.InventingSignalingGame` et `ict.signaling_convention.mutual_information` (l. 44-45) — une mécanique de base différente de celle de l'attestation 1.

**Ce que le carnet imprime** (cellules 5 à 18) :

| Mesure | Valeur | Lecture |
|---|---|---|
| vocabulaire, inhibition libre / maximale | `4.00` → `1.00` | verdict `rigidifies = True` |
| inhibition à mi-parcours / à la fin | `1.000` / `1.000` | plafond du renoncement |
| vocabulaire final sous inhibition | `2.00` | sous-optimal contre `n_states = 4` |
| piège sous budget de calcul accru | `persistent_trap = True` | **structurel**, pas un manque de calcul |
| **contrôle négatif** : sans inhibition | vocabulaire `4.00 = n_states`, coordination `1.000` | `escapes = True` — c'est bien l'inhibition qui piège |

**Balayage dose-réponse**, dans les deux sens :

| `decay` | 0.000 | 0.010 | 0.030 | 0.100 |
|---|---|---|---|---|
| vocabulaire final moyen (`n_states=4`) | `2.00` | `3.33` | `4.00` | `4.00` |

| `growth` | 0.005 | 0.010 | 0.020 | 0.040 | 0.060 |
|---|---|---|---|---|---|
| vocabulaire final moyen | `4.00` | `4.00` | `3.33` | `2.67` | `2.00` |

Les deux balayages **se referment** : la sortie dépend de la dose dans les deux directions, ce qui exclut une lecture « le paramètre ne fait rien ». C'est la pièce que la définition §1 exige et que le contrôle négatif seul ne donnait pas.

## 5. Pesée de l'indépendance — trois axes du Correctif A7

| Axe | Verdict | Preuve |
|---|---|---|
| **(ii) algorithme identifiable et distinct** | **réuni, et mesuré** | `inhibited_action.py` n'importe que `numpy` (l. 40-42) ; `inhibited_invention.py` s'appuie sur `InventingSignalingGame` et `mutual_information` (l. 44-45). **Aucun import croisé entre les deux modules** : l'inhibition porte sur une dynamique d'action dans l'un, sur un processus d'invention au-dessus d'un jeu de signalisation dans l'autre. |
| **(iii) témoin mesuré** | **réuni des deux côtés** | §3 et §4 : contrastes chiffrés, robustesse 5/5 seeds d'un côté, sweeps dose-réponse des deux côtés, et **contrôle négatif dans chaque banc**. |
| **(i) littérature propre** | **partagé — consigné comme limite** | la lignée Laborit / animat est commune à la série ICT : les deux bancs partagent leur cadre théorique. |

**Limite consignée, pas dissimulée** : les deux témoins vivent dans la **même série** (`IIT/ICT-Series`) et le **même paquet** (`ict`). Ce n'est pas l'indépendance de substrat qu'exigeait la promotion de `point fixe` en A6 (lake Lean contre substrat .NET). La paire établit l'opération sur deux **mécanismes** et deux **problèmes**, avec du code disjoint, pas sur deux **théories étrangères**. C'est exactement la forme de limite qu'[A12](12204-ict-chantier-1-a12.md) a consignée pour `réviser une croyance` (canon AGM partagé) — et A12 a statué la promotion en la consignant.

À la différence d'A12 toutefois, le jumeau C#/IKVM avait été **écarté** parce qu'il rejouait la même bibliothèque : ici, il n'y a pas de bibliothèque tierce commune, puisque les deux modules d'inhibition sont **propres au dépôt** et sans dépendance mutuelle.

## 6. Verdict

**`inhiber` → TABLE** (17ᵉ entrée de la table ; 1ʳᵉ entrée non numérotée admise depuis `réviser une croyance` en A12).

**Condition de rétrogradation** (format [A8](12204-ict-chantier-1-a8.md)) :

- **(a) la loi ne tient plus sur re-exécution** — si `rigidified` ou `lost_control` tombe sur les 5 seeds d'ICT-12d, ou si le contrôle négatif d'ICT-30 cesse de s'échapper (vocabulaire final `< n_states` sans inhibition) ;
- **(b) perte d'un témoin** — retrait d'un des deux carnets ou d'un des deux modules, ou sorties vidées (mesure : `execution_count` non contigu, ou erreur dans `outputs`) ;
- **(c) inversion d'un balayage dose-réponse** — si `growth 0.060` remonte à `4.00`, ou si `decay 0.000` atteint `n_states`, la dose-réponse ne porte plus le témoin et l'attestation 2 tombe.

Ni une réécriture pédagogique du carnet, ni un changement de graine ne sont des conditions par eux-mêmes : ce sont les **verdicts imprimés** qui font foi, pas la prose.

## 7. Ce que cette tranche ne fait pas

- **Elle ne statue pas `institutionnaliser`.** L'entrée reste en file d'attente, mais son motif « DAO seulement » est lui aussi à re-mesurer : deux bancs candidats existent sur `main`, mesurés ce cycle sans être pesés — `SymbolicAI/SmartContracts/02-Solidity-Advanced/SC-09-DAO-Governance-Python.ipynb` (code `1..8` contigu, 0 erreur) et `SymbolicAI/SmartContracts/00-Foundations/SC-02b-Bac-ASable-Institutionnel-Python.ipynb` (code `1..18` contigu, 0 erreur, avec ses bras et contrôles dans `sc2b_resultats/`). Le prochain grain du chantier doit les peser sur les trois axes, et écrire d'abord la définition de l'opération — elle n'existe pas davantage que celle de `inhiber` (§1).
- **Elle ne corrige pas le lien mort du corps de l'EPIC** vers `docs/ledgers/12204-ict-chantier-1-audit-froid.md` : le fichier vit à [`docs/transients/2026-08-24-12204-ict-chantier-1-audit-froid.md`](../transients/2026-08-24-12204-ict-chantier-1-audit-froid.md) depuis son déplacement en lane transiente. Signalé ici, à porter au body dans une édition séparée.
- **Elle ne relit pas** les mesures de contenu des tranches antérieures (témoins d'A9, verdicts d'A11) : elles ne sont citées ici que comme contexte, jamais comme preuve.

## 8. État de la table après A14

**TABLE** : opérations numérotées **1 à 14** (14) + `point fixe` + `réviser une croyance` + **`inhiber`** = **17 entrées**.
**FILE D'ATTENTE** : `institutionnaliser` (**1** entrée, motif à re-mesurer — voir §7).

La table numérotée du premier jet reste complète et entièrement instruite ; les entrées non numérotées passent de deux à une.
