# Chantier 1 — tranche A6 : statuation des opérations 11-13 (promotions TABLE) et de la file d'attente

**EPIC** : [#12204](https://github.com/jsboige/CoursIA/issues/12204) · **lane** `myia-po-2024:CoursIA` · **date de mesure** 2026-09-27 · **base** `1e19752a233`
**Tranches sœurs** : [A2](12204-ict-chantier-1-a2.md) (opération 1) · [A3](12204-ict-chantier-1-a3.md) (opérations 3, 9) · [A4](12204-ict-chantier-1-a4.md) (opération 4) · [audit froid](12204-ict-chantier-1-audit-froid.md) (les 14 opérations, trois axes)

## Ce que cette tranche fait, et ce qu'elle ne fait pas

L'audit froid laissait les opérations **11, 12, 13** « en constitution », chacune avec sa seconde attestation **livrée mais non comptée** — la convention posée pour l'opération 7 (reprise telle quelle ici) : *une attestation ne compte qu'une fois son artefact mergé sur `main`*. Cette tranche vérifie **mécaniquement** que la condition est à présent remplie pour les trois, et opère les promotions que l'audit froid renvoyait « à statuer ». Elle ne re-décide ni les provenances (toutes `FIRSTHAND` déjà), ni les témoins (forms fixées par l'audit froid) — elle **active des promotions déjà conditionnées**.

Elle statue aussi sur la **file d'attente** : le seul candidat à promotion (`point fixe`, « à promouvoir dès le second usage ») est examiné et **écarté comme homonyme**, avec preuve.

## Promotions — les trois secondes attestations comptées

Constitution des trois : artefacts présents sur `origin/main` (base `1e19752a233`), état mécanique mesuré par lecture du JSON des carnets (comptes de cellules, `execution_count`, erreurs).

### Opération 11 — Descendre sous budget → TABLE

| Attestation | Témoin | État mesuré sur main |
|---|---|---|
| `mimo_lean/Descent.lean` (thèse op 11 explicite, sorry-free — A6/c.1208) | le budget atteint, ou le blocage | préexistante, comptée |
| `Search/Part1-Foundations/Search-11d-Descente-Sous-Budget.ipynb` (#16392) | décroissance stricte + barrière + non-blocage hors cible | **17 cellules, 6 code, 6 exécutées, 0 erreur** — mesuré ce cycle |

Deux substrats indépendants (Lean-formel + empirique-notebook). Promotion **TABLE**.

### Opération 12 — Composer des regards → TABLE

| Attestation | Témoin | État mesuré sur main |
|---|---|---|
| GT-21 #12259 (jeux 2×2, merged) | la paire de lectures incompatibles exhibée | préexistante, comptée |
| `Search/Part1-Foundations/Search-12a-Composer-Regards.ipynb` (#16426) | gridworld pondéré, play/coplay | **27 cellules, 9 code, 9 exécutées, 0 erreur** — mesuré ce cycle |

Deux attestations directes sur substrats indépendants, witness form connu (§5 du carnet). Promotion **TABLE**.

### Opération 13 — Traverser un mur → TABLE

| Attestation | Témoin | État mesuré sur main |
|---|---|---|
| GT-24 #12364 (MERGED) | chambre → mur → chambre voisine, six swaps générateurs | préexistante, comptée |
| `Search/Part1-Foundations/Search-13a-Traverser-Murs-Certifies.ipynb` (#16438) | chemin minimal certifié, épaisseur m_path / largeur m + test négatif morphisme/percement | **20 cellules, 10 code, 10 exécutées, 0 erreur** — mesuré ce cycle |

Promotion **TABLE**.

## File d'attente — statuation

- **`point fixe`** : le seul candidat second-usage repéré par grep (`knaster|tarski`, hors `.lake`) est `formal_logic_lean/FormalLogic/FolBridge.lean:124` — lu firsthand : c'est la **sémantique de Tarski** (le théorème `models_iff_eval` : la satisfaction d'une phrase par la restriction de structure est son évaluation `Eval`), **pas** un point fixe de Knaster-Tarski d'un opérateur monotone. Homonyme, écarté avec preuve. L'opération **reste en file d'attente** — son unique usage demeure `argumentation_lean` (opérateur caractéristique, `Extensions.lean:44`, propriétés dans `Grounded.lean`).
- **`institutionnaliser`** (DAO seulement), **`inhiber`** (pas de banc), **`réviser une croyance`** (Tweety non branché) : aucune seconde attestation repérée ce cycle — inchangées.

## État de la table après cette tranche

**TABLE (10)** : 1, 4, 7, 8, 9, 10, 14 (promotions antérieures) + **11, 12, 13 (ce cycle)**.
**FILE D'ATTENTE (4)** : 2, 5, 6 (attendent leurs secondes attestations — op 2/6 via la distillation Sandholm, chantier 5) + `point fixe` (homonyme écarté).

La table compte désormais dix opérations attestées deux fois — contre quatre tombées et quatre en attente, chaque sortie documentée.
