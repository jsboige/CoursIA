# `scripts/smartcontracts/_archive/` — convention standardisée

S'applique au sous-dossier `_archive/` de `scripts/smartcontracts/`. Référence parente :
[`docs/reference/_archive-convention.md`](../../../docs/reference/_archive-convention.md) (modèle ML-Training-Pipeline généralisé,
4 critères d'éligibilité, header disposition per-function).

## État au 2026-10-01

Archive alimentée par le sous-grain `#18153` palier 1 (axe D #16473), claim `myia-po-2023:CoursIA-2` du 2026-10-01
(paths: `scripts/smartcontracts/create_sc{0,15,16,18,19}_notebook.py`, `scripts/smartcontracts/create_sc24_25_26.py`,
`scripts/smartcontracts/convert_print_to_deploy.py`, `scripts/smartcontracts/refactor_solidity_notebooks.py`,
`scripts/smartcontracts/_archive/**`).

Critère palier 1 vérifié par ai-01 dans #18153 :
- en-tête « temporary script, delete after use » ou codepath machine-local ;
- produit déjà sur `main` (notebooks SC-00, SC-15, SC-16, SC-18, SC-19, SC-24, SC-25, SC-26 présents).

## Table 4 colonnes (convention `_archive/`)

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `create_sc0_notebook.py` | NO BEATS (one-shot generator terminé, header « temporary, delete after use » ; notebook SC-00-Cypherpunk-Origins-Python.ipynb sur main) | none (closed dead-end) | #18153 palier 1 + #18153 thread |
| `create_sc15_notebook.py` | NO BEATS (one-shot generator terminé, header « temporary, delete after use » ; notebook SC-15-Zero-Knowledge-Proofs-Python.ipynb sur main) | none (closed dead-end) | #18153 palier 1 + #18153 thread |
| `create_sc16_notebook.py` | NO BEATS (one-shot generator terminé, header « temporary, delete after use » ; notebook SC-16-Homomorphic-Encryption-Python.ipynb sur main) | none (closed dead-end) | #18153 palier 1 + #18153 thread |
| `create_sc18_notebook.py` | NO BEATS (one-shot generator terminé, header « Delete after use » ; notebook SC-18-Vyper-Python.ipynb sur main) | none (closed dead-end) | #18153 palier 1 + #18153 thread |
| `create_sc19_notebook.py` | NO BEATS (one-shot generator terminé, header « temporary, delete after use » ; notebook SC-19-Ripple-XRP-Python.ipynb sur main) | none (closed dead-end) | #18153 palier 1 + #18153 thread |
| `create_sc24_25_26.py` | NO BEATS (one-shot generator terminé, codepath machine-local `d:/CoursIA/...` ; SC-24-SC-25-SC-26 sur main) | none (closed dead-end) | #18153 palier 1 + #18153 thread |
| `convert_print_to_deploy.py` | NO BEATS (one-shot migration print→deploy terminé ; test orphelin archivé avec — `scripts/tests/test_convert_print_to_deploy.py` → `_archive/`) | none (closed dead-end ; la migration manuelle par carnet remplace — phase 2 du script lui-même dit « manual, per-notebook ») | #18153 palier 1 + #18153 thread |
| `refactor_solidity_notebooks.py` | NO BEATS (one-shot refactor Solidity terminé, phase 1/2 décrite dans le header ; codepath terminé, phase 2 manuelle par carnet) | none (closed dead-end) | #18153 palier 1 + #18153 thread |

## Pourquoi ce standard

Sans `_archive/` standardisé, un script superseded rejoint un puits de code mort sans en-tête de disposition —
personne ne sait s'il est **encore vivant mal étiquetté** ou **réellement abandonné**. Ce README rend la
décision **vérifiable** : pour chaque fichier archivé, le verdict est daté, le successeur nommé, et la
référence durable (issue umbrella, PR) citée.

## Périmètre

- **Inclus** : scripts Python archivés sous `scripts/smartcontracts/_archive/` selon la convention parente.
- **Exclus** : `_archive/` d'autres domaines — chacun a son propre dossier, sa propre convention de nommage.
  Pas d'unification en `docs/archive/code/` (cf convention parente §4 — garder `_archive/` près du domaine).

## Pour ajouter un fichier à ce `_archive/`

1. Vérifier les **4 critères** (convention parente §3) : NO BEATS verdict, zéro référence, zéro import, successeur nommé.
2. Ajouter l'en-tête de disposition per-function au fichier déplacé (`# Archive header (standard _archive convention, ...)`).
3. Ajouter la ligne dans la table ci-dessus, datée du jour d'archivage.
4. PR + claim-AMEND sur l'issue umbrella parente avec paths ciblé.

## Voir aussi

- Convention parente : [`docs/reference/_archive-convention.md`](../../../docs/reference/_archive-convention.md)
- Claim parent : `#18153` « scripts/ : 71 candidats a l'archivage ou au cablage (audit haiku du 27/09, axe D de #16473) »
- Epic parente : `#16473` « [EPIC] Consolidation globale du dépôt — parapluie anti-entropie (axes A-F, 2026-09-17) »

---

`Grain: LIGHT/refactor — lane myia-po-2023:CoursIA-2 — prev: MED/notebook-python #18598`