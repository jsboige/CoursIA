# PARCOURS — Schéma maturité 3 axes

**Issue** : [#8051](https://github.com/jsboige/CoursIA/issues/8051)
**Statut** : ACCEPTÉ (2026-07-23), pilote en cours (c.763 critères 1-3)
**Auteur du schéma** : ai-01 / lane `myia-po-2023:CoursIA-2` (po-2023 = générateur)
**Date** : 2026-07-23
**Base SHA** : `8092a4aec` (post-merge pool QC, post-#8064)

---

## Pourquoi décomposer le monolithique `maturity`

Le catalogue généré (`COURSE_CATALOG.generated.json`) porte aujourd'hui un champ **`maturity`** monolithique à 5 valeurs (`TEMPLATE / PRODUCTION / BETA / ALPHA / DRAFT`). Ce schéma mélange trois préoccupations **orthogonales** qu'il vaut mieux séparer pour les rendre auditables indépendamment :

1. **Maturité éditoriale** — où en est la *prose pédagogique* ? (de DRAFT = jamais relu à FINAL = relu, stable, prêt à publier).
2. **Reproductibilité** — le notebook a-t-il *réellement tourné* et avec quel niveau de garantie ? (de UNTESTED = aucune cellule exécutée à REPRODUCED = ré-exécuté de bout en bout avec succès, horodaté).
3. **Confiance scientifique** — quel *risque* la substance prend-elle sur ce qu'elle affirme ? (de UNASSESSED = pas d'appréciation portée à RESEARCH = recherche active, contenu explicitement en cours d'élaboration).

Mélanger ces axes en une seule étiquette (PRODUCTION, BETA…) a trois défauts :
- **Illisible** : « BETA » ne dit pas si le notebook a réellement exécuté, ni si la substance est revue — il dit juste « pas tout à fait finalisé ».
- **Non-auditable** : on ne peut pas filtrer « notebooks qui n'ont jamais exécuté » ou « notebooks dont la substance n'est pas relue » parce que la granularité est perdue.
- **Non-réversible** : si la prose est FINAL mais l'exécution a régressé, on doit downgrader toute l'étiquette alors qu'un seul axe a changé.

## Les 3 axes — définitions contractuelles

### Axe 1 — `editorial` (maturité éditoriale)

| Valeur | Définition | Critère vérifiable |
|--------|-----------|--------------------|
| `DRAFT` | Première rédaction, structure incomplète, fautives fréquentes | `cells_markdown / cells_total < 0.20` OU titre placeholder OU TODO dans la première cellule markdown |
| `ALPHA` | Structure pédagogique en place, exemples partiels, trous assumés | DRAFT non vérifié ET ≥1 cellule markdown d'introduction ET ≥1 exemple |
| `BETA` | Pédagogie complète, tous les concepts couverts, relecture interne auteur | `cells_markdown >= 0.40` ET conclusion présente ET ≥3 exercices (cf [`three-exercises-per-notebook.md`](../.claude/rules/three-exercises-per-notebook.md)) |
| `FINAL` | Relecture externe (cluster ou peer), stable, prêt à publier | `BETA` + relu par ≥1 agent non-auteur (signal `editorial_reviewed_by` non-null dans le catalogue) |

### Axe 2 — `reproducibility` (reproductibilité)

**Source de vérité** : forensic scan (`scripts/notebook_tools/forensic_scan.py`) — categories A/B/C/D + timestamp `last_commit_sha`.

| Valeur | Définition | Critère vérifiable (catégorie forensic) |
|--------|-----------|----------------------------------------|
| `UNTESTED` | Aucune cellule code exécutée | `C_NEVER_EXECUTED` OU `NO_CODE` |
| `STATIC_OK` | Notebook *valide statiquement* (parse OK, structure OK) mais non exécuté | `STATIC_OK` (parse réussi, `n_code > 0`, `n_exec == 0`, pas d'erreur statique) |
| `EXECUTED` | Toutes les cellules code exécutées avec succès | `A_ALL_EXEC_OK` — `execution_count != null` partout + 0 erreur |
| `REPRODUCED` | Ré-exécution *horodatée* de bout en bout, attestation d'exécution | `EXECUTED` + `executed_at` présent ET `last_success_sha == head_sha` |

**Différence EXECUTED vs REPRODUCED** : `EXECUTED` est un état *intrinsèque* du fichier (au moment du commit) ; `REPRODUCED` est un état *daté* (on peut affirmer « ce notebook a tourné le JJ/MM avec succès sur le SHA X »). REPRODUCED est ce qui permet de répondre « oui, ce notebook marche *aujourd'hui* » ; EXECUTED peut dater de 2 ans et avoir régressé depuis.

**Provenance des champs (`executed_at`, `last_success_sha`)** : ils doivent venir d'une **attestation d'exécution** (exécuteur, date, SHA des sources, environnement, résultat) — pas d'une date de dernière modification `git log` (#14814). Une référence jamais exécutée (`metadata.qc_reference == true`) est un **type de document** (`forensic_category == REFERENCE`), pas un claim de reproductibilité : son axe 2 vaut `UNTESTED`, jamais `REPRODUCED`. Tant qu'aucune attestation n'existe, `REPRODUCED` n'est pas émis — un champ vide est honnête, un champ dérivé d'une date de modification ne l'est pas.

### Axe 3 — `scientific_review` (revue scientifique)

**L'axe mesure le risque du contenu, pas la provenance de sa relecture** (#14831,
sign-off user 2026-09-21). L'échelle précédente (`UNREVIEWED` → `AUTHOR_REVIEWED` →
`PEER_REVIEWED` → `FORMALLY_VERIFIED`) classait *qui avait relu, avec quelle rigueur
formelle*. Elle était **inversée dans ses effets** : une série de recherche active relue
par des pairs atteignait le haut de l'échelle, pendant qu'un notebook de cours classique,
universellement admis et sans aucun risque, restait `UNREVIEWED` faute de reviewer nommé.
Elle reposait de plus sur le compte de `sorry`, un indicateur qui ne concerne qu'une
poignée de notebooks Lean, pour piloter un axe couvrant tout le corpus.

| Valeur | Définition | D'où elle vient |
|--------|-----------|-----------------|
| `UNASSESSED` | Aucune appréciation portée. **Ce n'est pas un mauvais score** : c'est l'absence de jugement, et c'est le défaut honnête. | défaut ; aucune entrée de registre |
| `ESTABLISHED` | Contenu communément admis et universellement pratiqué. Le notebook ne prend aucun risque sur ce qu'il affirme. | `confidence: established` au registre |
| `ADVANCED` | Protocoles plus avancés, exécutions moins contrôlées, théories récentes, interprétations discutables. Le contenu tient, mais il engage. | `confidence: advanced` |
| `RESEARCH` | Recherche active — ICT au premier chef. Le contenu est explicitement en cours d'élaboration, et le dire est la seule position honnête. | `confidence: research` |

Une valeur non reconnue retombe sur `UNASSESSED` (**fail-CLOSED**) : c'est la propriété
qui empêche le label-gaming.

#### L'appréciation se périme quand le code bouge

Une appréciation porte sur ce que le notebook **calcule et affirme**. Si le calcul change,
elle ne porte plus sur ce qui est là. Le catalogue émet donc `scientific_review_stale:
true` lorsque l'empreinte du code diffère du `reviewed_code_sha` enregistré au moment de
la revue — **la grade est conservée**, seul le drapeau bascule : la perdre effacerait
l'information (« personne n'a jamais apprécié ») alors que le fait est autre (« quelqu'un
a apprécié, puis le code a bougé »).

Cela met l'audit scientifique en **régime permanent**, ce qui est l'effet recherché : une
nouvelle revue est due, sous le protocole de [SCIENTIFIC_REVIEW_CARD.md](notebook-metadata/SCIENTIFIC_REVIEW_CARD.md).

L'empreinte exclut délibérément trois choses, chacune pour une raison mesurée :

- **le markdown** — la campagne de densification a modifié 178 notebooks en trois semaines
  sans toucher une ligne de code ; l'inclure rétrograderait tout le corpus au premier
  passage, et une rétrogradation qui frappe tout ne signale plus rien ;
- **les sorties** — une ré-exécution les change sans changer ce que le notebook affirme ;
- **`execution_count`** — pur artefact d'ordre d'exécution.

C'est une empreinte de **contenu**, jamais un blob SHA git : un squash-merge réécrit les
blobs et tuerait l'ancre à chaque merge (#11919).

`sorry_free` et `scientific_reviewed_by` restent rendus **comme preuves à côté** — ils ne
pilotent plus la grade.

---

## Migration / rétro-compatibilité

Le champ `maturity` monolithique actuel reste **présent** dans `COURSE_CATALOG.generated.json` pour ne casser aucun consommateur existant (README, dashboards, scripts tiers). Il est désormais **calculé comme l'agrégat** des 3 axes, selon la règle :

```
production_signed (tampon du responsable pédagogique, cf docs/notebook-metadata/production-scope.md)
  → maturity = "PRODUCTION"
editorial in ("BETA", "FINAL") AND reproducibility in ("EXECUTED", "REPRODUCED")
  → maturity = "BETA"
editorial in ("ALPHA", "BETA") AND reproducibility in ("STATIC_OK", "EXECUTED")
  → maturity = "ALPHA"
is_template (filename contains "template")
  → maturity = "TEMPLATE"
sinon
  → maturity = "DRAFT"
```

**`PRODUCTION` ne se dérive plus d'aucune combinaison d'axes** (#14831, sign-off user
2026-09-21). Il ne décrit pas une propriété mesurable du fichier : il dit que le
responsable pédagogique a **apposé son tampon**, et juge le notebook finalisé pour être
utilisé en cours **par d'autres**. Le calculer revenait à fabriquer une signature.

Le signal vient donc de la colonne « Verdict » de
[production-scope.md](notebook-metadata/production-scope.md), qui est la surface de
décision. Un notebook non tranché reste `BETA` — et c'est le verdict **correct**, pas un
manque : l'auteur enseigne lui-même sur les beta et les beta-teste avec ses étudiants.

`scientific_review` reste **nécessaire mais pas suffisant** pour `PRODUCTION` : il est
exigé par le validateur de périmètre, pas par l'agrégat — un axe qui *gate* ne doit pas
être le même objet que l'axe qui *décrit*.

**Le consommateur qui veut plus de granularité** lit directement `editorial`,
`reproducibility`, `scientific_review` (+ `scientific_review_stale`). Celui qui veut
l'ancien label lit `maturity`. Aucun breaking change.

## Statut séparé — non touché par ce schéma

Le champ `status` (`READY`, `DEMO`, `RESEARCH`, `BROKEN`) reste **orthogonal** aux 3 axes maturité. Un notebook peut être :
- `editorial=FINAL` + `reproducibility=REPRODUCED` + `scientific_review=ESTABLISHED` + `status=BROKEN` (ex : notebook qui marchait mais dont une dépendance externe est cassée) ;
- `editorial=ALPHA` + `reproducibility=EXECUTED` + `scientific_review=RESEARCH` + `status=DEMO` (ex : démo scientifique sans valeur pédagogique aboutie).

`status` répond à « *peut-on le faire tourner en l'état ?* », les 3 axes répondent à « *où en est sa substance ?* ». Séparer les deux est une décision architecturale stable (issue #8051 acceptance critère 2).

## Métadonnée d'exécution horodatée (critère 3)

Le catalogue embarque, par notebook, deux nouveaux champs :

| Champ | Type | Source | Signification |
|-------|------|--------|---------------|
| `last_success_sha` | string (7 chars hex) | `git rev-parse --short HEAD` au moment du commit si forensic = `A_ALL_EXEC_OK` | Commit court qui correspond à la dernière exécution validée |
| `executed_at` | ISO 8601 string | `last_commit` du forensic scan (ISO 8601, `+00:00` UTC) | Date de la dernière exécution vérifiée |

Ces deux champs permettent de calculer `reproducibility = REPRODUCED` (cohérence `last_success_sha` avec le SHA HEAD) et de répondre « *quand ce notebook a-t-il été vérifié pour la dernière fois ?* ».

## Critères d'acceptance #8051 (extrait)

- [x] **#1** Schéma 3 axes + définitions contractuelles → ce document.
- [x] **#2** Le générateur de catalogue émet `editorial`, `reproducibility`, `scientific_review` + champ rétro-compatible `maturity`.
- [x] **#3** Métadonnée d'exécution horodatée (`last_success_sha` + `executed_at`) branchée sur le forensic scan.
- [ ] **#4** Pilote sur 2 familles (Sudoku + GenAI) → phase 2, c.764+.

## Liens

- **Issue [#8051](https://github.com/jsboige/CoursIA/issues/8051)** — décomposer `maturity` en 3 axes.
- **[`scripts/notebook_tools/generate_catalog.py`](../scripts/notebook_tools/generate_catalog.py)** — générateur (modifié c.763).
- **[`scripts/notebook_tools/forensic_scan.py`](../scripts/notebook_tools/forensic_scan.py)** — source des catégories A/B/C/D + `last_commit_sha`.
- **[`COURSE_CATALOG.generated.json`](../COURSE_CATALOG.generated.json)** — artefact généré, regénéré par cron.
- **EPIC [#4208](https://github.com/jsboige/CoursIA/issues/4208)** — open-courseware fiabilisé (parent).
- **[`.claude/rules/three-exercises-per-notebook.md`](../.claude/rules/three-exercises-per-notebook.md)** — règle ≥3 exercices, critère `BETA` axe éditorial.