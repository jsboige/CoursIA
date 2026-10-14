# Archive — scripts one-shot de la racine

Ce dossier conserve les scripts retirés de `scripts/` une fois leur mission
livrée ou leur comportement absorbé par un outil actif. C'est un **registre de
décisions**, pas une boîte à outils : rien ici ne s'importe ni ne se rejoue sans
une issue dédiée.

Standard appliqué : [convention `_archive/`](../../docs/reference/_archive-convention.md).

## Registre des sous-archives

Chaque sous-dossier porte son propre registre de disposition (table à quatre
colonnes), qui nomme le successeur de chaque script archivé.

| Sous-archive | Archivage | Décision d'archivage | Registre |
|---|---|---|---|
| [`c8257-lean18-enrichment/`](c8257-lean18-enrichment/README.md) | 2026-09-02 | PR #14251 — helpers c.8257 devenus obsolètes après le déplacement du notebook par #13685 | [README](c8257-lean18-enrichment/README.md) |
| [`one_shot_fixes/`](one_shot_fixes/README.md) | 2026-08-06 | PR #9607 (item 4-ter de #9535) et PR #9731 (item 4-quater) | [README](one_shot_fixes/README.md) |
| [`one_shots_post_463/`](one_shots_post_463/README.md) | 2026-08-06 | PR #9580 (item 4-bis de #9535) | [README](one_shots_post_463/README.md) |
| [`recycle_csp/`](recycle_csp/README.md) | 2026-08-06 | PR #9575 — transformations CSP-3 à CSP-9 pour l'issue #463 | [README](recycle_csp/README.md) |

## Règle d'usage

- **Aucun import actif.** Chaque sous-registre a vérifié par `git grep` qu'aucun
  script actif ne référence les fichiers archivés ; ceux qui portent une
  référence n'en ont que depuis un autre fichier archivé du même dossier.
- **Réactivation explicite.** Un script archivé ne ressort de `_archive/` que
  par une issue dédiée puis un `git mv` vers un emplacement actif, avec ses
  tests remis dans la collecte. Le laisser sur place ne le réactive pas.
- **Préservation, pas suppression.** `git log --follow` retrouve le source exact
  et la décision d'archivage : c'est l'application de « Consolider != Archiver ».

## Note de recensement

L'inventaire de la [convention](../../docs/reference/_archive-convention.md)
marquait ce dossier conforme pour ses sous-archives citées, mais
`c8257-lean18-enrichment/` n'y figurait pas : la ligne ne reflétait que les
sous-dossiers issus de #9535. Le présent registre liste l'ensemble des
sous-archives présentes, y compris celle archivée plus tard par #14251.

## Références

- #13749 — standardisation des dossiers `_archive/`
- #9535 — nettoyage et rangement du dépôt (archivage des one-shots de `scripts/`)
- #14251 — archivage des helpers c.8257
- [convention `_archive/`](../../docs/reference/_archive-convention.md)
