# Cadrage — index des documents épistémiques

> Issue [#17525](https://github.com/jsboige/CoursIA/issues/17525) · règle d'agrégation par **communauté interlocutrice**, pas par texte externe. Le nom du document porte sa **relation** (`-lens`, `-dialogue`, `-position`, `-self-audit`, `-armature`).

Ce répertoire rassemble les documents qui positionnent le dépôt face à un texte externe (déclarations, manifestes, consensus) ou face à un courant de pensée qui irrigue plusieurs séries. Chaque document entre comme **section** du document de sa communauté ; il gagne un fichier propre seulement s'il change une pratique ou un gate que le document de communauté ne peut pas porter.

Une **veille** (texte connu et non traité) figure dans le tableau comme une ligne à part entière — un texte non traité est un ligne explicite, pas un oubli.

## Tableau agrégateur

| Communauté interlocutrice | Document | Relation | Textes rattachés | Statut |
|---|---|---|---|---|
| Communauté mathématique | [`leiden-declaration-position.md`](../leiden-declaration-position.md) | position | Déclaration de Leiden (2026), SAIR Open Models | traité |
| Autorité morale | [`magnifica-humanitas-dialogue.md`](../magnifica-humanitas-dialogue.md) | dialogue | *Magnifica Humanitas* (Léon XIV, 2026) | traité (reprise user en attente, voir #11359) |
| Recherche en sûreté de l'IA | [`singapore-consensus-self-audit.md`](singapore-consensus-self-audit.md) | self-audit | *2026 Singapore Consensus* (R11, Casper et al.) | traité (#16757) |
| Recherche en sûreté de l'IA — veille | — | veille | *International AI Safety Report 2026* (arXiv 2602.21012) et ses deux *Key Updates* | non traité |
| Recherche en sûreté de l'IA — veille | — | veille | *Towards Guaranteed Safe AI* | non traité (#16761) |
| Science ouverte et évaluation | — (section de Leiden tant qu'il n'y a pas de pratique propre) | section | UNESCO Open Science, FAIR, DORA | traité (section du document Leiden) |
| Fondateurs de la discipline | — (`aima-armature.md` à créer, arc E de Epic #17528) | armature | AIMA 4e, textes de position des auteurs, position « benchmark-driven AI » (OpenReview 2026) | non traité |
| Lecture interne transversale | [`grothendieckian-lens.md`](../grothendieckian-lens.md) | lens | — | traité (clé de lecture) |

## Règles d'agrégation

1. **Un document par communauté interlocutrice.** Une nouvelle déclaration entre comme section du document de sa communauté. Un texte gagne un fichier propre s'il change une pratique ou un gate que le document de communauté ne peut pas porter.
2. **La relation est encodée dans le nom.** `-lens` (clé de lecture), `-dialogue` (échange avec une autorité morale), `-position` (engagement mesurable), `-self-audit` (audit du dépôt par un texte externe), `-armature` (socle technique). Une relation nouvelle se nomme avant d'écrire.
3. **Un auteur n'est pas une communauté.** Ses textes de position vont au document de la communauté concernée. Ses résultats techniques vont dans les séries, par un organe que la série exécute — pas par une citation dans le cadrage. Un même auteur peut apparaître à plusieurs endroits ; c'est l'index qui rend ces liens visibles.

## Migration par tranches (cf #17525)

- **Tranche 1** : Singapore entre dans `docs/cadrage/` directement (#16757), et le répertoire naît avec son index.
- **Tranche 2** : `leiden-declaration-position.md` et `grothendieckian-lens.md` migrent après merge de #17495 et #17467.
- **Tranche 3** : `magnifica-humanitas-dialogue.md` migre après reprise user du texte (arbitrage du 22/09).

## Voir aussi

- `docs/README.md` — index général de la documentation du dépôt
- `docs/PARCOURS.md` — schéma maturité 3 axes (#8051)
- `docs/audit/` — audits cross-famille
