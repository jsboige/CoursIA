# Lot apparie avec et sans sophisme

Chaque paire conserve le scenario, la position defendue, le locuteur
(`smoothTalker`) et l'interlocuteur. Seule la maniere d'argumenter change.
Le bras positif est le texte du corpus val FR deja valide ; le negatif est
accepte seulement si son reclassement rejette le sophisme cible et, quand la
taxonomie declare une vertu opposee, si un controle la retrouve.

## Resultat

- paires tentees : 60
- paires acceptees : **55**
- paires rejetees : **5** (motifs dans le rapport JSON)
- lignes publiees : 110 (deux par paire acceptee)
- paires acceptees avec controle positif sur vertu liee : 3

| Mesure | Valeur |
|---|---:|
| Taux d'acceptation | 0.9167 |
| Accuracy du raccourci role -> polarite | 0.5000 |

Le role reste `smoothTalker` dans les deux bras : il ne predit plus la
polarite. L'accuracy affichee est celle de la meilleure regle constante
utilisant uniquement ce role ; 0,5 sur un lot equilibre est le hasard.

## Rejets a la derniere tentative

| Motif | Paires |
|---|---:|
| `negative_target_reclassified` | 4 |
| `virtue_not_reclassified` | 1 |

## Empreintes et rejeu

- corpus source : `d7621fffa05dc857b2110fc44299b04fdbce670efbd76c633ec3917e83aef52c`
- lot JSONL : `112f68e26b42217beaf9acb4a03840d8749190c4391a6190547d419b77294ba1`
- rapport JSON : `5374631a26474fef7f1e150e12b5414a15ff8022431398a067de5902678e4743`

Le checkpoint est local et non committe. `--report-only` le relit sans
cle ni reseau ; sur un clone frais, il reconstruit depuis le rapport
publie, dont `attempted_pairs` conserve toutes les tentatives et tous
les votes. Les motifs `vote_unparsed` et `vote_missing` sont des rejets
de prudence, jamais des preuves d'absence de sophisme.
