# Ledger #17375 -- md-content-loss justification

Le marqueur `md-content-loss: reecriture assumee` dans le body de #17375 declare
que la cellule d'index 19 (markdown `## Exercices`, 9c) n'est pas une perte
mais le resultat d'un appariement par index legacy declenche par l'ajout de
deux cellules neuves (`bdacbcfe` md Temoin negatif reformule RP^2/3-points,
et `ac3a3e6b` code aligne) precedant `cell-18` dans le head.

Design c.8254 + fallback legacy documente (lignes 609-613 de
`scripts/notebook_tools/detect_md_content_loss.py`) : quand les ensembles
d'ids divergent entre base et head, l'organe retombe sur l'appariement par
index, ce qui produit le TRUNCATED_CELL. Le marker `#13491` en PR body est
la porte assumee par l'auteur : la cellule devient
`TRUNCATED_CELL_JUSTIFIED_BY_BODY`, le verdict binaire `--check` reste 0,
et la trace reste visible en sortie machine pour l'auditeur.

Aucune cellule n'est reellement perdue : `cell-17` (md `## Exercices`) et
`cell-18` (md `### Exercice 1`) sont intactes en id, seul leur index global
a change a cause des ajouts en amont.
