# Notebook Audio archivé — VoiceLeading RenduGenAI (pré-renumérotation)

Ce dossier conserve l'unique notebook archivé de la série Audio : la version
d'origine du rendu GenAI du voice-leading CSP, **remplacée** par le notebook
courant de la série renumérotée. Le notebook archivé n'est ni modifié ni
réexécuté — il est préservé comme provenance historique.

## Registre de disposition

| Notebook | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `04-14-VoiceLeading-RenduGenAI.ipynb` | OBSOLETE (consolidation **#13741**) — sibling pédagogique minimal (9 cellules, 51 Ko), archivé pour éliminer le doublon de slot 04-14 ; le contenu reste préservé | [`../04-Applications/04-14-VoiceLeading-Rendu-GenAI.ipynb`](../04-Applications/04-14-VoiceLeading-Rendu-GenAI.ipynb) (notebook canonique, version complète) | Note de consolidation #13741 en tête du [README de `04-Applications/`](../04-Applications/README.md) ; ce registre |

## Disposition par section

La convention exige un en-tête de disposition par fonction pour chaque fichier
`.py` archivé. Pour un **notebook** archivé, non modifiable sans casser
l'archive, la disposition équivalente vit ici : chaque bloc de contenu est
relié à son devenir.

| Bloc du notebook archivé | Devenu | Preuve |
|---|---|---|
| Titre et cadrage « Du Voice-Leading CP-SAT à l'Audio MusicGen » (md 0) | Reformulé en « Voice Leading Rendu GenAI — donner un spectre aux accords réparés », avec liens de navigation de série (md 0 du notebook courant) | Comparaison cellule à cellule des deux notebooks sur `main` (2026-09-25) |
| Lecture des spectrogrammes / interprétation pédagogique (md 1) | Développé en section « 1. Le problème du rendu : des hauteurs ne sont pas un son » | idem |
| Cellules de code (7) | Reprises et étendues à 13 cellules de code dans le notebook canonique (28 cellules markdown d'enrichissement en plus) | Comptes mesurés le 2026-09-25 : 9 cellules (2 md / 7 code) → 41 cellules (28 md / 13 code) ; la note #13741 en annonçait 27 à sa date, l'enrichissement a continué depuis |

## Vérifications faites à la mise au standard (2026-09-25)

- **Successeur nommé et présent** — `04-Applications/04-14-VoiceLeading-Rendu-GenAI.ipynb`
  existe sur `main`, avec `execution_count` renseigné sur toutes ses cellules
  de code (les deux versions sont exécutées : aucune n'est un brouillon).
- **Référence entrante assumée** — le notebook archivé est cité **une fois**,
  par la note de consolidation #13741 du [README de `04-Applications/`](../04-Applications/README.md),
  qui documente précisément son archivage. Ce n'est pas un consommateur (aucun
  appel, aucun chemin d'exécution) mais c'est la référence durable du verdict :
  elle est conservée et ce registre y renvoie plutôt que de la dupliquer.
- La disposition vit dans ce README (et non en en-tête du notebook), parce que
  modifier le JSON d'un notebook archivé romprait la préservation byte-exacte
  qui justifie son archivage — modèle `SymbolicAI/Planners/_archive/`.