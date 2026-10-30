# Archives de la série RAG-et-Memoire-Semantique

Ce dossier conserve les carnets **archivés** de la série : leur contenu a été repris ailleurs
dans la série, et l'original est préservé **byte pour byte** (sha256 du fichier archivé identique
au blob de `main` au moment de l'archivage). Un carnet archivé n'est ni réécrit ni réexécuté — il
est préservé comme provenance historique, et son registre de disposition vit ici.

## Registre de disposition

| Notebook | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `05c-Moteurs-Vectoriels-Compares.ipynb` | OBSOLETE (fusion **#23588**) — comparatif de trois architectures de stockage vectoriel sur un corpus **propre à ce carnet** ; archivé pour que la comparaison et le corpus ne fasse plus qu'un, dans le carnet fusionné | [`../05b-Stockage-Vectoriel-Serveur.ipynb`](../05b-Stockage-Vectoriel-Serveur.ipynb) (carnet canonique, sections 3 à 8) | Issue #23588 (corps + critères d'acceptation) ; la PR de fusion qui la livre ; ce registre |

## Disposition par section

La convention exige un en-tête de disposition par fonction pour chaque fichier `.py` archivé. Pour
un **notebook** archivé, non modifiable sans casser la préservation byte-exacte qui justifie son
archivage, la disposition équivalente vit ici : chaque bloc de contenu est relié à son devenir.

| Bloc du notebook archivé | Devenu | Preuve |
|---|---|---|
| §2 FAISS — code et mesure (md 8, code 9, md 10) | §3 du carnet fusionné, code repris à l'identique (seul le préfixe du répertoire temporaire change : `rag05c_faiss_` → `rag05b_faiss_`) | Comparaison cellule à cellule du notebook archivé et du carnet fusionné (2026-10-30) |
| §3 pgvector — code et mesure (md 11, code 12, md 13, code 14, md 15) | §4 du carnet fusionné ; le conteneur est renommé `rag05c_pgvector` → `rag05b_pgvector` et la base `rag05c` → `rag05b` (cohérence de série) | idem |
| §4 Qdrant via le SDK (md 16, code 17, md 18) | §5 du carnet fusionné, **corrigé** : le SDK y **réutilise** la collection `rag05b_demo` déjà ingérée par la section 2 (même serveur, deux portes d'entrée) au lieu d'en créer une seconde, et le nom du conteneur est détecté dynamiquement au lieu d'être codé en dur | idem ; l'écart est motivé dans le corps de la PR de fusion |
| §5 table comparative (md 19, code 20, md 21) | §7 du carnet fusionné, **étendue** : la série « Qdrant HTTP » (résultats de la section 2) est ajoutée aux trois autres, et le genou du compromis est calculé sur quatre séries | idem |
| §6 filtre métadonnées (md 22, code 23, md 24) | §6 du carnet fusionné, identique ; la collection interrogée est la collection partagée | idem |
| §7 exercices (md 27, code 28, code 29, code 30) | §8 du carnet fusionné — exercices **4** (paramètre `m` de FAISS), **5** (plancher `ef_search` de pgvector) et **6** (sur-tir minimal de FAISS), renumérotés pour laisser la place aux exercices 1 à 3 du serveur | idem |
| §1 Objectifs, protocole, corpus, ground truth (md 1, code 2, md 3, code 4, md 5, code 6, md 7) | **Abandonné ici, repris une seule fois** dans les sections 1 et 2 du carnet fusionné : un seul générateur de corpus, une seule graine, une seule vérité NumPy pour tout le carnet. C'est la raison de la fusion — comparer trois moteurs suppose un corpus unique | idem |
| Courbe comparative (code 25, md 26) | §7 du carnet fusionné, **étendue à quatre séries** et sauvegardée sous `courbe_moteurs_rag05b.png` (la courbe du seul Qdrant reste `courbe_signature_rag05b.png`) | idem |

## Vérifications faites à la mise au standard (2026-10-30)

- **Préservation byte-exacte** — `sha256(05c-Moteurs-Vectoriels-Compares.ipynb)` =
  `caae8ad9ebf3400af45d675d9cb4df31ac07687aa0bd5276451777265b8915fd`, identique au blob de `main`
  au moment du déplacement ; le fichier n'a reçu ni en-tête, ni réécriture, ni réexécution.
- **Successeur nommé et présent** — `../05b-Stockage-Vectoriel-Serveur.ipynb` existe sur la branche
  de la fusion, avec ses cellules de code **exécutées et leurs sorties réelles** (C.2).
- **Références maintenues à la main** — quatre points pointaient vers `05c` hors artefacts
  générés (le README de la série, la barre de navigation du carnet 06, la navigation du carnet 03b
  et la clé de la base de densité pédagogique). Trois ont été purgés dans la même PR : le README
  de la série, la navigation du carnet 03b et la clé de la base ; le carnet fusionné ne cite plus
  `05c` que pour nommer sa provenance. **Le quatrième, la barre de navigation du carnet 06,
  conserve volontairement une entrée `05c (archive)`** pointée sur
  `_archive/05c-Moteurs-Vectoriels-Compares.ipynb` : retirer cette entrée ferait perdre au
  lecteur le chemin vers la comparaison des moteurs (le lien « next » de la série), et le garde
  « No markdown content loss in changed notebooks » la relèverait. Ce pointeur vise la copie
  archivée, qui préserve le contenu byte-exact — ce n'est pas une référence résiduelle à un
  carnet actif.
- **Artefacts générés, laissés à l'automatisation** — `COURSE_CATALOG.generated.json`,
  `COURSE_CATALOG.generated.md`, `docs/curriculum/genai.md` et `_quarto.yml` mentionnent encore
  `05c` : ils restent **byte-identiques à `main`** sur la branche de la fusion (règle
  `catalog-pr-hygiene`), et leur régénération appartient au cron du catalogue après le merge
  (#23266).
- **Le contenu n'est pas perdu** — chaque mesure de ce carnet existe dans le carnet fusionné, et
  l'original reste lisible ci-dessus, exécuté et daté.
