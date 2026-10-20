# Reproductibilité des socles 3D — mesure sur deux postes

**Objet.** Les carnets de la série `MyIA.AI.Notebooks/GenAI/3D/` portent, dans leurs sorties committées, des mesures de fidélité (PSNR, corrélations, pertes) que la recette 3D (`jsboige/CoursIA#20386`) projette déjà vers un validateur externe. Avant de **promettre** ces chiffres dans un cahier des charges, il faut savoir s'ils sont **stables d'une machine à l'autre** : un nombre obtenu sur un seul poste n'est pas une promesse, c'est une observation.

Ce document enregistre la mesure de reproductibilité faite depuis le poste **`myia-po-2028`** (machine `MYIA-PO-2028`, RTX 3070 Ti Laptop 8 Go, `torch 2.8.0+cu126`), comparée aux sorties validées dans le dépôt.

**Ce que ce document n'est pas.** Ce n'est pas un audit de la série 3D, ni une réexécution de tous les carnets : deux socles sont mesurés, deux ne le sont pas (et pourquoi, en §4). Les chiffres de référence sont **ceux des sorties committées** du dépôt ; ceux de `po-2028` sont **des exécutions fraîches** de ce poste.

---

## 1. Méthode

| | |
|---|---|
| Machine de mesure | `myia-po-2028` — Windows 11, i7-12700H, **RTX 3070 Ti Laptop GPU (8 192 MiB)**, `torch 2.8.0+cu126` (même version que la référence), Python 3.13.16 |
| Exécution | `scripts/notebook_tools/notebook_tools.py execute <carnet> --timeout 2400` (Papermill, kernel `python3`) |
| Contrôle | Semences du carnet inchangées (`SEED = 20261008` pour 3D-01, `SEED = 42` pour 3D-03), jeu de données identique (dataset officiel `tiny_nerf_data.npz` téléchargé depuis la source des auteurs), aucun paramètre modifié |
| Comparaison | Colonne « référence » = sorties **committées** du dépôt ; colonne « po-2028 » = exécution fraîche du même carnet, sans modification de source |

**Une précision de périmètre, importante pour la lecture.** Pour le socle A1, l'exécution fraîche a été faite **sur une copie du carnet hors dépôt**, et **le carnet du dépôt n'est pas modifié** : son fichier est dans le scope de claims actifs d'autres lanes (PR #21413 et #20544). La mesure est donc réelle, mais elle ne remplace pas les sorties committées — elle les **confronte**. Pour le socle splats (`3D-03`), le carnet **est** dans le diff : il était libre de collision, et ses sorties committées ont été remplacées par les sorties fraîches (identiques en valeur, §3).

---

## 2. Socle A1 — NeRF from scratch (`3D-01-NeRF-From-Scratch.ipynb`)

Fidélité de la reconstitution de la scène Lego (dataset officiel NeRF, 106 vues 100×100), en décibels PSNR — plus haut est plus fidèle.

| Itération | Référence (sorties committées) | po-2028 (exécution fraîche) | Écart |
|---:|---:|---:|---:|
| 1 | 7,49 dB | 7,49 dB | 0,00 |
| 200 | 11,01 dB | 11,01 dB | 0,00 |
| 400 | 15,16 dB | 14,89 dB | −0,27 |
| 600 | 18,92 dB | 18,88 dB | −0,04 |
| 800 | 19,96 dB | 20,00 dB | +0,04 |
| 1 000 | 20,15 dB | 20,22 dB | +0,07 |
| 1 200 | 20,45 dB | 20,56 dB | +0,11 |
| 1 400 | 20,89 dB | 21,03 dB | +0,14 |
| 1 600 | 21,13 dB | 21,26 dB | +0,13 |
| 1 800 | 21,89 dB | 21,82 dB | −0,07 |
| **2 000** | **21,85 dB** | **21,92 dB** | **+0,07** |

**Verdict.** Le chiffre-clé du socle — « la reconstitution atteint **≈ 21,9 dB** » — **se reproduit à 0,07 dB près** sur un second poste de la flotte, avec un **GPU différent** et la même version de `torch`. L'erreur au point de départ est identique au bit près (MSE 0,17804), et l'écart ne dépasse jamais 0,27 dB en cours d'apprentissage. Le témoin « le résultat tient sur toutes les machines » est donc **tenu pour ce socle**, dans la plage de machines et de versions testées.

**Ce que la mesure ne dit pas.** La carte de référence ne dit pas **quel** GPU a produit les sorties committées (l'en-tête du carnet n'enregistre que `device: cuda` et la version de `torch`). Le contrôle est donc « un autre poste de la flotte, GPU CUDA », et non « la même architecture ». L'écart observé (± 0,1 dB) est de toute façon d'un ordre de grandeur inférieur à l'écart entre deux **méthodes** de la série (3D-02 mesure des plafonds à ~1 dB près).

**Vitesse, pour dimensionner un calcul.** Le poste `po-2028` enchaîne à **15,5 it/s** sur la scène Lego, contre **24,7 it/s** sur le poste de référence : un facteur **1,6**. Le temps de calcul du socle A1 est donc à multiplier par ~1,6 pour un GPU de classe portable.

---

## 3. Socle splats (`3D-03-Gaussian-Splats-Concepts.ipynb`) — reproduction **exacte**

Exécution fraîche sur `po-2028` (torch 2.8.0+cu126, semences du carnet inchangées, 15 cellules de code, **0 `execution_count` nul, 0 erreur**), comparée aux sorties committées du dépôt.

| Mesure | Référence (sorties committées) | po-2028 (exécution fraîche) | Écart |
|---|---:|---:|---:|
| Perte finale (L1 moyen par vue, 550 itérations) | 0,0168 | **0,0168** | **0** |
| Corrélation, vue azimut 20° | 0,976 | **0,976** | **0** |
| Corrélation, vue azimut 110° | 0,978 | **0,978** | **0** |
| Corrélation, vue azimut 200° | 0,983 | **0,983** | **0** |
| L1 azimut 20° / 110° / 200° | 0,0181 / 0,0149 / 0,0175 | **0,0181 / 0,0149 / 0,0175** | **0** |
| L1 périphérie vs centre (azimut 20°) | 0,0045 vs 0,0395 | **0,0045 vs 0,0395** | **0** |
| Splats significatifs (opacité > 0,15) | 457 / 600 | **457 / 600** | **0** |
| Anisotropie médiane (init. 1,11) | 1,83 | **1,83** | **0** |
| Anisotropie cœur (284 splats) / anneau (167) | 1,67 / 2,17 | **1,67 / 2,17** | **0** |
| Opacités optimisées : médiane / max / > 0,1 | 0,189 / 0,426 / 592-600 | **0,189 / 0,426 / 592-600** | **0** |
| Évaluations par pixel (splats) | 12,1 (max 133) | **12,1 (max 133)** | **0** |

**Verdict.** Le socle splats est **reproductible au chiffre près** sur un autre poste : les onze grandeurs mesurées sont **identiques**, à la précision imprimée. La différence avec le socle NeRF (§2, écart de 0,07 dB) est explicite : l'optimisation splats est **entièrement déterministe** (semences fixes, arithmétique CPU), alors que le NeRF accumule des flottants GPU dont le résultat dépend de l'architecture — d'où un écart faible mais non nul.

**Ce que la mesure dit en plus, et qui n'était pas dans le carnet.** Les durées, en revanche, ne sont **pas** reproductibles : elles dépendent de la machine et de sa charge.

| Chrono | Référence | po-2028 | Facteur |
|---|---:|---:|---:|
| Optimisation (550 itérations) | 426,0 s | **951,4 s** | **× 2,2** |
| Rendu volumique (80×80) | 16 ms | **37 ms** | × 2,3 |
| Rendu splats (600 primitives) | 56 ms | **167 ms** | × 3,0 |

`po-2028` est un poste **partagé** (plusieurs sessions d'agents, charge CPU mesurée à 42 % pendant la mesure) et l'optimisation splats est **purement CPU**. **Conséquence de dimensionnement** : un démonstrateur fondé sur ce socle doit compter **~16 minutes de CPU par run** sur une machine de cette classe, et non les ~7 minutes mesurées sur un poste libre — l'écart se comporte comme la charge, pas comme le carnet.

**Les sorties committées du carnet sont remplacées par les présentes.** La re-exécution a produit des sorties **identiques en valeur** (tableau ci-dessus) mais des **images re-encodées** (diff de 992 insertions / 98 suppressions, essentiellement des blobs d'images et les horodatages d'exécution) : le carnet est committé avec ses sorties fraîches, conformément à C.2, et le tableau de mesures ci-dessus est la preuve de l'équivalence.

**Un défaut de portabilité trouvé au passage.** `3D-05-3DGS-Optimization-Tradeoffs.ipynb` pose `os.environ["CUDA_VISIBLE_DEVICES"] = "1"` dans sa première cellule. Sur une machine à **un seul GPU** — dont `po-2028` — cette ligne masque le device et rend le carnet inexécutable tel quel. C'est un défaut **du carnet**, pas de la machine, et il serait corrigé par une ligne. Il est signalé ici pour la lane qui porte ce carnet, plutôt que corrigé dans une PR qui aurait déformé le périmètre de ce cycle.

---

## 4. Ce qui n'est pas mesurable sur ce poste, et pourquoi

| Carnet | Exigence | État sur `po-2028` |
|---|---|---|
| `3D-04-3DGS-From-Scratch-with-gsplat` | moteur `gsplat` (extension CUDA compilée) | **Non exécutable ici** : `nvcc` absent, pas de chaîne CUDA installée ; l'installation du moteur est un chantier à part |
| `3D-05-3DGS-Optimization-Tradeoffs` | idem + `CUDA_VISIBLE_DEVICES` **codé en dur à `"1"`** | **Non exécutable ici** : même moteur, et l'index de GPU codé en dur rend le carnet **invalide sur toute machine à un seul GPU** (dont celle-ci) |

Deux observations qui valent pour la flotte, au-delà de ce poste :

1. **Le carnet `3D-05` n'est pas portable** : `os.environ["CUDA_VISIBLE_DEVICES"] = "1"` est posé dans sa première cellule. Sur une machine à un seul GPU (dont `po-2028`), cette ligne masque le device et fait échouer l'exécution. C'est un défaut de portabilité du carnet, pas de la machine.
2. Les mesures de `3D-04` / `3D-05` **existent** et sont validées dans le dépôt (PR #20398) ; ce document ne les re-mesure pas, il en **rappelle la provenance** : exécution validée, `gsplat 1.5.3+pt24cu124`, `torch 2.4.1+cu124`, RTX 3080 Ti.

---

## 5. Ce que cela dit pour la recette (`jsboige/CoursIA#20386`)

- Le **socle A1** peut être promis à un validateur avec son chiffre : **21,9 dB ± 0,1**, **reproduit sur deux postes** de la flotte.
- Le **socle splats** (3D-03) est, lui, **reproductible** au sens de §3, et son volet « tradeoffs » (3D-05) est **stable par construction** (runs de 2 à 3 s, semences fixes) mais **non rejouable sur ce poste** faute de moteur `gsplat`.
- Le **passage à l'échelle** reste hors de portée de toute cette série : les mesures sont à 1 145 points et 400 itérations (3D-05) et à 2 000 itérations sur une scène de 100×100 pixels (3D-01). **Aucun de ces chiffres ne dit ce qui se passe sur une vraie scène de terrain.**

---

## 6. Comment reproduire

```bash
# Prérequis : env Conda avec torch 2.8.0+cu126 (cu126 pour la reproductibilité du bit)
pip install "torch==2.8.0" --index-url https://download.pytorch.org/whl/cu126 numpy matplotlib

# Exécution (timeout par cellule : 2400 s — la cellule d'optimisation du socle
# splats dépasse 300 s sur un portable, et le défaut de nbclient tue l'exécution)
python scripts/notebook_tools/notebook_tools.py execute \
    MyIA.AI.Notebooks/GenAI/3D/3D-01-NeRF-From-Scratch.ipynb --timeout 2400
```

Le dataset Lego est téléchargé automatiquement dans `data/` (hors dépôt, gitignoré) depuis la source des auteurs.

## Références

- `MyIA.AI.Notebooks/GenAI/3D/` — la série 3D et ses carnets
- `docs/reference/kernels-runtime.md` — inventaire kernels du poste `myia-po-2028`
- `jsboige/CoursIA#20386` — recette du pipeline 3D (MOA externe)
- `jsboige/CoursIA#20398` — PR d'origine des carnets `3D-04` / `3D-05`
