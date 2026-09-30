# Manifeste des figures — GenAI/Image/05-History/assets/clipasso

Provenance des images cibles du notebook `05-2-CLIPasso-Semantic-Sketching.ipynb`.

> **QA visuelle déléguée (merge-gate)** : ce MANIFEST est rédigé sur la lane `myia-po-2023:CoursIA` (GLM, sans vision). Les champs mécaniques (dimensions PIL, poids octets, provenance git/livre) sont vérifiés par outil ; les champs descriptifs (`Contenu réel vérifié`, alt-text) sont des descriptions de provenance — **la vérification visuelle firsthand est déléguée au merge-gate** (ai-01 ou lane CoursIA-2 MiniMax, doctrine vision des figures).

## target_camel.png

- **Source** : `target_images/camel.png` du dépôt officiel CLIPasso (`github.com/yael-vinker/CLIPasso`, MIT) — démo canonique de la Figure 1 du papier Vinker et al. 2022.
- **Description visuelle** : photographie d'un chameau de profil sur fond uni, cadrage carré.
- **Contenu réel vérifié** : PNG 248×248 RGB (dimensions PIL vérifiées). Contenu décrit par la provenance officielle (Fig. 1 du papier) ; vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Photographie d'un chameau de profil sur fond uni — cible canonique des esquisses CLIPasso du papier (Fig. 1).
- **Poids** : 34 205 octets
- **Provenance** : copie byte-identique (pas de retouche) — `D:/Dev/clipasso-run/repo/target_images/camel.png`.

## target_robot.png

- **Source** : image de référence robot du notebook `03-4` (workflow VLM in-graph, série GenAI/Image) — `assets/krea2-character/reference_robot.png`, copiée localement pour rendre ce rayon autoportant (indépendant de l'ordre de merge de la PR krea2).
- **Description visuelle** : personnage robot en vignette générée, fond neutre.
- **Contenu réel vérifié** : PNG 591×591 RGB (dimensions PIL vérifiées). Contenu décrit par la provenance ; vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Portrait de personnage robot — seconde cible des esquisses CLIPasso (grille de l'exercice 2).
- **Poids** : 309 749 octets
- **Provenance** : copie locale depuis le worktree krea2 (source : sortie ComfyUI du cours).

## grid_abstraction.png

- **Source** : sortie de la cellule « Lecture de la grille » du notebook `05-2` (rendu côte à côte matplotlib) — **extraction directe de l'output d'exécution**, pas un montage.
- **Description visuelle** : bande de 4 panneaux — photo cible chameau puis esquisses officielles CLIPasso 32/16/8/ traits (SVG rendus en PNG), abstraction croissante de gauche à droite.
- **Contenu réel vérifié** : PNG 1589×344 RGBA (dimensions PIL vérifiées, 122 880 octets). Les 4 SVG sources sont les `_best.svg` produits par les runs officiels GPU du 17-18/09/2026 (logs de provenance dans les outputs du notebook). Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Grille d'abstraction CLIPasso — la cible chameau et ses esquisses à 32, 16, 8 puis 4 traits de Bézier.
- **Poids** : 122 880 octets
- **Provenance** : `base64` du `image/png` de l'output de la cellule grille de l'exécution finale (papermill, kernel python3).

## grid_robot_abstraction.png

- **Source** : sortie de la cellule « Rendu de la grille robot » du notebook `05-2` (matplotlib) — extraction directe de l'output d'exécution.
- **Description visuelle** : bande de 5 panneaux — source robot puis esquisses officielles CLIPasso 32/16/8/4 traits, toutes optimisées sur la cible **masquée** (`mask_object=1`, fond retiré par U²-Net).
- **Contenu réel vérifié** : PNG 1589×344 RGBA (195 180 octets, dimensions PIL vérifiées). Les 4 SVG sources sont les `_best.svg` des runs officiels GPU du 18/09/2026 (00:32-00:58). Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : Grille d'abstraction CLIPasso sur le robot — la source et ses esquisses à 32, 16, 8 puis 4 traits, fond masqué par U²-Net.
- **Poids** : 195 180 octets
- **Provenance** : `base64` du `image/png` de l'output de la cellule rendu robot de l'exécution finale.

## ab_fond_masque_brut.png

- **Source** : sortie de la cellule « A/B : le coût du fond non extrait » du notebook `05-2` (matplotlib) — extraction directe de l'output d'exécution.
- **Description visuelle** : triplet — source robot, esquisse 16 traits fond masqué (similarité CLIP 0.6519), esquisse 16 traits fond brut (0.5903) : même budget, mêmes graines.
- **Contenu réel vérifié** : PNG 1036×368 RGBA (195 642 octets, dimensions PIL vérifiées). Les deux SVG sont des `_best.svg` de runs officiels GPU du 18/09/2026 (00:40 fond masqué, 00:46 fond brut). Vérification visuelle déléguée merge-gate.
- **Alt-text (FR)** : A/B CLIPasso à 16 traits — esquisse optimisée sur cible masquée contre cible brute, même budget de traits.
- **Poids** : 195 642 octets
- **Provenance** : `base64` du `image/png` de l'output de la cellule A/B de l'exécution finale.
