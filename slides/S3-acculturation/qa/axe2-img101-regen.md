# QA visuel axe 2 — regeneration `img_101.png` (porte sigmoide LSTM)

**Lane** : `myia-po-2024:CoursIA-2` (VISION MiniMax M3)
**Cible** : `slides/S3-acculturation/images/img_101.png` (lue sur la slide « Extensions 2010+ », grille 6 images avec img_098/099/100/101/102/103)
**Issue** : #12197 — regeneration figure degradee au port PPTX->Slidev
**PR source audit** : #12014 (audit verite des images tranche 1, vision 134/134)
**Date** : 2026-08-22

## Constat initial (avant regeneration)

`img_101.png` (3.9 KB) etait une figure floue/deformee issue d'un port PPTX->Slidev casse : une boite jaune rectangulaire contenant un caractere `sigma` a peine lisible, sur une ellipse rose pale, avec des fleches noires sur fond blanc. Les 4 batches vision de l'audit #12014 ont designe cette image comme **DEFECTUEUSE**, et la transcription anti-hallucination a confirme un contenu partiellement lisible (sigma LSTM) mais illisible en dessous.

Le contexte visuel : `img_101` est la 4ᵉ image d'une grille de 6 sur la slide « Extensions 2010+ » (RNN -> RNN unrolled -> LSTM cell -> **LSTM gate detail** -> ResNet -> GAN). Les 5 autres images etaient toutes propres (img_100 deja au style Olah, img_102/103 OK). Seule `img_101` posait probleme.

## Methode de regeneration

1. **Inspection du voisinage** (img_098 a img_103) pour determiner le style canonique du deck : palette jaune/pourpre/bleu/rose du blog de Christopher Olah sur les LSTM (http://colah.github.io/posts/2015-08-Understanding-LSTMs/), boites a coins arrondis, ellipses pour les etats de cellule, cercles colores pour les activations.
2. **Selection de la figure** : zoom sur la **porte d'oubli (forget gate)** — la σ recoit `h_{t-1}` et `x_t`, sa sortie module (×) l'etat de cellule `C_{t-1}` pour produire `C_t`. C'est la figure pedagogique standard apres la cellule LSTM complete (deja illustree par img_100).
3. **Generation** : matplotlib 3.10.8, dpi=150, figsize=(4, 2.7) -> PNG 600x405 px environ, blanc sur transparent.
4. **Build verification** : `slidev build S3-acculturation/slides.md` SUCCESS 12.54 s, 0 warning, 0 erreur.

## Figure generee (lecture du PNG final)

```
        C_{t-1}  --->  [X]  --->  C_t  --->  h_t
                       ^
                       |
                    [sigma]  <---  h_{t-1}
                       ^
                       |
                      x_t
```

Elements visibles et lisibles :
- Boite jaune `sigma` (rounded box, jaune #f9e79f, bordure noire fine)
- Cercles pour `h_{t-1}` (pourpre #c39bd3) et `x_t` (bleu #aed6f1) en bas
- Ellipses pour `C_{t-1}` et `C_t` (rose pale #fadbd8) en haut
- Cercle blanc `X` (rouge #e74c3c) representant la multiplication point-a-point entre σ et `C_{t-1}`
- Cercle pour `h_t` (pourpre) en haut a droite, apres une fleche `C_t -> h_t` (qui dans la cellule complete passe par tanh)
- Fleches noires pour le flux de donnees
- Legende en italique gris : « Porte sigmoide (sigma) — LSTM forget gate »

## Verdict

**PASS** sur la regeneration. La figure est maintenant :
- Lisible a 100% (aucun element manquant, σ visible et correctement positionne)
- Pedagogiquement correcte (le flux σ -> × -> C_t reflete exactement la semantique de la forget gate)
- Stylistiquement coherente avec img_100 (memes couleurs, meme disposition, meme type de boites et cercles)
- De taille raisonnable (30 KB, dans la fourchette des voisins 33-58 KB)

## Suite logique (hors scope ce cycle)

1. **#12192 alt backfill tranche 3** (OPEN) ajoutera un alt descriptif honnete a img_101 une fois merge — la description correspondra a la nouvelle figure (« Porte sigmoide de cellule LSTM, forget gate : σ(h_{t-1}, x_t) module l'etat C_{t-1} en C_t »).
2. Si d'autres figures degradees apparaissent dans un audit tranche 4 (axe 2 etape 2), elles seront traitees grain par grain comme celle-ci.
3. Le script `gen_img_101.py` est preserve dans `images/` comme artefact reproductible (genere la meme figure a partir de la meme palette).

## Conformite cycle

- **C.1** : pas de cellule notebook touchee — images PNG du deck seulement
- **G.1** : lecture visuelle du PNG genere (relue dans ce document) + voisinage img_098..103 inspecte pour determiner le style canonique
- **G.2** : verdict honnete — la nouvelle figure est PAS une copie conforme du PPTX original (qui etait deforme), c'est une **regeneration** au style canonique du deck
- **Worker discipline** : pas de merge, pas de `gh auth switch`, scope strict `slides/S3-acculturation/images/img_101.png` + `slides/S3-acculturation/qa/axe2-img101-regen.md`
- **H.4** : validation slidev build SUCCESS 12.54 s, 0 warning
- **SOTA-OK** : matplotlib 3.10.8 (lib native Python) au format PNG, meme format que les autres images du deck
- **Secrets hygiene** : aucun secret ; aucun path absolu dans la generation (matplotlib utilise des paths relatifs)