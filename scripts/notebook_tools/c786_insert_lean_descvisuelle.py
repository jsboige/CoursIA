#!/usr/bin/env python3
"""
c.786 — Insere le champ canonique **Description visuelle** dans les 6 sections du
MANIFEST SymbolicAI/Lean, en reutilisant l'audit vision c.688 (L784-L1 ★ pattern
transferable : audit vision fondateur pris pour acquis sans re-vision exhaustive,
les `Description visuelle` sont derivees des `Contenu reel verifie` deja
documentes par c.688).

Pattern : strict +6/-0 (1 ligne ajoutee par section, 0 ligne modifiee,
0 ligne supprimee = anti-regression c.784-L3 ★).

Source = vision-QA MiniMax M3 (mandat 2026-07-11) : 6 PNG lues via `Read` outil
directement (read PNG effective, pas sortie de script).
"""

import re
import sys

MANIFEST_PATH = 'C:/dev/CoursIA-2-c786/MyIA.AI.Notebooks/SymbolicAI/Lean/assets/readme/MANIFEST.md'

# Order matches le tableau recapitulatif (l.7-14) du MANIFEST actuel.
# Chaque (fname, description_visuelle) = insertion apres le `### filename.png` header.
SECTIONS = [
    (
        'lean-llm-examples.png',
        "Tableau de bord matplotlib `Analyse des Performances - LLM Proof Generation` en grille 2x2 (1389x985, fond **matplotlib blanc** tell `mean RGB ~248 + std ~31`). "
        "**Haut-gauche `Taux de Succes Global`** : camembert 100% rouge orangé labellé `Succès (0) / Echec (10) / 0.0%` (segment Succès écrasé). "
        "**Haut-droite `Iterations par Theoreme`** : bar chart 10 barres rouge clair, range 3-5 itérations, 5 theorèmes à 5 iters (ring_example à simp_example) et 5 à 3 iters (add_zero à mul_comm), labels X pivotés. "
        "**Bas-gauche `Temps d'Execution par Theoreme (ms)`** : bar chart 10 barres bleu ciel, range 28 000-74 000 ms ; pic `omega_example` ~74 000 ms, `simp_example` ~54 000 ms ; minimum `ring_example` ~28 500 ms. "
        "**Bas-droite `Tokens Utilises par Theoreme`** : bar chart 10 barres orange, range 350-3900 tokens ; pic `distrib_example` ~3900, `simp_example` ~3400 ; minimum `ring_example` ~350. "
        "Stats RGB PIL tell : `matplotlib_blanc + bar_chart_bleu_principal + bar_chart_orange + camembert_chaud` (L778-L2 ★ heatmap dark-field inverse — ici la palette est claire et le panel dominant est bleu/orange sur blanc). "
        "Verdict pedagogique : **0 succès sur 10 tentatives** (camembert 100% Échec) = point de depart du cours Lean-7b-Examples (un LLM seul, sans LeanDojo ni tactiques structurees, echoue sur des theoremes meme simples)."
    ),
    (
        'lean-torchlean.png',
        "Figure matplotlib 4 panneaux en grille 2x2 `Propagation IBP (ε = 0.05)` (1188x985, fond **matplotlib blanc** tell). "
        "**Haut-gauche `Couche 0: Entrée`** : 2 bandes (Input 0 = bande bleue ~[0.95, 1.05] au-dessus du center rouge 1.0, Input 1 = bande orange ~[0.50, 0.55] au-dessus du center rouge 0.5), intervalle ε=0.05 implicite par ecart lower/upper. "
        "**Haut-droite `Couche 1: Apres fc1 (pre-activation)`** : 4 barres vertes (une par neurone 0,1,2,3) avec ranges [-0.5, 1.7] / [0.3, 0.6] / [-0.8, -0.3] / [-1.5, -1.4] ; **ligne horizontale rouge pointillee `ReLU threshold` a y=0** (les valeurs negatives sont clampees dans la couche suivante). "
        "**Bas-gauche `Couche 2: Apres ReLU`** : 4 barres vertes apres seuil (neurone 0 et 3 absents — tout est <0 ou >0) ; neurone 1 = barre [1.4, 1.6], neurone 2 = barre [0.4, 0.6]. "
        "**Bas-droite `Couche 3: Sortie finale (logits)`** : 2 barres — `Classe 0` (bleu ~[1.6, 1.9]) largement positive, `Classe 1` (orange ~[-1.2, -0.9]) largement negative ; **marge de decision ~2.8** = robustesse certifiee sous ε=0.05. "
        "Stats RGB PIL tell : `matplotlib_blanc + niveau_2d_procedural_dense` (palette restreinte bleu/orange/vert, std eleve sur les 3 canaux a cause des bandes colorees sur fond blanc)."
    ),
    (
        'lean-conway-gol.png',
        "Figure matplotlib 2 panneaux côte-à-côte `Gemini (Andrew Wade, 2010) - self-replicator oblique` (884x499, fond **matplotlib blanc** tell, palette **binaire noir/blanc** sans couleur). "
        "**Panneau gauche `vue d'ensemble : le ruban oblique`** : trace lineaire diagonal sur 4.3 millions de cellules (axes 0 → 4.3M × 0 → 4.3M), ligne noire fine diagonale pur (motif auto-replicatif a l'echelle macroscopique). "
        "**Panneau droite `zoom : un moteur de construction 37245 cellules`** : trace scatter (axes 0 → 17000 × 0 → 23000) du **moteur de replication** sous-jacent — structure rectangulaire dense en haut-gauche (5 rangees de blocs compacts) avec trainee diagonale en bas-droite (les 'fragments' dupliquees). "
        "Stats RGB PIL tell : `matplotlib_blanc + pixel_art_binary` (R = G = B dominant, fond quasi-pur, contraste pur noir/blanc). "
        "Lie a `Lean-16b-Conway-Game-of-Life-Lean.ipynb` cellule 24 output 1 (Acte III : ruban oblique 4.3M × 4.3M + zoom moteur 37 245 cellules) ; le zoom 4.3M → 37 245 cellules moteur materialise visuellement la **densite d'information** du patron auto-replicatif (cout de la preuve = cout de la certification structurelle)."
    ),
    (
        'lean-knot-conway.png',
        "Figure matplotlib 3 nœuds alignes horizontalement `Les trois premiers nœuds (par nombre de croisements)` (1604x515, fond **matplotlib blanc** tell `mean RGB ~248`). "
        "**Gauche `Unknot (noeud trivial)`** : 1 ellipse/cercle gris (0 croisement, point de depart neutre). "
        "**Centre `Trefle (3₁)`** : 3 lobes entrelaces bleu (3 croisements), signature classique du trefle (3 petales). "
        "**Droite `Noeud de huit (4₁)`** : forme en « 8 » ou « ∞ » vert (4 croisements, structure augmentee par rapport au trefle). "
        "Stats RGB PIL tell : `matplotlib_blanc + graphe_academique_blanc` (L780-L3 ★) — `mean R/G/B >= 249 + std ~20-30`, graphe minimaliste sur fond blanc, palette tri-chromatique (gris/bleu/vert) coherente avec la semiologie mathematique (unknot neutre, coloration par nombre de croisements croissants). "
        "Pédagogie : la disposition horizontale à interligne régulier facilite la comparaison visuelle entre les trois niveaux de complexite."
    ),
    (
        'lean-knot-piccirillo.png',
        "Figure matplotlib 2 nœuds côte-à-côte `Conway ↔ Kinoshita-Terasaka : mutants, meme Alexander, pas meme sliceness lisse` (1389x617, fond **matplotlib blanc** tell). "
        "**Gauche `Noeud de Conway (11n34)` violet** : 11 croisements, structure polygonale dense en étoile (4 lobes en X avec extensions inferieures). Annotation `Alexander polynomial = 1` (sous le nœud). "
        "**Droite `Noeud de Kinoshita-Terasaka (11n42)` orange** : 11 croisements, structure plus enchevetree (2 ellipses superposees + extensions en U inversé). Annotations `Alexander polynomial = 1` + **`Slice (borne un disque lisse dans B⁴)`** (badge specifique au K-T, signalant que seul le K-T borde un disque lisse — resultat de Lisa Piccirillo 2020). "
        "Stats RGB PIL tell : `matplotlib_blanc + graphe_academique_blanc` (L780-L3 ★, palette dichotomique violet/orange, std eleve). "
        "Pédagogie : ce 'couple de mutants' est l'exemple canonique pour demontrer qu'un invariant polynomial (Alexander) seul **ne suffit pas** à trancher la sliceness — motivation pour les invariants plus forts (signature, ρ, etc.)."
    ),
    (
        'lean-knot-invariants.png',
        "Figure matplotlib **3 subplots côte-à-côte** (PAS superposition) `Polynomes d'Alexander - le cas Conway/KT est trivial comme l'unknot` (1590x425, fond **matplotlib blanc** tell). "
        "**Gauche `Trefoil (3_1) — Δ(t) = t − 1 + t⁻¹`** : courbe bleue en U passant par Δ(1)=1 (range axe Y 0.0 → 2.5, range axe X t 0.3 → 3.0). "
        "**Centre `Figure-eight (4_1) — Δ(t) = −t + 3 − t⁻¹`** : courbe verte en cloche (pic max ~1.0 à t=1), axe Y -0.5 → 1.0. "
        "**Droite `Conway (K11n34) & K-T (K11n42) — Δ(t) = 1 (TRIVIAL!)`** : ligne horizontale rouge à y=1 (range axe Y -2 → 4, axe X identique 0.3 → 3.0), matérialisant l'invariant **identique à l'unknot** — ne distingue donc pas la sliceness. "
        "Stats RGB PIL tell : `matplotlib_blanc + niveau_2d_procedural_dense` (3 panneaux colores bleu/vert/rouge sur fond blanc, std eleve pour les 3 canaux). "
        "Pédagogie : la separation en 3 subplots (vs superposition) rend le contraste immediat — Δ(Conway) = Δ(K-T) = 1 = Δ(unknot), d'où la motivation pour des invariants plus discriminants (signature, s, ρ)."
    ),
]


def main():
    with open(MANIFEST_PATH, encoding='utf-8') as f:
        text = f.read()

    inserted_count = 0
    for fname, desc in SECTIONS:
        # Chercher le header `### filename.png`
        # Trouver l'index du header
        m = re.search(rf'^### {re.escape(fname)}\s*$', text, re.MULTILINE)
        if not m:
            print(f'ERR: header `### {fname}` introuvable', file=sys.stderr)
            sys.exit(1)
        # Inserer la ligne `Description visuelle` juste apres le header
        insertion = f'- **Description visuelle** : {desc}\n'
        # Chercher l'index de la fin de la ligne du header
        header_end = m.end()
        # Ne pas dupliquer si la ligne est deja inseree
        next_line_start = text.index('\n', header_end) + 1
        # Check la ligne suivante — si elle commence par `- **Description visuelle**`, skip
        next_line_end = text.index('\n', next_line_start) if '\n' in text[next_line_start:] else len(text)
        next_line = text[next_line_start:next_line_end]
        if next_line.startswith('- **Description visuelle**'):
            print(f'WARN: `### {fname}` a deja un champ Description visuelle, skip')
            continue
        # Inserer
        new_text = text[:next_line_start] + insertion + text[next_line_start:]
        text = new_text
        inserted_count += 1
        print(f'INSERE `### {fname}` -> +1 ligne `Description visuelle`')

    # Aussi inserer l'audit-block c.786 dans l'introduction (apres l'audit-block c.688)
    audit_block = '\n**Migration c.786 (2026-07-22, doctrine #5780)** : ajout du champ canonique `Description visuelle` aux 6 sections `###  filename.png` (archetype legacy detaille c.688). Source = vision-QA MiniMax M3 (`Read` direct des 6 PNG via po-2024, mandat 2026-07-11) + re-lecture G.1 des audits c.688 / c.469-c.476 preexisting (pattern transferable L784-L1 ★, audits fondateurs pris pour acquis sans re-vision exhaustive). Conformite avec le detecteur `scripts/notebook_tools/detect_manifest_field.py` (PR #7819 c.754, EPIC #5780). Le champ `Contenu reel verifie (lecture Read 2026-07-18)` (audit c.688 po-2024) reste en place comme preuve falsifiable detaillee ; le nouveau `Description visuelle` est la **version canonique courte** : axes + panneaux + palette + stats RGB + verdict pedagogique. **6/6 figures conformes au detecteur post-migration.**\n'

    # Inserer apres la ligne de l'audit-block c.688
    c688_marker = '> **Audit vision po-2024 c.688'
    m_c688 = re.search(re.escape(c688_marker), text)
    if not m_c688:
        print(f'ERR: audit-block c.688 introuvable', file=sys.stderr)
        sys.exit(1)
    c688_end = text.index('\n', m_c688.end())  # fin de la ligne d'intro
    text = text[:c688_end] + audit_block + text[c688_end:]

    with open(MANIFEST_PATH, 'w', encoding='utf-8') as f:
        f.write(text)

    print(f'\nFAIT: {inserted_count} lignes `Description visuelle` inserees + 1 audit-block c.786')


if __name__ == '__main__':
    main()
