# Vision Comparison — Slide 1 Cover: Slidev (A) vs PPTX (B)

**Date**: 2026-04-19
**Deck**: 03-logique (EPITA IA — Bases de connaissances et Logique)
**Method**: Direct visual analysis (multimodal LLM, both images read simultaneously)

---

## Comparison by Criterion

### 1. Layout / Structure

| | Slidev (A) | PPTX (B) |
|---|---|---|
| Division | Two zones: large white top half (title), grey bottom half (content) | Single unified white slide with centred content |
| Separator | Visible dashed horizontal line + circle "1" page number in the middle | Solid dark-red horizontal rule under the title |
| Navigation element | Page number circle "1" interrupts the visual flow | None — clean |

**Winner: B (PPTX)**. The dashed-line separator and the "1" bubble are artefacts of Slidev's default theme that break the professional cover aesthetic. PPTX has a single clean rule.

---

### 2. Titre

| | Slidev (A) | PPTX (B) |
|---|---|---|
| Text | "Bases de connaissance et Logique" (two lines, wrapped, centred) | "Bases de connaissances et Logique" (single line, left-aligned) |
| Spelling | **"connaissance" (singular) — TYPO** | "connaissances" (plural) — correct |
| Font size | Very large (~80–90pt equivalent) | Large (~48pt equivalent) — more proportionate |
| Weight | Regular | Regular |
| Colour | Salmon/orange-red | Deep dark red (bordeaux) |

**Winner: B (PPTX)**. PPTX has correct spelling, better colour (authoritative dark red vs. garish salmon), and does not wrap awkwardly. Slidev introduces a **spelling error** not present in the PPTX.

---

### 3. Sous-titres / Hiérarchie

| | Slidev (A) | PPTX (B) |
|---|---|---|
| "Intelligence Artificielle – III" | ALL CAPS, spaced, grey, small — treated as a label | ALL CAPS, spaced, dark, clearly readable |
| "Logique propositionnelle" | Listed as a bullet point (same level as others) | **Bold, larger, highlighted in orange-red** — visually prominent first topic |
| Bullet list items | Three items at same visual weight; "Planification" is indented under LPO | Three items with clear hierarchy: LPO prominent, LPO→Planification indented, Représentation below |
| Colour differentiation | All bullets in same grey-blue | LPO is highlighted (orange-red), others in dark grey |

**Winner: B (PPTX)**. PPTX communicates that "Logique propositionnelle" is the primary topic of *this* session via colour emphasis. Slidev flattens all bullets to the same weight.

---

### 4. Couleurs / Fond

| | Slidev (A) | PPTX (B) |
|---|---|---|
| Background top | White | White |
| Background bottom | Medium grey (#b0b8c0 approx.) | Light grey gradient (very subtle, nearly white) |
| Overall palette | 2-zone bicolour — feels like unfinished template | Unified near-white with soft gradient — professional |
| Accent colour | Salmon/coral for title | Dark bordeaux for title, orange-red for emphasis |

**Winner: B (PPTX)**. The grey panel in Slidev is a heavy visual element that dominates the lower half and makes the slide feel like a demo template, not a finished academic deck.

---

### 5. Équilibre

| | Slidev (A) | PPTX (B) |
|---|---|---|
| Vertical distribution | Title takes ~40% of height; separator + number are visible; content is in a grey box ~50% | Title at ~30% height; separator rule; content floats in open white space ~55% |
| White space | Very little — title is oversized, grey panel is dense | Generous — content breathes |
| Bottom whitespace | Minimal | Large bottom margin, "IA 101" footer in bottom-left corner is subtle |

**Winner: B (PPTX)**. Better breathing room, no intrusive grey panel, clean footer.

---

### 6. Lisibilité (projection amphithéâtre)

| | Slidev (A) | PPTX (B) |
|---|---|---|
| Title legibility | Good (large) but colour contrast is slightly low (salmon on white) | Excellent (dark red on white, high contrast) |
| Bullet legibility | Moderate (grey on grey background — contrast risk) | Good (dark grey on very light background) |
| Estimated note | **6/10** | **8/10** |

**Winner: B (PPTX)**. Grey text on grey background (Slidev) will wash out on a projector. PPTX dark text on near-white is projector-safe.

---

### 7. Typographie

| | Slidev (A) | PPTX (B) |
|---|---|---|
| Title font | Serif, very large | Serif, large but controlled |
| Body font | Sans-serif, spaced | Serif, classic academic |
| Consistency | Mismatch: serif title + sans body | Consistent serif throughout |
| Diacritics | "Representation" (missing accents in some bullets) | "Représentation des connaissances" (correct) |

**Winner: B (PPTX)**. Consistent serif, correct French diacritics, no font mismatch.

---

## Verdict Final

**B (PPTX) is better across all 7 criteria.**

---

## Top 3 Changements Concrets à Appliquer à Slidev

### 1. CRITIQUE — Corriger la faute d'orthographe dans le titre
- **Actuel**: "Bases de connaissance et Logique"
- **Correct**: "Bases de connaissances et Logique"
- Livrer un deck avec une faute dans le titre de couverture est une erreur visible immédiatement par les étudiants.

### 2. CRITIQUE — Supprimer le panneau gris et le numéro de page en séparateur
- Le grey panel `background: #b0b8c0` dans la zone inférieure doit être remplacé par un fond blanc/très clair.
- Le cercle "1" positionné sur la ligne de séparation doit être déplacé ou supprimé du layout de couverture.
- Ce sont des artefacts du thème par défaut Slidev — ils doivent être overridés dans le CSS du thème.

### 3. IMPORTANT — Remettre l'emphase couleur sur "Logique propositionnelle"
- Dans PPTX, "Logique propositionnelle" est en orange-rouge bold, plus grand, signalant que c'est le thème du jour.
- Dans Slidev, c'est un simple bullet de même poids que les autres.
- Solution Slidev: utiliser `**Logique propositionnelle**` avec une règle CSS `.slidev-layout li strong { color: #c0392b; font-size: 1.15em; }` ou équivalent.

### 4. (Bonus) Couleur du titre: salmon → bordeaux
- `#c0392b` ou `#7b1a1a` correspond mieux au dark red professionnel du PPTX.
- Le salmon/coral actuel a un contraste plus faible sur fond blanc et paraît moins académique.

---

## Niveau de Confiance

**Confiance: HAUTE (9/10)**

Les deux images ont été lues directement par analyse visuelle multimodale. Les différences identifiées sont objectives et visuellement vérifiables:
- La faute d'orthographe dans le titre Slidev est **factuelle** (lettre s manquante).
- Le panneau gris est **visible** et mesurable.
- La hiérarchie des bullets est **directement comparable**.
- Le numéro de page au centre est **un artefact de thème connu**.

La seule incertitude est la valeur exacte des codes couleur (estimés visuellement), mais les corrections de direction (plus foncé, plus de contraste) sont fiables.

---

## Notes sur le Workflow sk-agent

Le MCP `sk-agent` n'est pas configuré dans `.mcp.json` du projet CoursIA ni dans `~/.claude.json`.
L'analyse a été réalisée directement via les capacités vision multimodales du modèle Claude (claude-sonnet-4-6).
Pour scaler sur ~200 slides avec des sous-agents haiku, il faudra soit:
- Ajouter la config sk-agent dans `.mcp.json`, soit
- Utiliser la capacité vision native de Claude Code avec des sous-agents `haiku` via le SDK agents.
