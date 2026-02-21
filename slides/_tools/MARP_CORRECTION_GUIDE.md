# Marp Correction Guide

Reference guide for correcting and improving Marp slides converted from PPTX.
Based on visual comparison of deck 01-introduction (PPTX originals vs Marp renders).

---

## 1. Layout Patterns That Work Well

### 1.1 `![bg right:X%]` / `![bg left:X%]` -- Single Image Positioning

**Status**: Works correctly. Use consistently.

```markdown
# Slide Title

- Bullet point content
- More content here

![bg right:35%](images/img_001.jpg)
```

**Notes**:
- Percentages 30-40% work best for text-heavy slides
- The image fills the right/left portion and scales proportionally
- Verified on Marp slide 3 "Sommaire" -- image renders exactly as intended

### 1.2 Markdown Tables

**Status**: Works correctly. Tables render clean and readable.

```markdown
| Column A | Column B | Column C |
|----------|----------|----------|
| Data 1   | Data 2   | Data 3   |
```

**Notes**:
- Verified on Marp slide 29 "PEAS table" -- content matches PPTX original
- Tables scale to fit the available width
- For wide tables (5+ columns), consider reducing font size or splitting

### 1.3 `columns-layout` with Text + Images

**Status**: Works correctly when HTML structure is valid.

```markdown
<!-- _class: columns-layout -->

# Title

<div class="columns">
<div class="col-left">

- Text content here
- More bullets

</div>
<div class="col-right">

![Image description](images/img_XXX.png)

</div>
</div>
```

**Critical**: Blank lines MUST surround the markdown content inside `<div>` tags,
otherwise Marp treats it as raw HTML and doesn't parse markdown.

**Verified**: Marp slide 33 "Agent reflexe" -- text left, diagrams right, renders well.

---

## 2. Known Problems and Fixes

### 2.1 img-grid Overflow

**Problem**: Logo/image grids overflow the slide bottom, overlapping with the footer.

**Example**: Marp slide 17 "Qui fait de l'IA?" -- 12+ logos in a grid, bottom row clips.

**Cause**: The `img-grid` CSS class doesn't enforce maximum height per item,
and too many items push content below the slide boundary.

**Fix options**:
1. **Reduce items**: Show fewer logos per slide, split into 2 slides if needed
2. **Constrain sizes**: Add inline `style="max-height:50px"` to img tags
3. **Use img-grid-3 or img-grid-2x2**: Smaller grid variants from ia101.css

```markdown
<!-- BEFORE (overflows) -->
<div class="img-grid">
<img src="images/logo1.png" alt="Logo1">
<img src="images/logo2.png" alt="Logo2">
<!-- ... 10+ images ... -->
</div>

<!-- AFTER (constrained) -->
<div class="img-grid">
<img src="images/logo1.png" alt="Logo1" style="max-height:55px; max-width:90px; object-fit:contain;">
<img src="images/logo2.png" alt="Logo2" style="max-height:55px; max-width:90px; object-fit:contain;">
<!-- ... fewer images, or split into 2 slides ... -->
</div>
```

### 2.2 Diagram-to-Text Degradation

**Problem**: Complex PPTX diagrams (SmartArt trees, flowcharts, hierarchies) were
converted to flat bulleted text lists, losing significant visual impact.

**Example**: PPTX slide 28 "Intelligence de la pensee logique" had a beautiful
hierarchical tree (Type -> Inference -> Modeles -> Apprentissage -> Agents) with
colored boxes. Marp slide 27 "Intelligences" has a flat text list with thumbnails.

**Cause**: pptx_to_marp.py cannot reproduce SmartArt/diagram objects.

**Fix options** (in order of preference):
1. **Extract diagram as image**: If the PPTX diagram is in `extracted/images/`,
   use it directly as `![bg right:50%](images/extracted_diagram.png)`
2. **Recreate with HTML table**: For simple hierarchies, use styled HTML
3. **Accept text version**: For complex diagrams, keep the text but improve formatting
4. **Create new diagram**: Use an external tool (draw.io, Mermaid) and save as PNG

### 2.3 Footer/Content Overlap

**Problem**: Content at the bottom of dense slides overlaps the Marp footer area.

**Examples**: Marp slide 17 (logos), Marp slide 33 (Wolfram book at bottom).

**Fix**:
- Reduce content density (split into 2 slides if >8 bullet points or >150 words)
- Move bottom-of-slide images to `![bg right]` or `![bg left]` instead
- Add `<br>` spacing before footer-adjacent content

### 2.4 Section Header Slides

**Problem**: PPTX section headers had full-width colored backgrounds with
sommaire/navigation showing the current position in the course outline.
Marp section slides are minimal.

**Example**: PPTX slide 21 "Systemes d'agents" shows the full course outline
with grayed-out previous sections and highlighted current section.
Marp slide 24 "Systemes d'agents" is just a title.

**Fix**: Optionally add a mini-sommaire under the section title:

```markdown
<!-- _class: section -->

# Systemes d'agents

- ~~Introduction~~
- ~~Qu'est-ce que l'IA?~~
- **Systemes d'agents** -- *vous etes ici*
- Types d'agents
```

### 2.5 Title Slides (Cosmetic)

**Problem**: PPTX title slides had decorative gradients, card designs, visual effects.
Marp `_class: title` produces a clean but simpler centered layout.

**Status**: Acceptable trade-off. The ia101.css theme provides a professional look
with the dark red accent. No action required unless specific visual impact is desired.

### 2.6 Slide Numbering Drift

**Problem**: PPTX and Marp have different slide counts (e.g., 43 vs 42 for deck 01).
Slides don't align by position number.

**Cause**: Marp conversion split or merged some slides differently.

**Impact**: Cannot do automated positional comparison.
Must match slides by title/content for PPTX vs Marp comparison.

**For automated tools**: Use title extraction (grep `^# ` in slides.md) and
compare against PPTX content.md titles for mapping.

---

## 3. Content Enrichment Rules

### 3.1 Text Improvement

- **Reformulate telegraphic fragments** into short, fluent sentences
- **Develop cryptic points**: add examples, context, explanations
- **Preserve all original meaning** -- enrich, never impoverish
- **Update dated content**: add recent examples (GPT-4/5, Claude, DeepSeek, etc.)

### 3.2 Slide Density

- **Split slides with >8 bullet points or >150 words** into 2-3 slides
- **Keep the "one idea per slide" principle** when possible
- Splitting is better than cramming

### 3.3 TODO Resolution

For each `<!-- TODO: ... -->` comment in slides.md:
1. **If an image exists** in `images/` or `extracted/images/` that matches: add it
2. **If a free-use image can be found**: download, save to `images/`, reference it
3. **If neither**: remove the TODO comment (don't leave orphan comments)

### 3.4 Cross-References

Add references to relevant notebooks where appropriate:
```markdown
> **Notebook associe:** `MyIA.AI.Notebooks/Search/` -- Resolution de problemes
```

---

## 4. CSS Classes Reference (ia101.css)

| Class | Usage | Notes |
|-------|-------|-------|
| `title` | First/last slide | Centered, large title, dark background |
| `section` | Section dividers | Accent color header |
| `questions` | Q&A slides | Centered "Questions?" |
| `columns-layout` | Two-column HTML | Requires `<div class="columns">` |
| `dense` | Compact slides | Smaller font, tighter spacing |
| `crossref` | Reference slides | For "pour aller plus loin" |
| `img-grid` | Image grid | Flexbox, auto-wrapping |
| `img-grid-2x2` | 2x2 image grid | Fixed 2-column layout |
| `img-grid-3` | 3-column grid | Three equal columns |
| `image-row` | Horizontal images | Inline row layout |
| `framed` | Bordered content | Adds border around content |

---

## 5. Quality Checklist (per deck)

Before committing a corrected deck, verify:

- [ ] All `images/img_XXX` references resolve to existing files
- [ ] No `<!-- TODO: -->` comments remain (resolved or removed)
- [ ] No slides exceed 8 bullet points or ~150 words
- [ ] `columns-layout` divs have blank lines around markdown content
- [ ] `img-grid` items have size constraints (no overflow)
- [ ] Tables are readable (not too many columns for slide width)
- [ ] Section headers include position context if relevant
- [ ] Marp renders without errors (`marp slides.md --html -o test.html`)
- [ ] Content matches PPTX original intent (no accidental deletions)

---

## 6. sk-agent Vision Prompts (calibrated)

Use these prompts when sending slide PNGs to sk-agent for automated verification:

### Layout verification
```
"Analyze this slide image. Is the text readable and well-formatted?
Are images properly positioned and not overlapping the footer or header?
Is there any content that appears cut off or misaligned?"
```

### PPTX vs Marp comparison
```
"Compare these two slide renders. The first is the PPTX original, the second
is the Marp conversion. Report: (1) Is the content identical? (2) Are images
in the same relative position? (3) What layout differences do you see?
(4) Is the Marp version readable for classroom projection?"
```

### Content density check
```
"How many bullet points are on this slide? Is the text density appropriate
for a classroom presentation, or does it feel cramped? Would you recommend
splitting this into multiple slides?"
```

---

## 7. Marp CLI Commands

```bash
# Render single deck to PNG (2x resolution)
marp slides/XX-name/slides.md --images png --image-scale 2 --html \
  --allow-local-files --theme-set slides/themes/ia101.css \
  -o slides/XX-name/output/marp_renders/slide.png

# Render to HTML (fastest, no Puppeteer dependency)
marp slides/XX-name/slides.md --html \
  --allow-local-files --theme-set slides/themes/ia101.css \
  -o slides/XX-name/output/slides.html

# Check image references
python slides/_tools/slide_tools.py check-refs slides/XX-name

# Compare slide counts PPTX vs Marp
python slides/_tools/slide_tools.py compare slides/XX-name
```

**Known issue**: marp-cli PNG/PDF export crashes with `TargetCloseError` on
some Windows systems (Puppeteer/Chrome incompatibility with Node.js v24+).
Workaround: run via PowerShell `mcp__win-cli__execute_command`, or use
HTML export and screenshot.
