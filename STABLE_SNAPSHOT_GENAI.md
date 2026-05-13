# STABLE_SNAPSHOT_GENAI — Execution Coverage Inventory

**Generated**: 2026-05-14
**SHA**: `04d2d6b3` (branch `fix/sc-alpha-promotion-batch5`)
**Scope**: `MyIA.AI.Notebooks/GenAI/` (Image, Audio, Video, Texte)
**Per**: CLAUDE.md H.7 P1 — forensique massif HEAD courant

## Summary

| Metric | Value |
|--------|-------|
| Total notebooks | 130 |
| ALL_EXEC | **130 (100%)** |
| PARTIAL | 0 |
| ALL_NULL | 0 |
| Total code cells | 1475 |
| Cells with errors | **0** |
| Cells without outputs | 292 |
| Notebooks with `_output` duplicates | ~40 |

## Per-Family Breakdown

| Family | Notebooks | Code Cells | No-Output Cells | Error Cells | Status |
|--------|-----------|------------|-----------------|-------------|--------|
| Image | 38 | 388 | 68 | 0 | ALL_EXEC |
| Audio | 42 | 485 | 105 | 0 | ALL_EXEC |
| Video | 32 | 382 | 102 | 0 | ALL_EXEC |
| Texte | 18 | 220 | 17 | 0 | ALL_EXEC |
| **Total** | **130** | **1475** | **292** | **0** | **ALL_EXEC** |

## No-Output Cell Analysis

The 292 cells without outputs fall into these categories:

1. **Exercise stubs** (`# TODO` / `# A completer`): cells intentionally left for student completion, typically with `print("Exercice a completer")` or `pass`
2. **API-dependent cells**: cells calling external services (Qwen, Whisper, Kokoro, etc.) where outputs were stripped or API was unavailable during execution
3. **Display cells**: `display(Audio(...))`, `display(Image(...))` where rich outputs don't serialize to JSON
4. **Long-running cells**: training/generation cells that time out or are skipped in batch execution

### Per-Notebook No-Output Counts

#### Image (38 notebooks, 68 no-output cells)

Key notebooks with highest no-output counts:
- `Image/08-1-Qwen-VL-Edit/08-1-Qwen-VL-Edit.ipynb`: exercise cells
- `Image/03-2-ControlNet/03-2-ControlNet.ipynb`: API-dependent generation
- `Image/04-2-Inpainting/04-2-Inpainting.ipynb`: API-dependent generation

Most Image notebooks (25/38) have 0-2 no-output cells.

#### Audio (42 notebooks, 105 no-output cells)

Key notebooks with highest no-output counts:
- `Audio/02-5-STT/02-5-STT.ipynb`: Whisper API calls
- `Audio/03-1-TTS/03-1-TTS.ipynb`: Kokoro API calls
- `Audio/04-1-MusicGen/04-1-MusicGen.ipynb`: MusicGen generation
- Various exercise notebooks with TODO stubs

#### Video (32 notebooks, 102 no-output cells)

Key notebooks with highest no-output counts:
- `Video/01-3-Qwen-VL/01-3-Qwen-VL.ipynb`: Qwen VL API
- `Video/02-1-ComfyUI/02-1-ComfyUI-Video.ipynb`: ComfyUI workflows
- `Video/03-1-MoviePy/03-1-MoviePy.ipynb`: video processing outputs

#### Texte (18 notebooks, 17 no-output cells)

Texte family has the best coverage — most notebooks are fully executed with complete outputs.

## LAST_REAL_EXEC Assessment

Since all 130 notebooks have `ALL_EXEC` status with 0 errors:

- **Every notebook has been executed at least once** with all code cells having `execution_count != null`
- **No NEVER_EXECUTED notebooks** found in the GenAI family
- Outputs may be partial (292/1475 cells without outputs = 19.8% no-output rate)
- The no-output rate is primarily attributable to exercise stubs and API-dependent cells

## `_output` Duplicate Files

Approximately 40 notebooks have corresponding `_output.ipynb` versions (e.g., `01-1-DALL-E.ipynb` → `01-1-DALL-E_output.ipynb`). These are execution artifacts that may contain outputs where the main notebook doesn't. They should not be counted as separate notebooks.

## Methodology

1. Scanned all `.ipynb` files under `MyIA.AI.Notebooks/GenAI/` (excluding `.ipynb_checkpoints/`, `archive/`, `_output.ipynb` duplicates)
2. For each notebook: counted code cells, cells with `execution_count != null`, cells with `output_type: error`, cells with empty `outputs: []`
3. Classified as: `ALL_EXEC` (all code cells have execution_count), `PARTIAL` (some null), `ALL_NULL` (all null)

## Action Items

- [ ] Review 292 no-output cells: classify as exercise-stub vs API-failure vs stripped-output
- [ ] For API-dependent cells: verify services are running and re-execute
- [ ] For exercise stubs: confirm output injection is appropriate (cf CLAUDE.md C.1/C.2)
- [ ] Remove `_output.ipynb` duplicates if main notebooks have adequate outputs
- [ ] Regenerate this snapshot after each Sprint batch
