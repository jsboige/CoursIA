# Onset-drop detection — classifier onset/mid/end des spans d'omission

> Cadrage : issue [#19739](https://github.com/jsboige/CoursIA/issues/19739) — `feat(audio,#19692): phase 2 -- garde d'attaque ASR par chunk (onset-drop CV3 mesure, porte #17586 non conforme)`. Lane `myia-po-2027:CoursIA-2`, scope **CPU** (re-roll GPU hors périmètre ; l'extension GPU est la suite logique, à livrer par lane po-2023 ou po-2024 RTX 3090).

## Pourquoi ce module ?

La phase 1 ([PR #19699](https://github.com/jsboige/CoursIA/pull/19699), MERGEDe par lane `myia-po-2023:CoursIA`) a livré l'organe `p7` — vote 2/3 ASR (tiny, large-v3, large-v3-turbo) sur 20 segments échantillonnés de l'audiobook Boule de Suif v4, avec détection de spans ≥ 3 mots omis. Sur la passe 3, **24 spans / 145 mots** sont mesurés. Plusieurs debutent au **mot 0** du segment source : c'est la signature d'un **onset-drop** intrinsèque au moteur CosyVoice3 (cf. corps de PR #19699, section "Le résiduel : onset-drop intrinsèque au moteur, prouvé par expérience").

Le défaut est **graine-dépendant** : seg 57 dit la première proposition sous les graines 4243/4244/4245, et aucune ne la prononce. C'est documenté comme **non corrigeable côté pipeline** — c'est au moteur qu'il faut parler. Phase 2 introduit une garde d'attaque par chunk (ASR turbo sur chaque chunk ≤ 280 c rendu, re-roll ciblé si l'attaque manque). Cette PR ne livre **que** le diagnostic : un classifier déterministe qui prend les spans d'omission déjà mesurés par phase 1 et les range par position (onset_drop, mid_omission, end_drop, spread, none). La garde d'attaque elle-même et son re-roll GPU sont **hors périmètre CPU**.

## Catégorie de défaut : `onset_drop` vs `mid_omission` vs `end_drop` vs `spread`

Le défaut mesuré par phase 1 — "24 spans d'omission" — est **position-agnostique** : p7 détecte les spans sans dire **où** dans le segment ils se trouvent. Or, un onset-drop (premier triplette omise, parole démarre au milieu du texte fourni) n'est **pas le même remède** qu'un mid_omission (un passage du milieu est tombé) ou un end_drop (la queue est coupée). Re-rouler la graine d'un onset-drop est la voie documentée dans le corps de #19699 ; re-rouler un mid_omission est une intervention plus profonde.

Convention de classification (CPU pur, déterministe) :

| Catégorie | Condition | Lecture humaine |
|---|---|---|
| `onset_drop` | `span_start == 0` (et pas SPREAD) | La première proposition est omise. Re-roll ciblé (graine espacée, ASR turbo par chunk). |
| `end_drop` | `span_end >= seg_len` (et pas SPREAD) | La queue du segment est coupée. Probable troncature (cf. PR #19699 cause n°2). |
| `mid_omission` | sinon (et span ≥ 3 mots) | Un passage intermédiaire a disparu. Re-roll souvent inefficace. |
| `spread` | span couvre ≥ 80 % du segment | Catastrophe — le moteur a quasi-rien dit. À investiguer (cache, decoder). |
| `none` | span < 3 mots **ou** seg < 3 mots | Hors signal p7 — pas un span d'omission par convention. |

**Hiérarchie de priorité par span** : `SPREAD > ONSET_DROP > END_DROP > MID_OMISSION > NONE`. Un span qui couvre 90 % du segment **est** un spread (catastrophe), même s'il commence au mot 0. Un span (0, 7) sur 10 mots est onset_drop (70 % < 80, start = 0). Cette hiérarchie est documentée dans le module et testée (`test_classify_span_spread`, `test_classify_records_mixed_spread_dominates`).

**Hiérarchie par record** : un record (un segment) rapporte le verdict le plus haut parmi ses spans — `SPREAD` s'il y a un spread parmi les spans, sinon `ONSET_DROP`, sinon `END_DROP`, sinon le verdict du premier span. Cela reflète l'intuition "un seul spread suffit à dire catastrophe".

## Usage

```bash
# Diagnostic post-mesure p7 (artefact omission_report.json).
python corpus_damage_chunk.py \\
    --omission-report outputs/omission_report.json \\
    --annotated outputs/annotated_v4.json \\
    --out outputs/onset_chunk_report.json
```

Codes de retour :

| Code | Sens |
|---|---|
| 0 | Diagnostic émis, JSON écrit. |
| 2 | Artefact `--omission-report` absent (à signaler en dashboard). |

Sortie `onset_chunk_report.json` (compatible avec le banc de référence [#19695](https://github.com/jsboige/CoursIA/issues/19695)) :

```json
{
  "method": "classification onset/mid/end/spread par position de span ...",
  "n_records": 20,
  "n_classified": 18,
  "counts": {"onset_drop": 3, "mid_omission": 8, "end_drop": 5, "spread": 2, "none": 0},
  "onset_segments": [{"seg_index": 57, "speaker": "narrator",
                      "first_span_words": "chacun guettait l'arrivee",
                      "n_spans": 1, "verdict": "onset_drop"}],
  "end_drop_segments": [...],
  "spread_segments": [...],
  "unclassified": [...]
}
```

Le stdout ajoute un résumé compact : counts + 5 premiers onset_segments (lecture humaine rapide avant d'agir).

## Tests

`tests/test_onset_chunk.py` — **16 tests unitaires, tous verts** (c.1468).

| Test | Vérifie |
|---|---|
| `test_normalize_for_length` | Compte de mots normalisés = convention p7 (NFC, lower, non-alnum → espace). |
| `test_classify_span_onset` | span (0, 3) seg 10 → onset_drop. |
| `test_classify_span_end` | span (7, 10) seg 10 → end_drop. |
| `test_classify_span_mid` | span (3, 6) seg 10 → mid_omission. |
| `test_classify_span_spread` | 8/10 = 80 % → spread ; 7/10 = 70 % → onset_drop (hiérarchie). |
| `test_classify_span_too_short` | span 2 mots → none (invariant p7 min_words=3). |
| `test_classify_seg_too_short` | seg 2 mots → none. |
| `test_classify_span_empty_range` | end ≤ start → none. |
| `test_classify_records_majority` | Verdict par record = hiérarchie SPREAD > ONSET > END > MID. |
| `test_classify_records_mixed_spread_dominates` | Un spread parmi plusieurs spans impose SPREAD. |
| `test_classify_records_unclassified` | seg_index absent de seg_len_map → unclassified. |
| `test_classify_records_onset_segment_listed` | onset_segments populé avec first_span_words. |
| `test_build_seg_word_count_map_missing_file` | Fichier annoté absent → `{}`. |
| `test_build_seg_word_count_map_parses_annotated` | Parsing standard JSON. |
| `test_main_no_omission_report` | omission-report absent → exit 2. |
| `test_smoke_run_end_to_end` | Run complet fixtures → structure JSON conforme. |

Câblage CI : la suite `tests/` de `v4/prosody_lab/` est collectée par `Scripts & Notebook-Tools Tests` (runner `Scripts Tests (CPU)`). Pas de gate CI bloquant propre — voir [#19468 sweep 100 obsolètes 4.2c-k] pour l'opportunit. Le test est **off-CI** pour l'instant (pas de pytest dans `scripts/notebook_tools/`), à intégrer quand la suite v4 pytest sera officialisée.

## Limites et suites

- **Pas d'appel ASR** : ce module **détecte** l'onset-drop dans les artefacts déjà mesurés. La **garde d'attaque par chunk** (ASR turbo sur chaque chunk rendu, re-roll ciblé) est une extension GPU à livrer par une autre lane — cf. issue [#19739](https://github.com/jsboige/CoursIA/issues/19739) pour le périmètre complet.
- **Segments courts (< 3 mots)** : aucun span classifié (`none`). C'est l'invariant p7 — un span ≥ 3 mots nécessite un segment ≥ 3 mots.
- **Mesure E2E absente** : les artefacts `omission_report.json` et `annotated_v4.json` sont produits sur une machine GPU (RTX 3090, po-2024 ou po-2023). Cette PR n'inclut pas de mesure end-to-end faute d'accès GPU ; un cycle ultérieur lancera `p7_verify.py` puis ce classifier sur les 270 segments.
- **Pas de diagnostic cross-cycle** : ce module lit un seul artefact à la fois. La non-régression (cf. issue [#15002](https://github.com/jsboige/CoursIA/issues/15002) critère #3) — un run qui dégrade par rapport au précédent — est portée par le **banc de référence TTS** [#19695](https://github.com/jsboige/CoursIA/issues/19695), pas par ce module.

## Anti-patterns évités

- **Ré-implémenter p7** : refus. Ce module **consomme** l'artefact de p7_verify.py, ne le duplique pas. Cf. [#13564 organ-first implementation](https://github.com/jsboige/CoursIA/issues/13564) — `p7` est l'organe canonique de détection d'omission.
- **Re-render GPU local** : refus (règle F). La mesure GPU est déléguée à une lane capable, jamais un workaround dégradé en local.
- **Hand-edit de sortie** : refus (règle 6 secrets-hygiene). Le diagnostic est produit par le code, jamais maquillé.

## Pointeurs

- Module : [`corpus_damage_chunk.py`](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/corpus_damage_chunk.py)
- Tests : [`tests/test_onset_chunk.py`](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/tests/test_onset_chunk.py)
- Phase 1 : [PR #19699](https://github.com/jsboige/CoursIA/pull/19699) — organe p7 (MERGEDe)
- EPIC parent : [#19692](https://github.com/jsboige/CoursIA/issues/19692)
- Banc de référence : [#19695](https://github.com/jsboige/CoursIA/issues/19695) — `bake_bank` schema v1
- Issue : [#19739](https://github.com/jsboige/CoursIA/issues/19739)
- Cadrage coordinateur : DM ai-01 11:09Z 07/10 (file audio post-#19820)
- `corpus_damage.py` (phase 1) : [PR #19699](https://github.com/jsboige/CoursIA/pull/19699) — instrument de mesure plancher 40 car/s

— daté 2026-10-08, lane `myia-po-2027:CoursIA-2`, cycle c.1468