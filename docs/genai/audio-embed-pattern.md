# GenAI Audio — pattern d'embed audio + leçons de réparation

Consolide les leçons durables de l'audio-roll (#4520 MusicGen, #4522 Demucs, #4540 MIDI, #4549 Dia, #4550 TTS-Gateway) sur la stack GenAI Audio self-hostée. Destiné à tout worker abordant un notebook `GenAI/Audio/*.ipynb` en défaut C.2 (committé sans embeds → l'étudiant n'entend rien).

Voir aussi [genai-services.md](genai-services.md) (inventaire services Docker), [CLAUDE.md](../../CLAUDE.md) règles C.2/C.3/F, [.claude/rules/sota-not-workaround.md](../../.claude/rules/sota-not-workaround.md) (taxonomy 5-verdicts).

## Décision (b) — embed ~3s, audio complet sur disque

Un notebook de génération audio produit typiquement des clips de 10–30 s. Embarquer la totalité en base64 dans `display(Audio(...))` gonfle le notebook (stéréo 44.1 kHz × plusieurs clips = 5–17 MB/notebook). Convention adoptée :

```python
# Garde l'audio COMPLET sur disque (gitignored : MyIA.AI.Notebooks/GenAI/outputs/*)
sf.write(str(OUTPUT_DIR / f"{name}.wav"), audio_full, sr)
# Embarque seulement un APERÇU ~3s dans le notebook
preview = audio_full[:sr * 3]          # samples-axis — voir § axis-inverse ci-dessous
display(Audio(data=preview, rate=sr))
```

Justification pédagogique : 3 s suffisent à entendre la qualité/distinction d'une voix ou d'un stem ; le notebook reste léger ; l'audio complet reste reproductible sur disque. Vérifier TOUJOURS la durée réelle en décodant l'embed (`wave.open(io.BytesIO(base64.b64decode(b64)))` → `nframes/framerate`) — ne pas truster le slice source.

## Leçon 1 — axis-inverse du trim (samples vs channels)

**La forme du tableau audio détermine l'axe de temps — toujours vérifier avant de trimmer.**

| Source audio | Shape | Trim ~3s correct |
|--------------|-------|------------------|
| torchaudio, Demucs, la plupart des libs | `(channels, samples)` ex. `(2, N)` | `audio[..., :sr*3]` (ellipsis dernière axe) |
| FluidSynth (synthèse MIDI), certains codecs | `(samples, channels)` ex. `(N, 2)` | `audio[:sr*3]` (axe 0 = temps) |
| Dia / sortie 1-D mono | `(samples,)` | `audio[:sr*3]` |

`arr[:sr*3]` sur une shape `(channels, samples)` prend TOUT (axe 0 = 2 canaux) → clip de 10 s au lieu de 3 s (21 MB). `arr[..., :sr*3]` marche pour `(ch,samp)` ET `(samp,)`. **Décodez un embed pour confirmer la durée réelle** avant de committer. (Incidents : Demucs c.65 axis-bug 10 s, MIDI c.67 inverse.)

## Leçon 2 — API-GHOST : vérifier le vrai import path

Les notebooks anciens héritent souvent d'APIs **imaginées** qui n'ont jamais existé. Exemple Dia (02-8) : la cellule appelait `from dia import DiaTTS` + `DiaTTS(device=device)` — mais `dia/__init__.py` est **vide** et aucune classe `DiaTTS` n'existe dans aucun release. La vraie API : `from dia.model import Dia` + `Dia.from_pretrained(...)`.

**Avant de committer une cellule de model-load** : lire le `__init__.py` du package (souvent vide) + la signature réelle dans le source (`model.py` / `pyproject.toml` sur github), puis un **smoke test standalone** (5 min, hors notebook) qui importe + charge + génère 1 clip. Le smoke attrape l'API-GHOST, le mauvais sample-rate, et le pin torch conflictuel avant d'investir dans une papermill complète.

## Leçon 3 — sample rate du codec DAC (jamais hardcoder)

Les modèles qui décodent via le codec **Descript Audio Codec** (DAC) — Dia, variants MusicGen — sortent au rate natif du codec, pas un rate « standard ». Dia : `DEFAULT_SAMPLE_RATE = 44100` (`SAMPLE_RATE_RATIO = 512` dans `dia/model.py`). Hardcoder `sr = 24000` (erreur Dia 02-8) fait jouer l'audio à mauvaise vitesse/pitch.

**Lire `DEFAULT_SAMPLE_RATE` / config codec, jamais hardcoder un sample rate.** Vérifier en décodant l'embed : `framerate` du WAV = le vrai rate.

## Leçon 4 — path-leak root-fix = `relative_to(GENAI_ROOT)`

Les notebooks impriment souvent `print(f"Sortie : {OUTPUT_DIR}")` où `OUTPUT_DIR = GENAI_ROOT / 'outputs' / ...` → leak du chemin absolu de checkout/worktree (`D:\Dev\CoursIA\.claude\worktrees\...`). Le scrubber `scripts/notebook_tools/scrub_papermill_paths.py --outputs` anonymise en `<repo>.claude\worktrees\...` (moche, révèle la structure worktree, doit être re-scrubbé à chaque ré-exec).

**Root-fix durable** : `print(f"Sortie : {OUTPUT_DIR.relative_to(GENAI_ROOT)}")` → `outputs/audio/midi` propre, **0 leak quelle que soit la checkout path, no scrub needed**. Comme `OUTPUT_DIR` est toujours `GENAI_ROOT`-dérivé, `relative_to(GENAI_ROOT)` est toujours safe. À appliquer à tous les prints de chemins dérivés (`OUTPUT_DIR`, `MIDI_MODEL_DIR`, `env_path`, etc.).

**Warnings biblio sur stderr** (tqdm `IProgress not found`, torch `weight_norm` FutureWarning) émettent aussi le chemin absolu de l'env conda (`C:\Users\...\envs\...\site-packages`). Fix = `warnings.filterwarnings("ignore", ...)` à la source (cellule setup), pas un scrub output. Cf [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) règle 6 (Stop & Repair : cause A env → fix source + re-exec).

## Venv dédié pour pin torch conflictuel

Quand un modèle pin un `torch==X.Y` exact qui diffère du kernel partagé, **ne pas casser le kernel existant** — build un venv conda dédié + kernel dédié. Exemple Dia : `torch==2.6.0` conflit avec `mcp-jupyter-py310` (torch 2.1.0 pour MusicGen/MIDI/Demucs) → env dédié `dia-tts` + kernel `dia-tts`. Préserve les notebooks audio déjà fixés.

## Vérification canonique d'un notebook audio réparé

Script réutilisable (`scratchpad`-style, adapter le path) :
1. `execution_count` séquentiel 1..N sur toutes les cells code (0 `None`).
2. 0 erreur (`output_type == "error"`).
3. Compter les embeds : `data.text/html` contenant `<audio` + `src="data:audio/..."`.
4. Décoder chaque embed (`wave.open` sur le base64) : confirmer magic `RIFF...WAVE`, `framerate`, `nchannels`, durée ≈ 3 s.
5. 0 path-leak (scan `C:\Users` / `D:\Dev` / `/home/` / `.conda` dans `outputs[].text`).
6. 0 C.1 (`raise NotImplementedError` / `assert False` / `1/0` dans le source).

## État de l'audio-roll (2026-06-28)

5/5 défauts **local-résolvables** livrés. Résiduels = tous non-local :
- **02-7 YuE** → RECOVERABLE-MACHINE (flash-attn = no Windows wheels → Linux).
- **02-9 AceStep** → RECOVERABLE-USER-HAND (HF `ACE-Step/ACE-Step` RepositoryNotFound même avec token valide).
- **02-8 Fish S2 Pro** → RECOVERABLE-USER-HAND (`FISH_AUDIO_API_KEY` gitignored).
- **02-2 XTTS** → DEFERRED (Coqui archived, py ≤ 3.11 + GPU).

Quand un résiduel devient local-débloqué (clé provisionnée, repo HF restauré, machine Linux dispo), ré-appliquer ce pattern.
