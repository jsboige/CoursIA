# Audio FADING — remédiation et SOTA verdicts (issue #11719)

> **Statut** : référence opérationnelle. Le détecteur FADING est dans
> [`prosody_lab/spectral_envelope.py`](../../MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/spectral_envelope.py)
> (seuil `DECAY_FADING_DB = -2.5`). Issue parente : **#1028** (audiobook
> detection). Issue fille : **#11719** (classe FADING voix B).

## Origine du signal

`breath_verdict = "FADING"` est posé par `spectral_envelope._breath` quand
`decay_db = med(rms_db[last_third]) - med(rms_db[first_third]) <= -2.5 dB`.
Ce n'est **pas** un défaut de monotonie (mélodie) ni de cohérence (timbre) :
c'est une **décroissance d'énergie** sur la durée du sample, audible comme
un narrateur qui « s'essouffle » ou un clone dont la voix perd de la
puissance vers la fin.

Le verdict ne devient **REJECT** que par escalade WINDED :
`decay_db <= -4.0 AND max_run >= 7.0 s`. Tant que la voix reste hachée
par des pauses, elle ne monte pas en WINDED — d'où la classe WARN
informations qui n'est pas un blocage mais un drapeau.

## Mesure de référence (issue #11719, sweep c.371 du 2026-08-19)

| Voix | Verdict gate | decay_db | max_run | n_pauses | Motif |
|------|--------------|----------|---------|----------|-------|
| A | **REJECT / DRONE** | non mesuré (DRONE) | non mesuré | non mesuré | 6.0 notes effectives, 82.2 % motifs répétés |
| **B** | **WARN / FADING** | **-4.54 dB** | < 7 s | 14.9 notes | registre medium, audible 80–100 s |
| L2 | **PASS-TO-EAR** | -1.17 dB (STEADY) | non mesuré | 10.2 notes | registre grave ~109 Hz, 86 syllabes |

L2 retenue pour la présentation user (cf DM ai-01
`msg-20260819T042200-wj8rzp`). B documentée ici comme **classe FADING
distincte de la monotonie** : elle reapparaîtra sur le prochain moteur
TTS évalué et mérite d'être tracée.

## Trois pistes de remédiation

### Piste 1 — modèle TTS (RECOVERABLE-MACHINE probable)

Hypothèse : la décroissance d'énergie est un artefact du modèle XTTS-v2
sur les voix clonées. Sur la mesure, ce moteur a déjà montré deux
problèmes distincts (DRONE voix A + FADING voix B), ce qui suggère
qu'XTTS-v2 n'est pas le bon candidat pour les clones à registre medium.

**SOTA verdict** : RECOVERABLE-MACHINE. Le prochain benchmark (#11624)
doit inclure **Qwen/Qwen3-TTS-12Hz-1.7B-VoiceDesign** et **FishAudio
S2-Pro**. Mesure d'abord : si la voix B re-mesurée sur Qwen-TTS sort
un `decay_db > -2.5`, le FADING était XTTS-v2 spécifique. Si elle
re-sort en FADING, c'est une classe du **dataset** (échantillon de
référence), pas du modèle.

### Piste 2 — qualité du sample de référence (RECOVERABLE-LOCAL)

Hypothèse : le sample de référence utilisé pour cloner la voix B (un
audio ancien, compressé, ou bruité) dégrade la sortie. Un re-sample
propre (44.1 kHz, mono, sans compression) pourrait relancer la voix.

**SOTA verdict** : RECOVERABLE-LOCAL. Régénérer le sample de référence
depuis une source propre, relancer XTTS-v2 sur le même texte, mesurer
le `decay_db`. Si la voix redevient STEADY, le sample était la cause.

Coût : ~5 min de calcul GPU + 2 min de mesure. Faisable sur la machine
de routage du benchmark #11624.

### Piste 3 — tokenisation SSML (INTRINSIC probable)

Hypothèse : la décroissance est en fait une **coupure de phrase** que
le modèle TTS interrompt, puis reprend — la coupure coupe le souffle
du locuteur, et la reprise est plus basse. SSML avec `<break>` aux
mauvais endroits, ou un texte mal segmenté pour le moteur, produit
cet effet.

**SOTA verdict** : INTRINSIC. Trois axes à vérifier avant de trancher :
1. Le jeu de test contient-il une coupure forcée au milieu de la voix
   B ? (axe 1 — `prompt_audio` + `text` du notebook de référence)
2. La voix B a-t-elle un sample unique concaténé, ou un mix ? (axe 2
   — `voice_verdict` consistency)
3. Le benchmark suivant change-t-il de tokenisateur ? (axe 3 — dépen-
   dance de la classe)

Si les trois axes sont « oui, mais mesure confirme » alors INTRINSIC
reste le bon verdict. Si l'un des axes est « non testé », la classe
FADING n'est pas documentée — la documente honnêtement et quitte la
**classe prouvable** à un cycle ultérieur.

## Acceptance (issue #11719) — mapping

| Acceptance | Cible | Couvert par |
|------------|-------|-------------|
| (a) Caractériser la classe FADING vs DRONE | `test_fading_class_distinct_from_drone` | Test unitaire sur le verdict seul |
| (b) Documenter les 3 pistes | Ce document | Sections « Piste 1/2/3 » + SOTA verdicts |
| (c) Si la classe réapparaît sur Qwen-TTS/FishAudio → ajuster le gate | À faire post-benchmark #11624 | Hors scope (réservé) |
| (d) Tracer WARN dans le rapport 8 voix | `test_fading_alone_in_report_no_double_count` | Test anti-double-count |

## Critère de promotion WARN → REJECT

Aujourd'hui : `decay_db <= -4.0 AND max_run >= 7.0 s` (WINDED, donc
REJECT). Si la mesure benchmark #11624 confirme qu'un FADING
systématique (decay_db -3.0 à -4.0, max_run < 7s) **casse** la
présentation user (audible à l'oreille non-entraînée), le seuil
WINDED peut descendre à -3.0. **À mesurer d'abord** sur les 8 voix
candidates — ne pas changer le seuil sans mesure fresh.

## Lien avec le travail en cours

- **#1028** (audiobook) — parente. L2 retenue, B documentée.
- **#11624** (benchmark TTS) — gisement de mesure prochain. Les 3
  voix sont à re-mesurer sur Qwen-TTS et FishAudio S2-Pro.
- **#11656** (chantier outillage) — la classe FADING est un cas
  typique de défaut non détecté par les 3 vérifications absolues
  (execution_count, error, vide). À suivre avec `verdict_sota`.

## Voir aussi

- `scripts/tts_verification/verify_prosody.py` — gate decision
- `MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/spectral_envelope.py` — détecteur
- `audio-embed-pattern.md` — pattern d'embed audio dans les notebooks
