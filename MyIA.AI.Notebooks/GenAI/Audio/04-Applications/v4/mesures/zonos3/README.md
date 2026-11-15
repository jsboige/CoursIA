# ZONOS3-Mini — mesure du banc TTS #19695 sur `extract_C`

**Issue** : [#25835](https://github.com/jsboige/CoursIA/issues/25835) (tranche 2 — **mesure seule**)
**Banc de reference** : [#19695](https://github.com/jsboige/CoursIA/issues/19695) — schema `prosody_lab/bank_schema_v1.json`
**Lane** : `myia-ai-01:CoursIA-2` · **Graine** : 42 · **Backend** : runtime natif **ggml (C++/CUDA)**, pas le serveur SGLang

Ce dossier porte la **mesure** du moteur ZONOS3-Mini sur l'extrait de reference `C`
(narration longue, 1 650 caracteres). Les WAV restent **hors depot** (GDrive) ; le depot ne
porte que le JSON de mesure, le pilote de mesure, l'entree de banc et le controle de rejeu.

---

## 1. Ce qui est mesure

| Grandeur | Instrument | Fichier |
|---|---|---|
| Rendu, decoupe, RTF, VRAM, provenance des poids | `zonos3_measure.py` (pilote) | `zonos3-mini-a0c-metrics.json` |
| WER normalise, omissions votees, prosodie | `prosody_lab/a0c_rerun/measure_3asr.py` | `zonos3-mini-a0c-metrics.json` (champs `wer`, `omissions`, `prosody`) |
| Entree de banc (schema v1) | `build_bank_entry.py` | `bank_entry.json` |
| Rejeu a graine fixee | `zonos3_replay.py` | `replay-determinisme.json` |
| Prosodie (rapport complet) | `scripts/tts_verification/verify_prosody.py --single` | `prosody-verdict.json` |
| Densite de silence des deux rendus | `zonos3_silence.py` | `silence-comparaison.json` |

## 2. Protocole — identique au rendu de reference

Le comparateur est le rendu **Zonos v0.1** du meme extrait (`A0-review-20261006/A0C-zonos-chunked-metrics.json`).
La comparabilite n'est pas supposee, elle est **construite** :

- **meme texte** : `extract_C_long_narration.txt`, sha256 `a2cab722b97d2378838e9ca04a246425b168da36e264cce7c2903ce7277bc5bd`
  (1 650 octets, identique au fichier GDrive de la suite A0C — verifie par hachage, pas par nom) ;
- **meme decoupe** : fin de phrase (`[.!?]` + espace), repli a une frontiere de proposition
  (`, ; :`) quand une phrase depasse 280 caracteres, regroupement glouton d'unites entieres,
  **une phrase trop longue formant un groupe autonome** (ses propositions ne rejoignent jamais
  le groupe precedent), pause de 0,25 s entre morceaux, jamais de troncature de phrase ;
- **meme partition** : 8 morceaux de **149 / 138 / 162 / 266 / 231 / 189 / 266 / 241** caracteres,
  identique caractere pour caractere au rendu de reference ;
- **meme jeu d'ASR** : `tiny`, `small`, `large-v3` (l'enumeration du schema v1) — le JSON de
  mesure porte en plus `large-v3-turbo`, votant de la suite A0C de reference, **hors enum du
  schema v1** : il est mesure et publie, il n'entre pas dans l'entree de banc ;
- **meme mesure de prosodie** : `scripts/tts_verification/verify_prosody.py --single`.

La regle de decoupe a ete **corrigee** en cours de route : la premiere version laissait les
propositions d'une phrase trop longue rejoindre le morceau precedent, ce qui produisait une
partition differente de celle de la reference (265/277/117 au lieu de 266/231). La regle
« groupe autonome » est celle du rendu de reference ; elle est portee par le pilote livre ici.

## 3. Resultats

Mesure unique : un extrait, une graine, un rendu par moteur. Le comparateur est le rendu
**Zonos v0.1** du meme extrait, obtenu dans les conditions de la suite A0C (repertoire
`A0-review-20261006`).

| Grandeur | ZONOS3-Mini (ici) | Zonos v0.1 (reference) |
|---|---|---|
| Backend | runtime natif **ggml (C++/CUDA)**, GPU 2 | SGLang / Python |
| Morceaux | 8 (149 / 138 / 162 / 266 / 231 / 189 / 266 / 241 car.) | 8 (**meme partition**) |
| Duree du rendu | **146,75 s** | 88,384 s |
| RTF global (wallclock / duree) | **0,415** | 4,775 |
| VRAM pic | **1 713 Mo** | 4 125 Mo |
| WER `tiny` / `small` / `large-v3` | 29,96 % / 17,60 % / **6,37 %** | — (run #14059 : 0,097, protocole anterieur) |
| Omissions (>= 3 mots, vote >= 2 ASR sur 3) | **0** | 11 segments |
| Prosodie — verdict de melodie | **DRONE** | EXPRESSIVE (12,85 st d'amplitude) |
| Prosodie — mouvement | **1,03 st/syll** | 2,83 st/syll |
| Prosodie — gate | **REJECT** (MONOTONE + FADING) | WARN (ERRATIC + FADING) |
| Prosodie — voix | CONSISTENT | CONSISTENT |
| Silences internes (>= 0,3 s, sous -45 dBFS) | 36,29 s en 60 pauses (24,7 % du rendu) | 13,12 s en 23 pauses (14,8 %) |
| Debit de lecture (car. / s de signal) | 14,87 | 21,82 |
| Rejeu a graine 42 | **bit-identique** | — |

### Lecture

- **Intelligibilite** : le WER `large-v3` de **6,37 %** est sous le seuil de 0,15 du gate
  pre-UAT (#17586) et **aucune omission** n'est votee — ou Zonos v0.1 en laissait 11.
- **Cout** : **11,5x plus rapide** que le temps reel et **2,4x moins de VRAM** que le rendu
  de reference, sur le meme extrait et le meme materiel de comparaison.
- **Prosodie : c'est le point faible.** Le gate de prosodie **rejette** le rendu
  (`MONOTONE` + `FADING`) : 5 notes effectives, 78,7 % de la melody sur trois notes, 82,8 %
  de motifs a trois notes repetes, amplitude de 7,0 st et mouvement de 1,03 st/syll — sous
  le seuil de 2,0 st/syll de l'issue #25835. La voix reste **stable** (1 cluster, CONSISTENT).
- **Le rendu est plus long** (146,75 s contre 88,38 s pour le meme texte) et **plus silencheux**
  (60 pauses internes contre 23) : le debit tombe a 14,9 car/s de signal contre 21,8 pour
  Zonos v0.1. L'ecart de duree n'est donc pas un artefact de decoupe — les deux rendus ont
  **exactement la meme partition** et le meme texte.

### Verdict pour la shortlist Phase A0 (#17586)

Sur ce seul extrait, ZONOS3-Mini est **intelligible et peu couteux**, mais **monotone et
essoufflant** : il ne franchit pas le plancher prosodique du depot. Un PASS sur l'intelligibilite,
un FAIL sur la prosodie — par moteur, jamais en moyenne.

## 4. Reproduction

```bash
# 1. Rendu (GPU 2, runtime natif compile en CUDA)
python zonos3_measure.py \
  --binary /chemin/vers/zonos3-cli \
  --model  /chemin/vers/gguf/backbone-ptq.gguf \
  --embedding /chemin/vers/Gaspard_fr_M_1.embedding.npy \
  --text /chemin/vers/extract_C_long_narration.txt \
  --out-dir /chemin/vers/out --json-out /chemin/vers/zonos3-mini-a0c-metrics.json \
  --seed 42 --max-frames 449 --device 2 --model-dir /chemin/vers/gguf

# 2. WER + omissions + prosodie (enrichit le JSON en place)
python ../../prosody_lab/a0c_rerun/measure_3asr.py \
  --wav /chemin/vers/out/A0C-zonos3-mini-chunked.wav \
  --ref-text-file /chemin/vers/extract_C_long_narration.txt \
  --metrics-json /chemin/vers/zonos3-mini-a0c-metrics.json \
  --asr-models tiny small large-v3 large-v3-turbo --device cuda

# 3. Entree de banc (validee contre le schema v1)
python build_bank_entry.py --metrics zonos3-mini-a0c-metrics.json \
  --prosody prosody-verdict.json --out bank_entry.json --schema ../../prosody_lab/bank_schema_v1.json
```

## 5. Ce que cette mesure ne dit pas

- Le **classement ZTTS2-Eval** de l'editeur (Zyphra) n'est **pas** notre mesure : il est cite
  comme la mesure de l'editeur, jamais reifie ici.
- Le WER porte sur **un** extrait et **une** graine : il compare des moteurs sur ce passage,
  il ne classe pas un modele.
- La voix employee est la **voix livree** avec le checkpoint (embedding 192-d),
  pas un zero-shot depuis un clip de reference : le mode zero-shot n'est pas mesure ici.
- Les WAV et les poids (9 Go) **ne sont pas dans le depot** : les chemins sont cites dans le
  JSON, les empreintes SHA-256 y sont consignees.
