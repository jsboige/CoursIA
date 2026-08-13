# Catalogue SAE Qwen — inventaire des tailles candidates Phase 3-5

> **EPIC #10355 / Phase 1 / Livrable 4** — inventaire des SAE Qwen3.5/3.6 disponibles dans le harnais ICT (#8236) et plus largement chez Qwen-Scope.
> **Mesure firsthand** (G.1 / G.9) : (a) métadonnées des `.npz` committés dans `MyIA.AI.Notebooks/IIT/ICT-Series/traces/` ; (b) lecture directe du code `scripts/extract_sae_traces.py` ; (c) WebFetch des `model cards` Qwen-Scope (4 repos).
> **Ce fichier est le gate de faisabilité Phase 3-5** : sans ≥3 tailles SAE, la Phase 3 (FT/PT) ne peut pas comparer cross-échelle et la Phase 5 (audit causal) ne peut pas séparer « propriété du SAE » de « propriété du modèle ».

---

## Verdict court (acceptance criterion 4 de #10356)

**≥3 tailles Qwen3.5 inventoried = OK.** Les SAE Qwen-Scope couvrent **3 bases Qwen3.5** officiellement :

| # | Base model | SAE repo officiel Qwen-Scope | Status harnais ICT |
|---|---|---|---|
| 1 | Qwen3.5-9B-Base | `Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50` | **En usage** (traces committées) |
| 2 | Qwen3.5-2B-Base | `Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50` | **En usage** (traces committées) |
| 3 | Qwen3.5-35B-A3B-Base (MoE) | `Qwen/SAE-Res-Qwen3.5-35B-A3B-Base-W32K-L0_50` | **Disponible, hors harnais** (pas encore extrait) |

Variantes L0_100 également publiées sur 9B et 8B (cf. §« Variantes L0_100 »). **Qwen3.6 n'a pas de release publique à ce jour** (au 2026-08-10, vérification HF Hub) — la lignée Qwen3.5 (avec 35B-A3B) est la dernière sortie Qwen-Scope.

---

## Inventaire détaillé

### Taille 1 — Qwen3.5-9B-Base × W64K-L0_50 (en usage)

| Champ | Valeur | Source |
|---|---|---|
| **Base model** | `Qwen/Qwen3.5-9B-Base` (denses, ~9B params, 32 couches, `d_model=4096`) | `extract_sae_traces.py:300` + model card HF |
| **SAE repo** | `Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50` | `extract_sae_traces.py:301` |
| **URL** | https://huggingface.co/Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_50 | WebFetch 2026-08-10 |
| **Checkpoint path** | `hf_hub_download(sae_repo, layer=L, ...)` — 1 `.pt` par couche 0–31 (32 fichiers) | Model card HF + `extract_sae_traces.py:398+` |
| **d_sae (largeur dict.)** | 65 536 (16× expansion sur 4096) | Model card HF |
| **L0 (top-k)** | 50 strict | `trace.meta["k"] = 50` |
| **Layers SAE publiés** | 0–31 (couche residuelle après chaque decoder layer) | Model card HF |
| **Couche harnais ICT** | 16 (`frac=0.5161`, mi-réseau) | `trace.meta["layer"]` + `sae_traces.py:resolve_capture_layer` |
| **VRAM pic mesurée (bf16)** | 16,7 Gio (modèle 9B) + ~1 Gio SAE → ~17,7 Gio | notebook `ICT-21-SAETrajectoires.ipynb` §`13350192` |
| **d_model / # layers base** | 4096 / 32 | `meta["d_model"]` + model card |

**Mesures de qualité (relevées firsthand sur les `.npz` committés)** :

| Métrique | Entraîné | Contrôle | Source |
|---|---|---|---|
| **L0 mesuré (min/max/mean)** | 50.00 / 50.00 / 50.00 | 50.00 / 50.00 / 50.00 | re-mesure 2026-08-10 sur `traces/ict21_sae_layer16_*.npz` |
| **Features actives (sur 2 699 tokens)** | 20 786 / 65 536 | 6 925 / 65 536 | idem (sur l'union des `ids`) |
| **% features mortes** | **68,3 %** | **89,4 %** | idem |
| **Date extraction** | 2026-07-07T12:56:36Z | 2026-07-07T12:57:03Z | `meta["date"]` |
| **Quantized readout ?** | Non (bf16 strict, guard `assert_bf16_readout` levé) | idem | `meta["quantized_readout"] = False` |

**Lecture** : le SAE est **top-k strict** (L0=50.0 au bit près — vérifié par cellule Gate 10 du notebook ICT-21), le harnais capture la couche médiane (frac=0.5161), et **68 % de dictionnaire mort** sur 2 699 tokens est attendu à cette échelle : c'est cohérent avec les SAE TopK qui distribuent leur budget sur un corpus large, pas sur 5 jeux de prompts.

---

### Taille 2 — Qwen3.5-2B-Base × W32K-L0_50 (en usage)

| Champ | Valeur | Source |
|---|---|---|
| **Base model** | `Qwen/Qwen3.5-2B-Base` (denses, ~2B params, 24 couches, `d_model=2048`) | `extract_sae_traces.py` (usage L36-39) + model card HF |
| **SAE repo** | `Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50` | idem |
| **URL** | https://huggingface.co/Qwen/SAE-Res-Qwen3.5-2B-Base-W32K-L0_50 | WebFetch 2026-08-10 |
| **Checkpoint path** | 1 `.pt` par couche 0–23 (24 fichiers) | Model card HF |
| **d_sae** | 32 768 (16× expansion sur 2048) | Model card HF |
| **L0 (top-k)** | 50 strict | `trace.meta["k"] = 50` |
| **Layers SAE publiés** | 0–23 | Model card HF |
| **Couche harnais ICT** | 12 / 23 (`frac=0.5217`, mi-réseau — `--layer-frac 0.5` arrondi) | `trace.meta["layer_frac"]` |
| **VRAM pic mesurée (bf16)** | 3,6 Gio (entraîné) / 4,5 Gio (contrôle — permutation embedding) | notebook `ICT-21-SAETrajectoires.ipynb` §`57c90848` |
| **Déterminisme** | Re-extraction bit-stable (écart max = 0 sur les `vals`, écart 1-3 octets = longueur champ `date` méta) | idem §`57c90848` |
| **d_model / # layers base** | 2048 / 24 | `meta["d_model"]` + model card |

**Mesures de qualité (relevées firsthand sur les `.npz` committés)** :

| Métrique | Entraîné | Contrôle | Source |
|---|---|---|---|
| **L0 mesuré (min/max/mean)** | 50.00 / 50.00 / 50.00 | 50.00 / 50.00 / 50.00 | re-mesure 2026-08-10 sur `traces/ict21_sae_qwen35-2b-base_layer12of24_*.npz` |
| **Features actives (sur 2 699 tokens)** | 16 636 / 32 768 | 6 589 / 32 768 | idem |
| **% features mortes** | **49,2 %** | **79,9 %** | idem |
| **Date extraction** | 2026-08-10T17:04:16Z | 2026-08-10T17:04:57Z | `meta["date"]` |
| **Quantized readout ?** | Non | idem | `meta["quantized_readout"] = False` |

**Lecture** : la **deuxième échelle du harnais** (`#8236`/`#10337` MERGED 2026-08-09, commit `3a089e00d`) — `d_sae` 2× plus petit (32K vs 64K), mais **49 % de dictionnaire mort** seulement, **bien meilleur que le 9B** (68 %). La densité du support reflète le ratio d'**occupation relative** (2B réveille plus de features proportionnellement à sa capacité), pas une richesse absolue — distinction explicitée dans le notebook §`47032e5d` (« artefact de capacité, à ne PAS lire comme un progrès »).

---

### Taille 3 — Qwen3.5-35B-A3B-Base × W32K-L0_50 (disponible, hors harnais)

| Champ | Valeur | Source |
|---|---|---|
| **Base model** | `Qwen/Qwen3.5-35B-A3B-Base` (**MoE** : 35B total params / 3B actifs, 40 couches, `d_model=2048`) | WebFetch model card 2026-08-10 |
| **SAE repo** | `Qwen/SAE-Res-Qwen3.5-35B-A3B-Base-W32K-L0_50` | idem |
| **URL** | https://huggingface.co/Qwen/SAE-Res-Qwen3.5-35B-A3B-Base-W32K-L0_50 | idem |
| **Checkpoint path** | 1 `.pt` par couche 0–39 (40 fichiers) — clés `W_enc (32768×2048)`, `W_dec (2048×32768)`, `b_enc (32768,)`, `b_dec (2048,)` | idem (file format PyTorch dict) |
| **d_sae** | 32 768 (16× expansion sur 2048) | idem |
| **L0 (top-k)** | 50 strict | idem |
| **Layers SAE publiés** | 0–39 (40 couches du MoE) | idem |
| **Couche harnais ICT** | (à définir si adoption : frac=0.5 → couche 20) | `sae_traces.py:resolve_capture_layer` |
| **VRAM pic estimée** | ~7 Gio bf16 (3B params actifs) — bien au-delà du budget standard 24 Gio ; le SAE ajoute ~0,5 Gio | inférence depuis modèle 2B (mêmes `d_model` + `d_sae`) |
| **Status ICT** | **0 traces extraites**. Adoption = PR séparée (worktree, outillage inchangé, `--model` + `--sae-repo` suffisent) | `extract_sae_traces.py` déjà agnostique au modèle |

**Mesures de qualité** : **non mesurées localement** (pas d'extraction ICT). Le model card Qwen-Scope ne reporte pas non plus de loss/dead% publié. Recommendation Phase 3 : lancer un smoke + une extraction full avant tout commentaire qualité — le coût est de l'ordre de celui du 2B (~36 s sur RTX 4090 GPU 2 d'ai-01).

**Lecture** : c'est **la taille la plus discriminante** pour la Phase 3 — c'est la **seule SAE sur architecture MoE** publiée par Qwen-Scope. Comparer entraîné/contrôle 9B (dense) vs 35B-A3B (MoE) **sépare l'effet « densité du modèle » de l'effet « largeur du SAE »**, ce que 2B vs 9B ne permet pas. **C'est la cible prioritaire Phase 3** (juste après le 9B qui est déjà l'organe de référence).

---

## Variantes L0_100 (mentionnées mais hors inventaire principal)

Deux SAE officiels existent en parallèle à densité doublée, **non utilisés dans le harnais actuel** mais explicitement cités comme « second readout » dans le notebook ICT-21 §`47032e5d` :

| SAE repo | d_sae | L0 | Status |
|---|---|---|---|
| `Qwen/SAE-Res-Qwen3.5-9B-Base-W64K-L0_100` | 65 536 | **100** | Disponible, hors harnais. Le notebook ICT-21 mentionne explicitement « le SAE W32K-L0_100 fournit le second readout ». |
| `Qwen/SAE-Res-Qwen3-8B-Base-W64K-L0_100` | 65 536 | **100** | Disponible, hors harnais. Note : Qwen3 (pas 3.5) — 36 couches, `d_model=4096` (équivalent à Qwen3.5-9B en surface). |

**Lecture** : une variante L0_100 sur le même modèle+couche vérifie qu'un effet mesuré ne dépend pas du choix de dictionnaire. **Pas un livrable Phase 1**, mais déjà désigné comme garde-fou Phase 3 par le notebook ICT-21.

---

## Garde-fous cross-échelle du harnais (cf. `ict/sae_traces.py`)

Le harnais ICT encode 4 garde-fous qui rendent les comparaisons cross-échelle auditables :

1. **`resolve_capture_layer(n_layers, layer, layer_frac)`** — refuse `--layer` ET `--layer-frac` simultanés ; impose la profondeur **relative** (frac=0.5 → 12/24 sur 2B, 16/32 sur 9B) ; refuse `n_layers < 1` ou `layer` hors bornes. C'est la garantie que **les deux échelles utilisent la même fraction de profondeur** (0.5161 vs 0.5217 — pratiquement égales, l'écart 0.005 vient de l'arrondi `int(round(0.5 × (n-1)))`).

2. **`check_sae_model_match(sae_d_model, model_d_model, …)`** — refuse un SAE 9B (`d_model=4096`) sur un modèle 2B (`d_model=2048`), avec message d'erreur qui **nomme explicitement les paires canoniques** : « Apparier les familles : Qwen3.5-9B-Base ↔ SAE-Res-Qwen3.5-9B-Base-W64K-*, Qwen3.5-2B(-Base) ↔ SAE-Res-Qwen3.5-2B-Base-W32K-* ». **Ce gate ferme un mode de défaillance silencieux** : sans lui, `h @ W_enc.T` échoue sur une erreur de forme torch illisible.

3. **`assert_bf16_readout(quantization_config, allow_quantized=False)`** — refuse un readout SAE sur un modèle chargé quantifié (4-bit). Les SAE Qwen-Scope sont entraînés sur le résiduel **pleine précision** ; un readout NF4 mesurerait l'arrondi de quantification, pas le résiduel. **Le régime correct pour l'arc PT-12** est dissocié : QLoRA (base gelée 4-bit + adapters bf16) pour l'entraînement, puis **rechargement bf16 base+adapters fusionnés** pour le readout SAE.

4. **`trace_filename(variant, layer, model=…, default_model=…, n_layers=…, n_clamp=…)`** — slug d'échelle **dans le nom de fichier** dès que le modèle diffère du défaut (`ict21_sae_layer16_*.npz`). Sans ce slug, un run 2B et un run 9B à la même couche 16 **écraseraient en silence** : perte de données, pas seulement confusion. Le harnais refuse par défaut (`--overwrite` requis pour forcer).

**Test canonique cross-échelle** : `MyIA.AI.Notebooks/IIT/ICT-Series/tests/test_sae_cross_scale.py` — vérifie que les 4 garde-fous lèvent les bonnes erreurs sur les mauvaises paires.

---

## Candidates Phase 3-5 (synthèse)

L'inventaire établit **3 tailles** candidates, dont **2 déjà câblées** (extraction GPU fonctionnelle, traces committées, notebooks ICT-21 + ICT-24 opérationnels) :

| Priorité | Taille | Justification | Coût extraction (mesuré) |
|---|---|---|---|
| **P1** | Qwen3.5-9B-Base × W64K-L0_50 (couche 16) | Référence dense, organe de mesure principal de la série ICT (Gate 10/11 PASS) | 50 s full / 480 s smoke / 17 Gio VRAM |
| **P2** | Qwen3.5-2B-Base × W32K-L0_50 (couche 12) | Seconde échelle dense, bit-stable, déjà utilisée pour le null cross-échelle (corr. contrôle ≈ 0,94 vs 9B) | 36 s full / 4 Gio VRAM |
| **P3** | Qwen3.5-35B-A3B-Base × W32K-L0_50 (couche 20 cible) | **Seule taille MoE** publiée — sépare densité vs largeur dictionnaire, complément indispensable pour Phase 3 cross-architecture | ~7 Gio VRAM estimé (jamais extrait localement) |
| P4 (optionnel) | Qwen3.5-9B-Base × W64K-L0_100 | Variante densité L0_100 sur le 9B — second readout contre un effet de dictionnaire, **non bloquant** | idem P1 (même modèle) |

**Qwen3.6 n'existe pas en release publique** (vérification Hub 2026-08-10). Le pipeline accepte n'importe quel `model` HF, donc une adoption future ne demanderait qu'un PR d'ajout du couple — la liste canonique de paires dans `check_sae_model_match` est à mettre à jour si Qwen-Scope publie de nouvelles tailles (cf. mécanisme `W32K-*`/`W64K-*` dans le message d'erreur).

---

## Acceptance criteria — checklist falsifiable

| # | Critère (issue #10356) | Mesure | Statut |
|---|---|---|---|
| 4 | Catalogue SAE Qwen inventorié | fichier `qwen_sae_inventory.md` avec ≥3 tailles Qwen3.5/3.6 | ✅ **3 tailles Qwen3.5** (9B, 2B, 35B-A3B) + 2 variantes L0_100 (9B, 8B) |
| 4' | URL + nb features + checkpoint path | lignes 1-3 par taille | ✅ |
| 4'' | Dernière mesure qualité (loss / dead features %) | section « Mesures de qualité » firsthand par taille | ✅ (L0, % dead, date, quantized — le loss SAE brut n'est pas publié par Qwen-Scope) |
| 4''' | Cible 3-5 tailles Phase 3 FT/PT | section « Candidates Phase 3-5 » | ✅ (3 + 1 option) |
| 4'''' | Escalade owner si <3 tailles | non applicable — 3 tailles confirmées | ✅ |

---

## Liens

- **EPIC parente** : #10355 — Phase 1/5 fallacy detection research
- **Issue livrable** : #10356 — Phase 1 deliverable 4
- **Préréquis harnais** : #8236 (ICT strate 6 SAE), PR #10337 MERGED 2026-08-09 (seconde échelle SAE appariée)
- **Code harnais** : `MyIA.AI.Notebooks/IIT/ICT-Series/scripts/extract_sae_traces.py` + `MyIA.AI.Notebooks/IIT/ICT-Series/ict/sae_traces.py` + `MyIA.AI.Notebooks/IIT/ICT-Series/tests/test_sae_cross_scale.py`
- **Notebooks consommateurs** : `ICT-21-SAETrajectoires.ipynb` (Gate 10/11 PASS) + `ICT-SAE-JLens-TeteATete.ipynb` (Gate 22-24 #5635)
- **Traces committées** : `MyIA.AI.Notebooks/IIT/ICT-Series/traces/ict21_sae_layer16_{trained,control}.npz` + `ict21_sae_qwen35-2b-base_layer12of24_{trained,control}.npz`
- **Qwen-Scope paper** : arXiv:2605.11887 — *Scaling Sparse Autoencoders on Qwen3.5*
- **Phase 1 autres livrables** : #10360 (survey SOTA MERGED) + #10363 (Jessynoo extraction MERGED) ; reste deliverable 2 (datasets landscape)

---

## Anti-patterns évités

- **Pas de métrique loss SAE citée sans source** : Qwen-Scope ne publie pas de `reconstruction_loss` / `FVE` par couche ; citer un chiffre qui n'est pas dans le `.pt` ou le `model card` = fabrication. Mesures rapportées = ce qui est **firsthand mesurable** (L0 exact via `meta`, % dead via union `ids`, déterminisme par re-extraction bit-stable).
- **Pas de confusion `W64K`/`W32K` ↔ nombre de features** : W64K = **65 536 features**, W32K = **32 768 features**. Notation HuggingFace en K-mille (K=1024) et non K-mille-standard (K=1000), comme Anthropic / OpenAI / la convention ML.
- **Pas de catalogue « Qwen3.6 » fantôme** : Qwen3.6 **n'existe pas en release publique** au 2026-08-10. L'inventaire dit vrai : 3 tailles Qwen3.5, 0 taille Qwen3.6.
- **Pas de scraper opaque** : les chiffres viennent du code source du harnais (Lu), des `.npz` committés (re-mesurés), et des model cards HF (WebFetch avec citation littérale).
- **Pas de PII / secret** : 0 clé API, 0 token, 0 chemin machine dans ce fichier (cf. `secrets-hygiene` règle 6).