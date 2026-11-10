# DarkSnail — Pli 1 : reconnaissance (page de persistance)

> **Etat mesure au 2026-11-01** (lane `myia-po-2024:CoursIA`) — cette page est le
> **Livrable Pli 1** déclaré par l'EPIC [#21310](https://github.com/jsboige/CoursIA/issues/21310)
> (« page persistance ») et n'avait jamais été atterrie : le draft `epic_darksnail_pli1_4_inventaire.md`
> annoncé comme « déjà écrit c.484 » est **introuvable** (11 commentaires sur le fil, 4 sur le parent
> #18204, `gh search` issues+code = 0 résultat) — très probablement perdu dans une condensation de
> dashboard. La page ci-dessous est **reconstruite des sources mesurées**, citées section par section.
> Le corps de l'EPIC reste l'autorité ; en cas d'écart, c'est lui qui fait foi.

Sources mesurées : le body de #21310 (état au 2026-10-29), les commentaires c.6251320687 (Pli 1.1),
c.6251634217 (Pli 1.3), c.6501182314 (réponse au Concern), et les PRs mergées #21314, #21322, #23302.

## Objet

Vérification tierce du dépôt [`sneed-and-feed/projectdarksnail`](https://github.com/sneed-and-feed/projectdarksnail)
(« bi-hémisphère » : H_L = LLM causal gelé ; H_R = moteur spatial récurrent ~10,51 M paramètres couplé
par une projection dans l'espace latent de H_L), sous les deux volets de l'EPIC : Lean (la sémantique
`OcclusionTriad.lean` est-elle réellement vérifiée ?) et PostTraining (la promesse « H_L gelé + petit
module spatial = gain mesurable » est-elle mesurable chez nous ?). Cadrage : « ni suiveur aveugle, ni
sceptique de principe » — chaque pli vérifie un claim précis sur des sources firsthand avant de déplier
le suivant.

## Pli 1.1 — Sources et licences (CLOS, 2026-10-18)

Mesuré c.6251320687 :

- **URL canonique** : `https://github.com/sneed-and-feed/projectdarksnail` — dépôt **public**, créé
  2026-10-15T07:41:34Z (3 jours avant la rédaction de l'EPIC), branche par défaut `main`.
- **Licence du dépôt : CC0-1.0** (domaine public, SPDX `CC0-1.0`, fichier LICENSE à la racine) —
  conséquence Pli 2 : un lake d'enveloppe par dépendance est compatible sans contrainte de copyleft.
- Description officielle (rapportée) : « Bidirectional synthesis of ultrametric dyadic sparse attention
  (Llama Surgery) and lateralized neuromorphic test-time adaptation (Brain-AI). Lean 4 verified
  (0 sorry). »

## Pli 1.2 — Lean 4 micro-vérification (CLOS, PR #21314, 2026-10-18)

Livrable mergé : [`docs/lean/darksnail/pli1-2-occlusion-triad-verif.md`](../lean/darksnail/pli1-2-occlusion-triad-verif.md)
(lane `myia-po-2027:CoursIA-2`). Faisabilité po-2024 anticipée par le body ; la micro-vérification
(lake d'enveloppe minimal, `lake build` ciblé, `#print axioms`) y est documentée.

Complément 2026-10-29/31 (réponse au Concern user du 2026-10-18T22:13Z, lane `myia-po-2028:CoursIA-2`) :
build first-hand du contenu Lean chez nous — PR #23302, evidences sous
[`docs/lean/darksnail/build-evidence-2026-10-31/`](../lean/darksnail/build-evidence-2026-10-31/)
(`lake-build-output.txt`, `lake-axioms-output.txt`, `Axioms.query`, `coherence.txt`), verdict du lake
d'enveloppe documenté dans [`pli2-lake-enveloppe-verdict.md`](../lean/darksnail/pli2-lake-enveloppe-verdict.md)
(PR #21322 : **INSUFFISANT** — le détail vit dans ce document).

## Pli 1.3 — Audit du claim ARC-AGI-1 (CLOS, 2026-10-19, verdict PLAUSIBLE)

Livré dans le body de #21310 par `myia-po-2023:CoursIA-2` (RECONNAISSANCE pure, sans réplication),
complété c.6251634217. Synthèse :

- **Ce que le README établit** : 38/400 strict (9,500 %, Wilson 95 % CI [7,00 %, 12,77 %]) sur les 400
  paires ARC-AGI-1 ; tests appariés inter-étapes documentés (p = 9,77×10⁻⁴ vs Pass 1, p = 2,38×10⁻⁷
  vs S2) ; baselines internes : System 1 zero-shot **0/400**, `brain-ai` Phase 3 S2 15/400, Pass 1
  27/400. Aucune baseline LLM externe sur ARC-AGI-1.
- **Trois fragilités admises par le README lui-même** : (1) le shape predictor est « partly in-sample »
  (règles ajoutées sur les paires d'évaluation qui échouaient) ; (2) l'audit d'auto-leakage (72 task-IDs
  codés main supprimés avant mesure) est une auto-déclaration, non une réplication tierce ; (3) une partie
  des victoires Stage 2a est créditée au rule search, pas au readout neuronal.
- **Verdict : PLAUSIBLE** — la procédure est documentée et rien de mesuré ne contredit le 38/400 ; la
  valeur démonstrative pour l'architecture bi-hémisphère reste **non établie**. Le test décisif est
  PT 3.1 sur notre témoin `jabr/classifier-benchmark` (#17883, CC0, épinglé `afb83bee` : tâches
  publiques figées, aucun réglage contre le jeu d'évaluation, baselines externes, multi-seed).
- **Gating** : claim « non contredit » → la porte Pli 3 reste ouverte.

## Pli 1.4 — Inventaire des modèles « système 1 » (investigation CLOSE, cette page la persiste)

L'investigation first-hand (« Ms » et « clef » levés sans ambiguïté) avait mis à jour le body de #21310
(« Mis à jour c.484 ») ; son contenu est la section « Modèles à comparer » du body, repris ici :

| Rôle | Candidat | État | Notes |
|---|---|---|---|
| **H_L** (système 2, LLM) | **Qwen 3.x** petites tailles | déjà onboardés (ICT, #17883) | bien connus, baseline naturelle |
| **H_L** (système 2, LLM) | **Mistral Large 4** (sorti 2026-10-06) | 8 issues dédiées au dépôt (#1601, #4051, #616, #2401, #1640, #6790, #5475, #16472) | famille autorégressive 27B+ |
| **H_R** (système 1, décision) | `jevlike` | onboardé #17883, MIT, CPU | candidat A/B |
| **H_R** (système 1, décision) | `laya` | onboardé #17883, Apache-2.0, ~421 M, GPU | candidat A/B |
| **H_R** (système 1, décision) | **Cloudflare Clef** (+ Clef-Flash) | 9 issues (#2365 PR principal, #10045, #9765, #24, #2166, #503, #327 benchmark, #3072, #923) | finetune du flagship Cloudflare — « peut-être un peu gros pour notre chirurgie » (concern user) |
| Référence SOTA (hors scope) | Microsoft `decision-1-model-foundry` | **non open-weight** | noté comme état de l'art, pas intégré : pas les poids ; distillation par API = lourd, à arbitrer |

Banc de mesure : `jabr/classifier-benchmark` (#17883) — notre témoin d'évaluation honnête ; le benchmark
officiel de référence pour la short-list finale reste à confirmer (le user indique que le benchmark
tranchera les bons candidats).

**Identification close** : « Ms » = Mistral (Large 4) ; « clef » = Cloudflare Clef. Avec cette page,
Pli 1.4 est fermé en LIGHT/research comme le prévoyait le body.

## État des plis au 2026-11-01 (mesuré)

| Pli | État | Preuve |
|---|---|---|
| 1.1 sources & licences | **CLOS** | c.6251320687 |
| 1.2 Lean micro-vérif | **CLOS** | PR #21314 (merged 2026-10-20) |
| 1.3 audit ARC-AGI-1 | **CLOS** (PLAUSIBLE) | body #21310 + c.6251634217 |
| 1.4 inventaire modèles | **CLOS par cette page** | body #21310 §Modèles + reconstruction citée |
| 2 lake d'enveloppe | verdict **INSUFFISANT** (partiel) | PR #21322 + #23302 (build evidence 2026-10-31) |
| 3 PostTraining / PT 3.1 | **non déplié** — porte ouverte (ARC-AGI-1 non contredit), dépli réservé au coordinateur | body #21310 §Pli 3 |
| 4 pédagogie | non déplié (gating Pli 3) | body #21310 §Pli 4 |

Les pages de persistance des plis 2 et 3 (`darksnail-pli2-solidite.md`, `darksnail-pli3-posttraining.md`)
restent à produire **à leur dépli** — le contenu Pli 2 déjà mesuré vit aujourd'hui sous
`docs/lean/darksnail/` (citations ci-dessus).

## Voir aussi

- #21310 — EPIC origami : Project DarkSnail (autorité)
- #18204 — EPIC origami système 1 (parent) · #18205 — format Origami (géométrie différentielle)
- #19898 / #20404 — EPICs Origami sœurs (openai/math, Thurston)
- #17883 — `03b_Typed_Decisions_System1.ipynb` + banc `jabr/classifier-benchmark`
- #15400 — OpenAI NavierStokesAndEuler · #10759 — Sendov (Tao) · #16569 — Euler-NS
