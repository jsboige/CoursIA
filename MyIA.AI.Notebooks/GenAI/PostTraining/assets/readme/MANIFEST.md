# Manifeste des figures — GenAI/PostTraining (racine)

Provenance de la figure de référence à la racine de `PostTraining/` (EPIC #1742 « Post-Training SOTA 2024-2025 »).

> **Audit vision M3 po-2023 c.658 (2026-07-19)** : le PNG unique ci-dessous a été ouvert via l'outil `Read` et son contenu réel confronté à la description existante (README parent + cellule génératrice `aa756193` du notebook `PT_06_eval_comparative.ipynb`). **SOTA-OK** : `pt06_cost_comparison.png` = **vrai barplot matplotlib 2 panneaux** (Coût Compute Relatif + Mémoire GPU Relative) montrant les 4 techniques de post-training (SFT / DPO / GRPO / RLVR) avec annotations de valeur par barre, généré par `plt.savefig("pt06_cost_comparison.png", dpi=100, bbox_inches="tight")` dans la cellule 17 du notebook. Couleurs blue/orange/green/pink distinctes, axes gradués, titre suptitle complet « Post-Training SOTA 2024-2025 — Cout Compute vs Memoire (Qwen2.5-0.5B, 1K samples, 3 epochs) ». **0 figure DROP**. **0 PNG régénéré** (cellule déjà exécutée et son output commité dans la PR d'origine #1772 « feat(post-training): add PT-06 eval comparative (Epic #1742 COMPLETE) »). **0 notebook ré-exécuté** (C.3 strict respectu00e9). La présente PR ajoute la **MANIFEST.md** d'origine (manquante) pour aligner ce dossier sur la doctrine #5780 (chaque figure placée dans la MANIFEST de la section du README où elle est référencée).

---

## pt06_cost_comparison.png

- **Source** : notebook `PT_06_eval_comparative.ipynb` (cellule 17 / id `aa756193`, output matplotlib `plt.savefig` + `plt.show()`) — commité dans PR #1772 « feat(post-training): add PT-06 eval comparative (Epic #1742 COMPLETE) ».
- **Contenu réel vérifié** (re-lecture M3 c.658 2026-07-19) : PNG 37 296 octets, **figure matplotlib 2 panneaux (1×2 layout)** générée par la cellule code, dimensions dpi=100 + bbox_inches=tight :
  - **Panneau gauche** : « **Cout Compute Relatif** » — barplot vertical 4 barres (SFT / DPO / GRPO / RLVR), axe Y = « Heures GPU (RTX 3070, estim.) » gradué 0 → 1.6, valeurs annotées au-dessus de chaque barre : **SFT 0.5h** (bleu `#2196F3`), **DPO 0.8h** (orange `#FF9800`), **GRPO 1.2h** (vert `#4CAF50`), **RLVR 1.3h** (rose `#E91E63`).
  - **Panneau droit** : « **Memoire GPU Relatif** » — barplot vertical 4 barres, axe Y = « VRAM requise (Go) » gradué 0 → 5, valeurs annotées : **SFT 2.0 Go** (bleu), **DPO 3.5 Go** (orange), **GRPO 4.0 Go** (vert), **RLVR 4.0 Go** (rose).
  - **Suptitle** central : « **Post-Training SOTA 2024-2025 — Cout Compute vs Memoire (Qwen2.5-0.5B, 1K samples, 3 epochs)** ».
- **Alt-text (FR)** : Barplots matplotlib côte-à-côte comparant les 4 techniques de post-training (SFT / DPO / GRPO / RLVR) sur Qwen2.5-0.5B (1K samples, 3 epochs, RTX 3070) — panneau gauche = heures GPU estimées (0.5h / 0.8h / 1.2h / 1.3h), panneau droit = VRAM requise (2.0 / 3.5 / 4.0 / 4.0 Go).
- **Poids** : 37,3 Ko (natif PNG)
- **Note** : ces chiffres sont des **estimations pédagogiques** (voir cellule `7e53b4b7` du même notebook : « Note : ces chiffres sont des ESTIMATIONS pedagogiques. Pas de claim BEATS quantitatif (sample insuffisant pour multi-seed) »). La figure illustre **proportionnellement** la hiérarchie coût/mémoire (SFT < DPO < GRPO ~ RLVR), pas des valeurs absolues certifiées sur GPU spécifique. Conforme à H.2 du CLAUDE.md (problème non-trivial, vraie sortie matplotlib, pas un ASCII fallback).

---

**Total** : 1 figure, ~37 Ko. **Politique** (#5654) : ≤200 KB/fichier, downscale ≤1200 px max. Arc pédagogique : la figure est la sortie visuelle centrale de la **section 2.1 « Comparaison technique »** du notebook PT-06 (section 2 du notebook contient le tableau textuel puis la cellule code qui produit la figure). Pas d'autre figure dans ce dossier à ce jour (les notebooks PT-01 à PT-05 / PT-07 n'ont pas de figure de référence `assets/readme/` distincte — ils s'appuient sur leurs propres cellules de visualisation internes au notebook).

**⚠️ Limitations de cette MANIFEST** :
- Les **valeurs « 0.5h / 0.8h / 1.2h / 1.3h » et « 2.0 / 3.5 / 4.0 / 4.0 Go »** sont des **estimations pédagogiques** codées en dur dans la cellule `aa756193` (variables `gpu_hours` / `memory_gb`) — PAS des mesures empiriques d'un entraînement réel. Un·e lecteur·rice parcourant `PostTraining/` sans ouvrir le notebook pourrait croire à des chiffres mesurés : la cellule `7e53b4b7` du même notebook rappelle honnêtement « Estimate, pas de claim BEATS ». Cette note préserve la transparence.
- Migration Qwen3.5 en cours (#5078) — PT-03 a migré mais PT-02 / PT-04 / PT-05 / PT-06 utilisent encore Qwen2.5-0.5B. Les chiffres de cette figure reflètent l'état **pré-migration** ; un re-run sur Qwen3.5 modifierait (probablement à la hausse) les heures GPU et la VRAM.
- La figure est conservée **telle quelle** sur disque ; cette PR ne supprime AUCUN fichier PNG et ne touche à AUCUNE cellule notebook (C.3 strict).
- **0 secret inline** : aucun path, token ou credential n'apparaît dans la figure ou dans le code qui l'a produite.

Audit vision M3 po-2023 c.658 (2026-07-19, doctrine #5780) — choix éditorial = byte-safe MANIFEST-add, 0 PNG régénéré, 0 notebook ré-exécuté (C.3 strict). PR meraillage parent = #1772 (« feat(post-training): add PT-06 eval comparative (Epic #1742 COMPLETE) »).
