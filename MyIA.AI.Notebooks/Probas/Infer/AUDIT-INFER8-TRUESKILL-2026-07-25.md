# Audit de fidélité — Infer-8-TrueSkill vs MBML Ch.3 (Meeting Your Match)

**Notebook audité** : `Infer-8-TrueSkill.ipynb` (63 cellules, 19 cellules de code, kernel `.net-csharp`, exec 1..19)
**Source canonique** : *Model-Based Machine Learning* (Winn), **Chapitre 3 — « Meeting Your Match »** ([mbmlbook.com/TrueSkill.html](https://www.mbmlbook.com/TrueSkill.html)), lui-même distillé de Herbrich, Minka & Graepel (2007), *TrueSkill™: A Bayesian Skill Rating System*, NIPS 20.
**Date** : 2026-07-25 — **Auditeur** : po-2023 — **Épic** : #8081 (audit fidélité distillation Probas/Infer.NET)
**Verdict global** : **FIDÈLE ~90 %** — distillation dense et pédagogiquement forte ; une correction de lignée et un backfill optionnel recommandés.

> Méthode : audit firsthand, notebook lu cellule par cellule ET source MBML Ch.3 lue en ligne (sections *Modelling the outcome of games*, *Inferring the players' skills*, *A solution: expectation propagation*, *Extensions to the core model*, *Allowing the skills to vary*). Comparaison axe par axe selon le protocole #8081. Aucune modification du notebook dans cet audit (verdict FIDÈLE — un backfill optionnel est spécifié §5 pour soumission séparée).

---

## 1. Correction de lignée (important)

Le notebook se présente (titre, prérequis `Infer-7-Skills-IRT`, intro cell[0]/cell[6]) comme le successeur direct de l'assessment de skills. La table des matières MBML établit la correspondance exacte :

| Notebook CoursIA | Chapitre MBML | Scénario source |
|------------------|---------------|-----------------|
| `Infer-7-Skills-IRT` | **Ch.2 — Assessing People's Skills** (`LearningSkills.html`) | Test QCM, skill déduit des réponses (modèle de type Rasch/IRT) |
| **`Infer-8-TrueSkill`** | **Ch.3 — Meeting Your Match** (`TrueSkill.html`) | Matchs Xbox Live/Halo 2, skill déduit du résultat (1v1, équipes, multi-joueurs) |

L'incident déclencheur de #8081 (Elo « table-foil » dans `PyMC-8-TrueSkill`) et le titre `Infer-8-TrueSkill` laissaient penser à un audit Ch.2, mais **le classement par matchs est Ch.3**. Le `README.md` de la série doit refléter cette lignée à deux niveaux (Ch.2 → Infer-7, Ch.3 → Infer-8) pour éviter la confusion. **Action recommandée** (markdown-only, hors scope de cet audit) : ajouter la colonne « Chapitre MBML » au tableau de lignée de `Probas/Infer/README.md`.

---

## 2. Comparaison axe par axe (avec preuve cellulaire)

| Axe MBML Ch.3 | Couverture CoursIA | Preuve (cellule) | Verdict |
|---------------|--------------------|------------------|---------|
| Skill ~ Gaussienne `N(μ, σ²)` | Oui, formulée | cell[6] `skill_i ~ N(μ_i, σ_i²)` | FIDÈLE |
| Performance = skill + bruit `N(0, β²)` | Oui | cell[6], cell[12] `perf = skill + eps` | FIDÈLE |
| Facteur `IsGreaterThan` (joueur 1 gagne si perf₁ > perf₂) | Oui, visualisé | cell[12–15], cell[17] graphe de facteurs | FIDÈLE |
| **Pourquoi EP** (posterior exact non-Gaussien : Gaussienne × Gaussienne cumulée) | **Oui, profond** | cell[19] : la troncation par `>` produit une sigmoïde → EP reprojette sur une Gaussienne | **FIDÈLE (profond)** — capte le cœur conceptuel de Ch.3 §3.3 |
| Match nul (seuil ±ε, `ConstrainBetween`) | Oui | cell[20–22] `Variable.ConstrainBetween` | FIDÈLE |
| Équipes (perf d'équipe = somme des perfs) | Oui (2v2) | cell[35–37], cell[39] graphe | FIDÈLE |
| Multi-joueurs / free-for-all (contraintes d'ordre transitives) | Oui (course 4 joueurs) | cell[41–43], cell[45] graphe | FIDÈLE |
| Apprentissage en ligne (posteriorₙ₋₁ → priorₙ) | Oui, classe `TrueSkillOnline` | cell[28–31], cell[33] tournoi | FIDÈLE |
| Rating conservatif **μ − 3σ** (leaderboard) | **Oui, explicité** | cell[34] « mu - 3σ pénalise les joueurs avec peu de matchs », « ~99.7 % de confiance » | FIDÈLE |
| Elo from-scratch (prédécesseur déterministe) | Oui, implémenté + analysé | cell[8–10] (formule, dérivation, « Elo est aveugle à sa propre incertitude ») | FIDÈLE (valeur ajoutée) |
| Citation source (Herbrich/Minka/Graepel 2007) | Partielle | cell[7] cite Herbrich + Graepel (2006) ; **Minka absent** | MINEUR — voir §4 |

**Synthèse** : sur les 10 axes conceptuels de Ch.3, **9 sont couverts avec fidélité**, dont l'axe le plus difficile (la nécessité d'EP, §3.3) traité avec une profondeur remarquable. La distillation n'est pas un contournement : EP, les graphes de facteurs et les contraintes d'ordre sont **exécutés** (Infer.NET, outputs réels, ec 1..19), pas narrés.

---

## 3. PERTE DOCUMENTÉE (omissions légitimes, choix pédagogique)

Ces omissions sont cohérentes avec la série entière et ne constituent pas une perte par complaisance :

1. **Dialogue de dérivation itératif MBML** : le livre construit le modèle par améliorations successives (assomption 3.1 → diagnostic → extension). Le notebook présente le modèle fini. **Choix pédagogique assumé** (un notebook de 55 min ne peut reproduire le dialogue livresque) — mais à documenter comme tel, non à laisser implicite.
2. **Vraies données Halo 2** (MBML Table 3.1, dataset *Head to Head* Halo 2) : le notebook utilise des tournois synthétiques (Alice/Bob/Charlie/Dave, Magnus/Fabiano/Ian). Choix légitime (reproductibilité, contrôle des « vrais skills » pour l'évaluation, cell[52]) — la version synthétique permet même la comparaison vrai-vs-estimé que les données réelles ne donnent pas.
3. **TrueSkill 2 (Minka et al. 2018)** : extension moderne (kills in-game, corrélation inter-modes, quit-mid-game). Hors scope d'une intro — le notebook le signale correctement en extension (cell[55]).

---

## 4. Points mineurs (corrections cosmétiques, non bloquantes)

- **Citation source incomplète** (cell[7]) : « développé en 2006 par Ralf Herbrich et Thore Graepel ». La publication canonique est **Herbrich, Minka & Graepel (2007)**, NIPS 20 — **Tom Minka** (auteur d'EP lui-même, et co-auteur TrueSkill/TrueSkill 2) est omis. Suggestion markdown-only : « Herbrich, Minka & Graepel (2007) ».
- **Date 2006 vs 2007** : la conférence NIPS 2006, publiée dans les proceedings NIPS 20 (2007). Les deux dates circulent ; « 2007 » (publication) est plus canonique.

---

## 5. Backfill recommandé (optionnel — soumission séparée)

### 5.1 Le gap : skills dynamiques (MBML Ch.3 §3.5 — *Allowing the skills to vary*)

Le notebook **signale lui-même** la limitation (cell[55] : « Suppose une skill stable dans le temps (pas d'apprentissage du joueur) ») et mentionne Glicko-2/TrueSkill 2 comme extensions. **Ce n'est donc PAS une perte par complaisance** (le gap est reconnu). Cependant, MBML élève cette extension au rang de **climax du chapitre** (§3.5, modèle final assomption 1) :

> « You may think that our online learning process updates our skill distribution for a player over time and so would allow the skill to change. **This is a common misconception about online learning, but it is not true.** » — MBML §3.5

Or la cellule[31] du notebook (« le système n'oublie jamais mais l'influence des anciens matchs diminue naturellement ») décrit précisément le modèle à skill **fixe**, et pourrait laisser le lecteur avec la conception erronée que MBML §3.5 corrige explicitement. Le notebook possède même une section Échecs (cell[47–50]) qui serait le point d'ancrage naturel vers *TrueSkill Through Time* (Dangauthier et al. 2007, chess through time) — connexion non faite.

### 5.2 Spécification de backfill (pour PR follow-up)

- **Minimal (markdown-only, exception C.2)** : 1 cellule markdown après cell[31] ou cell[55] corrigeant la misconception (« online learning ≠ skill drift : le posterior se resserre sur un skill *fixe* ; si le joueur s'améliore vraiment, il faut un modèle dynamique ») + renvoi à MBML §3.5 et Dangauthier et al. (2007). Coût faible, valeur pédagogique élevée (détruit la misconception).
- **Complet (code + re-exec, grain MED)** : 1 cellule code démontrant le **Gaussian random walk sur le skill** — `skill[t] ~ Gaussian(skill[t-1], change²)` via Infer.NET (variables `Variable<double>` chaînées, `Variable.Random` / prior dynamique). Re-exec end-to-end (63 cellules, kernel .NET) avec `strip_probe_banner.py --apply` post-exec (règle #6, bannière Kestrel/probeAddresses) + normalisation des chemins à la source (helper `RepoRelative`). Démonstration sur la section Échecs existante (cell[47–50]) : un Magnus dont le skill *augmente* sur la carrière, mal suivi par le modèle fixe, bien suivi par le modèle dynamique — réplique exacte de la Figure 3.38/3.40 MBML.

**Recommandation** : le backfill minimal (markdown correctif) est à forte valeur/coût ; le backfill complet est un grain MED substantiel pouvant faire l'objet d'une PR dédiée ou sous-issue #8081. Cet audit documente le verdict ; le notebook reste **FIDÈLE** en l'état.

---

## 6. Matrice de verdict

| Classe | Items | Action |
|--------|-------|--------|
| **FIDÈLE** (~90 %) | Modèle skill/perf, facteur `>`, **nécessité d'EP**, matchs nuls, équipes, multi-joueurs, online learning, rating μ−3σ, Elo from-scratch | Rien (notebook solide) |
| **PERTE DOCUMENTÉE** | Dérivation itérative MBML, vraies données Halo 2, TrueSkill 2 (2018) | Documenté ici (choix pédagogique légitime) |
| **MINEUR** | Citation Minka absente, date 2006→2007 | Markdown-only, follow-up optionnel |
| **Backfill recommandé** | Skills dynamiques (MBML §3.5) — limitation déjà signalée par le notebook | PR follow-up (minimal markdown ou complet code, §5.2) |

---

## 7. Sources (vérifiées, non fabriquées)

- MBML Ch.3 *Meeting Your Match* : https://www.mbmlbook.com/TrueSkill.html (+ sous-sections *Modelling the outcome of games*, *A solution: expectation propagation*, *Allowing the skills to vary*)
- Code compagnon MBML Ch.3 : https://github.com/dotnet/mbmlbook/tree/main/src/3.%20Meeting%20Your%20Match
- Herbrich, Minka, Graepel (2007), *TrueSkill™: A Bayesian Skill Rating System*, NIPS 20, pp. 569–576
- Dangauthier et al. (2007), *TrueSkill Through Time: Revisiting the History of Chess*, NIPS (pour le backfill §5)
- Minka et al. (2018), *TrueSkill 2: An improved Bayesian skill rating system*, MSR-TR-2018-8

---

*Audit conduit dans le cadre de l'épic #8081 (audit fidélité distillation Probas/Infer.NET). Convention de nommage : `AUDIT-INFER<N>-<NOM>-<DATE>.md` (cf. `AUDIT-INFER4-BAYESIAN-NETWORKS-2026-07-25.md`, po-2026 #8528). See #8081.*
