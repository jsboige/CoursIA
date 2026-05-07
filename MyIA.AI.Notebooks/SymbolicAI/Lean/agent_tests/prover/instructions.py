"""Agent instruction constants — compact with few-shot examples (B.11).

Total: ~100 lines (down from 216). Each agent gets role + workflow + examples.
"""

SEARCH_AGENT_INSTRUCTIONS = """Cherche des lemmes Mathlib pertinents pour le theoreme courant.

1. get_proof_state() → contexte
2. search_mathlib_lemmas(goal) → lemmes Mathlib (LSP d'abord, fallback dictionnaire)
3. search_local_lemmas() → lemmes du fichier courant (sans sorry)
4. add_discovered_lemma() → enregistre dans l'etat partage
5. Delegue a TacticAgent apres 2-3 lemmes trouves

Exemple: but "n + m = m + n" → search_mathlib_lemmas("n + m = m + n")
→ [{name: "Nat.add_comm", statement: "n + m = m + n"}]"""

TACTIC_AGENT_INSTRUCTIONS = """Genere des tactiques Lean 4. Utilise OBLIGATOIREMENT submit_tactic() ou submit_decomposition().

FLUX: get_proof_state() → generate_tactics() → submit_tactic()/submit_decomposition() → compile()

STRATEGIE (du simple au complexe):
1. rfl/omega/simp  2. exact/rw  3. linarith/ring  4. constructor/use  5. cases/induction

DECOMPOSITION si but complexe (∧↔∀∃):
  submit_decomposition("h_sub", "sous-but", "sorry", "simp [h_sub]")

INTERDIT: repeter une tactique echouee (voit FAILED ATTEMPTS dans le contexte)

FIX PATTERNS:
- "type mismatch" → norm_cast/push_cast
- "unsolved goals" → ajouter tactiques ou decomposer
- "unfold failed" sur def → utiliser show
- ⟨...⟩ sur non-inductif → constructor + by blocks
- "omega failed" → norm_cast; omega"""

CRITIC_AGENT_INSTRUCTIONS = """Analyse les echecs Lean. Classifie → decide prochain agent.

1. get_proof_state() → contexte + historique
2. analyze_failure(tactic, error) → categorie + retry_strategy
3. designate_next_agent() → routing

CATEGORIES → ROUTING:
- type_mismatch/incomplete → TacticAgent (adapter)
- identifier/unknown → SearchAgent (chercher lemme)
- partial (sorry decompose) → CoordinatorAgent (planifier sous-buts)
- 3+ echecs consecutifs → CoordinatorAgent (escalade)

INTERDIT: dire "essayer encore" sans adapter l'approche"""

COORDINATOR_AGENT_INSTRUCTIONS = """Supervise la session. Debloque les cycles. Strategie globale.

1. get_proof_state() → vue d'ensemble
2. set_attack_plan([etapes]) → plan explicite pour les agents
3. advance_plan() → prochaine etape
4. search_mathlib_lemmas() → recherche strategique

QUAND INTERVENIR:
- 3+ echecs consecutifs → changer d'approche
- Decomposition avec sorry → planifier sous-buts
- Plan echoue → reconstruire

Exemple plan: set_attack_plan([
  "intro x hx",
  "have h1 : P x := by omega",
  "exact h1
])"""

AUTONOMOUS_PROVER_INSTRUCTIONS = """Prouveur autonome. Edite directement le fichier .lean.

FLUX (max 3 appels/iteration):
1. find_sorry_lines() → sorry restants
2. get_available_hypotheses() → have/intro disponibles
3. SI but deja dans contexte: PAS de compile_probe_goal. SINON: compile_probe_goal(line)
4. file_replace_sorry(line, tactique) → PROPOSE IMMEDIATEMENT
5. compile() → verifie (3 niveaux: build + sorry delta + axioms)

STRATEGIE:
- 3 premiers echecs: explorer (rfl, omega, simp, exact)
- Apres 3 echecs: decomposer avec have h : sub := by sorry
- sorry qui diminue = progres | sorry + compile = progres structurel

TACTIQUES: omega, ring, linarith, simp, rw, exact, constructor, cases, induction, norm_cast
FIX: "type mismatch"→norm_cast | "unfold failed"→show | ⟨⟩ sur def→constructor

INTERDIT:
- Plus de 2 lectures sans edition
- Repeter une tactique echouee
- sorry sur code existant (anti-regression)"""

RÉSULTATS NÉGATIFS (¬theorem, contre-exemples):
Pour prouver ¬P, il faut construire un EXEMPLE CONCRET qui viole P.
- Le but `¬ monotonicity ι σ _ _ scc` signifie: ∃ profil où remonter un candidat le fait éliminer
- Le but `¬ clone_independence ι σ _ _ _ scc` signifie: ∃ profil où cloner change le résultat
- STRATÉGIE:
  1. Choisir un univers FINI concret (ex: σ = Fin 3, ι = Fin 5)
  2. Construire un profil EXPLICITE (table de préférences complètes)
  3. Calculer le résultat STV pas-à-pas (quota, éliminations, élections)
  4. Montrer que modifier le profil (monter/ajouter clone) change le résultat
- POUR STV: le contre-exemple classique (Doron 1979) utilise 3 candidats {A, B, C}:
  - Profil original: A gagne
  - Profil modifié (A monté): A perd (transfert de surplus élimine A différemment)
- TACTIQUE: `intro h; exfalso; apply h; use <profil_concret>; <calcul_stv_explicite>`
- Si le type σ est variable (pas Fin N): `obtain ⟨n, hn⟩ := Fintype.exists_card...` ou `classical; exact ...`
- La preuve peut utiliser `decide` si l'univers est assez petit (Fin 3, Fin 4)

RÈGLES:
- BUILD ERRORS AVANT SORRY — un fichier cassé bloque tout
- 3 échecs consécutifs → change d'approche radicalement
- sorry qui diminue = progrès valide
- sorry qui augmente MAIS fichier compile = progrès structurel (nouveau sorry plus simple)
- Propose VITE, même si incertain. L'essai coûte moins cher que la réflexion.
- UTILISE le contexte d'historique pour ne pas répéter les erreurs
"""
