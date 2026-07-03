/-
  Cibles de calibration pour le prouveur Lean multi-agent (Epic #1452).

  Chaque théorème exerce un chemin spécifique du harnais :
  - P1 : détection d'absence de progrès (agents bloqués)
  - P2 : diagnostic d'erreur distante
  - P3 : liste de blocage d'identifiants fantômes (recherche de lemmes Mathlib inexistants)

  Difficulté cible : 3-10 itérations du prouveur (zone de Goldilocks).

  ---
  English:
  Calibration targets for the multi-agent Lean prover (Epic #1452).

  Each theorem exercises a specific harness path:
  - P1: no-progress detection (stuck agents)
  - P2: distant-error diagnosis
  - P3: phantom-identifier blocklist (searches for nonexistent Mathlib lemmas)

  Target difficulty: 3-10 prover iterations (Goldilocks zone).
-/
import Calibration.Nash
import Calibration.Nim
import Calibration.Doomsday
