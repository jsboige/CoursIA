/-
  Cibles de calibration pour le prouveur Lean multi-agent (Epic #1452).

  Chaque théorème exerce un chemin spécifique du harnais :
  - P1 : détection d'absence de progrès (agents bloqués)
  - P2 : diagnostic d'erreur distante
  - P3 : liste de blocage d'identifiants fantômes (recherche de lemmes Mathlib inexistants)

  Difficulté cible : 3-10 itérations du prouveur (zone de Goldilocks).

  Convention i18n #4980 (sibling pair) : cette racine est FR-seule canonique,
  le jumeau anglais agrégateur est `Calibration_en.lean`.
-/
import Calibration.Nash
import Calibration.Nim
import Calibration.Doomsday
