import Lake
open Lake DSL

-- Socle KLS (Kannan-Lovasz-Simonovits) pour ANALYSE-05 (#19765, EPIC #19729).
--
-- Audit Mathlib au pin v4.32.1 (520045a, mesure le 2026-10-07 sur tous les
-- clones locaux : t1, knot11256, groth11286, calibration_lean, minimax11256) :
-- AUCUNE des notions de la chaine Bizeul-Klartag-Lehec n'y vit -- pas de
-- `IsLogConcave` (0 occurrence toutes casses confondues), pas de constante de
-- Poincare pour les mesures, pas de constante de Cheeger, pas de thin-shell.
-- Ce lake pose les premieres pierres de ce socle manquant : les DEFINITIONS
-- (mesure log-concave au sens de Borell, isotropie, constante de Poincare,
-- constante de Cheeger) plus une premiere instance prouvee (log-concavite de
-- la densite gaussienne, fonctionnelle). Les enonces de la chaine BKL
-- (Thm 1.1), Chen-Klartag (thin-shell Var |X|^2 <= 8n) et Letwin (germe
-- quadratique) restent HORS du lake tant que la preuve n'existe pas -- ils
-- vivent en prose commentee dans le carnet, jamais en `sorry`.
package «kls» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.1"

@[default_target]
lean_lib «KLS» where
  -- makeLib au lieu de globs : le socle est encore petit, chaque module
  -- ajoute doit compiler seul.
  globs := #[.one `KLS.Defs]
