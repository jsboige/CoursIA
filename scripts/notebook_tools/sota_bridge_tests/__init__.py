"""Reusable vector comparison helpers for SOTA bridge tests.

Issue #11058 : « Ponts SOTA : comparer les vecteurs from-scratch <-> oracle, pas
des constantes attendues. »  Pattern livre in-cell sur GT-14 DifferentialGames
(PR #11074, lane myia-po-2024:CoursIA-2, 2026-08-15).  Ce module extrait le
pattern en helper reutilisable pour tout futur pont SOTA (nashpy, Gambit,
OR-Tools, pyspiel, Z3, QuikGraph, etc.).

Conventions :
- deux vecteurs numpy-like de meme longueur ;
- une tolerance declaree, pas une const hardcodee ;
- sortie structuree exploitable comme verdict machine (status, distance, indices)
  ET lisible humain (resume).
"""
