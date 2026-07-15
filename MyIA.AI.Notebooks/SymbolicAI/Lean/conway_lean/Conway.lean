/-
Conway hommage : formalisations accessibles de résultats méconnus
de John Horton Conway (1937-2020).

John Conway a été emporté par la COVID-19 le 11 avril 2020.
Ce workspace formalise quelques-uns de ses élégants résultats méconnus.

Noix 1 : algorithme du Doomsday (calcul du jour de la semaine)
Noix 2 : suite Look-and-Say (désintégration audioactive)
Noix 3 : machine universelle FRACTRAN (encode tout programme en une liste
         de fractions ; le temps de calcul est le numérateur)
Noix 4 : Jeu de la Vie (automate cellulaire 2D, familles de structures :
         oscillateurs, vaisseaux, canons ; calcul rapide par Hashlife)

Calibration track (Epic #1453) : Nim/Sprague-Grundy + Doomsday/Look-and-Say
servent de gradient de difficulté pour le prouveur multi-agent (sorry
intentionnels comme échelle de calibration ; voir aussi
`Conway.DoomsdayLemmas` et `Conway.LookAndSayLemmas`).

Substance réelle :
- `Conway.Doomsday` + `Conway.DoomsdayLemmas` : algorithme du Doomsday
  (Conway 1973 *Tomorrow is the Day After Doomsday*) — calcul mental
  rapide du jour de la semaine pour toute date du calendrier grégorien.
- `Conway.LookAndSay` + `Conway.LookAndSayLemmas` : suite audioactive
  (Conway 1986 *The Weird and Wonderful Chemistry of Audioactive Decay*),
  suite de Conway (1, 11, 21, 1211, 111221, 312211, ...), preuve que
  les chiffres se stabilisent asymptotiquement (théorème de Conway).
- `Conway.Fractran` + `Conway.FractranLemmas` : FRACTRAN, langage
  ésotérique inventé par Conway (1987 *FRACTRAN: A Simple Universal
  Programming Language for Arithmetic*) — toute machine de Turing peut
  être encodée comme une liste de fractions, l'exécution est la
  multiplication répétée par la première fraction applicable.
- `Conway.Nim` : Nim (jeu combinatoire impartial) — preuve de
  Sprague-Grundy (1935 / 1946) que toute position a une valeur Grundy
  entière et que la stratégie gagnante est déterministe.
- `Conway.Life` (+ 12 sous-modules Life) : Jeu de la Vie de Conway
  (1970 *The Game of Life* dans Scientific American, M. Gardner). Calcul
  rapide par Hashlife (Hashing + Lifetime, Bill Gosper 1984) ; preuve
  de correction `HashlifeCorrectness` + bornes de complexité
  (`HashlifeMarginDemo`, `LightCone`, `Pillars`).
- `Conway.KochenSpecker` + `Conway.FreeWillTheorem` : théorème
  Kochen-Specker (1967) et théorème du libre arbitre de Conway-Kochen
  (2006 *The Free Will Theorem*) — résultats profonds sur la
  non-contextualité et le déterminisme en mécanique quantique.
- `Conway.CollatzLike` : généralisations de type Collatz (3n+1) — la
  conjecture de Syracuse reformalisée en Lean.
- `Conway.Angel` : problème de l'Ange de Conway (J. Conway 1996 / 2002
  *Angel Problem*, résolu 2006 par Máthé, complétion 2017 par
  Bowditch) — peut-on piéger un Ange dans un jeu de type évitement ?
- `Conway.MathlibMap` : table de correspondance entre les concepts
  formalisés ici et les modules Mathlib 4 sous-jacents.

Ce workspace est un hommage pédagogique à un mathématicien extraordinairement
fécond et créatif. Tous les `sorry` ne sont pas comblés — la plupart sont
des échafaudages intentionnels pour le prouveur multi-agent (cf. Epic #1453).

Convention i18n (EPIC #4980 ratifiée user 2026-07-04) : ce fichier est le
jumeau FR canonique du root aggregator. Le miroir EN vit dans le fichier
jumeau `Conway_en.lean` (sibling pair pattern, cf. PR #6682
`Knots.lean` ↔ `Knots_en.lean` pour knot_lean). Les modules substantiels
habitent les fichiers siblings `Conway.X` (FR) et `Conway.X_en` (EN), auto-
découverts par le `globs := #[.submodules `Conway, `Conway_en]` du lakefile.
-/
import Conway.Doomsday
import Conway.LookAndSay
import Conway.Fractran
import Conway.Nim
import Conway.DoomsdayLemmas
import Conway.LookAndSayLemmas
import Conway.Angel
import Conway.Life
import Conway.Life.GridCanonical
import Conway.Life.Spaceships
import Conway.Life.Oscillators
import Conway.Life.RLE
import Conway.Life.MacroCell
import Conway.Life.Hashlife
import Conway.Life.Computation
import Conway.Life.HashlifeCorrectness
import Conway.Life.HashlifeMemo
import Conway.Life.HashlifeMarginDemo
import Conway.Life.ConeGeometry
import Conway.Life.LightCone
import Conway.Life.Pillars
import Conway.KochenSpecker
import Conway.FreeWillTheorem
import Conway.MathlibMap
import Conway.CollatzLike
