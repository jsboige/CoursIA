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

---

English: Conway tribute — accessible formalizations of lesser-known results
by John Horton Conway (1937-2020).

John Conway was taken by COVID-19 on April 11, 2020.
This workspace formalizes some of his elegant lesser-known results.

Nut 1: Doomsday algorithm (day-of-week calculation)
Nut 2: Look-and-Say sequence (audioactive decay)
Nut 3: FRACTRAN universal machine (encodes any program as a list of
       fractions; running time is the numerator)
Nut 4: Game of Life (2D cellular automaton, structure families:
       oscillators, spaceships, guns; fast computation via Hashlife)

Calibration track (Epic #1453): Nim/Sprague-Grundy + Doomsday/Look-and-Say
lemmas as a prover-harness difficulty gradient (intentional sorry as
a calibration scale; see also `Conway.DoomsdayLemmas` and
`Conway.LookAndSayLemmas`).

Substance (English):
- `Conway.Doomsday` + `Conway.DoomsdayLemmas`: Doomsday algorithm
  (Conway 1973 *Tomorrow is the Day After Doomsday*) — fast mental
  calculation of the day of the week for any Gregorian calendar date.
- `Conway.LookAndSay` + `Conway.LookAndSayLemmas`: audioactive decay
  (Conway 1986 *The Weird and Wonderful Chemistry of Audioactive Decay*),
  Conway sequence (1, 11, 21, 1211, 111221, 312211, ...), proof that
  digits stabilize asymptotically (Conway's theorem).
- `Conway.Fractran` + `Conway.FractranLemmas`: FRACTRAN, esoteric
  language invented by Conway (1987 *FRACTRAN: A Simple Universal
  Programming Language for Arithmetic*) — any Turing machine can be
  encoded as a list of fractions; execution is repeated multiplication
  by the first applicable fraction.
- `Conway.Nim`: Nim (impartial combinatorial game) — Sprague-Grundy
  proof (1935 / 1946) that every position has an integer Grundy value
  and that the winning strategy is deterministic.
- `Conway.Life` (+ 12 Life sub-modules): Conway's Game of Life
  (1970 *The Game of Life* in Scientific American, M. Gardner). Fast
  computation via Hashlife (Hashing + Lifetime, Bill Gosper 1984);
  correctness proof `HashlifeCorrectness` + complexity bounds
  (`HashlifeMarginDemo`, `LightCone`, `Pillars`).
- `Conway.KochenSpecker` + `Conway.FreeWillTheorem`: Kochen-Specker
  theorem (1967) and Conway-Kochen Free Will Theorem (2006 *The Free
  Will Theorem*) — deep results on non-contextuality and determinism
  in quantum mechanics.
- `Conway.CollatzLike`: Collatz-type generalizations (3n+1) — Syracuse
  conjecture reformalized in Lean.
- `Conway.Angel`: Conway's Angel problem (J. Conway 1996 / 2002
  *Angel Problem*, solved 2006 by Máthé, completion 2017 by Bowditch)
  — can an Angel be trapped in an avoidance-type game?
- `Conway.MathlibMap`: correspondence table between the concepts
  formalized here and the underlying Mathlib 4 modules.

This workspace is a pedagogical tribute to an extraordinarily prolific
and creative mathematician. Not all `sorry`s are filled — most are
intentional scaffolds for the multi-agent prover (cf. Epic #1453).

Convention i18n (EPIC #4980 ratifiée user 2026-07-04) : ce fichier root
aggregator est bilingue inline (FR canonique d'abord, EN en miroir),
conformément au pattern canonique `CooperativeGames.lean` (PR #5883,
pilote EPIC), `Utility.lean` (PR #6045), `RepeatedGames.lean` (PR #6048),
`Minimax.lean` (PR #6101), `SocialChoice.lean` (PR #6106). Les modules
substantiels vivent dans des fichiers siblings (cf. structure lake ci-dessous),
auto-découverts par le `globs := #[`Conway.*`, `Conway.Life.*`]` du lakefile.
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
import Conway.Life.LightCone
import Conway.Life.Pillars
import Conway.KochenSpecker
import Conway.FreeWillTheorem
import Conway.MathlibMap
import Conway.CollatzLike
