/-
Conway hommage: accessible formalizations of lesser-known results
by John Horton Conway (1937-2020).

John Conway was taken by COVID-19 on April 11, 2020.
This workspace formalizes some of his elegant lesser-known results.

Noix 1: Doomsday algorithm (day-of-week calculation)
Noix 2: Look-and-Say sequence (audioactive decay)
Noix 3: FRACTRAN universal machine

Calibration track (Epic #1453): Nim/Sprague-Grundy + Doomsday/Look-and-Say
lemmas as a prover-harness difficulty gradient (sorry scaffolding, intentional).
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
import Conway.Life.LightCone
import Conway.Life.Pillars
import Conway.KochenSpecker
import Conway.FreeWillTheorem
import Conway.MathlibMap
import Conway.CollatzLike
