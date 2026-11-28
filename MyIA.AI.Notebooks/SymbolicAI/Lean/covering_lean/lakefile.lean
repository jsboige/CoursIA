import Lake
open Lake DSL

-- Jalon 3 de #27477 (Greffe B) : consommateur epingle du paquet `covering`
-- de jamesyc/covering. Lake lit le paquet dans la racine du depot amont, au
-- commit epingle : aucun module amont n'est copie ni adapte.
--
-- Le toolchain suit le paquet amont (v4.35.0-rc3, qui epingle Mathlib au
-- meme tag). C'est une decision mesuree, pas un contournement : notre lac
-- `formal_logic_lean` est en 4.33.x, et un retour a 4.33.x pour ce seul
-- besoin demanderait de porter tout le corpus amont (le meme raisonnement que
-- pour le lac `busybeaver_lean`, jalon 2). Les deux lakes restent donc
-- independants, chacun avec son toolchain.
--
-- Le paquet amont declare trois bibliotheques : `Covering` (la preuve),
-- `Challenge` (les enonces, avec `sorry`) et `Solution` (les memes enonces
-- prouves, pour la soumission Palomar). Le consommateur n'en importe qu'une,
-- `Covering`, et interroge le module de son propre pour l'audit d'axiomes.
package «covering_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «covering» from git
  "https://github.com/jamesyc/covering.git" @ "e28962cff844f155ca5a5cfb22563083369b490e"

@[default_target]
lean_lib «CoveringConsumer» where
