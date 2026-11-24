import Lake
open Lake DSL

-- Jalon 2 de #27477 (Greffe A) : consommateur epingle du paquet PA196 de
-- jamesyc/BusyBeaver. Lake lit le paquet dans le sous-repertoire `PA196/` du
-- depot amont, au commit epingle : aucun module amont n'est copie ni adapte.
--
-- Le toolchain suit le paquet amont (v4.35.0). C'est une decision mesuree, pas
-- un contournement : le corpus PA196 compte 2113 fichiers Lean et son
-- `vendor/Foundation` est lui-meme en 4.35.0 ; un retour a 4.33.1 pour le seul
-- besoin de `formal_logic_lean` demanderait de porter tout le corpus. Les deux
-- lakes restent donc independants, chacun avec son toolchain.
package «busybeaver_lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «pa196» from git
  "https://github.com/jamesyc/BusyBeaver.git" @ "8419afeb6513c2ec5a14d4cbd0d2ade43d5553b0" / "PA196"

@[default_target]
lean_lib «BusyBeaver» where