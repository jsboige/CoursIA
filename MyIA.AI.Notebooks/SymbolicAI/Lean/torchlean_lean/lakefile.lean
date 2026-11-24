import Lake
open Lake DSL

package «torchlean_serie» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Dépendance réelle TorchLean (issue #21053) : paquet public lean-dojo/TorchLean,
-- épinglé au commit mesuré b64a6fec (toolchain v4.35.0, dernier push 2026-10-15).
-- Le build par défaut n'exige ni LibTorch ni CUDA (shim « unavailable backend ») ;
-- il exige un compilateur C (cc) pour csrc/cpu/torchlean_tensor.c.
require torchlean from git
  "https://github.com/lean-dojo/TorchLean" @ "b64a6feccbeba9547e19fa902fa878c00b994dd0"

@[default_target]
lean_lib «TorchLeanSerie»

/-- CLI de vérification croisée Lean/Python (`lake exe torchlean_serie`) :
imprime les rapports IBP/CROWN/export du module, et rejoue la chaîne IBP sur un
`state_dict` PyTorch exporté en JSON par le carnet Lean-11b.

Le carnet passe par ce binaire et non par un `#eval` parce que l'interpréteur de
Lean ne résout pas les primitives `@[extern]` de la Storage TorchLean (mesure du
2026-10-20 : `ibpReport`, `crownReport` et `exportReport` y tuent le processus sur
`floatBufferAppendSliceNative`, seules les lectures pures `getAtOrZero` survivent).
`supportInterpreter` n'est pas une issue : le champ n'existe pas dans
`LeanLibConfig` en v4.35 (lake avertit « unknown field » et l'ignore), et
`precompileModules := true` fait entrer `torchlean/torchlean_allocator` (C++) dans
le graphe de la lib. -/
@[default_target]
lean_exe «torchlean_serie» where
  root := `TorchLeanSerieCLI
