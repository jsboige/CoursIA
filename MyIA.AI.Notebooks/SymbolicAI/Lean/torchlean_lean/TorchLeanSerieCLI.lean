/-
CLI `lake exe torchlean_serie` (issue #21053) : vérification croisée Lean/Python.

Le carnet Lean-11b exporte le `state_dict` PyTorch de son `SimpleBinaryClassifier`
en JSON (`fc1.weight`, `fc1.bias`, `fc2.weight`, `fc2.bias`) ; ce CLI le recharge
via `Import.PyTorch.MLP.load`, exécute la même chaîne IBP que le module
`TorchLeanSerie` sur les poids importés, et affiche bornes et certificat.

Usage :
- `lake exe torchlean_serie reports [epsilon]` : imprime les rapports IBP, CROWN
  et l'aperçu d'export PyTorch du classifieur du module.
- `lake exe torchlean_serie <chemin/vers/state_dict.json> [epsilon]` : charge un
  `state_dict` PyTorch exporté par le carnet Lean-11b et rejoue la chaîne IBP.

Pourquoi un exécutable et pas un `#eval` dans le carnet : l'interpréteur de Lean
ne résout pas les primitives `@[extern]` de la Storage TorchLean — mesuré le
2026-10-20, `ibpReport`, `crownReport` et `exportReport` y tuent le processus sur
« Could not find native implementation of external declaration
'TorchLean.Storage.Internal.floatBufferAppendSliceNative' ». Le binaire lié, lui,
les résout (c'est son code natif) : passer par lui n'est pas un contournement,
c'est le runtime supporté.
-/

import TorchLeanSerie
import NN.Runtime.PyTorch.Import.MLP

open TorchLean
open _root_.Spec
open TorchLeanSerie

/-- Exécute la chaîne IBP sur des paramètres importés et affiche le résultat. -/
def verifyImportedParams
    (params : nn.State Float TorchLeanSerie.paramShapes)
    (x0t : TorchLean.Tensor Float TorchLeanSerie.xShape) (eps : Float) : IO Unit := do
  let outB ← ibpOutputBox (α := Float) params x0t eps
  let lo0 : Float := getAtOrZero outB.lo [0]
  let hi1 : Float := getAtOrZero outB.hi [1]
  IO.println s!"output box lo: {pretty outB.lo}"
  IO.println s!"output box hi: {pretty outB.hi}"
  if lo0 > hi1 then
    IO.println s!"IBP certificate: class 0 certified (margin {lo0 - hi1})"
  else
    IO.println s!"IBP certificate: NOT certified (gap {lo0 - hi1})"

/-- Un rapport nommé du module. Le carnet Lean-11 en affiche un par cellule
(`report ibp 0.01`), ce qui garde la granularité pédagogique du `#eval` d'origine
tout en passant par le binaire lié. -/
def report (name : String) (eps : Float) : IO Unit := do
  match name with
  | "ibp" => IO.println (← ibpReport eps)
  | "crown" => IO.println (← crownReport eps)
  | "cert" => IO.println (← certificateReport eps)
  | "export" => IO.println (← exportReport)
  | _ => throw (IO.userError
      s!"rapport inconnu : {name} (attendu : ibp, crown, cert, export)")

/-- Imprime les quatre rapports du module d'un coup (sonde de la chaîne
complète) : IBP, CROWN, certificat et aperçu d'export PyTorch. -/
def reports (eps : Float) : IO Unit := do
  IO.println s!"--- IBP (eps = {eps}) ---"; IO.println (← ibpReport eps)
  IO.println s!"--- CROWN (eps = {eps}) ---"; IO.println (← crownReport eps)
  IO.println s!"--- certificat (eps = {eps}) ---"; IO.println (← certificateReport eps)
  IO.println "--- export PyTorch (apercu) ---"; IO.println (← exportReport)

/-- Un nombre nu ("0.1") est du JSON valide ; on suit l'idiome du paquet
(`parseTensor` : match sur le constructeur `.num`, cf Import/Core.lean). -/
def parseEps (epsStr : String) : IO Float :=
  match Lean.Json.parse epsStr with
  | .ok (.num n) => pure n.toFloat
  | _ => throw (IO.userError s!"epsilon invalide : {epsStr}")

/-- Dernier segment d'un chemin, quel que soit le séparateur.

Le CLI n'imprime **jamais** le chemin absolu qu'on lui passe : sa sortie est
recopiée telle quelle dans un carnet committé, où un chemin de machine est un
défaut (ratchet `MACHINE_PATH`, `scripts/notebook_tools/check_output_failure_text.py`).
Le nom du fichier suffit à ce que l'appelant reconnaisse son entrée. -/
def baseName (p : String) : String :=
  match ((p.splitOn "/").flatMap (·.splitOn "\\")).reverse with
  | last :: _ => last
  | [] => p

/-- Imprime les valeurs des trois tenseurs de l'exemple 1 du carnet Lean-11.

Le `#eval Spec.pretty …` correspondant ne peut pas les imprimer : `pretty`
passe par `Tensor.unstack`, donc par le tampon natif `@[extern]` de la Storage,
que l'interpréteur ne résout pas. Le binaire lié l'exécute — c'est le runtime
supporté du paquet (voir l'en-tête de ce module). Les définitions sont celles
du carnet, à l'identique. -/
def printTensors : IO Unit := do
  let v3 : TorchLean.Tensor Float [3] :=
    (Tensor.from (#[1.0, 2.0, 3.0] : Array Float)).reshape [3] (by dsimp; decide)
  let m23 : TorchLean.Tensor Float [2, 3] :=
    (Tensor.from (#[1.0, 2.0, 3.0, 4.0, 5.0, 6.0] : Array Float)).reshape
      [2, 3] (by dsimp; decide)
  IO.println s!"v3  = {pretty v3}"
  IO.println s!"m23 = {pretty m23}"
  IO.println s!"w1  = {pretty w1}"

/-- Imprime les valeurs de l'exemple 2 du carnet Lean-11 : couche Linear réelle
(`fc1`), ReLU, puis forward complet — même raison que `printTensors`. Le point
nominal et les poids sont ceux de `TorchLeanSerie` et du carnet Lean-11b. -/
def printLayer : IO Unit := do
  -- Annoter `[2]` en littéral : `TorchLeanSerie.xShape` est un `def`, et la
  -- synthèse d'instance ne le déplie pas — `Shape.EndsWith 2 xShape` échoue,
  -- alors qu'elle réussit sur la forme littérale (même type par définition).
  let x0 : TorchLean.Tensor Float [2] := x0Tensor
  let fc1 : TorchLean.Tensor Float [4] := x0.linear w1 b1
  let h : TorchLean.Tensor Float [4] := fc1.relu
  let out : TorchLean.Tensor Float [2] := h.linear w2 b2
  IO.println s!"fc1       = {pretty fc1}"
  IO.println s!"relu(fc1) = {pretty h}"
  IO.println s!"forward   = {pretty out}"

def main (args : List String) : IO Unit := do
  match args with
  | ["reports"] => reports 0.1
  | ["reports", epsStr] => reports (← parseEps epsStr)
  | ["report", name] => report name 0.1
  | ["report", name, epsStr] => report name (← parseEps epsStr)
  | ["print", "tensors"] => printTensors
  | ["print", "layer"] => printLayer
  | [jsonPath] => run jsonPath 0.1
  | [jsonPath, epsStr] => run jsonPath (← parseEps epsStr)
  | _ => throw (IO.userError
      "usage: torchlean_serie report <ibp|crown|cert|export> [epsilon] | reports [epsilon] | print <tensors|layer> | <state_dict.json> [epsilon]")
where
  run (jsonPath : String) (eps : Float) : IO Unit := do
    -- `IO.FS.readFile` rend le chemin absolu dans son exception : on la capte
    -- pour la même raison que `baseName` ci-dessus (aucun chemin de machine
    -- dans une sortie de carnet, y compris sur le chemin d'échec).
    let txt ←
      try IO.FS.readFile ⟨jsonPath⟩
      catch _ => throw (IO.userError
        s!"lecture impossible : {baseName jsonPath} (fichier absent ou illisible)")
    match Lean.Json.parse txt with
    | .error e => throw (IO.userError s!"JSON illisible ({e}) : {baseName jsonPath}")
    | .ok json =>
      match Import.PyTorch.MLP.load 2 4 2 json with
      | none => throw (IO.userError
          "state_dict incompatible avec le format MLP 2-4-2 (cles attendues : fc1.weight, fc1.bias, fc2.weight, fc2.bias)")
      | some p =>
        let params : nn.State Float TorchLeanSerie.paramShapes :=
          nn.State.empty
            |>.push p.inputWeight
            |>.push p.inputBias
            |>.push p.outputWeight
            |>.push p.outputBias
        IO.println s!"state_dict charge depuis {baseName jsonPath} (MLP 2-4-2)"
        verifyImportedParams params x0Tensor eps
