/-
Pont de la série SymbolicAI/Lean vers le paquet réel TorchLean (issue #21053).

Les carnets Lean-11 et Lean-11b importent ce module au lieu de redéfinir des
types locaux : modèle, chaîne IBP, certificat et interop PyTorch vivent dans le
paquet public `lean-dojo/TorchLean` (namespace `TorchLean`).

Le réseau est le classifieur binaire partagé par les deux carnets :
2 -> 4 -> ReLU -> 2, poids identiques au `SimpleBinaryClassifier` de Lean-11b.
La chaîne `lowerForwardToIR / seedInputBox / runIBP / outputBox?` est celle du
workflow officiel `NN.Verification.Builtin.IBPWorkflow`, sur notre réseau.
-/

import NN
import NN.Runtime.PyTorch.Export.MLP
import NN.Runtime.PyTorch.Import.MLP

open TorchLean
open _root_.Spec
open _root_.TorchLean.Tensor

namespace TorchLeanSerie

open NN.MLTheory.CROWN.Graph
open NN.MLTheory.CROWN

/-! ## Le classifieur binaire des carnets Lean-11 / Lean-11b

Architecture 2 -> 4 -> ReLU -> 2. `nn.build 0 mkModel` instancie le graphe de
façon déterministe ; les poids réels sont poussés dans un `nn.State` séparé,
exactement comme le fait le workflow IBP de référence du paquet.
-/

/-- Largeur d'entrée du classifieur binaire partagé (Lean-11 / Lean-11b). -/
def inDim : Nat := 2
/-- Largeur cachée (4 neurones, un par coin du plan). -/
def hidDim : Nat := 4
/-- Largeur de sortie (2 classes). -/
def outDim : Nat := 2

/-- Forme d'entrée du classifieur. -/
def xShape : Spec.Shape := [2]
/-- Forme de sortie du classifieur. -/
def yShape : Spec.Shape := [2]

/-- Poids de la première couche (fc1.weight de Lean-11b) : chaque ligne
détecte un coin du plan (x1+x2, -x1+x2, x1-x2, -x1-x2). -/
def w1 : Tensor Float [4, 2] :=
  (Tensor.from (#[1, 1, -1, 1, 1, -1, -1, -1] : Array Float)).reshape
    [4, 2] (by dsimp; decide)

/-- Biais de la première couche (fc1.bias de Lean-11b). -/
def b1 : Tensor Float [4] :=
  (Tensor.from (#[0, 0, 0, 0] : Array Float)).reshape
    [4] (by dsimp; decide)

/-- Poids de la deuxième couche (fc2.weight de Lean-11b). -/
def w2 : Tensor Float [2, 4] :=
  (Tensor.from (#[1, 0.5, 0.5, 1, -0.5, -1, -1, -0.5] : Array Float)).reshape
    [2, 4] (by dsimp; decide)

/-- Biais de la deuxième couche (fc2.bias de Lean-11b). -/
def b2 : Tensor Float [2] :=
  (Tensor.from (#[0, 0] : Array Float)).reshape
    [2] (by dsimp; decide)

/-- MLP 2 -> 4 -> ReLU -> 2 : la même architecture que `SimpleBinaryClassifier`
du carnet Lean-11b. -/
def mkModel : nn.Builder (nn.Sequential xShape yShape) :=
  nn.Sequential![
    nn.linear 2 4,
    nn.relu,
    nn.linear 4 2
  ]

/-- Instanciation déterministe (seed 0) du squelette du modèle. -/
def model : nn.Sequential xShape yShape :=
  nn.build 0 mkModel

/-- Formes des paramètres attendues par `model` (W1, b1, W2, b2). -/
def paramShapes : List Spec.Shape := nn.stateShapes model

/-- Poids du classifieur poussés dans un `nn.State`, dans l'ordre de
`paramShapes` (comme dans le workflow IBP de référence du paquet). -/
def classifierParams {α : Type} [TorchLean.Storage α] [_root_.Context α]
    [Runtime.FromFloat α] : nn.State α paramShapes :=
  nn.State.empty
    |>.push (TorchLean.Tensor.map Runtime.ofFloat w1)
    |>.push (TorchLean.Tensor.map Runtime.ofFloat b1)
    |>.push (TorchLean.Tensor.map Runtime.ofFloat w2)
    |>.push (TorchLean.Tensor.map Runtime.ofFloat b2)

/-- Point nominal du carnet Lean-11b (autour duquel on certifie).

`abbrev` (et non `def`) : la preuve du `reshape [2]` doit déplier ce littéral
à l'élaboration (`dsimp` ne déplie que le réductible) — même idiome que le
workflow IBP de référence du paquet, qui reshape un littéral direct. -/
abbrev x0Array : Array Float := #[1.0, 0.5]

/-- Point nominal déjà façonné en tenseur : la preuve du `reshape [2]` vit ici,
sur le littéral (réductible via `abbrev`) — les fonctions en aval reçoivent un
tenseur déjà dimensionné, jamais un `Array` runtime à reshaper (la preuve
exigerait `.size` d'une variable libre, indécidable). -/
abbrev x0Tensor : TorchLean.Tensor Float xShape :=
  (Tensor.from x0Array).reshape [2] (by dsimp; decide)

/-! ## Chaîne IBP complète (TorchLean réel)

`lowerForwardToIR` abaisse le forward TorchLean vers le graphe IR ; `lInfBall`
construit la boîte d'entrée ; `runIBP` propage les intervalles ; `outputBox?`
relit la boîte de sortie. C'est la chaîne du `lake exe verify -- torchlean-ibp`
officiel, appliquée à notre classifieur.
-/

/-- Boîte de sortie IBP du classifieur pour une boîte L∞ de rayon `eps`
autour du tenseur nominal `x0t` (déjà façonné — cf `x0Tensor` : la preuve du
reshape vit sur le littéral, pas sur un paramètre runtime). -/
def ibpOutputBox {α : Type} [TorchLean.Storage α] [_root_.Context α] [ToString α]
    [Runtime.FromFloat α] [BoundOps α] [NonlinearBoundOps α]
    (params : nn.State α paramShapes) (x0t : TorchLean.Tensor Float xShape) (eps : Float) :
    IO (FlatBox α) := do
  let cast : Float → α := Runtime.ofFloat
  let lowered ← IO.ofExcept (
    Verification.lowerForwardToIR (α := α) model params)
  let xB : FlatBox α := NN.Verification.Builtin.lInfBall (α := α)
    (TorchLean.Tensor.map cast x0t) (cast eps)
  let ps : ParamStore α := lowered.seedInputBox xB
  let boxes := lowered.runIBP ps
  IO.ofExcept (lowered.outputBox? boxes)

/-- Nombre de noeuds du graphe IR abaissé (sonde pédagogique : on voit que le
modèle TorchLean devient un graphe de contraintes concret). -/
def loweredNodeCount {α : Type} [TorchLean.Storage α] [_root_.Context α]
    [Runtime.FromFloat α]
    (params : nn.State α paramShapes) : IO Nat := do
  let lowered ← IO.ofExcept (
    Verification.lowerForwardToIR (α := α) model params)
  return lowered.graph.nodes.size

/-- Certificat IBP du classifieur en arithmétique `Float`, avec le même critère
que le carnet Lean-11b : la classe 0 est certifiée si sa borne inférieure
dépasse la borne supérieure de la classe 1.

Retourne `(boîte de sortie, verdict, marge)`. -/
def ibpCertificate (eps : Float) : IO (FlatBox Float × Bool × Float) := do
  let outB ← ibpOutputBox (α := Float) classifierParams x0Tensor eps
  let lo0 : Float := getAtOrZero outB.lo [0]
  let hi1 : Float := getAtOrZero outB.hi [1]
  if lo0 > hi1 then
    return (outB, true, lo0 - hi1)
  else
    return (outB, false, lo0 - hi1)

/-- Rapport IBP prêt pour le carnet : boîte de sortie à rayon `eps`
autour du point nominal. -/
def ibpReport (eps : Float) : IO String := do
  let outB ← ibpOutputBox (α := Float) classifierParams x0Tensor eps
  pure s!"eps = {eps} | output lo: {pretty outB.lo} | hi: {pretty outB.hi}"

/-- Rapport de certificat prêt pour le carnet : verdict + marge certifiée
(ou écart restant si non certifié). -/
def certificateReport (eps : Float) : IO String := do
  let (_, ok, margin) ← ibpCertificate eps
  pure s!"eps = {eps} | classe 0 certifiee: {ok} | marge/écart: {margin}"

/-- Bornes CROWN du réseau : la passe CROWN (`Verification.runCROWN lowered`)
réutilise les
boîtes IBP comme bornes intermédiaires et propage des relaxations affines
(backward) ; `lowered.outputBoxCROWN?` évalue ensuite la borne affine du nœud
de sortie sur la boîte d'entrée. Retourne le nombre de noeuds couverts et les
bornes chiffrées des deux classes. -/
def crownReport (eps : Float) : IO String := do
  let cast : Float → Float := Runtime.ofFloat
  let lowered ← IO.ofExcept (
    Verification.lowerForwardToIR (α := Float) model classifierParams)
  let x0t : TorchLean.Tensor Float xShape :=
    TorchLean.Tensor.map cast x0Tensor
  let xB : FlatBox Float := NN.Verification.Builtin.lInfBall (α := Float) x0t (cast eps)
  let ps : ParamStore Float := lowered.seedInputBox xB
  let boxes := lowered.runIBP ps
  let crown ← IO.ofExcept (Verification.runCROWN lowered ps boxes)
  let covered := (crown.filter (·.isSome)).size
  let outB ← IO.ofExcept (lowered.outputBoxCROWN? ps xB)
  let lo0 : Float := getAtOrZero outB.lo [0]
  let hi0 : Float := getAtOrZero outB.hi [0]
  let lo1 : Float := getAtOrZero outB.lo [1]
  let hi1 : Float := getAtOrZero outB.hi [1]
  pure s!"eps = {eps} | noeuds CROWN couverts: {covered}/{crown.size} | classe 0: [{lo0}, {hi0}] | classe 1: [{lo1}, {hi1}]"

/-- Aperçu du script Python généré par le paquet (`Export.PyTorch.MLP.weights`)
pour ce classifieur : classe `SimpleBinaryClassifier` + `state_dict` embarqué,
prêt à coller dans le carnet Lean-11b. -/
def exportReport : IO String := do
  let src := Export.PyTorch.MLP.weights w1 b1 w2 b2
    (className := "SimpleBinaryClassifier")
  let preview : String :=
    (src.splitOn "\n").take 14 |>.foldl (fun acc l => acc ++ l ++ "\n") ""
  pure (preview ++ "... (" ++ toString src.length ++ " caracteres au total)")

end TorchLeanSerie
