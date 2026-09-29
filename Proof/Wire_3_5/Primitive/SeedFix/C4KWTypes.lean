import Proof.Wire_3_5.Primitive.SeedFix.C4KW
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4

/-! # C4KW: the three docks in the HASH setup (types, for the assembly)

P3:3011-3016 (the setup before the loop) and P3:2253-2290 (the Hb printer's static words): on the HASH setup's bank
`3 + x` (`setupH`), three stages on fresh regions, each a machine with every head `0 → 0`, a cost, and a region
contract (tape indices are parameters):

* **`DataRerun`** (T-a): the v4 data stage `S.M3` (from any run of it at the request) and the copy-in `cpZ`, docked on
  the region `[oD, oD + drN S)`, the request, `1^n`, `1^L`, `1^W` on `t0, tN, tL, tD` below it: the call's counts
  `unaryList cs` on the region's tape `oD + drTU S`, the request kept, every tape outside the region and `tN, tL, tD`
  unchanged.
* **`KwDock`** (T-b): the kept words writer `KWW` docked with its outputs on `oK + j`, its inputs on `kIn i < oK`, its
  scratch on `oK + 94 + k`: the framed kept words on `oK + j`, every tape outside the region unchanged, the scratch
  falses.
* **`QCopy`** (T-c): `1^q` from `src < oQ` copied to `oQ`, every tape outside `[oQ, oQ + 3)` unchanged, the two scratch
  tapes falses, within `qCost q = 10q + 10`.

Paper quantities of the main types: the setup's counts, the Hb printer's static words `KW`, the compiler request's
`1^{Q'}` (P3:3011-3016). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.PrimT.C4H NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.Data (DS DR sIN sNT sLT sCT sOUT rawIn dataWord unaryList)

noncomputable section

/-! ## T-b: the kept words writer, docked -/

/-- The writer's tapes on the bank: outputs `oK + j`, inputs `kIn i`, scratch `oK + 94 + k`. -/
def kwSl (W : KWW) (x oK : ℕ) (hK : oK + 94 + W.x ≤ 3 + x) (kIn : Fin 12 → Fin (3 + x)) :
    Fin (94 + 12 + W.x) → Fin (3 + x) :=
  Fin.addCases (Fin.addCases (fun j : Fin 94 => ⟨oK + j.val, by omega⟩) kIn)
    (fun k : Fin W.x => ⟨oK + 94 + k.val, by omega⟩)

/-- **T-b's machine**: the writer docked by `kwSl`. -/
def kwDockM (W : KWW) (x oK : ℕ) (hK : oK + 94 + W.x ≤ 3 + x) (kIn : Fin 12 → Fin (3 + x)) :=
  RecoveryFocus.machine (kwSl W x oK hK kIn) W.M

/-- **T-b's contract**: from the inputs on `kIn` and the region `[oK, oK + 94 + W.x)` blank, the framed kept words on
`oK + j`, every tape outside the region unchanged (the inputs included), the region's scratch falses. -/
def KwDock (W : KWW) (x oK : ℕ) (hK : oK + 94 + W.x ≤ 3 + x) (kIn : Fin 12 → Fin (3 + x)) : Prop :=
  Function.Injective kIn → (∀ i, (kIn i).val < oK) →
  ∀ (D : HashData) (cap : ℕ) (B : Fin (3 + x) → List Bool), (∀ i, B (kIn i) = kwIns D cap i) →
    (∀ i : Fin (3 + x), oK ≤ i.val → i.val < oK + 94 + W.x → B i = []) →
    ∃ B' : Fin (3 + x) → List Bool, Step (kwDockM W x oK hK kIn) (W.cost D cap) (fun _ => 0) B (fun _ => 0) B' ∧
      (∀ j : Fin 94, B' ⟨oK + j.val, by omega⟩ = frame (kw D cap j)) ∧
      (∀ i : Fin (3 + x), (i.val < oK ∨ oK + 94 + W.x ≤ i.val) → B' i = B i) ∧
      (∀ i : Fin (3 + x), oK + 94 ≤ i.val → i.val < oK + 94 + W.x →
        ∃ m ≤ W.cost D cap, B' i = List.replicate m false)

/-! ## T-c: the copy of `1^{Q'}` -/

/-- Copy the unary word on stream `0` onto stream `1`. -/
def qW : WM 1 0 := .whs 0 (.seq (.wr 1 true) (.seq (.fwd 1) (.fwd 0)))

/-- The copy under the masked reset (tapes: the source, the cell, the copy, the log). -/
def qM := MaskedReset.machine qW.toProg.compile (fun _ => true)

/-- The copy's tapes on the bank: the source `src`, the copy `oQ`, the cell `oQ + 1`, the log `oQ + 2`. -/
def qSl (x oQ : ℕ) (hQ : oQ + 3 ≤ 3 + x) (src : Fin (3 + x)) (j : Fin (1 + 2 + 0 + 1)) : Fin (3 + x) :=
  if j.val = 0 then src else ⟨oQ + (if j.val = 2 then 0 else if j.val = 1 then 1 else 2), by split_ifs <;> omega⟩

/-- **T-c's machine**. -/
def qDockM (x oQ : ℕ) (hQ : oQ + 3 ≤ 3 + x) (src : Fin (3 + x)) := RecoveryFocus.machine (qSl x oQ hQ src) qM

/-! ## T-a: the data stage's re-run and the copy-in -/

variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}

/-- The data stage's tape count. -/
abbrev drM3 (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) : ℕ := DS + 2 + DR + 1 + S.x3

/-- T-a's region size: the data stage's tapes, then the copy-in's cell, output and log. -/
abbrev drN (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) : ℕ := drM3 S + 3

/-- The region offset of the counts' tape. -/
abbrev drTU (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) : ℕ := drM3 S + 1

/-- The data stage's tapes on the bank: its request, `1^n`, `1^L`, `1^W` streams on `t0, tN, tL, tD`, every other
tape `j` on `oD + j`. -/
def drSl (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (x oD : ℕ) (hD : oD + drN S ≤ 3 + x)
    (t0 tN tL tD : Fin (3 + x)) (j : Fin (drM3 S)) : Fin (3 + x) :=
  if j.val = 0 then t0 else if j.val = 2 then tN else if j.val = 3 then tL else if j.val = 4 then tD
  else ⟨oD + j.val, by have := j.isLt; have : drN S = drM3 S + 3 := rfl; omega⟩

/-- The copy-in's tapes on the bank: the data word's tape `oD + 6` (the data stage's `sOUT`), then the region's last
three tapes (the cell, the counts, the log). -/
def cpSl (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (x oD : ℕ) (hD : oD + drN S ≤ 3 + x)
    (j : Fin (1 + 2 + 0 + 1)) : Fin (3 + x) :=
  ⟨if j.val = 0 then oD + 6 else oD + drM3 S + (j.val - 1), by
    have := j.isLt; have : drN S = drM3 S + 3 := rfl; have : drM3 S = DS + 2 + DR + 1 + S.x3 := rfl
    have : DS = 9883 := rfl; split_ifs <;> omega⟩

/-- **T-a's machine**: the data stage, then the copy-in. -/
def drM (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (x oD : ℕ) (hD : oD + drN S ≤ 3 + x)
    (t0 tN tL tD : Fin (3 + x)) :=
  Composition.machine (RecoveryFocus.machine (drSl S x oD hD t0 tN tL tD) S.M3)
    (RecoveryFocus.machine (cpSl S x oD hD) C4Set.cpZ)

/-- **T-a's contract**: from any run of the data stage at the request `w` (its data word `dataWord cs`, its request
kept), the request, `1^n`, `1^L`, `1^W` on `t0, tN, tL, tD` (distinct, below `oD`) and the region blank, the counts
`unaryList cs` on `oD + drTU S`, the request kept on `t0`, every tape outside the region and `tN, tL, tD` unchanged. -/
def DataRerun (S : PrimAsm.ThrData.ThrDataStage4 alg Dexp capT) (x oD : ℕ) (hD : oD + drN S ≤ 3 + x)
    (t0 tN tL tD : Fin (3 + x)) : Prop :=
  t0 ≠ tN → t0 ≠ tL → t0 ≠ tD → tN ≠ tL → tN ≠ tD → tL ≠ tD → t0.val < oD → tN.val < oD → tL.val < oD →
  tD.val < oD →
  ∀ (w : List Bool) (n L W : ℕ) (cs : List ℕ) (c3 : ℕ) (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ)
    (J : Fin S.x3 → List Bool) (B : Fin (3 + x) → List Bool),
    Step S.M3 c3 (fun _ => 0)
      (Fin.addCases (m := DS + 2 + DR + 1) (n := S.x3) (motive := fun _ => List Bool)
        (Fin.addCases (rawIn w n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => []))
      (fun _ => 0)
      (Fin.addCases (m := DS + 2 + DR + 1) (n := S.x3) (motive := fun _ => List Bool)
        (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J) →
    tout (sTape sOUT) = dataWord cs → tout (sTape sIN) = frame w →
    B t0 = frame w → B tN = List.replicate n true → B tL = List.replicate L true → B tD = List.replicate W true →
    (∀ i : Fin (3 + x), oD ≤ i.val → i.val < oD + drN S → B i = []) →
    ∃ B' : Fin (3 + x) → List Bool,
      Step (drM S x oD hD t0 tN tL tD) (c3 + 1 + C4Set.cpZCost (unaryList cs)) (fun _ => 0) B (fun _ => 0) B' ∧
      B' ⟨oD + drTU S, by have : drN S = drM3 S + 3 := rfl; have : drTU S = drM3 S + 1 := rfl; omega⟩ =
        unaryList cs ∧ B' t0 = frame w ∧
      (∀ i : Fin (3 + x), i ≠ t0 → i ≠ tN → i ≠ tL → i ≠ tD → (i.val < oD ∨ oD + drN S ≤ i.val) → B' i = B i)

end

end NearCubicWires.WireExponent3_5.PrimT.C4KW
