import Proof.Wire_3_5.Primitive.SeedFix.C4H

/-! # C4H2 (C4H-a): the HASH contract with the Hb unit's kept words FRAMED

C4H (verified) keeps the Hb printer's 94 static words `KW = hb0 X` raw. The HASH child re-creates its working
Hb bank at every child from them, and the invariant needs the exact lists; many words end in `false` (the register
tapes, the log, the elimination's pads), and on a tape trailing falses cannot be told apart from blank, so no machine
copies them exactly. C4H-a keeps them framed: `hKN2` (`frame (KW j)` on the unit's tape `A.t + j`), `HashFamAt2`
(C4H's `HashFamAt` at `hKN2`), `HBank2` (C4H's `HBank` with `hKW : B (hkT j) = frame (KW j)`). Every other part of C4H
(`HbCaps`, `HashData`, `hbX`, `hb0`, `hKeepN`, `HashFinSpec`, `HashEAt`, C4HD's `hashDataOf`) is unchanged.

* `hKN2`, **`HashFamAt2`**, **`HBank2`**.

Paper quantity of the main types: the HASH stage's loop (the fixed hash's bits) and its inputs (`filt:soft`,
P3:2221-2336). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.C4Set

noncomputable section

/-- The kept words, by index, the Hb unit's words FRAMED (C4H-a; the prefix tape's word is the loop's). -/
def hKN2 (A : C4Iface.AsmStage) (wa : RepairRepresentation.WilliamsAlgorithm) (PRE POST : List Bool)
    (KW : Fin 94 → List Bool) (q uu : ℕ) (v : ℕ) : List Bool :=
  if v < A.t then (if v = A.pA.val then frame PRE else if v = A.pB.val then frame POST else [])
  else if h : v - A.t < 94 then (if v < A.t + HU then frame (KW ⟨v - A.t, h⟩) else [])
  else if v < A.t + HU then []
  else if v < CTH A wa then
    (if v - A.t - HU = (C4Pipe.childQQ wa).val then List.replicate q true
     else if v - A.t - HU = (C4Pipe.childUU wa).val then List.replicate uu true else [])
  else []

/-- **(i) The HASH child family** (C4H-a: the unit's kept words framed) at the interface: tapes, kept tapes and words, prefix and sum tapes, the sum's width
`W`, the `s_h` decisions, and the loop's decisions `bits`. -/
structure HashFamAt2 (A : C4Iface.AsmStage) (wa : RepairRepresentation.WilliamsAlgorithm) (PRE POST : List Bool)
    (KW : Fin 94 → List Bool) (q uu W sh : ℕ) (bits : List Bool) : Type where
  F : C4Loop.ChildFam
  ht : F.t = CTH A wa + 1
  keep : ∀ v (h : v < F.t), F.keep ⟨v, h⟩ = hKeepN A wa v
  K : ∀ v (h : v < F.t), F.K ⟨v, h⟩ = hKN2 A wa PRE POST KW q uu v
  pfx : F.PFX.val = A.t + 94
  sum : F.SUM.val = A.t + (HU + (C4Pipe.childSum wa).val)
  hW : F.W = W
  bound : F.bound = sh
  loop : SeedFix.greedyLoop F.bound F.Rv = bits

/-- **(ii) The HASH setup's exit bank** (C4H-a: the kept words framed) on its big bank `3 + x` (the layout `L` on its first `L.N` tapes):
SymBank's fields on `L` (the HASH tape on port `1`, `1^{uu}`, `1^{2^ρ}`, the compiler's fields, the log, the loop's
cells) and the 94 kept words and `1^{Q'}` on the setup's tapes `hkT`, `hqT` (off `L`'s, distinct, below `off`); the
bank blank from `off` up. -/
structure HBank2 (L : Lay) {x : ℕ} (hLx : L.N ≤ 3 + x) (B : Fin (3 + x) → List Bool) (w v PRE POST : List Bool)
    (KW : Fin 94 → List Bool) (q uu ρ : ℕ) (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x)) (off : ℕ) : Prop where
  p0 : B ⟨0, by omega⟩ = frame w
  p1 : B ⟨L.gP1.val, by omega⟩ = v
  p2 : B ⟨2, by omega⟩ = []
  hUU : B ⟨L.gUU.val, by omega⟩ = List.replicate uu true
  hRR : B ⟨L.gRR.val, by omega⟩ = List.replicate (2 ^ ρ) true
  hPRE : B ⟨L.gPRE.val, by omega⟩ = frame PRE
  hPOST : B ⟨L.gPOST.val, by omega⟩ = frame POST
  hLG : B ⟨L.gLG.val, by omega⟩ = List.replicate (2 ^ ρ + 1) false
  hmask : ∀ i : Fin L.N, L.maskLP i = true → B ⟨i.val, by omega⟩ = List.replicate (2 ^ ρ) false
  cells : ∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B ⟨i.val, by omega⟩ = []
  hKW : ∀ j, B (hkT j) = frame (KW j)
  hQ : B hqT = List.replicate q true
  kinj : Function.Injective hkT
  koff : ∀ j, L.N ≤ (hkT j).val ∧ (hkT j).val < off
  qoff : L.N ≤ hqT.val ∧ hqT.val < off ∧ ∀ j, hkT j ≠ hqT
  blank : ∀ i : Fin (3 + x), off ≤ i.val → B i = []

end

end NearCubicWires.WireExponent3_5.PrimT.C4H
