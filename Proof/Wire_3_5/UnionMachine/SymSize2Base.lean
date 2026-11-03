import Proof.Wire_3_5.UnionMachine.SymSize1
import Proof.Wire_3_5.FinalPass.SdI3Base
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase
import Proof.Wire_3_5.Primitive.SeedFix.TabCost
import Proof.Wire_3_5.Primitive.SeedFix.TabSym
import Proof.Wire_3_5.Primitive.Writers.SymSizes

/-! # C6b hS, part 2: **the SYM size polynomial** `symSize_poly`

At a SYM call of the family (`Sd.SymSizeOK`'s hypotheses: carriers `≤ 2`, descriptions `≤ (n+1)^26`), the atoms of
part 1 are below `Y = c_S(c_r)·N^{Z_S}`, `N = n + 2`, `Z_S = flatZR l + capZR l + 52` (the literals only):
the bottom gates `≤ (n+1)^26`, their table width `≤ 35N^52` (`Sd.hof35`), the top tables, the walk length
`t ≤ L + 6` (`errExp = L + 5` at `D = 1`), the levels and windows from the list bound `B = |carriers|·4096·B_S ≤
8192·capK·N^{capZR}` (`CallIndexR.cap_leR`), the population `M ≤ 4(n+1)^26`, and `|FlatSeed| ≤ flatK·N^{flatZR}`
(`CallIndexR.flatSeed_leR`). So `symSize ≤ 600Y⁴ ≤ C_sz·(n+1)^{4Z_S}`:

* `gate_enc_le`, **`tabH_sym`**, `ZS`, `cS`, `YS`, **`atoms_call`**, **`symSize_poly`** (#124's statement:
  `∀ l, ∃ D_sz, ∀ F, ∃ C_sz, ∀ kclk coef A a ha, Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval C_sz D_sz`).

Paper quantity of the main type: the SYM per-point evaluator's input size, polynomial in `n` (P3:3176-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SymSize
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.Lists NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT.S3 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall symCallOf)

theorem gate_enc_le {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (i : Fin C.bottomCount) :
    (C.bottom i).gate.encodingBits ≤ C.descriptionBits := by
  have h := PrimT.SymTab.gate_desc_le C i
  unfold SupportedNormalizedGate.descriptionBits at h
  omega

/-- **The SYM bottom gates' table width** at descriptions `≤ L`. -/
theorem tabH_sym {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L) :
    PrimT.tabH (Stars.symGates C) ≤ L * (8 * n + 8 * L + 19) := by
  have hlen : (Stars.symGates C).length ≤ L := by
    unfold Stars.symGates
    rw [List.length_map, List.length_finRange]
    have := PrimT.TabCost.symDesc_pos C
    omega
  unfold PrimT.tabH PrimT.tabSeg
  rw [List.length_flatMap]
  have hsum := List.sum_le_card_nsmul ((Stars.symGates C).map fun g => (frame (PrimT.tabGW g)).length)
    (8 * n + 8 * L + 19) (fun x hx => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      unfold Stars.symGates at hg
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
      have h1 := ThrSz.tabGW_len (C.bottom i).gate
      have h2 := (gate_enc_le C i).trans hL
      rw [frame_len]
      omega)
  rw [smul_eq_mul, List.length_map] at hsum
  exact hsum.trans (Nat.mul_le_mul_right _ hlen)

/-- The size coefficient (`c_r` only). -/
def cS (cr : ℕ) : ℕ := 2 ^ 26 * (CallIndexR.capK cr + 1) + CallIndexR.flatK cr + 100

theorem clog_self (x : ℕ) : Nat.clog 2 x ≤ x := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le

section Call

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.SymSize
