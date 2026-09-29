import Proof.Wire_3_5.UnionMachine.FrontSemC1Cap

/-! # C6 front, the semantic core (18): the valid path's caps at a guess (P3:3669-3691)

**`pathCaps_of`**: `FrontSemPath.PathCaps` at a guess from its size envelope `GEnv g Λ K` (with `2·nv`, `2^{cb+2}`,
`3`, `r`, `c_r`, the atoms' and parities' description bits `≤ K`), the width `W = K_w(q+1)^{D_w}` above `PW K` and
C1's carrier preparation `CP·(K+2)^{51}`, the data bound above `BK K`, the fold's exponents (`foldCapsG`), and the
star hypotheses at `q`. `Vb := K`.

Paper quantity of the main type: every capacity the valid path's machines read at a guess. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPathCaps
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.BlockPlatform.UnaryCalc (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (GEnv natWord_le natWord_bits)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap2 (BK PW pow2_bits bits_le pw_small)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldBound (eT)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemFold (eMt)

theorem pw_cube (K : ℕ) : 4 * (K * K * K) + 100 * (K * K) + 300 * K + 100 ≤ PW K := by
  unfold PW; ring_nf; omega

theorem pw_six (K : ℕ) : 200 * K ^ 6 + 20 * (K * K) + 50 * K + 100 ≤ PW K := by
  unfold PW; ring_nf; omega

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {g : UnionGuess S z} {Λ K : ℕ} {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The valid path's capacities at a guess** (`Vb := K`). -/
theorem pathCaps_of (hG : GEnv g Λ K) {Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr t : ℕ} {d : ℕ} (c : Plan.C1At d)
    (hsS : g.s = Ledger.rowBSparse h0 h1 2 Cδ g.q) (hΛ : Λ = Ledger.rowBLambda h0 h1 2 g.q)
    (hV2 : 2 * nvG g ≤ K) (hcb4 : 2 ^ (g.pcpp.clauseBits + 2) ≤ K) (h3 : 3 ≤ K) (hcr : cr ≤ K)
    (hr : B.rOf g.q ≤ K) (hrr : Ledger.rowBr cr g.q ≤ K)
    (hL : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ K) (hP : ∀ X, g.mode.descriptionBits (g.parity X) ≤ K)
    (hstar : I.StarAt g.q)
    (hsp : PrimAsm.SparseNum.sparseBound ζ Cδ (Ledger.Lq g.q) (Ledger.rowBt h0 h1 g.q - 1) ≤
      2 * (Kw * (g.q + 1) ^ Dw) + 2)
    (hBK : BK K ≤ Kb * (g.q + 1) ^ Db) (hW1 : PW K ≤ Kw * (g.q + 1) ^ Dw)
    (hW3 : Kb * (g.q + 1) ^ Db + Kb + (g.q + 1) ^ Db ≤ Kw * (g.q + 1) ^ Dw)
    (hHd : FrontSemCarPre.CP * (K + 2) ^ 51 + 4 * K + 4 ≤ Kw * (g.q + 1) ^ Dw)
    (hDe : ∀ m : Mode, eT (FrontCh5.PwM m) (FrontCh5.CwM m) I.carrierDeg ≤ De)
    (hCe : ∀ m : Mode, 2 ^ eT (FrontCh5.PwM m) (FrontCh5.CwM m) I.carrierDeg ≤ Ce)
    (hT : value De Ce (Kw * (g.q + 1) ^ Dw) ≤ (K + 2) ^ t)
    (hDt : ∀ m : Mode, eMt (FrontCh5.PwM m) (FrontCh5.CwM m) I.carrierDeg t + 6 ≤ Dt) (hCt : 2 * 2 ^ Dt ≤ Ct) :
    FrontSemPath.PathCaps g h0 h1 Kw Dw Dl De Ce Dt Ct Kb Db Cδ cr K c := by
  have hq := hG.q
  have hnv : g.pcpp.systematicBits + g.pcpp.auxiliaryBits ≤ K := hG.nv
  have hnvG : nvG g = g.pcpp.systematicBits + g.pcpp.auxiliaryBits := rfl
  have hs := hG.s
  have hs1 := hG.s1
  have hl := hG.lam
  have hcb := hG.cb
  have hcb' : g.pcpp.clauseBits ≤ K := le_trans (Nat.lt_two_pow_self (n := g.pcpp.clauseBits)).le hcb
  have e1 : 2 ^ (g.pcpp.clauseBits + 1) = 2 * 2 ^ g.pcpp.clauseBits := by rw [pow_succ]; ring
  have e2 : 2 ^ (g.pcpp.clauseBits + 2) = 4 * 2 ^ g.pcpp.clauseBits := by rw [pow_add]; ring
  have hsm := pw_small K
  have hcu := pw_cube K
  have hsx := pw_six K
  have hKW : K ≤ Kw * (g.q + 1) ^ Dw := by omega
  have hwn := FrontSemC1Cap.WnG_le hG
  have hlits : (C1Ref.litsG g).length = 2 * 2 ^ g.pcpp.clauseBits := FrontTW.pairsOf_length _ _
  have hlv : ∀ l ∈ C1Ref.litsG g, l < 2 * (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) :=
    FrontSemCap2.mem_pairsOf_lt _ _ (fun _ => FrontSemCap2.literalIndex_lt _) (fun _ => FrontSemCap2.literalIndex_lt _)
  obtain ⟨fenv, fcw, flen, fz⟩ := FrontSemFold.foldCapsG g K (Kw * (g.q + 1) ^ Dw) De Ce Dt Ct t I.carrierDeg hq
    hnv (fun X hX => hG.cw X hX) hKW hDe hCe hT hDt hCt
  have hsW : g.s * FrontSemPath.WnG g ≤ K * K := Nat.mul_le_mul hs hwn
  have hcapC : (nvG g + 1) * (2 * (g.s * FrontSemPath.WnG g) + 2 * FrontSemPath.WnG g + 3) + g.s + nvG g ≤
      4 * (K * K * K) + 100 * (K * K) + 300 * K + 100 := by
    have a1 : (nvG g + 1) * (2 * (g.s * FrontSemPath.WnG g) + 2 * FrontSemPath.WnG g + 3) ≤
        (K + 1) * (2 * (K * K) + 2 * K + 3) := Nat.mul_le_mul (by omega) (by omega)
    have a2 : (K + 1) * (2 * (K * K) + 2 * K + 3) = 2 * (K * K * K) + 4 * (K * K) + 5 * K + 3 := by ring
    omega
  have hB1 : (nvG g + 1) * (2 * g.q + 1) ≤ 2 * (K * K) + 3 * K + 1 := by
    have a1 : (nvG g + 1) * (2 * g.q + 1) ≤ (K + 1) * (2 * K + 1) := Nat.mul_le_mul (by omega) (by omega)
    have a2 : (K + 1) * (2 * K + 1) = 2 * (K * K) + 3 * K + 1 := by ring
    omega
  have b0 : natBitLength 3 ≤ 8 := bits_le 3
  have b1 := bits_le g.pcpp.systematicBits
  have b2 := bits_le g.pcpp.auxiliaryBits
  have b3 := bits_le g.pcpp.clauseBits
  refine
    { nums := ?_
      capC := ?_
      capB1 := by omega
      capB2 := by omega
      Z0 := fz
      env := fenv
      cwT := fcw
      len := flen
      sV := by omega
      aV := by omega
      cV := by omega
      lV := by omega
      vV := fun l hl' => by have := hlv l hl'; omega
      xV := by omega
      v3 := h3
      Hd := ?_
      xc := by omega
      capR := fun x hx => le_trans (FrontSemC1Cap.capR_le hG K le_rfl hcb4 x hx) (by omega)
      cap1 := by omega
      cap2 := le_trans (FrontSemC1Cap.cap2_le hG cr hr hrr hL hP (by omega)) (by omega)
      capC1 := le_trans (FrontSemC1Cap.capC1_le hG hstar) (by omega) }
  · exact FrontSemCap3.numsCaps_of h0 h1 hq hnv hcb (by rw [← hsS]; exact hs) (by rw [← hsS]; exact hs1)
      (by rw [← hΛ]; exact hl) hsp hBK hW1 hW3
  · rw [← hsS]; omega
  · intro x hx
    have hb := FrontSemC1Cap.csG_bits hG x hx
    have hp := FrontSemCarPre.carPre_le (C1Ref.CsG g x)
    have hp2 : FrontSemCarPre.CP * (natBitLength (C1Ref.CsG g x).code + 2) ^ 51 ≤ FrontSemCarPre.CP * (K + 2) ^ 51 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 51)
    rw [natWord_bits]
    exact max_le (by omega) (by omega)

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemPathCaps
