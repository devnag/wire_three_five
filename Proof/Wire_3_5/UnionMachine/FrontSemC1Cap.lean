import Proof.Wire_3_5.UnionMachine.FrontSemCarPre
import Proof.Wire_3_5.UnionMachine.C1Size

/-! # C6 front, the semantic core (17): C1's caps at a guess (P3:3669-3673; `star:selection`, P3:1324-1362)

From the carriers' code bits `≤ K` (and `q`, the variable count, `2^{cb+2}`, the grid, the atoms' and parities'
description bits, `r` all `≤ K`): C1's converter capacity **`capNeed_le`**, the gate totals **`gtF_le`**, `npF_le`,
the per-variable register capacity **`capR_le`**, the carrier-table fuel, the request word **`cap2_le`**, the
selection's output **`capC1_le`**, the entries' code width **`WnG_le`**, and C1's precondition **`pre_of`**.

Paper quantity of the main types: C1's request at the union's carriers and the union machine's per-variable work. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemC1Cap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord intWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1 (GEnv natWord_le natWord_bits)

theorem nbl_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem intWord_pred (t : ℤ) : (intWord (t - 1)).length ≤ (intWord t).length + 2 := by
  rw [GateConv.intWord_len', GateConv.intWord_len']
  have h1 : (t - 1).natAbs ≤ t.natAbs + 1 := by
    have := Int.natAbs_sub_le t 1; simpa using this
  have h2 := nbl_mono h1
  have h3 := FrontSemGate.nbl_succ_le t.natAbs
  omega

theorem sum_map_le {α : Type} (X : List α) (f g : α → ℕ) (h : ∀ a ∈ X, f a ≤ g a) :
    (X.map f).sum ≤ (X.map g).sum := by
  induction X with
  | nil => simp
  | cons a X ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem sum_map_affine {α : Type} (X : List α) (b : α → ℕ) (c d : ℕ) :
    (X.map fun a => c * b a + d).sum = c * (X.map b).sum + X.length * d := by
  induction X with
  | nil => simp
  | cons a X ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- **C1's converter capacity at a carrier.** -/
theorem capNeed_le {q : ℕ} (X : Stars.Carrier q) (K : ℕ) (hq : q ≤ K) (hb : natBitLength X.code ≤ K) :
    GateConv.capNeed X ≤ 24 * K + K * (68 * K + 168) := by
  obtain ⟨h1, h2⟩ := FrontSemGate.carrier_bits X
  unfold GateConv.capNeed
  have key : ∀ gt ∈ X, 2 * (GateConv.selGate gt).length + 10 * ((GateConv.gateW gt).length + 2) + 2 ≤
      24 * natBitLength (FrontSemGate.gcode gt) + (68 * q + 168) := by
    intro gt _
    have hs := FrontSemGate.selGate_len gt
    have hw := GateConv.gateW_len gt
    have hp := intWord_pred gt.threshold
    have hsel : (GateConv.selGate gt).length = ((List.ofFn gt.weight).flatMap intWord).length +
        (intWord gt.threshold).length := by simp [GateConv.selGate]
    have hn := natWord_le q
    omega
  have hle := sum_map_le X _ _ key
  rw [sum_map_affine] at hle
  have hX : X.length * (68 * q + 168) ≤ K * (68 * K + 168) :=
    Nat.mul_le_mul (le_trans h2 hb) (by omega)
  have hS : (X.map fun gt => natBitLength (FrontSemGate.gcode gt)).sum ≤ K := le_trans h1 hb
  omega

section Gates
variable {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ)

theorem gtF_le (L : ℕ) (h : ∀ j, (Cs j).length ≤ L) : ∀ x, C1Gates.gtF Cs lits x ≤ x * L
  | 0 => by simp [C1Gates.gtF]
  | x + 1 => by
    have ih := gtF_le L h x
    have hx := h x
    simp only [C1Gates.gtF]
    split_ifs <;> rw [Nat.add_mul, one_mul] <;> omega

theorem npF_le : ∀ x, C1Gates.npF lits x ≤ x
  | 0 => by simp [C1Gates.npF]
  | x + 1 => by
    have ih := npF_le x
    simp only [C1Gates.npF]
    split_ifs <;> omega

end Gates

/-- The dyadic weight's word. -/
theorem ratWord_cnt_le (c e M : ℕ) (hc : c ≤ 2 ^ e) (hM : 2 ^ e ≤ M) :
    (ratWord ((c : ℚ) / 2 ^ e)).length ≤ 4 * M + 7 := by
  rw [C1Rat.ratWord_dyadic, List.length_append, GateConv.intWord_len']
  have hc1 := C1Rat.rstepN_le c e
  have hd := C1Rat.rstepN_d c e
  have hp : 2 ^ (C1Rat.rstepN e (c, false, 0)).2.2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hd
  have e1 := C1Size.nw_le (2 ^ (C1Rat.rstepN e (c, false, 0)).2.2)
  have e2 := PrimAsm.CopyNat.natBitLength_le_self_succ (((C1Rat.rstepN e (c, false, 0)).1 : ℤ).natAbs)
  simp only [Int.natAbs_natCast] at e2 ⊢
  omega

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N} {g : UnionGuess S z} {Λ K : ℕ}

theorem csG_bits (hG : GEnv g Λ K) (x : ℕ) (hx : x < nvG g) : natBitLength (C1Ref.CsG g x).code ≤ K := by
  unfold C1Ref.CsG
  rw [dif_pos hx]
  exact hG.car ⟨x, hx⟩

theorem csG_len (hG : GEnv g Λ K) (x : ℕ) : (C1Ref.CsG g x).length ≤ K := by
  unfold C1Ref.CsG
  split_ifs with h
  · exact le_trans (FrontSemGate.carrier_bits _).2 (hG.car ⟨x, h⟩)
  · simp

/-- **The per-variable register capacity** (PathCaps' `capR`). -/
theorem capR_le (hG : GEnv g Λ K) (Vb : ℕ) (hVb : Vb ≤ K) (hcb4 : 2 ^ (g.pcpp.clauseBits + 2) ≤ K) (x : ℕ)
    (hx : x < nvG g) :
    g.pcpp.systematicBits * g.q + g.q + (C1Ref.litsG g).length + 6 * Vb + 8 + x + g.q +
      GateConv.capNeed (C1Ref.CsG g x) + 2 * ((C1Ref.CsG g x).flatMap GateConv.selGate).length +
      C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x + (C1Ref.CsG g x).length + C1Cnt.cntOf x (C1Ref.litsG g) +
      g.pcpp.clauseBits + C1Gates.npF (C1Ref.litsG g) x + 2 ^ (g.pcpp.clauseBits + 2) +
      (marks (natListWord (List.range' (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x)
        (C1Ref.CsG g x).length))).length +
      (marks (NearCubicWires.WireExponent3_5.ratWord
        ((C1Cnt.cntOf x (C1Ref.litsG g) : ℚ) / 2 ^ (g.pcpp.clauseBits + 1)))).length +
      6 * natBitLength (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x + (C1Ref.CsG g x).length) +
      6 * natBitLength (C1Cnt.cntOf x (C1Ref.litsG g) + 2 ^ (g.pcpp.clauseBits + 1)) + 40 ≤
        4 * (K * K * K) + 100 * (K * K) + 300 * K + 100 := by
  have hq := hG.q
  have hnv : g.pcpp.systematicBits + g.pcpp.auxiliaryBits ≤ K := hG.nv
  have hxK : x ≤ K := by
    have : nvG g = g.pcpp.systematicBits + g.pcpp.auxiliaryBits := rfl
    omega
  have hb := csG_bits hG x hx
  have hl := csG_len hG x
  have e1 : 2 ^ (g.pcpp.clauseBits + 1) = 2 * 2 ^ g.pcpp.clauseBits := by rw [pow_succ]; ring
  have e2 : 2 ^ (g.pcpp.clauseBits + 2) = 4 * 2 ^ g.pcpp.clauseBits := by rw [pow_add]; ring
  have hcb : g.pcpp.clauseBits ≤ K := by
    have := (Nat.lt_two_pow_self (n := g.pcpp.clauseBits)).le; omega
  have hlits : (C1Ref.litsG g).length = 2 * 2 ^ g.pcpp.clauseBits := FrontTW.pairsOf_length _ _
  have hcnt := C1Size.cnt_le g x
  have hsq : g.pcpp.systematicBits * g.q ≤ K * K := Nat.mul_le_mul (by omega) hq
  have hcap := capNeed_le (C1Ref.CsG g x) K hq hb
  have ecap : K * (68 * K + 168) = 68 * (K * K) + 168 * K := by ring
  have hsel : ((C1Ref.CsG g x).flatMap GateConv.selGate).length ≤ 4 * (K * K) + 10 * K := by
    calc _ ≤ (4 * g.q + 10) * natBitLength (C1Ref.CsG g x).code := FrontSemGate.selGates_len _
      _ ≤ (4 * K + 10) * K := Nat.mul_le_mul (by omega) hb
      _ = 4 * (K * K) + 10 * K := by ring
  have hgt : C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x ≤ K * K :=
    le_trans (gtF_le (C1Ref.CsG g) (C1Ref.litsG g) K (csG_len hG) x) (Nat.mul_le_mul_right K hxK)
  have hnp := npF_le (C1Ref.litsG g) x
  have hmk : (marks (natListWord (List.range' (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x)
      (C1Ref.CsG g x).length))).length ≤ 4 * (K * K * K) + 4 * (K * K) + 10 * K + 6 := by
    rw [FrontFold.marks_length, PrimAsm.CopyNat.natListWord_eq, List.length_append, List.length_range']
    have a1 := natWord_le (C1Ref.CsG g x).length
    have a2 := C1Size.len_flatMap_le (List.range' (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x)
      (C1Ref.CsG g x).length) natWord (2 * (K * K + K) + 3) (by
        intro j hj
        rw [List.mem_range'_1] at hj
        exact (natWord_le j).trans (by omega))
    rw [List.length_range'] at a2
    have a3 : (C1Ref.CsG g x).length * (2 * (K * K + K) + 3) ≤ K * (2 * (K * K + K) + 3) :=
      Nat.mul_le_mul_right _ hl
    have a4 : K * (2 * (K * K + K) + 3) = 2 * (K * K * K) + 2 * (K * K) + 3 * K := by ring
    omega
  have hrw : (marks (NearCubicWires.WireExponent3_5.ratWord
      ((C1Cnt.cntOf x (C1Ref.litsG g) : ℚ) / 2 ^ (g.pcpp.clauseBits + 1)))).length ≤ 8 * K + 14 := by
    rw [FrontFold.marks_length]
    have := ratWord_cnt_le (C1Cnt.cntOf x (C1Ref.litsG g)) (g.pcpp.clauseBits + 1) K hcnt (by omega)
    omega
  have hb1 := FrontSemCap2.bits_le (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) x + (C1Ref.CsG g x).length)
  have hb2 := FrontSemCap2.bits_le (C1Cnt.cntOf x (C1Ref.litsG g) + 2 ^ (g.pcpp.clauseBits + 1))
  omega

/-- **The request word's capacity** (PathCaps' `cap2`). -/
theorem cap2_le (hG : GEnv g Λ K) (cr : ℕ) (hr : B.rOf g.q ≤ K) (hrr : Ledger.rowBr cr g.q ≤ K)
    (hL : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ K) (hP : ∀ X, g.mode.descriptionBits (g.parity X) ≤ K)
    (hcb1 : 2 ^ (g.pcpp.clauseBits + 1) ≤ K) :
    g.q + Ledger.rowBr cr g.q + C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g) +
      C1Gates.npF (C1Ref.litsG g) (nvG g) + 6 * (natBitLength g.q + natBitLength (Ledger.rowBr cr g.q) +
        natBitLength (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g)) +
        natBitLength (C1Gates.npF (C1Ref.litsG g) (nvG g))) +
      (RepairOrdinary.frame (Plan.selWord (FrontSelReq.selReqOf g))).length + 50 ≤
        200 * K ^ 6 + 20 * (K * K) + 50 * K + 100 := by
  have hq := hG.q
  have hnv : nvG g ≤ K := hG.nv
  have hK1 : 1 ≤ K := by have := hG.q2; omega
  have hsw := C1Size.selWord_len_le g K hK1 hq hnv hG.s hL hP hcb1 hr
  rw [FrontSemCap1.frame_len]
  have hgt : C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g) ≤ K * K :=
    le_trans (gtF_le (C1Ref.CsG g) (C1Ref.litsG g) K (csG_len hG) (nvG g)) (Nat.mul_le_mul_right K hnv)
  have hnp := npF_le (C1Ref.litsG g) (nvG g)
  have b1 := FrontSemCap2.bits_le g.q
  have b2 := FrontSemCap2.bits_le (Ledger.rowBr cr g.q)
  have b3 := FrontSemCap2.bits_le (C1Gates.gtF (C1Ref.CsG g) (C1Ref.litsG g) (nvG g))
  have b4 := FrontSemCap2.bits_le (C1Gates.npF (C1Ref.litsG g) (nvG g))
  omega

/-- **The selection's output** (PathCaps' `capC1`). -/
theorem capC1_le (hG : GEnv g Λ K) (hstar : I.StarAt g.q) :
    8 * (SelectionMachine.selArgmin (FrontSelReq.selReqOf g)).length +
      2 * (natListWord (SelectionMachine.selArgmin (FrontSelReq.selReqOf g))).length + 17 ≤ 10 * K + 17 := by
  rw [FrontSelReq.selArgmin_selReq g hstar]
  have := hG.tr
  have := hG.trl
  omega

/-- **The entries' code width** is at most `K`. -/
theorem WnG_le (hG : GEnv g Λ K) : FrontSemPath.WnG g ≤ K := by
  unfold FrontSemPath.WnG
  refine FrontSemFold.supR_le _ _ _ (fun e he => ?_)
  unfold FrontFmtCA.codeE
  rw [List.getD_eq_getElem _ _ he]
  have hm : (FrontSemEnt.esOf g)[e] ∈ FrontSemEnt.esOf g := List.getElem_mem he
  obtain ⟨e', he', hee⟩ := List.mem_map.1 hm
  obtain ⟨X, a, rfl⟩ := (FrontDecode.mem_linE _ e').1 he'
  rw [← hee]
  exact hG.circ (Sum.inr (Sum.inl (X, a)))

/-- **C1's precondition at the union's request** (the contract's, and the size bound `|selWord| ≤ (q+1)^d`). -/
theorem pre_of (hG : GEnv g Λ K) (hstar : I.StarAt g.q) {d : ℕ} (c : Plan.C1At d) (hr : B.rOf g.q ≤ K)
    (hL : ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ K) (hP : ∀ X, g.mode.descriptionBits (g.parity X) ≤ K)
    (hcb1 : 2 ^ (g.pcpp.clauseBits + 1) ≤ K) (hd : 100 * K ^ 6 ≤ (g.q + 1) ^ d) :
    (Plan.c1sized d c.E₁ c.c₁).pre (FrontSelReq.selReqOf g) := by
  have hK1 : 1 ≤ K := by have := hG.q2; have := hG.q; omega
  refine ⟨FrontSelReq.pre_selReq g hstar, ?_⟩
  exact (C1Size.selWord_len_le g K hK1 hG.q hG.nv hG.s hL hP hcb1 hr).trans hd

end Guess

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemC1Cap
