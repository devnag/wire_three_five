import Proof.Wire_3_5.Stage35.ExecCostSpec
import Proof.Wire_3_5.Recovery.CaseTwoCost

/-!
# The Case-2 execution's cost class: the proofs

Paper v2, §H.6: "There are at most `2^{O(q)}` SAT queries and local work, in addition to `poly(T(N_a)) = 2^{O(q)}`
refuter work. Since `q = O(n)`, this is `2^{O(n)}` overall." The bounds of `Stage35.ExecCostSpec` at the
near-cubic-wires Case-2 source block `blockV h2 a` and its kit instances `KI`:
* `roundCost_le`, `foldCost_le`, `foldNeed_le`: every round of the fold costs the crop (linear in the address length
  `n`) plus twice the block's cost, which is at most `bEnv D x` (the source block's budget and the occurrence machine's
  local envelope, base `WholeBudget.occurrence_bound` at one copy);
* `poly_bEnv`, `poly_inst`: the instance quantities are at most a fixed polynomial of `2^ν` (the near-cubic-wires kit
  cost lemmas), hence of `2^n` for `ν ≤ n`;
* **`foldNeedCap`** and **`htwoCostPoly`**.
-/

set_option autoImplicit false

namespace Stage35.ExecCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open W3.NearCubicWires.RepairSource.Outer3 W3.NearCubicWires.RepairSource.Outer3.Case2
open Stage35.Fold Stage35.Exec
open _root_.NearCubicGates.Close _root_.NearCubicGates.Close.CheckedPCPP

noncomputable section

variable {mw : Outer.MWSource} {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  {SV : Outer.SuccinctVerifier H L} {a : PointwisePCPPAlgorithm} {d : ℕ}

/-- The block's per-round cost majorant: the source block's budget plus the occurrence machine's local envelope. -/
def bEnv (D : ℕ) (x : KI mw SV a d) : ℕ :=
  (blockV h2 a).budget x.i + 1 + WholeBudget.localEnvelope D 1 x.M

/-- **One round** costs the crop plus twice the block majorant. -/
theorem roundCost_le (D : ℕ) (x : KI mw SV a d) {n : ℕ} (point : BitInput n) (blk : ℕ)
    (hcb : (a.output x.i.req).clauseBits ≤ capOf (blockV h2 a) D x.i)
    (hfit : (blk + 1) * widthOf (blockV h2 a) D x.i ≤ n) :
    Fold.roundCost (blockV h2 a) D x.i point blk ≤ 12 * n + 16 + 2 * bEnv D x := by
  have hiw : blk * widthOf (blockV h2 a) D x.i + widthOf (blockV h2 a) D x.i ≤ n := by
    have : (blk + 1) * widthOf (blockV h2 a) D x.i =
      blk * widthOf (blockV h2 a) D x.i + widthOf (blockV h2 a) D x.i := by ring
    omega
  have hcb' : (a.output ((blockV h2 a).req x.i)).clauseBits ≤ capOf (blockV h2 a) D x.i := hcb
  have hocc := WholeBudget.occurrence_bound D 1 0 a ((blockV h2 a).req x.i)
    (AddressWindow.field point (blk * widthOf (blockV h2 a) D x.i) ((blockV h2 a).req x.i).arity)
    (AddressWindow.field point (blk * widthOf (blockV h2 a) D x.i + ((blockV h2 a).req x.i).arity)
      (a.output ((blockV h2 a).req x.i)).clauseBits)
    (AddressWindow.read point (blk * widthOf (blockV h2 a) D x.i + ((blockV h2 a).req x.i).arity +
      capOf (blockV h2 a) D x.i))
    (capOf (blockV h2 a) D x.i - (a.output ((blockV h2 a).req x.i)).clauseBits) (by omega)
    (by show _ = capOf (blockV h2 a) D x.i; omega)
  change _ ≤ WholeBudget.localEnvelope D 1 x.M at hocc
  unfold Fold.roundCost SBlock.wbudget SliceFrame.budget bEnv
  omega

/-- The fold's cost over `c` rounds. -/
theorem foldCost_le (D : ℕ) (x : KI mw SV a d) {n : ℕ} (point : BitInput n) (c : ℕ)
    (hcb : (a.output x.i.req).clauseBits ≤ capOf (blockV h2 a) D x.i)
    (hfit : c * widthOf (blockV h2 a) D x.i ≤ n) :
    foldCost (blockV h2 a) D x.i point c ≤ 12 * n + 16 + 2 * bEnv D x := by
  unfold foldCost
  refine Finset.sup_le fun i hi => ?_
  have hic := Finset.mem_range.1 hi
  exact roundCost_le D x point i hcb ((Nat.mul_le_mul_right _ (show i + 1 ≤ c by omega)).trans hfit)

/-- The fold's bank need. -/
theorem foldNeed_le (D : ℕ) (x : KI mw SV a d) {n : ℕ} (point : BitInput n) (c : ℕ)
    (hcb : (a.output x.i.req).clauseBits ≤ capOf (blockV h2 a) D x.i)
    (hfit : c * widthOf (blockV h2 a) D x.i ≤ n) :
    foldNeed (blockV h2 a) D x.i point c ≤ x.w + (2 * x.dd + 1) + x.q + 15 * n + 20 + 2 * bEnv D x := by
  have hfc := foldCost_le D x point c hcb hfit
  have hw0 : ((blockV h2 a).w0 x.i).length = x.w := rfl
  have hd0 : (RepairOrdinary.frame ((blockV h2 a).d x.i)).length = 2 * x.dd + 1 := by
    rw [RepairOrdinary.frame_length]; rfl
  have hp0 : (RepairOrdinary.frame (List.ofFn point)).length = 2 * n + 1 := by
    rw [RepairOrdinary.frame_length, List.length_ofFn]
  have hq0 : ((blockV h2 a).req x.i).arity = x.q := rfl
  unfold foldNeed
  refine max_le (max_le ?_ ?_) (max_le (max_le ?_ ?_) (max_le ?_ ?_))
  · rw [hw0]; omega
  · rw [hd0]; omega
  · rw [hp0]; omega
  · rw [hq0]; omega
  · omega
  · omega

/-! ## The instance quantities are polynomial in `2^ν` -/

theorem poly_bEnv (D : ℕ) : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => bEnv D x) := by
  have hM := poly_M (a := a) (d := d) (mw := mw) (SV := SV)
  have hblk := poly_block (a := a) (d := d) (mw := mw) (SV := SV)
  obtain ⟨el, cl, hloc⟩ := WholeBudget.local_polynomial D 1 PaddedRunnerBudgetClosure.sourcePoly_id
  have hl : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => WholeBudget.localEnvelope D 1 x.M) :=
    hM.comp ⟨cl, el, fun y => hloc y⟩
  exact ((hblk.add (PolyB.const 1)).add hl).mono fun x => le_rfl

/-- The fold's instance part. -/
theorem poly_need (D : ℕ) :
    PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => x.w + (2 * x.dd + 1) + x.q + 2 * bEnv D x) := by
  have hw := poly_w (a := a) (d := d) (mw := mw) (SV := SV)
  have hdd := poly_dd (a := a) (d := d) (mw := mw) (SV := SV)
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  exact ((hw.add ((PolyB.mul (PolyB.const 2) hdd).add (PolyB.const 1))).add hq).add
    (PolyB.mul (PolyB.const 2) (poly_bEnv D))

/-- `C (2^ν + 1)^E ≤ C (2^n + 1)^E` for `ν ≤ n`. -/
theorem lift_le (C E ν n : ℕ) (h : ν ≤ n) : C * (2 ^ ν + 1) ^ E ≤ C * (2 ^ n + 1) ^ E :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) h) 1) E)

variable (mw SV a d)

/-- **One capacity exponent covers the fold's bank need.** -/
theorem foldNeedCap (D : ℕ) : FoldNeedCap mw SV a d D := by
  obtain ⟨Cf, Ef, hf⟩ := poly_need (mw := mw) (SV := SV) (a := a) (d := d) D
  set C' := Cf + 40 with hC'
  set E' := Ef + 1 with hE'
  refine ⟨natBitLength C' + 2 * E' + 1, fun x n point c hcb hfit hνn => ?_⟩
  have hneed := foldNeed_le D x point c hcb hfit
  have hx : x.w + (2 * x.dd + 1) + x.q + 2 * bEnv D x ≤ Cf * (2 ^ n + 1) ^ Ef := (hf x).trans (lift_le Cf Ef x.ν n hνn)
  have hX1 : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have hn : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  have h1 : Cf * (2 ^ n + 1) ^ Ef ≤ Cf * (2 ^ n + 1) ^ E' :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by omega))
  have hh2 : 2 ^ n + 1 ≤ (2 ^ n + 1) ^ E' := Nat.le_self_pow (by omega) _
  have hh3 : 1 ≤ (2 ^ n + 1) ^ E' := Nat.one_le_pow _ _ hX1
  have hcap := poly_le_cap C' E' n
  have e : C' * (2 ^ n + 1) ^ E' = Cf * (2 ^ n + 1) ^ E' + 40 * (2 ^ n + 1) ^ E' := by rw [hC']; ring
  calc foldNeed (blockV h2 a) D x.i point c ≤ Cf * (2 ^ n + 1) ^ E' + 40 * (2 ^ n + 1) ^ E' := by
        nlinarith
    _ = C' * (2 ^ n + 1) ^ E' := e.symm
    _ ≤ _ := hcap


variable {mw SV a d}

/-- The instance part of the execution's cost: the converter's budget and twice the block majorant. -/
theorem poly_instCost (D : ℕ) :
    ∃ Ci Ei : ℕ, ∀ x : KI mw SV a d, Cold.budget x.cap x.B.pf + 2 * bEnv D x ≤ Ci * (2 ^ x.ν + 1) ^ Ei := by
  have hq := poly_q (a := a) (d := d) (mw := mw) (SV := SV)
  have hcap := poly_cap (a := a) (d := d) (mw := mw) (SV := SV)
  obtain ⟨Cc, Ec, _, hcold⟩ := ColdBudget.polynomial
  have hcd : PolyB (fun x : KI mw SV a d => 2 ^ x.ν) (fun x => Cold.budget x.cap x.B.pf) :=
    (PolyB.mul (PolyB.const Cc) (PolyB.pow ((hq.add hcap).add (PolyB.const 1)) Ec)).mono fun x =>
      hcold x.q x.cap x.B.pf (pf_le_cap x)
  exact hcd.add (PolyB.mul (PolyB.const 2) (poly_bEnv D))

/-- The outer polynomial in `X = 2^n`. -/
def Ψ (Ci Ei P eP e3 e4 cA : ℕ) (X : ℕ) : ℕ :=
  Ci * (X + 1) ^ Ei + P * (X + 1) ^ eP + 2 * (2 ^ e3 * (X + 1) ^ e3) + cA * (X + 1) ^ (e4 + 1) +
    2 * (2 ^ e4 * (X + 1) ^ e4) + 40 * X + 300 +
    X * (20 * X + 60 + Ci * (X + 1) ^ Ei + 2 * (2 ^ e4 * (X + 1) ^ e4))

theorem poly_Ψ (Ci Ei P eP e3 e4 cA : ℕ) : PolyB (fun X : ℕ => X) (Ψ Ci Ei P eP e3 e4 cA) := by
  have s1 : PolyB (fun X : ℕ => X) (fun X => X + 1) := PolyB.size.add (PolyB.const 1)
  have pw (c e : ℕ) : PolyB (fun X : ℕ => X) (fun X => c * (X + 1) ^ e) := PolyB.mul (PolyB.const c) (s1.pow e)
  refine ((((((((pw Ci Ei).add (pw P eP)).add (PolyB.mul (PolyB.const 2) (pw (2 ^ e3) e3))).add
    (pw cA (e4 + 1))).add (PolyB.mul (PolyB.const 2) (pw (2 ^ e4) e4))).add
    (PolyB.mul (PolyB.const 40) PolyB.size)).add (PolyB.const 300)).add
    (PolyB.mul PolyB.size ((((PolyB.mul (PolyB.const 20) PolyB.size).add (PolyB.const 60)).add (pw Ci Ei)).add
      (PolyB.mul (PolyB.const 2) (pw (2 ^ e4) e4))))).mono fun X => le_rfl

variable (mw SV a d)

/-- **The Case-2 execution runs in `2^{O(n)}`.** -/
theorem htwoCostPoly (D k A u v e1 e2 e3 e4 : ℕ) : HtwoCostPoly mw SV a d D k A u v e1 e2 e3 e4 := by
  obtain ⟨Ci, Ei, hI⟩ := poly_instCost (mw := mw) (SV := SV) (a := a) (d := d) D
  obtain ⟨C, E, hΨ⟩ := poly_Ψ Ci Ei (CertPrefix.prefixCoef u v e1 e2 e3) (e1 + e2 + e3 + 4) e3 e4
    (RepairSource.CloseoutCapacity.coefficient e4 e4)
  refine ⟨C, E, fun x n point hcb hqS hfit hνn hTs' => ?_⟩
  set X := 2 ^ n with hXdef
  set cc := candT k A u v (CertPrefix.prefixS k A u v D n) ((v - u) ^ 16) (v ^ 16) n + 1 with hcc
  have hnX : n ≤ X := Nat.lt_two_pow_self.le
  have hX1 : 1 ≤ X + 1 := Nat.le_add_left 1 _
  -- the instance part, lifted to `2^n`
  have hIx : Cold.budget x.cap x.B.pf + 2 * bEnv D x ≤ Ci * (X + 1) ^ Ei := (hI x).trans (lift_le Ci Ei x.ν n hνn)
  -- the widths
  have hwq : widthOf (blockV h2 a) D x.i = x.q + CloseoutLanguage.clauseWidth D x.q + 1 := rfl
  have hw1 : widthOf (blockV h2 a) D x.i ≤ cc * widthOf (blockV h2 a) D x.i := Nat.le_mul_of_pos_left _ (by omega)
  have hc1 : cc ≤ cc * widthOf (blockV h2 a) D x.i := Nat.le_mul_of_pos_right _ (by rw [hwq]; omega)
  -- the parameter stages
  have hS := CertPrefix.prefixS_le k A u v D n
  have hlen : (List.ofFn point).length = n := List.length_ofFn
  have hpar := CaseTwoCost.paramCost_le k A u v D e1 e2 e3 (List.ofFn point)
  have hpre := CertPrefix.prefixCost_le k A u v D e1 e2 e3 (List.ofFn point) (by rw [hlen]; exact hTs')
  rw [hlen] at hpar hpre
  rw [← hXdef] at hpre
  have hpsb := CaseTwoCost.paramScanBound_le k A v D (CertPrefix.prefixS k A u v D n) n ((v - u) ^ 16) (v ^ 16)
    (pcap e1 n) (pcap e2 n) n hS
  have hpw := CaseTwoCost.pwCost_le k A v D (CertPrefix.prefixS k A u v D n) n ((v - u) ^ 16) (v ^ 16) (pcap e1 n)
    (pcap e2 n) n
  rw [← hqS] at hpw
  have hcbm := candBound_mono k A v D (CertPrefix.prefixS k A u v D n) (n + 1) n ((v - u) ^ 16) (v ^ 16) (pcap e1 n)
    (pcap e2 n) n (by omega)
  have hsr : scanRoundBound k A v D n n ((v - u) ^ 16) (v ^ 16) (pcap e1 n) (pcap e2 n) n =
      candBound k A v D (n + 1) n ((v - u) ^ 16) (v ^ 16) (pcap e1 n) (pcap e2 n) n + 10 * n + 2 * pcap e1 n + 64 := rfl
  have hC3 : pcap e3 n ≤ 2 ^ e3 * (X + 1) ^ e3 := cap_le_poly e3 n
  have hP : (X + 1) ^ (e1 + e2 + e3 + 4) ≤ (X + 1) ^ (e1 + e2 + e3 + 4) := le_rfl
  -- the capacity and the fold
  have hcapb := RepairSource.CloseoutCapacity.budget_bound e4 e4 (List.ofFn point)
  rw [hlen, ← hXdef] at hcapb
  have hC4 : RepairSource.CloseoutCapacity.capacity e4 e4 n ≤ 2 ^ e4 * (X + 1) ^ e4 := cap_le_poly e4 n
  have hF := foldCost_le D x point cc hcb hfit
  have hstuff : foldCost (blockV h2 a) D x.i point cc + 1 +
      (2 * RepairSource.CloseoutCapacity.capacity e4 e4 n + 4 + 1 + (2 * (cc * widthOf (blockV h2 a) D x.i) + 6)) + 2 ≤
      20 * X + 60 + Ci * (X + 1) ^ Ei + 2 * (2 ^ e4 * (X + 1) ^ e4) := by omega
  have hccn : cc ≤ X := by omega
  have hprod := Nat.mul_le_mul hccn hstuff
  have hfb : foldBudget (blockV h2 a) D x.i point cc (RepairSource.CloseoutCapacity.capacity e4 e4 n) ≤
      X * (20 * X + 60 + Ci * (X + 1) ^ Ei + 2 * (2 ^ e4 * (X + 1) ^ e4)) + X + 10 := by
    unfold foldBudget; omega
  have hCN := hΨ X
  refine le_trans ?_ hCN
  unfold htwoCost preCost initCost Ψ
  rw [hlen]
  omega

end

end Stage35.ExecCost
