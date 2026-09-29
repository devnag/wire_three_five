import Proof.Wire_3_5.UnionMachine.FrontCostEnd

/-! # C6 front, the time (6): C1's loop, assembler and framing (P3:3669-3673)

With the chain's atoms at most `n`: **`gsCost_le`** (the gate converter within `1000·(capNeed+1)·capNeed`),
**`rcost_le`** (one round of C1's carrier loop), **`asmCost_le`**, **`convCost_le`** (C1's request assembly and its
output's framing), each a fixed numeral times a fixed power of `n`.

Paper quantity of the main types: the selection stage's per-variable time against the input length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostC1
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit
open NearCubicWires.RepairRepresentation (natWord natListWord)

/-- The gate converter's cost against its capacity need. -/
theorem gs_aux {q : ℕ} (K : ℕ) : ∀ C : List (NormalizedThresholdGate q), (∀ g ∈ C, (GateConv.gateW g).length ≤ K) →
    (C.map fun g => GateConv.gCost (GateConv.gateW g).length + 2).sum ≤
      1000 * (K + 1) * GateConv.capNeed C + 2 * C.length
  | [], _ => by simp [GateConv.capNeed]
  | g :: C, h => by
    have ih := gs_aux K C (fun g' hg' => h g' (by simp [hg']))
    have hg := h g (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons, GateConv.capNeed] at ih ⊢
    set L := (GateConv.gateW g).length
    set S := (GateConv.selGate g).length
    have hG : GateConv.gCost L = 1000 * (L + 1) * (L + 1) := rfl
    have h1 : 1000 * (L + 1) * (L + 1) ≤ 1000 * (K + 1) * (2 * S + 10 * (L + 2) + 2) := by
      have a : (L + 1) * (L + 1) ≤ (K + 1) * (2 * S + 10 * (L + 2) + 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      calc 1000 * (L + 1) * (L + 1) = 1000 * ((L + 1) * (L + 1)) := by ring
        _ ≤ 1000 * ((K + 1) * (2 * S + 10 * (L + 2) + 2)) := Nat.mul_le_mul_left _ a
        _ = 1000 * (K + 1) * (2 * S + 10 * (L + 2) + 2) := by ring
    rw [Nat.mul_add]
    omega

theorem gateW_le_capNeed {q : ℕ} (C : List (NormalizedThresholdGate q)) :
    ∀ g ∈ C, (GateConv.gateW g).length ≤ GateConv.capNeed C := by
  intro g hg
  unfold GateConv.capNeed
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun g => 2 * (GateConv.selGate g).length +
    10 * ((GateConv.gateW g).length + 2) + 2) hg)
  omega

/-- **The gate converter's cost.** -/
theorem gsCost_le {q : ℕ} (C : List (NormalizedThresholdGate q)) :
    GateConv.gsCost C ≤ 1000 * (GateConv.capNeed C + 1) * GateConv.capNeed C + 2 * C.length + 1 := by
  unfold GateConv.gsCost
  have := gs_aux (GateConv.capNeed C) C (gateW_le_capNeed C)
  omega

open NearCubicWires.RepairOrdinary.Streaming (marks) in
/-- **One round of C1's carrier loop.** -/
theorem rcost_le {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V Hd Vb : ℕ) (ws : List (List Bool)) (x n : ℕ)
    (hn : 1 ≤ n) (hHd : Hd ≤ n) (hVb : Vb ≤ n) (hx : x ≤ n) (hV : V ≤ n) (hq : q ≤ n) (hl : lits.length ≤ n)
    (hcb : cb ≤ n) (h2 : 2 ^ (cb + 1) ≤ n) (hL : (FrontTWKit.frItems ws).length ≤ n)
    (hpre : C1CarPre.carPreCost (Cs x) 0 0 ≤ n) (hGF : (C1Gates.GF Cs lits x).length ≤ n)
    (hcap : GateConv.capNeed (Cs x) ≤ n) (hcs : (Cs x).length ≤ n) (hsel : ((Cs x).flatMap GateConv.selGate).length ≤ n)
    (hgt : C1Gates.gtF Cs lits x ≤ n) (hcnt : C1Cnt.cntOf x lits ≤ n) (hPF : (C1Gates.PF Cs lits cb x).length ≤ n)
    (hnp : C1Gates.npF lits x ≤ n)
    (hm1 : (marks (natListWord (List.range' (C1Gates.gtF Cs lits x) (Cs x).length))).length ≤ n)
    (hm2 : (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length ≤ n) :
    C1Gates.rcost Cs lits cb V Hd Vb ws x ≤ 10 ^ 12 * n ^ 6 := by
  have hgs := gsCost_le (Cs x)
  have b1 := FrontSemEv.nbl_le_self (C1Cnt.cntOf x lits)
  have b2 := FrontSemEv.nbl_le_self (2 ^ (cb + 1))
  have b3 := FrontSemEv.nbl_le_self (Cs x).length
  have b4 := FrontSemEv.nbl_le_self (C1Gates.gtF Cs lits x + (Cs x).length)
  unfold C1Gates.rcost C1Item.itemC C1RoundW.roundC C1Cnt.cntC C1Cnt.litC C1Cnt.rdC C1RoundW.gateC C1RoundW.popC
    C1Rng.rangeCost C1Rat.ratCost C1Rng.wnCost
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

/-- **C1's request assembly.** -/
theorem asmCost_le (cr q gt np : ℕ) (Gs Ps : List Bool) (n : ℕ) (hn : 1 ≤ n) (hcr : cr ≤ n) (hq : q ≤ n)
    (hr : Ledger.rowBr cr q ≤ n) (hgt : gt ≤ n) (hnp : np ≤ n) (hG : Gs.length ≤ n) (hP : Ps.length ≤ n) :
    C1Asm.asmCost cr q gt np Gs Ps ≤ 10 ^ 9 * n ^ 3 := by
  have b1 := FrontSemEv.nbl_le_self q
  have b2 := FrontSemEv.nbl_le_self (Ledger.rowBr cr q)
  have b3 := FrontSemEv.nbl_le_self gt
  have b4 := FrontSemEv.nbl_le_self np
  unfold C1Asm.asmCost C1Asm.wCost C1Asm.wnC
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

/-- **The selection's framing.** -/
theorem convCost_le (xs : List ℕ) (n : ℕ) (hn : 1 ≤ n) (hx : xs.length ≤ n) (hw : (natListWord xs).length ≤ n) :
    C1Stage.convCost xs ≤ 10 ^ 6 * n ^ 2 := by
  unfold C1Stage.convCost
  exact np_fin hn (by c6np) (by norm_num) (by norm_num)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostC1
