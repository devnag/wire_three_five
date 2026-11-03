import Proof.Wire_3_5.UnionMachine.C1Loop
import Proof.Wire_3_5.UnionMachine.LoopWhile

/-! # C6 front, the C1 dock: the carrier loop over every PCPP variable (P3:1326-1330, 3395-3399, 3673)

`V` rounds of `C1Loop.rndM` under base's stream controller (condition: the count stream `JS = 1^{V−j} 0^j`). After round
`j` the request pieces hold the first `j` variables' contributions, the positive-count ones only:
* `GF j` the gates in C1's format (`GateConv.selGate`), `PF j` the populations (`natListWord (range' start len)` and
  `ratWord (c_X/2^{cb+1})`), `gtF j` the gate total, `npF j` the positive-count variables;
* **`gates_loop`**: from the loop's entry bank, `V` rounds reach the bank with `GF V`, `PF V`, `gtF V`, `npF V`.

Paper quantity of the main type: the weighted carriers of `star:selection`'s request (P3:1326-1330). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Gates
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.C1Loop
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (frItems)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord natListWord)

section Data
variable {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb : ℕ)

/-- Whether variable `x` has positive weight. -/
def pos (x : ℕ) : Prop := 0 < C1Cnt.cntOf x lits

instance (x : ℕ) : Decidable (pos lits x) := by unfold pos; infer_instance

/-- The gate total after `j` variables. -/
def gtF : ℕ → ℕ
  | 0 => 0
  | j + 1 => gtF j + if pos lits j then (Cs j).length else 0

/-- The positive-count variables among the first `j`. -/
def npF : ℕ → ℕ
  | 0 => 0
  | j + 1 => npF j + if pos lits j then 1 else 0

/-- The gates in C1's format after `j` variables. -/
def GF : ℕ → List Bool
  | 0 => []
  | j + 1 => GF j ++ if pos lits j then (Cs j).flatMap GateConv.selGate else []

/-- The populations after `j` variables. -/
def PF : ℕ → List Bool
  | 0 => []
  | j + 1 => PF j ++ if pos lits j then natListWord (List.range' (gtF Cs lits j) (Cs j).length) ++
      NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf j lits : ℚ) / 2 ^ (cb + 1)) else []

end Data

theorem marks_app (u v : List Bool) : marks (u ++ v) = marks u ++ marks v :=
  NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.marks_append u v

section Loop
variable {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V : ℕ) (po src : List Bool)

/-- The loop's streams after `j` rounds (`0`, `9` are the table's tapes). -/
def Sj (j : ℕ) : Fin 11 → List Bool := fun i =>
  if i.val = 1 then marks (GF Cs lits j)
  else if i.val = 2 then po
  else if i.val = 3 then List.replicate j true
  else if i.val = 4 then marks (PF Cs lits cb j)
  else if i.val = 5 then List.replicate (gtF Cs lits j) true
  else if i.val = 6 then List.replicate (npF lits j) true
  else if i.val = 7 then List.replicate q true
  else if i.val = 8 then src
  else if i.val = 10 then List.replicate (V - j) true ++ List.replicate j false
  else []

theorem rlR_congr (cap : ℕ) (S S' : Fin 11 → List Bool) (h : ∀ i : Fin 11, i ≠ 0 → i ≠ 9 → S i = S' i) (k : ℕ) :
    rlR cap S k = rlR cap S' k := by
  funext j
  refine Fin.addCases (m := 76) (n := 1) (fun i => ?_) (fun o => ?_) j
  · unfold rlR
    simp only [Fin.val_castAdd]
    split_ifs with hj
    · rfl
    · rw [Fin.addCases_left, Fin.addCases_left]
      push Not at hj
      exact wenc_other cap S S' h i hj.1 hj.2
  · unfold rlR
    split_ifs
    · rfl
    · rw [Fin.addCases_right, Fin.addCases_right]

end Loop

section Run
variable {q : ℕ} (Cs : ℕ → Stars.Carrier q) (lits : List ℕ) (cb V : ℕ) (po src : List Bool)

/-- One round's cost at variable `x`. -/
noncomputable def rcost (Hd Vb : ℕ) (ws : List (List Bool)) (x : ℕ) : ℕ :=
  (2 * Hd + 4) + 1 + ((2 * C1Item.itemC x (frItems ws).length + 2) + 1 +
    (C1CarPre.carPreCost (Cs x) 0 0 + 1 + (2 * (C1RoundW.roundC x q Vb lits.length cb
      (C1RoundW.gateC (Cs x) (GF Cs lits x).length + 1 +
        C1RoundW.popC (gtF Cs lits x) (Cs x).length (C1Cnt.cntOf x lits) cb (PF Cs lits cb x).length (npF lits x)
          (marks (natListWord (List.range' (gtF Cs lits x) (Cs x).length))).length
          (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length) + 1 +
      (3 * (V - x) + 5)) + 2)))

theorem cond_bit (cap Hd k j : ℕ) (D : Fin 1357 → List Bool) :
    readTapeBit (bank D (rlR cap (Sj Cs lits cb V po src j) k) Hd (wSl 11)) 0 = decide (j < V) := by
  rw [bank_w]
  have e : wview D (rlR cap (Sj Cs lits cb V po src j) k) 11 = Sj Cs lits cb V po src j 10 := by
    unfold wview rlR
    simp only [show ((11 : Fin 77)).val = 11 from rfl, show (11 : ℕ) ≠ 0 by decide, show (11 : ℕ) ≠ 10 by decide,
      if_false, or_self]
    have e2 : (11 : Fin 77) = Fin.castAdd 1 (sTape (nr := 64) (10 : Fin 11)) := Fin.ext (by simp [sTape])
    rw [e2, Fin.addCases_left, wenc_A_s]
    rfl
  rw [e]
  simp only [Sj, show ((10 : Fin 11)).val = 10 from rfl]
  simp only [show (10 : ℕ) ≠ 1 by decide, show (10 : ℕ) ≠ 2 by decide, show (10 : ℕ) ≠ 3 by decide,
    show (10 : ℕ) ≠ 4 by decide, show (10 : ℕ) ≠ 5 by decide, show (10 : ℕ) ≠ 6 by decide, show (10 : ℕ) ≠ 7 by decide,
    show (10 : ℕ) ≠ 8 by decide, if_false, if_true]
  unfold readTapeBit
  rw [C1RL.getD_rep]
  simp

theorem next_streams (j : ℕ) (S' : Fin 11 → List Bool)
    (s2 : S' 2 = po) (s7 : S' 7 = List.replicate q true) (s8 : S' 8 = src) (s3 : S' 3 = List.replicate (j + 1) true)
    (s1 : S' 1 = (if 0 < C1Cnt.cntOf j lits then marks (GF Cs lits j) ++ marks ((Cs j).flatMap GateConv.selGate)
      else marks (GF Cs lits j)))
    (s4 : S' 4 = (if 0 < C1Cnt.cntOf j lits then marks (PF Cs lits cb j) ++
      marks (natListWord (List.range' (gtF Cs lits j) (Cs j).length)) ++
      marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf j lits : ℚ) / 2 ^ (cb + 1))) else marks (PF Cs lits cb j)))
    (s5 : S' 5 = List.replicate (gtF Cs lits j + if 0 < C1Cnt.cntOf j lits then (Cs j).length else 0) true)
    (s6 : S' 6 = List.replicate (npF lits j + if 0 < C1Cnt.cntOf j lits then 1 else 0) true)
    (s10 : S' 10 = List.replicate (V - j - 1) true ++ List.replicate (j + 1) false) :
    ∀ i : Fin 11, i ≠ 0 → i ≠ 9 → S' i = Sj Cs lits cb V po src (j + 1) i := by
  intro i h0 h9
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 10 by
    fin_cases i <;> simp_all) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [s1]; show _ = marks (GF Cs lits (j + 1))
    rw [GF]; unfold pos; split_ifs <;> simp [marks_app]
  · rw [s2]; rfl
  · rw [s3]; rfl
  · rw [s4]; show _ = marks (PF Cs lits cb (j + 1))
    rw [PF]; unfold pos; split_ifs <;> simp [marks_app]
  · rw [s5]; show _ = List.replicate (gtF Cs lits (j + 1)) true
    rw [gtF]; unfold pos; rfl
  · rw [s6]; show _ = List.replicate (npF lits (j + 1)) true
    rw [npF]; unfold pos; rfl
  · rw [s7]; rfl
  · rw [s8]; rfl
  · rw [s10]; show _ = List.replicate (V - (j + 1)) true ++ List.replicate (j + 1) false
    congr 2

/-- **The carrier loop.** -/
theorem gates_loop (cap Hd Vb c : ℕ) (ws : List (List Bool)) (rest8 bits rest2 : List Bool) (sys aux : ℕ)
    (hsrc : src = frItems ws ++ rest8) (hpo : po = C1Cnt.poWord sys aux cb bits lits ++ rest2)
    (hbits : bits.length = sys * q) (hws : ∀ x < V, x < ws.length ∧ ws.getD x [] = natWord (Cs x).code)
    (hsV : sys ≤ Vb) (haV : aux ≤ Vb) (hcV : cb ≤ Vb) (hlV : lits.length ≤ Vb) (hV : ∀ l ∈ lits, l ≤ Vb)
    (hxV : V ≤ Vb) (h3V : 3 ≤ Vb)
    (hHd : ∀ x < V, max (2 * (natWord (Cs x).code).length + 1) (C1CarPre.carPreCost (Cs x) 0 0 + 1) ≤ Hd)
    (hxc : V ≤ cap)
    (hcapR : ∀ x < V, sys * q + q + lits.length + 6 * Vb + 8 + x + q + GateConv.capNeed (Cs x) +
      2 * ((Cs x).flatMap GateConv.selGate).length + gtF Cs lits x + (Cs x).length + C1Cnt.cntOf x lits + cb +
      npF lits x + 2 ^ (cb + 2) + (marks (natListWord (List.range' (gtF Cs lits x) (Cs x).length))).length +
      (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length +
      6 * natBitLength (gtF Cs lits x + (Cs x).length) + 6 * natBitLength (C1Cnt.cntOf x lits + 2 ^ (cb + 1)) + 40
        ≤ cap)
    (hc : ∀ x < V, rcost Cs lits cb V Hd Vb ws x ≤ c)
    (D0 : Fin 1357 → List Bool) (hD0 : ∀ i, (D0 i).length ≤ Hd) (k0 : ℕ) :
    ∃ (Hn : Fin 1436 → ℕ) (An : Fin 1436 → List Bool),
      Step (StreamController.machine rndM (wSl 11)) (V * (c + 2) + 1) (fun _ => 0)
        (bank D0 (rlR cap (Sj Cs lits cb V po src 0) k0) Hd) Hn An ∧
      Hn = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ), (∀ i, (D i).length ≤ Hd) ∧
        An = bank D (rlR cap (Sj Cs lits cb V po src V) k) Hd := by
  let Inv : ℕ → (Fin 1436 → ℕ) → (Fin 1436 → List Bool) → Prop := fun j H A =>
    H = (fun _ => 0) ∧ ∃ (D : Fin 1357 → List Bool) (k : ℕ), (∀ i, (D i).length ≤ Hd) ∧
      A = bank D (rlR cap (Sj Cs lits cb V po src j) k) Hd
  obtain ⟨Hn, An, hstep, hfin⟩ := FrontLoopKit.whileInv rndM (wSl 11) V c Inv
    (by
      intro j hj H A hI
      obtain ⟨rfl, D, k, hD, rfl⟩ := hI
      obtain ⟨hjw, hwsj⟩ := hws j hj
      obtain ⟨D', S', k', hs, hD', s2, s7, s8, s3, s1, s4, s5, s6, s10⟩ := roundStep cap Hd (Cs j) D
        (Sj Cs lits cb V po src j) k ws rest8 j hjw hwsj (GF Cs lits j) (PF Cs lits cb j) bits rest2 lits sys aux cb
        (gtF Cs lits j) (npF lits j) Vb (V - j) j hD
        (by simp [Sj]) (by simp [Sj, hpo]) hbits (by simp [Sj]) (by simp [Sj]) (by simp [Sj]) (by simp [Sj])
        (by simp [Sj]) (by simp [Sj, hsrc]) (by simp [Sj]) (by omega) hsV haV hcV hlV hV (by omega) h3V
        (hHd j hj) (by omega) (hcapR j hj)
      refine ⟨_, _, hs.enlarge (hc j hj), rfl, D', k', hD', ?_⟩
      rw [rlR_congr cap S' (Sj Cs lits cb V po src (j + 1)) (next_streams Cs lits cb V po src j S' s2 s7 s8 s3 s1 s4 s5
        s6 s10) k'])
    (by
      intro j hj H A hI
      obtain ⟨rfl, D, k, -, rfl⟩ := hI
      rw [cond_bit]; simp [hj])
    (by
      intro H A hI
      obtain ⟨rfl, D, k, -, rfl⟩ := hI
      rw [cond_bit]; simp)
    (fun _ => 0) (bank D0 (rlR cap (Sj Cs lits cb V po src 0) k0) Hd) ⟨rfl, D0, k0, hD0, rfl⟩
  obtain ⟨hHn, D, k, hD, hAn⟩ := hfin
  exact ⟨Hn, An, hstep, hHn, D, k, hD, hAn⟩

end Run

end NearCubicWires.WireExponent3_5.UnionMachine.C1Gates
