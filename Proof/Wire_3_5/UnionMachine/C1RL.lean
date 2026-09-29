import Proof.Wire_3_5.UnionMachine.C1RoundW
import Proof.Wire_3_5.UnionMachine.C1Item

/-! # C6 front, the C1 dock: the round's two register programs on one layout

The carrier loop's round runs two register programs around the carrier table: the item copy
(`C1Item.itemW`, `WState 2 2`) and the variable's round (`C1RoundW.roundW`, `WState 7 64`) followed by the loop's
count `JS := JS − 1` (**`decJ`**). Both run on one layout `WState 10 64` (FinalPass's `WM.liftW`): streams `0` REGN,
`1` G, `2` PO, `3` XS, `4` POPS, `5` GT, `6` NP, `7` QS, `8` SRC (the carriers' codes), `9` OUT (the table's input),
`10` JS; registers `0 … 63`, the item copy's two at `60, 61`.
* **`itemRL_spec`**, **`roundRL_spec`**: the lifted programs' effects, every register back at `0`.

Paper quantity: none (the loop's register programs; the carriers' gates and weights are `roundW_spec`'s). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1RL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord natListWord)

abbrev RLS := WState 10 64

/-! ## The loop's count -/

theorem write_at (u r : List Bool) (a b : Bool) : writeTapeBit (u ++ a :: r) u.length b = u ++ b :: r := by
  induction u with
  | nil => rfl
  | cons c u ih => simp [writeTapeBit, ih]

theorem getD_rep (j k i : ℕ) : (List.replicate j true ++ List.replicate k false).getD i false = decide (i < j) := by
  by_cases h : i < j
  · rw [List.getD_append _ _ _ _ (by simpa using h)]; simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]; simp [h]

/-- `JS := JS − 1` on `1^j 0^k` (head `0`). -/
def decJ (s : Fin 11) : WM 10 64 := .seq (.whs s (.fwd s)) (.seq (.bwd s) (.wr s false))

theorem decJ_loop (cap : ℕ) (s : Fin 11) (j k : ℕ) : ∀ (m : ℕ) (ρ : RLS),
    ρ.st s = List.replicate j true ++ List.replicate k false → ρ.sh s + m = j →
    WExec cap (.whs s (.fwd s)) ρ (ρ.seth s j) (3 * m + 1)
  | 0, ρ, hs, hsh => by
    have hb : wbit ρ s = false := by
      unfold wbit readTapeBit; rw [hs, getD_rep]; simp; omega
    rw [show ρ.seth s j = ρ by rw [← show ρ.sh s = j by omega, wseth_same]]
    exact WExec.whsF hb
  | m + 1, ρ, hs, hsh => by
    have hb : wbit ρ s = true := by
      unfold wbit readTapeBit; rw [hs, getD_rep]; simp; omega
    have h1 := WExec.fwd (cap := cap) s ρ
    have ih := decJ_loop cap s j k m (ρ.seth s (ρ.sh s + 1)) (by simp [hs]) (by simp; omega)
    refine WExec.cast cap (WExec.whsT hb h1 ih) (wseth_seth _ _ _ _) (by omega)

theorem decJ_spec (cap : ℕ) (s : Fin 11) (j k : ℕ) (hj : 1 ≤ j) (ρ : RLS)
    (hs : ρ.st s = List.replicate j true ++ List.replicate k false) (hsh : ρ.sh s = 0) :
    WExec cap (decJ s) ρ ((ρ.sets s (List.replicate (j - 1) true ++ List.replicate (k + 1) false)).seth s (j - 1))
      (3 * j + 5) := by
  have h1 := decJ_loop cap s j k j ρ hs (by omega)
  have h2 := WExec.bwd (cap := cap) s (ρ.seth s j)
  have h3 := WExec.wr (cap := cap) s false ((ρ.seth s j).seth s ((ρ.seth s j).sh s - 1))
  refine WExec.mono (WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ le_rfl) (by omega)
  have hw : writeTapeBit (List.replicate j true ++ List.replicate k false) (j - 1) false =
      List.replicate (j - 1) true ++ List.replicate (k + 1) false := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, List.replicate_succ', List.append_assoc, List.singleton_append]
    have := write_at (List.replicate j' true) (List.replicate k false) true false
    rw [List.length_replicate] at this
    rw [this, List.replicate_succ]
  apply WState.eq
  · funext i; by_cases hi : i = s
    · subst hi; simp
    · simp [hi]
  · funext i; by_cases hi : i = s
    · subst hi; simp [hs, hw]
    · simp [hi]
  · rfl
  · rfl

/-! ## The liftings -/

def fsI : Fin 3 → Fin 11 := ![8, 9, 3]
def frI : Fin 2 → Fin 64 := ![60, 61]
def fsR : Fin 8 → Fin 11 := Fin.castLE (by decide)
def frR : Fin 64 → Fin 64 := id

theorem fsI_inj : Function.Injective fsI := by decide
theorem frI_inj : Function.Injective frI := by decide
theorem fsR_inj : Function.Injective fsR := Fin.castLE_injective _
theorem frR_inj : Function.Injective frR := fun _ _ h => h

/-- The item copy on the loop's layout. -/
def itemRL : WM 10 64 := C1Item.itemW.liftW fsI frI

/-- The variable's round and the count on the loop's layout. -/
def roundRL : WM 10 64 := .seq (C1RoundW.roundW.liftW fsR frR) (decJ 10)

/-- The restriction of a loop state to a smaller layout. -/
def restrict {ns nr : ℕ} (fs : Fin (ns + 1) → Fin 11) (fr : Fin nr → Fin 64) (ρ : RLS) : WState ns nr :=
  ⟨fun i => ρ.sh (fs i), fun i => ρ.st (fs i), fun r => ρ.val (fr r), ρ.cell⟩

theorem liftW_restrict {ns nr : ℕ} (fs : Fin (ns + 1) → Fin 11) (fr : Fin nr → Fin 64) (ρ : RLS) :
    LiftW fs fr ρ (restrict fs fr ρ) := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

/-- **The item copy on the loop's layout.** -/
theorem itemRL_spec (cap : ℕ) (ρ : RLS) (ws : List (List Bool)) (rest : List Bool) (x k : ℕ)
    (hsrc : ρ.st 8 = frItems ws ++ rest) (hout : ρ.st 9 = List.replicate k false) (hxs : ρ.st 3 = List.replicate x true)
    (hsh : ∀ i, ρ.sh i = 0) (hv : ∀ r, ρ.val r = 0) (hx : x < ws.length)
    (hk : 2 * (ws.getD x []).length + 1 ≤ k) (hcap : x ≤ cap) :
    ∃ ρ' : RLS, WExec cap itemRL ρ ρ' (C1Item.itemC x (frItems ws).length) ∧
      ρ'.st 9 = frame (ws.getD x []) ++ List.replicate (k - (2 * (ws.getD x []).length + 1)) false ∧
      (∀ i : Fin 11, i ≠ 9 → ρ'.st i = ρ.st i) ∧ (∀ r, ρ'.val r = 0) ∧ ρ'.cell = ρ.cell := by
  obtain ⟨τ, e, t0, t1, t2, tv, tc⟩ := C1Item.itemW_spec cap (restrict fsI frI ρ) ws rest x k hsrc hout hxs
    (fun i => hsh _) (fun r => hv _) hx hk hcap
  obtain ⟨ρ', e', hl, ho⟩ := WExec.liftW cap cap le_rfl fsI fsI_inj frI frI_inj e ρ (liftW_restrict fsI frI ρ)
  refine ⟨ρ', e', ?_, ?_, ?_, ?_⟩
  · rw [show (9 : Fin 11) = fsI 1 from rfl, hl.st 1, t1]
  · intro i hi
    by_cases h8 : i = 8
    · subst h8; rw [show (8 : Fin 11) = fsI 0 from rfl, hl.st 0, t0]; rfl
    by_cases h3 : i = 3
    · subst h3; rw [show (3 : Fin 11) = fsI 2 from rfl, hl.st 2, t2]; rfl
    exact (ho.1 i (fun k => by fin_cases k <;> simp [fsI] <;> first | exact Ne.symm h8 | exact Ne.symm hi |
      exact Ne.symm h3)).2
  · intro r
    by_cases h60 : r = 60
    · subst h60; rw [show (60 : Fin 64) = frI 0 from rfl, hl.val 0, tv]
    by_cases h61 : r = 61
    · subst h61; rw [show (61 : Fin 64) = frI 1 from rfl, hl.val 1, tv]
    rw [ho.2 r (fun k => by fin_cases k <;> simp [frI] <;> first | exact Ne.symm h60 | exact Ne.symm h61), hv]
  · rw [hl.cell, tc]; rfl

/-- **The variable's round and the count on the loop's layout.** -/
theorem roundRL_spec (cap : ℕ) {q : ℕ} (C : List (NormalizedThresholdGate q)) (ρ : RLS)
    (rest0 Gacc Pacc bits rest2 : List Bool) (lits : List ℕ) (sys aux cb x gt np V j kk : ℕ)
    (h0 : ρ.st 0 = C1RoundW.hdr4 ++ GateConv.tabL C ++ rest0) (hr0 : readTapeBit rest0 0 = false)
    (h1 : ρ.st 1 = marks Gacc) (h2 : ρ.st 2 = C1Cnt.poWord sys aux cb bits lits ++ rest2)
    (hbits : bits.length = sys * q) (h3 : ρ.st 3 = List.replicate x true) (h4 : ρ.st 4 = marks Pacc)
    (h5 : ρ.st 5 = List.replicate gt true) (h6 : ρ.st 6 = List.replicate np true)
    (h7 : ρ.st 7 = List.replicate q true) (h10 : ρ.st 10 = List.replicate j true ++ List.replicate kk false)
    (hj : 1 ≤ j) (hsh : ∀ i, ρ.sh i = 0) (hv : ∀ r, ρ.val r = 0)
    (hsV : sys ≤ V) (haV : aux ≤ V) (hcV : cb ≤ V) (hlV : lits.length ≤ V) (hV : ∀ l ∈ lits, l ≤ V) (hxV : x ≤ V)
    (h3V : 3 ≤ V)
    (hcap : sys * q + q + lits.length + 6 * V + 8 + x + q + GateConv.capNeed C +
      2 * (C.flatMap GateConv.selGate).length + gt + C.length + C1Cnt.cntOf x lits + cb + np + 2 ^ (cb + 2) +
      (marks (natListWord (List.range' gt C.length))).length +
      (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length +
      6 * natBitLength (gt + C.length) + 6 * natBitLength (C1Cnt.cntOf x lits + 2 ^ (cb + 1)) + 40 ≤ cap) :
    ∃ ρ' : RLS, WExec cap roundRL ρ ρ' (C1RoundW.roundC x q V lits.length cb (C1RoundW.gateC C Gacc.length + 1 +
        C1RoundW.popC gt C.length (C1Cnt.cntOf x lits) cb Pacc.length np
          (marks (natListWord (List.range' gt C.length))).length
          (marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1)))).length) + 1 +
        (3 * j + 5)) ∧
      ρ'.st 0 = ρ.st 0 ∧ ρ'.st 2 = ρ.st 2 ∧ ρ'.st 7 = ρ.st 7 ∧ ρ'.st 8 = ρ.st 8 ∧ ρ'.st 9 = ρ.st 9 ∧
      ρ'.st 3 = List.replicate (x + 1) true ∧
      ρ'.st 1 = (if 0 < C1Cnt.cntOf x lits then marks Gacc ++ marks (C.flatMap GateConv.selGate) else marks Gacc) ∧
      ρ'.st 4 = (if 0 < C1Cnt.cntOf x lits then marks Pacc ++ marks (natListWord (List.range' gt C.length)) ++
        marks (NearCubicWires.WireExponent3_5.ratWord ((C1Cnt.cntOf x lits : ℚ) / 2 ^ (cb + 1))) else marks Pacc) ∧
      ρ'.st 5 = List.replicate (gt + if 0 < C1Cnt.cntOf x lits then C.length else 0) true ∧
      ρ'.st 6 = List.replicate (np + if 0 < C1Cnt.cntOf x lits then 1 else 0) true ∧
      ρ'.st 10 = List.replicate (j - 1) true ++ List.replicate (kk + 1) false ∧
      (∀ r, ρ'.val r = 0) ∧ ρ'.cell = ρ.cell := by
  obtain ⟨τ, e, t0, t2, t7, t3, t1, t4, t5, t6, tv, tc⟩ := C1RoundW.roundW_spec cap C (restrict fsR frR ρ)
    rest0 Gacc Pacc bits rest2 lits sys aux cb x gt np V h0 hr0 h1 h2 hbits h3 h4 h5 h6 h7 (fun i => hsh _)
    (fun r => hv _) hsV haV hcV hlV hV hxV h3V hcap
  obtain ⟨ρ1, e1, hl, ho⟩ := WExec.liftW cap cap le_rfl fsR fsR_inj frR frR_inj e ρ (liftW_restrict fsR frR ρ)
  have out : ∀ i : Fin 11, 8 ≤ i.val → ∀ k, fsR k ≠ i := fun i hi k e' => by
    have := congrArg Fin.val e'; simp [fsR] at this; omega
  have o10 := ho.1 10 (out 10 (by decide))
  have e2 := decJ_spec cap 10 j kk hj ρ1 (by rw [o10.2, h10]) (by rw [o10.1, hsh])
  refine ⟨_, WExec.seq e1 e2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (0 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (0 : Fin 11) = fsR 0 from rfl, hl.st 0, t0]; rfl
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (2 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (2 : Fin 11) = fsR 2 from rfl, hl.st 2, t2]; rfl
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (7 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (7 : Fin 11) = fsR 7 from rfl, hl.st 7, t7]; rfl
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (8 : Fin 11) ≠ 10 by decide, if_false]
    exact (ho.1 8 (out 8 (by decide))).2
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (9 : Fin 11) ≠ 10 by decide, if_false]
    exact (ho.1 9 (out 9 (by decide))).2
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (3 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (3 : Fin 11) = fsR 3 from rfl, hl.st 3, t3]
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (1 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (1 : Fin 11) = fsR 1 from rfl, hl.st 1, t1]
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (4 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (4 : Fin 11) = fsR 4 from rfl, hl.st 4, t4]
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (5 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (5 : Fin 11) = fsR 5 from rfl, hl.st 5, t5]
  · simp only [WState.seth_st, WState.sets_st, Function.update_apply, show (6 : Fin 11) ≠ 10 by decide, if_false]
    rw [show (6 : Fin 11) = fsR 6 from rfl, hl.st 6, t6]
  · simp
  · intro r; simp only [WState.seth_val, WState.sets_val]; rw [show r = frR r from rfl, hl.val r, tv]
  · simp only [WState.seth_cell, WState.sets_cell]; rw [hl.cell, tc]; rfl

end NearCubicWires.WireExponent3_5.UnionMachine.C1RL
