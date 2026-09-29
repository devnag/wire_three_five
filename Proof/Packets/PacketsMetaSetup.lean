import Proof.Packets.PacketsMetaTail

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.PacketsMeta.CutoffMath
noncomputable section

namespace Setup
open Lev

/-! ## Docked primitives -/

section At
variable {N W : ℕ}

theorem unframe_at (σ : Fin N → TS) (s d m : Fin N) (hi : Function.Injective ![s, d, m]) (h : ℕ)
    (w : List Bool) (fx : ℕ → Bool)
    (hX : ∀ i, i < (RepairOrdinary.frame w).length → fx (h + i) = (RepairOrdinary.frame w).getD i false)
    (hs : σ s = .cells fx h) (hd : σ d = .cells blank 0) (hm : σ m = .cells blank 0) :
    LRuns W (RecoveryFocus.machine ![s, d, m] Unframe.machine) (5 * w.length + 10) σ
      (Function.update (Function.update (Function.update σ m (.cells (sf (List.replicate w.length true)) 1))
        d (.cells (sf w) 1)) s (.cells fx (h + (RepairOrdinary.frame w).length))) :=
  (Unframe.lruns W h w fx hX).dockK ![s, d, m] hi σ
    (by intro j; fin_cases j
        · exact hs
        · exact hd
        · exact hm) [0, 1, 2]
    (by intro j hj; fin_cases j <;> simp at hj)

theorem moveR_at (σ : Fin N → TS) (x : Fin N) (h : ℕ) (f : ℕ → Bool) (hx : σ x = .cells f h) :
    LRuns W (RecoveryFocus.machine ![x] moveR) 1 σ (Function.update σ x (.cells f (h + 1))) :=
  (moveR_lruns W h f).dockK ![x] (by intro a b _; fin_cases a; fin_cases b; rfl) σ
    (by intro j; fin_cases j; exact hx) [0]
    (by intro j hj; fin_cases j; simp at hj)

theorem rappend_at (σ : Fin N → TS) (mk s r : Fin N) (hi : Function.Injective ![mk, s, r]) (k : ℕ) (hk : 1 ≤ k)
    (n P : ℕ) (hP : 1 ≤ P) (f : ℕ → Bool) (hm : σ mk = .cells (sf (List.replicate n true)) 1)
    (hs : σ s = .cells f 1) (hr : σ r = .cells (Ruler.rb P) P) :
    LRuns W (RecoveryFocus.machine ![mk, s, r] (Ruler.append k)) ((k + 1) * n + n + 7) σ
      (Function.update σ r (.cells (Ruler.rb (P + k * n)) (P + k * n))) :=
  (Ruler.append_lruns W k hk n P hP f).dockK ![mk, s, r] hi σ
    (by intro j; fin_cases j
        · exact hm
        · exact hs
        · exact hr) [2]
    (by intro j hj; fin_cases j <;> simp at hj ⊢)

theorem rfinish_at (σ : Fin N → TS) (r : Fin N) (hr : σ r = .cells (Ruler.rb (W + 1)) (W + 1)) :
    LRuns W (RecoveryFocus.machine ![r] Ruler.finish) (W + 3) σ (Function.update σ r .ruler) :=
  (Ruler.finish_lruns W).dockK ![r] (by intro a b _; fin_cases a; fin_cases b; rfl) σ
    (by intro j; fin_cases j; exact hr) [0]
    (by intro j hj; fin_cases j; simp at hj)

theorem peek_at (σ : Fin N → TS) (s fl : Fin N) (hi : Function.Injective ![s, fl]) (p : ℕ) (f : ℕ → Bool)
    (c : Bool) (hs : σ s = .cells f p) (hf : σ fl = .flag c) :
    LRuns W (RecoveryFocus.machine ![s, fl] peek) 1 σ (Function.update σ fl (.flag (f p))) :=
  (peek_lruns W p f c).dockK ![s, fl] hi σ
    (by intro j; fin_cases j
        · exact hs
        · exact hf) [1]
    (by intro j hj; fin_cases j <;> simp at hj ⊢)

theorem word_at (σ : Fin N → TS) (s m : Fin N) (hi : Function.Injective ![s, m]) (u : List Bool)
    (hs : σ s = .cells blank 0) (hm : σ m = .cells blank 0) :
    LRuns W (RecoveryFocus.machine ![s, m] (Word.machine u)) (2 * u.length + 7) σ
      (Function.update (Function.update σ m (.cells (sf (List.replicate u.length true)) 1)) s (.cells (sf u) 1)) :=
  (Word.lruns W u).dockK ![s, m] hi σ
    (by intro j; fin_cases j
        · exact hs
        · exact hm) [0, 1]
    (by intro j hj; fin_cases j <;> simp at hj)

end At

/-! ## The padding circuit -/

/-- The padding child: arity `0`, target `0`. -/
def padG : ExactThresholdGate 0 := ⟨Fin.elim0, 0⟩

/-- The padding circuit data: one child, record `(0, 0, 0)`. -/
def padCD : CD := ⟨0, [padG]⟩

theorem tab_pad : tab padCD = [((0 : ℕ), (0 : ℕ), (0 : ℕ))] := by
  simp [tab, padCD, padG, childRec]

/-- The circuit data of a list of present circuits, padded to four. -/
def dOf (ds : List CD) (c : Fin 4) : CD := ds.getD c.val padCD

/-- The `topWord` of a list of circuit data. -/
def twOf (ds : List CD) : List Bool := ds.flatMap (fun e => RepairOrdinary.frame (pay e))

/-- The `topWord` cursor after `k` circuits. -/
def p9 (ds : List CD) (k : ℕ) : ℕ := 1 + ((ds.take k).flatMap (fun e => RepairOrdinary.frame (pay e))).length

theorem pay_ne_nil (e : CD) : pay e ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [pay_eq] at this
  simp [ReadNat.natWord_length] at this

theorem peek_val (ds : List CD) (c : ℕ) : sf (twOf ds) (p9 ds c) = decide (c < ds.length) := by
  by_cases hc : c < ds.length
  · rw [decide_eq_true hc]
    have hsplit := flatMap_split (fun e => RepairOrdinary.frame (pay e)) ds c hc
    have h := read_sub (sf (twOf ds)) 1 ((ds.take c).flatMap (fun e => RepairOrdinary.frame (pay e)))
      (RepairOrdinary.frame (pay ds[c])) ((ds.drop (c + 1)).flatMap (fun e => RepairOrdinary.frame (pay e)))
      (by
        intro k _
        rw [Nat.add_comm, sf_succ, twOf, hsplit])
      0 (by rw [RepairOrdinary.frame_length]; omega)
    rw [Nat.add_zero] at h
    unfold p9
    rw [h]
    have hne : 0 < (pay ds[c]).length := List.length_pos_of_ne_nil (pay_ne_nil _)
    have h0 := frame_getD_even (pay ds[c]) 0
    simp only [Nat.mul_zero] at h0
    rw [h0]
    simp [hne]
  · rw [decide_eq_false hc]
    have ht : ds.take c = ds := List.take_of_length_le (by omega)
    unfold p9
    rw [ht]
    exact sf_out _ _ (by simp only [twOf]; omega)

/-! ## The extraction role map -/

def sOf : Option (List Bool) → TS
  | some w => .cells (sf w) 1
  | none => .cells blank 0

def mOf : Option (List Bool) → TS
  | some w => .cells (sf (List.replicate w.length true)) 1
  | none => .cells blank 0

/-- The roles during the extraction: flag `b`, the `topWord` stream at cursor `p`, the circuit streams
`ps` (filled or blank), `fx` elsewhere. -/
def Sv (fx : Fin 60 → TS) (tw : List Bool) (ps : Fin 4 → Option (List Bool)) (p : ℕ) (b : Bool) : Fin 60 → TS :=
  ![fx 0, fx 1, fx 2, fx 3, .flag b, fx 5, fx 6, fx 7, fx 8, .cells (sf tw) p, fx 10,
    sOf (ps 0), mOf (ps 0), sOf (ps 1), mOf (ps 1), sOf (ps 2), mOf (ps 2), sOf (ps 3), mOf (ps 3),
    fx 19, fx 20, fx 21, fx 22, fx 23, fx 24, fx 25, fx 26, fx 27, fx 28, fx 29, fx 30, fx 31, fx 32, fx 33, fx 34, fx 35, fx 36, fx 37, fx 38, fx 39, fx 40, fx 41, fx 42, fx 43, fx 44, fx 45, fx 46, fx 47, fx 48, fx 49, fx 50, fx 51, fx 52, fx 53, fx 54, fx 55, fx 56, fx 57, fx 58, fx 59]

section Sv
variable (fx : Fin 60 → TS) (tw : List Bool) (ps : Fin 4 → Option (List Bool)) (p : ℕ) (b : Bool)

theorem Sv_S (c : Fin 4) : Sv fx tw ps p b (sS c) = sOf (ps c) := by fin_cases c <;> rfl
theorem Sv_M (c : Fin 4) : Sv fx tw ps p b (sM c) = mOf (ps c) := by fin_cases c <;> rfl

theorem upS_fl (b' : Bool) : Function.update (Sv fx tw ps p b) 4 (.flag b') = Sv fx tw ps p b' := by
  funext i; fin_cases i <;> rfl
theorem upS_9 (p' : ℕ) : Function.update (Sv fx tw ps p b) 9 (.cells (sf tw) p') = Sv fx tw ps p' b := by
  funext i; fin_cases i <;> rfl
theorem upS_SM (c : Fin 4) (w : List Bool) :
    Function.update (Function.update (Sv fx tw ps p b) (sM c) (.cells (sf (List.replicate w.length true)) 1))
      (sS c) (.cells (sf w) 1) = Sv fx tw (Function.update ps c (some w)) p b := by
  funext i; fin_cases c <;> fin_cases i <;> rfl
end Sv

/-! ## One extraction step -/

def extC (c : Fin 4) := Ite (RecoveryFocus.machine ![9, 4] peek)
  (RecoveryFocus.machine ![9, sS c, sM c] Unframe.machine)
  (RecoveryFocus.machine ![sS c, sM c] (Word.machine (pay padCD))) 4

theorem dOf_lt (ds : List CD) (c : Fin 4) (hc : c.val < ds.length) : dOf ds c = ds[c.val] := by
  simp [dOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]

theorem dOf_ge (ds : List CD) (c : Fin 4) (hc : ds.length ≤ c.val) : dOf ds c = padCD := by
  simp [dOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none hc]

theorem pay_le_tw (ds : List CD) (i : ℕ) (hi : i < ds.length) : (pay ds[i]).length ≤ (twOf ds).length := by
  have h := flatMap_split (fun e => RepairOrdinary.frame (pay e)) ds i hi
  have hf := RepairOrdinary.frame_length (pay ds[i])
  unfold twOf
  rw [h]
  simp only [List.length_append]
  omega

theorem ext_step {W : ℕ} (fx : Fin 60 → TS) (ds : List CD) (c : Fin 4) (ps : Fin 4 → Option (List Bool))
    (hps : ps c = none) (b : Bool) :
    LRuns W (extC c) (1 + (5 * (twOf ds).length + 10) + (2 * (pay padCD).length + 7) + 2)
      (Sv fx (twOf ds) ps (p9 ds c.val) b)
      (Sv fx (twOf ds) (Function.update ps c (some (pay (dOf ds c)))) (p9 ds (c.val + 1)) (decide (c.val < ds.length))) := by
  have hc := peek_at (W := W) (Sv fx (twOf ds) ps (p9 ds c.val) b) 9 4 (by decide) (p9 ds c.val) (sf (twOf ds)) b rfl rfl
  rw [peek_val, upS_fl] at hc
  refine Ite.runs (W := W) (nc := 1) (np := 5 * (twOf ds).length + 10) (nq := 2 * (pay padCD).length + 7)
    _ _ _ 4 (decide (c.val < ds.length)) hc rfl ?_ ?_
  · intro hb
    have hlt : c.val < ds.length := of_decide_eq_true hb
    have hsplit := flatMap_split (fun e => RepairOrdinary.frame (pay e)) ds c.val hlt
    have hX : ∀ i, i < (RepairOrdinary.frame (pay ds[c.val])).length →
        sf (twOf ds) (p9 ds c.val + i) = (RepairOrdinary.frame (pay ds[c.val])).getD i false :=
      read_sub (sf (twOf ds)) 1 ((ds.take c.val).flatMap (fun e => RepairOrdinary.frame (pay e)))
        (RepairOrdinary.frame (pay ds[c.val])) ((ds.drop (c.val + 1)).flatMap (fun e => RepairOrdinary.frame (pay e)))
        (by
          intro k _
          rw [Nat.add_comm, sf_succ, twOf, hsplit])
    have h := unframe_at (W := W) (Sv fx (twOf ds) ps (p9 ds c.val) (decide (c.val < ds.length))) 9 (sS c) (sM c)
      (by fin_cases c <;> decide) (p9 ds c.val) (pay ds[c.val]) (sf (twOf ds)) hX rfl
      (by rw [Sv_S, hps]; rfl) (by rw [Sv_M, hps]; rfl)
    rw [upS_SM, upS_9] at h
    have e1 : p9 ds c.val + (RepairOrdinary.frame (pay ds[c.val])).length = p9 ds (c.val + 1) := by
      unfold p9
      rw [take_succ_flatMap (fun e => RepairOrdinary.frame (pay e)) ds c.val hlt, List.length_append]
      omega
    rw [e1, ← dOf_lt ds c hlt] at h
    refine h.enlarge ?_
    have := pay_le_tw ds c.val hlt
    rw [dOf_lt ds c hlt]
    omega
  · intro hb
    have hge : ds.length ≤ c.val := by
      have := of_decide_eq_false hb
      omega
    have h := word_at (W := W) (Sv fx (twOf ds) ps (p9 ds c.val) (decide (c.val < ds.length))) (sS c) (sM c)
      (by fin_cases c <;> decide) (pay padCD) (by rw [Sv_S, hps]; rfl) (by rw [Sv_M, hps]; rfl)
    rw [upS_SM] at h
    have e1 : p9 ds c.val = p9 ds (c.val + 1) := by
      unfold p9
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    refine h.congr_out ?_
    rw [dOf_ge ds c hge, ← e1]

/-! ## All four circuits -/

def extAll := Composition.machine (extC 0) (Composition.machine (extC 1) (Composition.machine (extC 2) (extC 3)))

def extCost (ds : List CD) : ℕ := 4 * (1 + (5 * (twOf ds).length + 10) + (2 * (pay padCD).length + 7) + 2) + 3

theorem ext_run {W : ℕ} (fx : Fin 60 → TS) (ds : List CD) (b : Bool) :
    LRuns W extAll (extCost ds) (Sv fx (twOf ds) (fun _ => none) 1 b)
      (Sv fx (twOf ds) (fun c => some (pay (dOf ds c))) (p9 ds 4) (decide (3 < ds.length))) := by
  have h0 := ext_step (W := W) fx ds 0 (fun _ => none) rfl b
  have h1 := ext_step (W := W) fx ds 1 (Function.update (fun _ => none) 0 (some (pay (dOf ds 0)))) rfl
    (decide ((0 : Fin 4).val < ds.length))
  have h2 := ext_step (W := W) fx ds 2 (Function.update (Function.update (fun _ => none) 0 (some (pay (dOf ds 0))))
    1 (some (pay (dOf ds 1)))) rfl (decide ((1 : Fin 4).val < ds.length))
  have h3 := ext_step (W := W) fx ds 3 (Function.update (Function.update (Function.update (fun _ => none) 0
    (some (pay (dOf ds 0)))) 1 (some (pay (dOf ds 1)))) 2 (some (pay (dOf ds 2)))) rfl
    (decide ((2 : Fin 4).val < ds.length))
  have hall := h0.seq (h1.seq (h2.seq h3))
  have hp0 : p9 ds (0 : Fin 4).val = 1 := by simp [p9]
  rw [hp0] at hall
  refine (hall.congr_out ?_).enlarge (by unfold extCost; omega)
  congr 1
  funext c
  fin_cases c <;> rfl

end Setup

end
end NearCubicWires.PacketsMeta

