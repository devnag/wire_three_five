import Proof.Packets.PacketsMetaMul
import Proof.Packets.PacketsMetaCutoffMath

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

/-! ## Reading a sub-word -/

theorem read_sub (f : ℕ → Bool) (p : ℕ) (A B C : List Bool)
    (h : ∀ k, k < (A ++ B ++ C).length → f (p + k) = (A ++ B ++ C).getD k false) :
    ∀ k, k < B.length → f (p + A.length + k) = B.getD k false := by
  intro k hk
  have := h (A.length + k) (by simp; omega)
  rw [← Nat.add_assoc] at this
  rw [this, List.append_assoc, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_append_left hk]

theorem flatMap_split {α β : Type} (F : α → List β) (ws : List α) (i : ℕ) (hi : i < ws.length) :
    ws.flatMap F = (ws.take i).flatMap F ++ F ws[i] ++ (ws.drop (i + 1)).flatMap F := by
  have e : ws = ws.take i ++ ws[i] :: ws.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  conv_lhs => rw [e]
  rw [List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem take_succ_flatMap {α β : Type} (F : α → List β) (ws : List α) (i : ℕ) (hi : i < ws.length) :
    (ws.take (i + 1)).flatMap F = (ws.take i).flatMap F ++ F ws[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append]
  simp

theorem intWord_length (z : ℤ) : (intWord z).length = 1 + (natWord z.natAbs).length := by
  simp [intWord]; omega

/-- Rewriting the source roles of a run. -/
theorem LRuns.congr_in {t s W : ℕ} {P : Machine t s} {n : ℕ} {σ0 σ σ' : Fin t → TS}
    (h : LRuns W P n σ σ') (e : σ0 = σ) : LRuns W P n σ0 σ' := e ▸ h

theorem readBit_at {N W : ℕ} (σ : Fin N → TS) (m s fl : Fin N) (hi : Function.Injective ![m, s, fl]) (q : ℕ)
    (f g : ℕ → Bool) (c : Bool) (hm : σ m = .cells g q) (hs : σ s = .cells f q) (hf : σ fl = .flag c) :
    LRuns W (RecoveryFocus.machine ![m, s, fl] readBit) 1 σ
      (Function.update (Function.update (Function.update σ m (.cells g (q + 1))) s (.cells f (q + 1)))
        fl (.flag (f q))) := by
  have h := (readBit_lruns W q f g c).dockK ![m, s, fl] hi σ
    (by intro j; fin_cases j
        · exact hm
        · exact hs
        · exact hf) [2, 1, 0]
    (by intro j hj; fin_cases j <;> simp at hj)
  exact h

namespace Child

abbrev rl : Fin 12 := 0
abbrev ss : Fin 12 := 1
abbrev mm : Fin 12 := 2
abbrev uu : Fin 12 := 3
abbrev na : Fin 12 := 4
abbrev kw : Fin 12 := 5
abbrev xx : Fin 12 := 6
abbrev aa : Fin 12 := 7
abbrev pp : Fin 12 := 8
abbrev qq : Fin 12 := 9
abbrev fl : Fin 12 := 10
abbrev zo : Fin 12 := 11

def rdBit := RecoveryFocus.machine ![mm, ss, fl] readBit
def rdNat := ReadNat.at5 rl ss mm uu xx

def init :=
  Composition.machine (swAt zeroF false true rl aa zo fl)
    (Composition.machine (swAt zeroF false true rl pp zo fl)
      (Composition.machine (swAt zeroF false true rl qq zo fl)
        (Composition.machine (swAt zeroF false true rl xx zo fl) (swAt copyF false true rl kw na fl))))

def body :=
  Composition.machine (swAt subF true true rl kw zo fl)
    (Composition.machine rdBit (Composition.machine rdNat (swAt addF false true rl aa xx fl)))

def test := swAt subF false false rl zo kw fl

def tail :=
  Composition.machine rdBit (Composition.machine rdNat
    (Composition.machine (Ite (nop 12) (swAt copyF false true rl qq xx fl) (swAt copyF false true rl pp xx fl) fl)
      (swAt zeroF false true rl xx zo fl)))

def machine := Composition.machine (Composition.machine init (Loop test body fl)) tail

/-- The roles: stream content `f` with marks `g` at cursor `c`. -/
def cst (f g : ℕ → Bool) (c n k x a pv qv : ℕ) (b : Bool) : Fin 12 → TS :=
  ![.ruler, .cells f c, .cells g c, .cells blank 0, .reg n, .reg k, .reg x, .reg a, .reg pv, .reg qv, .flag b, .reg 0]

section Run
variable (W : ℕ) (f g : ℕ → Bool) (p : ℕ) {n : ℕ} (G : ExactThresholdGate n)

/-- The weights. -/
abbrev ws := List.ofFn G.weight
/-- The cursor after `i` weights. -/
def pos (i : ℕ) : ℕ := p + (((ws G).take i).flatMap intWord).length
/-- The weight magnitudes read so far. -/
def asum (i : ℕ) : ℕ := (((ws G).take i).map Int.natAbs).sum
/-- The last weight magnitude read. -/
def xv (i : ℕ) : ℕ := if i = 0 then 0 else ((ws G).getD (i - 1) 0).natAbs

end Run

theorem ws_length {n : ℕ} (G : ExactThresholdGate n) : (ws G).length = n := List.length_ofFn

theorem exactWord_eq {n : ℕ} (G : ExactThresholdGate n) : exactWord G = (ws G).flatMap intWord ++ intWord G.target :=
  rfl

theorem asum_succ {n : ℕ} (G : ExactThresholdGate n) (i : ℕ) (hi : i < n) :
    asum G (i + 1) = asum G i + ((ws G)[i]'(by rw [ws_length]; exact hi)).natAbs := by
  unfold asum
  rw [List.take_succ_eq_append_getElem (by rw [ws_length]; exact hi)]
  simp

theorem asum_le {n : ℕ} (G : ExactThresholdGate n) (i : ℕ) : asum G i ≤ (childRec G).1 := by
  unfold asum
  have h1 : (childRec G).1 = ((ws G).map Int.natAbs).sum := by simp [childRec]
  rw [h1]
  conv_rhs => rw [← List.take_append_drop i (ws G)]
  rw [List.map_append, List.sum_append]
  omega

theorem asum_full {n : ℕ} (G : ExactThresholdGate n) : asum G n = (childRec G).1 := by
  unfold asum
  rw [List.take_of_length_le (by rw [ws_length])]
  simp [childRec]

theorem pos_succ (p : ℕ) {n : ℕ} (G : ExactThresholdGate n) (i : ℕ) (hi : i < n) :
    pos p G (i + 1) = pos p G i + 1 + (natWord ((ws G)[i]'(by rw [ws_length]; exact hi)).natAbs).length := by
  unfold pos
  rw [take_succ_flatMap intWord (ws G) i (by rw [ws_length]; exact hi), List.length_append, intWord_length]
  omega

/-- The stream facts of weight `i`. -/
theorem weight_read (f : ℕ → Bool) (p : ℕ) {n : ℕ} (G : ExactThresholdGate n)
    (hS : ∀ k, k < (exactWord G).length → f (p + k) = (exactWord G).getD k false) (i : ℕ) (hi : i < n) :
    f (pos p G i) = decide ((ws G)[i]'(by rw [ws_length]; exact hi) < 0) ∧
      ∀ k, k < (natWord ((ws G)[i]'(by rw [ws_length]; exact hi)).natAbs).length →
        f (pos p G i + 1 + k) = (natWord ((ws G)[i]'(by rw [ws_length]; exact hi)).natAbs).getD k false := by
  have hi' : i < (ws G).length := by rw [ws_length]; exact hi
  have e : exactWord G = ((ws G).take i).flatMap intWord ++ intWord (ws G)[i] ++
      (((ws G).drop (i + 1)).flatMap intWord ++ intWord G.target) := by
    rw [exactWord_eq, flatMap_split intWord (ws G) i hi']
    simp [List.append_assoc]
  rw [e] at hS
  have hsub := read_sub f p _ _ _ hS
  constructor
  · have := hsub 0 (by simp [intWord])
    rw [Nat.add_zero] at this
    rw [pos, this]; simp [intWord]
  · intro k hk
    have := hsub (1 + k) (by rw [intWord_length]; omega)
    rw [pos, show p + ((List.take i (ws G)).flatMap intWord).length + 1 + k =
      p + ((List.take i (ws G)).flatMap intWord).length + (1 + k) by omega, this]
    rw [show 1 + k = k + 1 by omega]
    simp [intWord]

/-- The stream facts of the target. -/
theorem target_read (f : ℕ → Bool) (p : ℕ) {n : ℕ} (G : ExactThresholdGate n)
    (hS : ∀ k, k < (exactWord G).length → f (p + k) = (exactWord G).getD k false) :
    f (pos p G n) = decide (G.target < 0) ∧
      ∀ k, k < (natWord G.target.natAbs).length →
        f (pos p G n + 1 + k) = (natWord G.target.natAbs).getD k false := by
  have e : exactWord G = ((ws G).take n).flatMap intWord ++ intWord G.target ++ [] := by
    rw [exactWord_eq, List.take_of_length_le (by rw [ws_length]), List.append_nil]
  rw [e] at hS
  have hsub := read_sub f p _ _ _ hS
  constructor
  · have := hsub 0 (by simp [intWord])
    rw [Nat.add_zero] at this
    rw [pos, this]; simp [intWord]
  · intro k hk
    have := hsub (1 + k) (by rw [intWord_length]; omega)
    rw [pos, show p + ((List.take n (ws G)).flatMap intWord).length + 1 + k =
      p + ((List.take n (ws G)).flatMap intWord).length + (1 + k) by omega, this]
    rw [show 1 + k = k + 1 by omega]
    simp [intWord]

theorem pos_full (p : ℕ) {n : ℕ} (G : ExactThresholdGate n) :
    pos p G n + 1 + (natWord G.target.natAbs).length = p + (exactWord G).length := by
  unfold pos
  rw [exactWord_eq, List.take_of_length_le (by rw [ws_length]), List.length_append, intWord_length]
  omega

theorem pos_zero (p : ℕ) {n : ℕ} (G : ExactThresholdGate n) : pos p G 0 = p := by simp [pos]
theorem asum_zero {n : ℕ} (G : ExactThresholdGate n) : asum G 0 = 0 := by simp [asum]
theorem xv_zero {n : ℕ} (G : ExactThresholdGate n) : xv G 0 = 0 := rfl
theorem xv_succ {n : ℕ} (G : ExactThresholdGate n) (i : ℕ) (hi : i < n) :
    xv G (i + 1) = ((ws G)[i]'(by rw [ws_length]; exact hi)).natAbs := by
  unfold xv
  rw [if_neg (by omega), Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by rw [ws_length]; exact hi)]

theorem init_run (W : ℕ) (f g : ℕ → Bool) (c n k x a pv qv : ℕ) (b : Bool) (hn : n < 2 ^ W) :
    LRuns W init (5 * (2 * W + 3) + 4) (cst f g c n k x a pv qv b) (cst f g c n n 0 0 0 0 false) := by
  have h := (zero_at (W := W) (cst f g c n k x a pv qv b) rl aa zo fl (by decide) a 0 b rfl rfl rfl rfl).seq
    ((zero_at (W := W) _ rl pp zo fl (by decide) pv 0 _ (by rfl) (by rfl) (by rfl) (by rfl)).seq
    ((zero_at (W := W) _ rl qq zo fl (by decide) qv 0 _ (by rfl) (by rfl) (by rfl) (by rfl)).seq
    ((zero_at (W := W) _ rl xx zo fl (by decide) x 0 _ (by rfl) (by rfl) (by rfl) (by rfl)).seq
    (cpy_at (W := W) _ rl kw na fl (by decide) k n _ (by rfl) (by rfl) (by rfl) (by rfl) hn))))
  refine (h.congr_out ?_).enlarge (by omega)
  funext j; fin_cases j <;> rfl

theorem test_run (W : ℕ) (f g : ℕ → Bool) (c n i x a : ℕ) (hi : i ≤ n) (hn : n < 2 ^ W) :
    LRuns W test (2 * W + 3) (cst f g c n (n - i) x a 0 0 false) (cst f g c n (n - i) x a 0 0 (decide (i < n))) := by
  have h := lt_at (W := W) (cst f g c n (n - i) x a 0 0 false) rl zo kw fl (by decide) 0 (n - i) false rfl rfl rfl rfl
    (Nat.two_pow_pos W) (by omega)
  refine h.congr_out ?_
  rw [show decide (0 < n - i) = decide (i < n) from dec_congr (by omega)]
  funext j; fin_cases j <;> rfl

theorem neg_case (t : ℤ) (h : t < 0) : t.toNat = 0 ∧ (-t).toNat = t.natAbs := by omega
theorem pos_case (t : ℤ) (h : ¬ t < 0) : t.toNat = t.natAbs ∧ (-t).toNat = 0 := by omega

theorem bits_lt (x W : ℕ) (h : natBitLength x ≤ W) : x < 2 ^ W :=
  lt_of_lt_of_le (ReadNat.lt_natBitLength x) (Nat.pow_le_pow_right (by norm_num) h)

theorem body_run (W : ℕ) (f g : ℕ → Bool) (p : ℕ) {n : ℕ} (G : ExactThresholdGate n)
    (hS : ∀ k, k < (exactWord G).length → f (p + k) = (exactWord G).getD k false) (i : ℕ) (hi : i < n)
    (hn : n < 2 ^ W) (hA : (childRec G).1 < 2 ^ W)
    (hbits : ∀ j (hj : j < n), natBitLength ((ws G)[j]'(by rw [ws_length]; exact hj)).natAbs ≤ W) :
    LRuns W body (7 * W + 15) (cst f g (pos p G i) n (n - i) (xv G i) (asum G i) 0 0 true)
      (cst f g (pos p G (i + 1)) n (n - (i + 1)) (xv G (i + 1)) (asum G (i + 1)) 0 0 false) := by
  obtain ⟨_, hnat⟩ := weight_read f p G hS i hi
  have hw := bits_lt _ W (hbits i hi)
  have hsum : asum G i + ((ws G)[i]'(by rw [ws_length]; exact hi)).natAbs < 2 ^ W := by
    rw [← asum_succ G i hi]; exact lt_of_le_of_lt (asum_le _ _) hA
  have hall := (dec_at (W := W) (cst f g (pos p G i) n (n - i) (xv G i) (asum G i) 0 0 true) rl kw zo fl
    (by decide) (n - i) 0 true rfl rfl rfl rfl rfl (by omega) (by omega)).seq
    ((readBit_at (W := W) _ mm ss fl (by decide) (pos p G i) f g _ (by rfl) (by rfl) (by rfl)).seq
    ((ReadNat.at_run (W := W) _ rl ss mm uu xx (by decide) (pos p G i + 1) _ (xv G i) f g (hbits i hi) hnat
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).seq
    (add_at (W := W) _ rl aa xx fl (by decide) (asum G i) _ _ (by rfl) (by rfl) (by rfl) (by rfl)
      (lt_of_le_of_lt (asum_le G i) hA) hw hsum)))
  refine (hall.congr_out ?_).enlarge (by omega)
  funext j; fin_cases j
  · rfl
  · exact congrArg (TS.cells f) (pos_succ p G i hi).symm
  · exact congrArg (TS.cells g) (pos_succ p G i hi).symm
  · rfl
  · rfl
  · exact congrArg TS.reg (by omega)
  · exact congrArg TS.reg (xv_succ G i hi).symm
  · exact congrArg TS.reg (asum_succ G i hi).symm
  · rfl
  · rfl
  · rfl
  · rfl

theorem tail_run (W : ℕ) (f g : ℕ → Bool) (p : ℕ) {n : ℕ} (G : ExactThresholdGate n)
    (hS : ∀ k, k < (exactWord G).length → f (p + k) = (exactWord G).getD k false)
    (hT : natBitLength G.target.natAbs ≤ W) (x a : ℕ) :
    LRuns W tail (9 * W + 20) (cst f g (pos p G n) n 0 x a 0 0 false)
      (cst f g (p + (exactWord G).length) n 0 0 a G.target.toNat (-G.target).toNat false) := by
  obtain ⟨hsign, hnat⟩ := target_read f p G hS
  have ht := bits_lt _ W hT
  have hall := (readBit_at (W := W) (cst f g (pos p G n) n 0 x a 0 0 false) mm ss fl (by decide) (pos p G n) f g
    false rfl rfl rfl).seq
    ((ReadNat.at_run (W := W) _ rl ss mm uu xx (by decide) (pos p G n + 1) _ x f g hT hnat
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).seq
    ((Ite.runs (W := W) (nop 12) (swAt copyF false true rl qq xx fl) (swAt copyF false true rl pp xx fl) fl
      (f (pos p G n)) (nop_lruns _) (by rfl)
      (ρ := cst f g (pos p G n + 1 + (natWord G.target.natAbs).length) n 0 G.target.natAbs a
        G.target.toNat (-G.target).toNat false)
      (fun hb => by
        rw [hsign] at hb
        obtain ⟨e1, e2⟩ := neg_case G.target (of_decide_eq_true hb)
        exact (cpy_at (W := W) _ rl qq xx fl (by decide) 0 G.target.natAbs _ (by rfl) (by rfl) (by rfl) (by rfl)
          ht).congr_out (by
            funext j; fin_cases j
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · exact congrArg TS.reg e1.symm
            · exact congrArg TS.reg e2.symm
            · rfl
            · rfl))
      (fun hb => by
        rw [hsign] at hb
        obtain ⟨e1, e2⟩ := pos_case G.target (of_decide_eq_false hb)
        exact (cpy_at (W := W) _ rl pp xx fl (by decide) 0 G.target.natAbs _ (by rfl) (by rfl) (by rfl) (by rfl)
          ht).congr_out (by
            funext j; fin_cases j
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · rfl
            · exact congrArg TS.reg e1.symm
            · exact congrArg TS.reg e2.symm
            · rfl
            · rfl))).seq
    (zero_at (W := W) _ rl xx zo fl (by decide) G.target.natAbs 0 false rfl rfl rfl rfl)))
  refine (hall.congr_out ?_).enlarge (by omega)
  funext j; fin_cases j
  · rfl
  · exact congrArg (TS.cells f) (pos_full p G)
  · exact congrArg (TS.cells g) (pos_full p G)
  all_goals rfl

theorem childRun (W : ℕ) (f g : ℕ → Bool) (p : ℕ) {n : ℕ} (G : ExactThresholdGate n)
    (hS : ∀ k, k < (exactWord G).length → f (p + k) = (exactWord G).getD k false)
    (hn : n < 2 ^ W) (hA : (childRec G).1 < 2 ^ W)
    (hbits : ∀ j (hj : j < n), natBitLength ((ws G)[j]'(by rw [ws_length]; exact hj)).natAbs ≤ W)
    (hT : natBitLength G.target.natAbs ≤ W) (k x a pv qv : ℕ) (b : Bool) :
    LRuns W machine ((n + 3) * (10 * W + 30)) (cst f g p n k x a pv qv b)
      (cst f g (p + (exactWord G).length) n 0 0 (childRec G).1 (childRec G).2.1 (childRec G).2.2 false) := by
  have h1 := (init_run W f g p n k x a pv qv b hn).congr_out
    (σ'' := cst f g (pos p G 0) n (n - 0) (xv G 0) (asum G 0) 0 0 false) (by
      rw [pos_zero, asum_zero, xv_zero, Nat.sub_zero])
  have h2 := Loop.runs (W := W) test body fl (fun i => cst f g (pos p G i) n (n - i) (xv G i) (asum G i) 0 0 false)
    (fun i => cst f g (pos p G i) n (n - i) (xv G i) (asum G i) 0 0 (decide (i < n))) n
    (fun i hi => test_run W f g (pos p G i) n i (xv G i) (asum G i) hi hn) (fun i _ => rfl)
    (fun i hi => by
      have hb := body_run W f g p G hS i hi hn hA hbits
      rwa [show decide (i < n) = true by simp [hi]])
  have h3 := tail_run W f g p G hS hT (xv G n) (asum G n)
  have hall := (h1.seq h2).seq (h3.congr_in (by rw [Nat.sub_self]; simp))
  refine (hall.congr_out ?_).enlarge ?_
  · rw [asum_full]; rfl
  · nlinarith

end Child

end
end NearCubicWires.PacketsMeta

