import Proof.Packets.PacketsMetaLevel

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

namespace Lev

/-! ## Predicates -/

/-- The record of level `j`. -/
def rec (g : GS) (j : Fin 4) : Rec := (g.ra j, g.ru j, g.rv j)

/-- Every stream cursor lies inside its stream. -/
def InR (d : Fin 4 → CD) (g : GS) : Prop :=
  ∀ j : Fin 4, 1 ≤ g.pos j ∧ g.pos j ≤ (pay (d j)).length + 1

/-- `S` keeps every field of the levels below `k`. -/
def Keeps (k : ℕ) (S : GS → GS) : Prop := ∀ (g : GS) (j : Fin 4), j.val < k →
  (S g).pos j = g.pos j ∧ (S g).kk j = g.kk j ∧ (S g).na j = g.na j ∧ rec (S g) j = rec g j

/-- A circuit's data fits the register width. -/
structure Fits (W : ℕ) (e : CD) : Prop where
  arity : natBitLength e.1 ≤ W
  count : natBitLength e.2.length ≤ W
  child : ∀ G ∈ e.2, (childRec G).1 < 2 ^ W ∧
    (∀ j (hj : j < e.1), natBitLength ((Child.ws G)[j]'(by rw [Child.ws_length]; exact hj)).natAbs ≤ W) ∧
    natBitLength G.target.natAbs ≤ W

/-- The invariant at the entry of a level `k` machine: cursors in range, the records of the levels
below `k` are table entries, and the accumulators have room for the rest of the sums. -/
def InvAt (d : Fin 4 → CD) (Fmax Cmax k : ℕ) (Φ : List Rec → ℕ) (Ψ : ℕ) (g : GS) : Prop :=
  InR d g ∧ (∀ j : Fin 4, j.val < k → rec g j ∈ tab (d j)) ∧
    g.f + Φ ((List.ofFn (rec g)).take k) ≤ Fmax ∧ g.cnt + Ψ ≤ Cmax

/-- One level of the nested sum. -/
def up (Φ : List Rec → ℕ) (T : List Rec) : List Rec → ℕ := fun pre => (T.map (fun x => Φ (pre ++ [x]))).sum

/-- The level's cost. -/
def levCost (W : ℕ) (e : CD) (nI : ℕ) : ℕ :=
  ((pay e).length + 5 + 1 + ((3 * W + 5) + 1 + (3 * W + 5))) + 1 +
    (e.2.length + 1) * ((2 * W + 3) + min e.2.length 1 * ((2 * W + 3) + 1 + ((e.1 + 3) * (10 * W + 30) + 1 + nI)) + 2)

/-! ## List facts -/

theorem take_ofFn_congr {n : ℕ} (f f' : Fin n → Rec) (k : ℕ) (h : ∀ j : Fin n, j.val < k → f j = f' j) :
    (List.ofFn f).take k = (List.ofFn f').take k := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_ofFn]
  apply h
  simp only [List.length_take, List.length_ofFn] at h1
  show i < k
  omega

theorem take_ofFn_succ {n : ℕ} (f : Fin n → Rec) (c : Fin n) :
    (List.ofFn f).take (c.val + 1) = (List.ofFn f).take c.val ++ [f c] := by
  rw [List.take_succ_eq_append_getElem (by simp), List.getElem_ofFn]

theorem sum_take_le {α : Type} (l : List α) (h : α → ℕ) (i : ℕ) :
    ((l.take i).map h).sum ≤ (l.map h).sum := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.map_append, List.sum_append]
  omega

theorem sum_take_succ {α : Type} (l : List α) (h : α → ℕ) (i : ℕ) (hi : i < l.length) :
    ((l.take (i + 1)).map h).sum = ((l.take i).map h).sum + h l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]
  simp

/-! ## Stream facts -/

theorem pay_eq (e : CD) : pay e = natWord e.1 ++ natWord e.2.length ++ e.2.flatMap exactWord := by
  simp [pay, exactListWord, List.append_assoc]

theorem sf_pay (e : CD) : ∀ k, k < (pay e).length → sf (pay e) (1 + k) = (pay e).getD k false := by
  intro k _
  rw [Nat.add_comm]
  exact sf_succ _ _

theorem read_at (e : CD) (A B C : List Bool) (h : pay e = A ++ B ++ C) :
    ∀ k, k < B.length → sf (pay e) (1 + A.length + k) = B.getD k false := by
  apply read_sub (sf (pay e)) 1 A B C
  rw [← h]
  exact sf_pay e

theorem hS_N (e : CD) : ∀ k, k < (natWord e.1).length → sf (pay e) (1 + k) = (natWord e.1).getD k false := by
  intro k hk
  have h := read_at e [] (natWord e.1) (natWord e.2.length ++ e.2.flatMap exactWord)
    (by rw [pay_eq]; simp [List.append_assoc]) k hk
  rwa [List.length_nil, Nat.add_zero] at h

theorem hS_K (e : CD) : ∀ k, k < (natWord e.2.length).length →
    sf (pay e) (1 + (natWord e.1).length + k) = (natWord e.2.length).getD k false :=
  read_at e (natWord e.1) (natWord e.2.length) (e.2.flatMap exactWord) (pay_eq e)

theorem cur_succ (e : CD) (i : ℕ) (hi : i < e.2.length) :
    cur e (i + 1) = cur e i + (exactWord e.2[i]).length := by
  simp only [cur, take_succ_flatMap exactWord e.2 i hi, List.length_append]
  omega

theorem cur_le (e : CD) (i : ℕ) : cur e i ≤ (pay e).length + 1 := by
  have h1 : ((e.2.take i).flatMap exactWord).length ≤ (e.2.flatMap exactWord).length := by
    conv_rhs => rw [← List.take_append_drop i e.2]
    rw [List.flatMap_append, List.length_append]
    omega
  rw [pay_eq]
  simp only [cur, h0, List.length_append]
  omega

theorem hS_child (e : CD) (i : ℕ) (hi : i < e.2.length) :
    ∀ k, k < (exactWord e.2[i]).length → sf (pay e) (cur e i + k) = (exactWord e.2[i]).getD k false := by
  have h := read_at e (natWord e.1 ++ natWord e.2.length ++ (e.2.take i).flatMap exactWord) (exactWord e.2[i])
    ((e.2.drop (i + 1)).flatMap exactWord)
    (by rw [pay_eq, flatMap_split exactWord e.2 i hi]; simp [List.append_assoc])
  have e1 : 1 + (natWord e.1 ++ natWord e.2.length ++ (e.2.take i).flatMap exactWord).length = cur e i := by
    simp only [cur, h0, List.length_append]
    omega
  rwa [e1] at h

theorem len_le_flatMap_intWord : ∀ l : List ℤ, l.length ≤ (l.flatMap intWord).length
  | [] => by simp
  | z :: l => by
    have := len_le_flatMap_intWord l
    simp only [List.flatMap_cons, List.length_append, List.length_cons, intWord_length]
    omega

theorem arity_le (e : CD) (i : ℕ) (hi : i < e.2.length) : e.1 ≤ (pay e).length := by
  have h1 : e.1 ≤ (exactWord e.2[i]).length := by
    rw [Child.exactWord_eq, List.length_append]
    have h2 := len_le_flatMap_intWord (Child.ws e.2[i])
    rw [Child.ws_length] at h2
    omega
  have h2 : (exactWord e.2[i]).length ≤ (pay e).length := by
    rw [pay_eq, flatMap_split exactWord e.2 i hi]
    simp only [List.length_append]
    omega
  omega

/-! ## The per-child states -/

section Facts
variable (d : Fin 4 → CD) (c : Fin 4) (innerS : GS → GS)

theorem stI_zero (g : GS) : stI d c innerS g 0 = hdrS d c g := by
  simp [stI]

theorem stI_succ (g : GS) (i : ℕ) (hi : i < (d c).2.length) :
    stI d c innerS g (i + 1) = innerS (chS c ((d c).2[i]) (decS c (stI d c innerS g i))) := by
  simp only [stI, List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem rec_chS {n : ℕ} (G : ExactThresholdGate n) (g : GS) (j : Fin 4) :
    rec (chS c G g) j = if j = c then childRec G else rec g j := by
  by_cases h : j = c
  · subst h
    simp [rec, chS]
  · simp [rec, chS, h, Function.update_of_ne h]

theorem take_chS {n : ℕ} (G : ExactThresholdGate n) (g : GS) :
    (List.ofFn (rec (chS c G g))).take (c.val + 1) = (List.ofFn (rec g)).take c.val ++ [childRec G] := by
  rw [take_ofFn_succ, rec_chS, if_pos rfl]
  congr 1
  apply take_ofFn_congr
  intro j hj
  rw [rec_chS, if_neg (fun e => by subst e; omega)]

variable (hk : Keeps (c.val + 1) innerS)
include hk

theorem step_cur (G : ExactThresholdGate (d c).1) (y : GS) :
    (innerS (chS c G (decS c y))).pos c = y.pos c + (exactWord G).length ∧
      (innerS (chS c G (decS c y))).kk c = y.kk c - 1 ∧ (innerS (chS c G (decS c y))).na c = y.na c := by
  obtain ⟨k1, k2, k3, _⟩ := hk (chS c G (decS c y)) c (by omega)
  refine ⟨k1.trans ?_, k2.trans ?_, k3.trans ?_⟩ <;> simp [chS, decS]

theorem step_keep (G : ExactThresholdGate (d c).1) (y : GS) (j : Fin 4) (hj : j.val < c.val) :
    (innerS (chS c G (decS c y))).pos j = y.pos j ∧ (innerS (chS c G (decS c y))).kk j = y.kk j ∧
      (innerS (chS c G (decS c y))).na j = y.na j ∧ rec (innerS (chS c G (decS c y))) j = rec y j := by
  have hne : j ≠ c := fun e => by subst e; omega
  obtain ⟨k1, k2, k3, k4⟩ := hk (chS c G (decS c y)) j (by omega)
  refine ⟨k1.trans ?_, k2.trans ?_, k3.trans ?_, k4.trans ?_⟩
  · simp [chS, decS, Function.update_of_ne hne]
  · simp [chS, decS, Function.update_of_ne hne]
  · simp [chS, decS, Function.update_of_ne hne]
  · rw [rec_chS, if_neg hne]
    rfl

theorem stI_cur (g : GS) : ∀ i, i ≤ (d c).2.length →
    (stI d c innerS g i).pos c = cur (d c) i ∧ (stI d c innerS g i).kk c = (d c).2.length - i ∧
      (stI d c innerS g i).na c = (d c).1
  | 0, _ => by
    rw [stI_zero]
    simp [hdrS, cur, h0]
  | i + 1, hi => by
    obtain ⟨h1, h2, h3⟩ := stI_cur g i (by omega)
    rw [stI_succ d c innerS g i (by omega)]
    obtain ⟨k1, k2, k3⟩ := step_cur d c innerS hk ((d c).2[i]) (stI d c innerS g i)
    refine ⟨k1.trans ?_, k2.trans ?_, k3.trans h3⟩
    · rw [h1]
      exact (cur_succ (d c) i (by omega)).symm
    · rw [h2]
      omega

theorem stI_keep (g : GS) (j : Fin 4) (hj : j.val < c.val) : ∀ i, i ≤ (d c).2.length →
    (stI d c innerS g i).pos j = g.pos j ∧ (stI d c innerS g i).kk j = g.kk j ∧
      (stI d c innerS g i).na j = g.na j ∧ rec (stI d c innerS g i) j = rec g j
  | 0, _ => by
    have hne : j ≠ c := fun e => by subst e; omega
    rw [stI_zero]
    simp [hdrS, rec, Function.update_of_ne hne]
  | i + 1, hi => by
    obtain ⟨h1, h2, h3, h4⟩ := stI_keep g j hj i (by omega)
    rw [stI_succ d c innerS g i (by omega)]
    obtain ⟨k1, k2, k3, k4⟩ := step_keep d c innerS hk ((d c).2[i]) (stI d c innerS g i) j hj
    exact ⟨k1.trans h1, k2.trans h2, k3.trans h3, k4.trans h4⟩

theorem stI_inR (hR : ∀ g', InR d g' → InR d (innerS g')) (g : GS) (hg : InR d g) :
    ∀ i, i ≤ (d c).2.length → InR d (stI d c innerS g i)
  | 0, _ => by
    rw [stI_zero]
    intro j
    by_cases h : j = c
    · subst h
      have := cur_le (d j) 0
      simp only [hdrS, Function.update_self]
      simp only [cur, List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero] at this
      exact ⟨by simp [h0]; omega, this⟩
    · simp only [hdrS, Function.update_of_ne h]
      exact hg j
  | i + 1, hi => by
    have ih := stI_inR hR g hg i (by omega)
    rw [stI_succ d c innerS g i (by omega)]
    apply hR
    intro j
    by_cases h : j = c
    · subst h
      obtain ⟨h1, _, _⟩ := stI_cur d j innerS hk g i (by omega)
      simp only [chS, decS, Function.update_self]
      rw [h1, ← cur_succ (d j) i (by omega)]
      refine ⟨?_, cur_le _ _⟩
      simp [cur, h0]
      omega
    · simp only [chS, decS, Function.update_of_ne h]
      exact ih j

theorem stI_acc (Φ : List Rec → ℕ) (Ψ : ℕ)
    (hΦ : ∀ g', (innerS g').f = g'.f + Φ ((List.ofFn (rec g')).take (c.val + 1)))
    (hΨ : ∀ g', (innerS g').cnt = g'.cnt + Ψ) (g : GS) : ∀ i, i ≤ (d c).2.length →
    (stI d c innerS g i).f = g.f + (((tab (d c)).take i).map (fun x => Φ ((List.ofFn (rec g)).take c.val ++ [x]))).sum ∧
      (stI d c innerS g i).cnt = g.cnt + i * Ψ
  | 0, _ => by
    rw [stI_zero]
    simp [hdrS]
  | i + 1, hi => by
    obtain ⟨h1, h2⟩ := stI_acc Φ Ψ hΦ hΨ g i (by omega)
    have hpre : (List.ofFn (rec (decS c (stI d c innerS g i)))).take c.val = (List.ofFn (rec g)).take c.val := by
      apply take_ofFn_congr
      intro j hj
      exact (stI_keep d c innerS hk g j hj i (by omega)).2.2.2
    have hl : i < (tab (d c)).length := by simp [tab]; omega
    rw [stI_succ d c innerS g i (by omega), hΦ, hΨ, take_chS, hpre, sum_take_succ _ _ i hl]
    have ht : (tab (d c))[i] = childRec ((d c).2[i]'(by omega)) := by simp only [tab, List.getElem_map]
    rw [ht]
    simp only [chS, decS]
    refine ⟨by rw [h1]; omega, by rw [h2]; ring⟩

end Facts

/-! ## The level's result -/

section Result
variable (d : Fin 4 → CD) (c : Fin 4) (innerS : GS → GS) (hk : Keeps (c.val + 1) innerS)
include hk

theorem levS_keeps : Keeps c.val (levS d c innerS) := by
  intro g j hj
  obtain ⟨h1, h2, h3, h4⟩ := stI_keep d c innerS hk g j hj (d c).2.length (le_refl _)
  exact ⟨h1, h2, h3, h4⟩

theorem levS_inR (hR : ∀ g', InR d g' → InR d (innerS g')) (g : GS) (hg : InR d g) :
    InR d (levS d c innerS g) :=
  stI_inR d c innerS hk hR g hg (d c).2.length (le_refl _)

theorem levS_f (Φ : List Rec → ℕ) (Ψ : ℕ)
    (hΦ : ∀ g', (innerS g').f = g'.f + Φ ((List.ofFn (rec g')).take (c.val + 1)))
    (hΨ : ∀ g', (innerS g').cnt = g'.cnt + Ψ) (g : GS) :
    (levS d c innerS g).f = g.f + up Φ (tab (d c)) ((List.ofFn (rec g)).take c.val) := by
  have h := (stI_acc d c innerS hk Φ Ψ hΦ hΨ g (d c).2.length (le_refl _)).1
  have ht : (tab (d c)).take (d c).2.length = tab (d c) := by
    rw [show (d c).2.length = (tab (d c)).length by simp [tab], List.take_length]
  rw [ht] at h
  exact h

theorem levS_cnt (Φ : List Rec → ℕ) (Ψ : ℕ)
    (hΦ : ∀ g', (innerS g').f = g'.f + Φ ((List.ofFn (rec g')).take (c.val + 1)))
    (hΨ : ∀ g', (innerS g').cnt = g'.cnt + Ψ) (g : GS) :
    (levS d c innerS g).cnt = g.cnt + (tab (d c)).length * Ψ := by
  have h := (stI_acc d c innerS hk Φ Ψ hΦ hΨ g (d c).2.length (le_refl _)).2
  have hl : (d c).2.length = (tab (d c)).length := by simp [tab]
  exact h.trans (by rw [hl])

end Result

/-! ## The run -/

section Run
variable {W : ℕ} (fx : Fin 60 → TS) (d : Fin 4 → CD) (c : Fin 4)

/-- The header: rewind, read the arity, read the child count. -/
theorem lv_hdr (hfx3 : fx 3 = .ruler) (g : GS) (hp1 : 1 ≤ g.pos c) (hp2 : g.pos c ≤ (pay (d c)).length + 1)
    (hfit : Fits W (d c)) :
    LRuns W (Composition.machine (RecoveryFocus.machine ![sM c, sS c] rewind)
      (Composition.machine (ReadNat.at5 3 (sS c) (sM c) 6 (sN c)) (ReadNat.at5 3 (sS c) (sM c) 6 (sK c))))
      ((pay (d c)).length + 5 + 1 + ((3 * W + 5) + 1 + (3 * W + 5))) (Gv fx d g) (Gv fx d (hdrS d c g)) := by
  have e1 := lv_rewind (W := W) fx d c g hp1 hp2
  have e2 := lv_readN (W := W) fx d c hfx3 { g with pos := Function.update g.pos c 1 } (d c).1 hfit.arity
    (by
      intro k hk
      simp only [Function.update_self]
      exact hS_N (d c) k hk)
  have e3 := lv_readK (W := W) fx d c hfx3
    { { g with pos := Function.update g.pos c 1 } with
      pos := Function.update (Function.update g.pos c 1) c (Function.update g.pos c 1 c + (natWord (d c).1).length),
      na := Function.update g.na c (d c).1 } (d c).2.length hfit.count
    (by
      intro k hk
      simp only [Function.update_self]
      exact hS_K (d c) k hk)
  refine (e1.seq (e2.seq e3)).congr_out ?_
  congr 1
  simp only [hdrS, h0, Function.update_idem, Function.update_self]

theorem lev_run (hfx3 : fx 3 = .ruler) (hfx5 : fx 5 = .reg 0) {si : ℕ} (inner : Machine 60 si)
    (innerS : GS → GS) (nI Fmax Cmax : ℕ) (Φ : List Rec → ℕ) (Ψ : ℕ) (hfit : Fits W (d c))
    (hin : ∀ g', InvAt d Fmax Cmax (c.val + 1) Φ Ψ g' → LRuns W inner nI (Gv fx d g') (Gv fx d (innerS g')))
    (hΦ : ∀ g', (innerS g').f = g'.f + Φ ((List.ofFn (rec g')).take (c.val + 1)))
    (hΨ : ∀ g', (innerS g').cnt = g'.cnt + Ψ)
    (hk : Keeps (c.val + 1) innerS) (hR : ∀ g', InR d g' → InR d (innerS g'))
    (g : GS) (hg : InvAt d Fmax Cmax c.val (up Φ (tab (d c))) ((tab (d c)).length * Ψ) g) :
    LRuns W (lev c inner) (levCost W (d c) nI) (Gv fx d g) (Gv fx d (levS d c innerS g)) := by
  obtain ⟨hgR, hgrec, hgf, hgc⟩ := hg
  have hmW : (d c).2.length < 2 ^ W := (ReadNat.lt_natBitLength _).trans_le
    (Nat.pow_le_pow_right (by norm_num) hfit.count)
  have hnW : (d c).1 < 2 ^ W := (ReadNat.lt_natBitLength _).trans_le
    (Nat.pow_le_pow_right (by norm_num) hfit.arity)
  have hlen : (tab (d c)).length = (d c).2.length := by simp [tab]
  have hH := lv_hdr (W := W) fx d c hfx3 g (hgR c).1 (hgR c).2 hfit
  rw [← stI_zero d c innerS g] at hH
  have hL := Loop.runs (W := W) (nc := 2 * W + 3)
    (nb := min (d c).2.length 1 * ((2 * W + 3) + 1 + (((d c).1 + 3) * (10 * W + 30) + 1 + nI)))
    (swAt subF false false 3 5 (sK c) 4)
    (Composition.machine (swAt subF true true 3 (sK c) 5 4)
      (Composition.machine (RecoveryFocus.machine (childSlots c) Child.machine) inner)) 4
    (fun i => Gv fx d (stI d c innerS g i))
    (fun i => Gv fx d { stI d c innerS g i with fl := decide (i < (d c).2.length) }) (d c).2.length
    (fun i hi => by
      obtain ⟨_, h2, _⟩ := stI_cur d c innerS hk g i hi
      have ht := lv_test (W := W) fx d c hfx3 hfx5 (stI d c innerS g i) (by rw [h2]; omega)
      rw [h2] at ht
      have hd : decide (0 < (d c).2.length - i) = decide (i < (d c).2.length) := by
        apply decide_eq_decide.mpr
        omega
      rw [hd] at ht
      exact ht)
    (fun i _ => rfl)
    (fun i hi => by
      obtain ⟨h1, h2, h3⟩ := stI_cur d c innerS hk g i (by omega)
      have hdec := lv_dec (W := W) fx d c hfx3 hfx5
        { stI d c innerS g i with fl := decide (i < (d c).2.length) }
        (by dsimp only; rw [h2]; omega) (by dsimp only; rw [h2]; omega)
      have hmem : (d c).2[i] ∈ (d c).2 := List.getElem_mem _
      obtain ⟨hA, hbits, hT⟩ := hfit.child _ hmem
      have hdd : decS c { stI d c innerS g i with fl := decide (i < (d c).2.length) } =
          decS c (stI d c innerS g i) := rfl
      rw [hdd] at hdec
      have hch := lv_child (W := W) fx d c hfx3 hfx5 (decS c (stI d c innerS g i))
        ((d c).2[i]) (by
          intro k hk
          have e : (decS c (stI d c innerS g i)).pos c = cur (d c) i := h1
          rw [e]
          exact hS_child (d c) i hi k hk) hnW hA hbits hT h3
      have hinv : InvAt d Fmax Cmax (c.val + 1) Φ Ψ (chS c ((d c).2[i]) (decS c (stI d c innerS g i))) := by
        obtain ⟨a1, a2⟩ := stI_acc d c innerS hk Φ Ψ hΦ hΨ g i (by omega)
        have hpre : (List.ofFn (rec (decS c (stI d c innerS g i)))).take c.val =
            (List.ofFn (rec g)).take c.val := by
          apply take_ofFn_congr
          intro j hj
          exact (stI_keep d c innerS hk g j hj i (by omega)).2.2.2
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j
          have hRi := stI_inR d c innerS hk hR g hgR i (by omega) j
          by_cases h : j = c
          · subst h
            simp only [chS, decS, Function.update_self]
            rw [h1, ← cur_succ (d j) i hi]
            refine ⟨?_, cur_le _ _⟩
            simp [cur, h0]
            omega
          · simp only [chS, decS, Function.update_of_ne h]
            exact hRi
        · intro j hj
          rw [rec_chS]
          by_cases h : j = c
          · rw [if_pos h, h]
            exact List.mem_map_of_mem hmem
          · rw [if_neg h]
            have hj' : j.val < c.val := by
              have : j.val ≠ c.val := fun e => h (Fin.ext e)
              omega
            have hr : rec (decS c (stI d c innerS g i)) j = rec g j :=
              (stI_keep d c innerS hk g j hj' i (by omega)).2.2.2
            rw [hr]
            exact hgrec j hj'
        · rw [take_chS, hpre]
          have hf0 : (chS c ((d c).2[i]) (decS c (stI d c innerS g i))).f = (stI d c innerS g i).f := rfl
          rw [hf0, a1]
          have hl : i < (tab (d c)).length := by rw [hlen]; exact hi
          have hs := sum_take_succ (tab (d c)) (fun x => Φ ((List.ofFn (rec g)).take c.val ++ [x])) i hl
          have ht : (tab (d c))[i] = childRec ((d c).2[i]) := by simp only [tab, List.getElem_map]
          rw [ht] at hs
          have hle := sum_take_le (tab (d c)) (fun x => Φ ((List.ofFn (rec g)).take c.val ++ [x])) (i + 1)
          have hup : up Φ (tab (d c)) ((List.ofFn (rec g)).take c.val) =
              ((tab (d c)).map (fun x => Φ ((List.ofFn (rec g)).take c.val ++ [x]))).sum := rfl
          rw [hup] at hgf
          omega
        · have hc0 : (chS c ((d c).2[i]) (decS c (stI d c innerS g i))).cnt = (stI d c innerS g i).cnt := rfl
          rw [hc0, a2]
          rw [hlen] at hgc
          have : (i + 1) * Ψ ≤ (d c).2.length * Ψ := Nat.mul_le_mul_right _ (by omega)
          have e : i * Ψ + Ψ = (i + 1) * Ψ := by ring
          omega
      have hI := hin _ hinv
      have hall := hdec.seq (hch.seq hI)
      rw [stI_succ d c innerS g i hi]
      refine hall.enlarge ?_
      rw [Nat.min_eq_right (by omega), Nat.one_mul])
  have hfin : Gv fx d { stI d c innerS g (d c).2.length with fl := decide ((d c).2.length < (d c).2.length) } =
      Gv fx d (levS d c innerS g) := by
    simp [levS]
  rw [hfin] at hL
  exact (hH.seq hL).congr_in rfl

end Run

end Lev

end
end NearCubicWires.PacketsMeta

