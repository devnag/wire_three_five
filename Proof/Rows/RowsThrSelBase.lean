import Proof.Rows.RowsThrSelCasc
import Proof.Rows.RowsThrBaseBounds
import Proof.Rows.RowsBaseJoin
import Proof.Rows.RowsInitBaseParams

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrSelBase
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open RowsConstruction.BaseLayout RowsConstruction.KeyStep RowsConstruction.KeyTop RowsConstruction.ThrKey
open RowsConstruction.ThrSel RowsConstruction.ThrSelCasc
noncomputable section

/-! ## 1. The base worker's parameter functions (`base_numeric`) -/

/-- The six constants of the base worker's parameter polynomials (`RowsInitBaseParams.base_numeric_explicit`). -/
def bcD : ℕ := Classical.choose RowsInit.BaseParams.base_numeric_explicit
def bdD : ℕ := Classical.choose (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit)
def bcU : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit))
def bdU : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  RowsInit.BaseParams.base_numeric_explicit)))
def bcF : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit))))
def bdF : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
  (Classical.choose_spec (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit)))))

/-- The parameter functions: CLOSED polynomials of `T` (so an initializer can write `1^(bU T)`). -/
def bD : ℕ → ℕ := fun T => ThrBaseBounds.DOf bcD bdD T
def bU : ℕ → ℕ := fun T => ThrBaseBounds.UOf' bcD bdD bcU bdU T
def bF : ℕ → ℕ := fun T => ThrBaseBounds.FOf' bcD bdD bcU bdU bcF bdF T

theorem b_spec :
    ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
      (four : r.circuits.length ≤ 4) (L target : Nat) (sel : ThresholdRows.Selection a r),
      PCJ45bee56da9f34d5a_FourfoldBaseData.Bounds (PCJ45bee56da9f34d5a_StreamPair.data a r four sel)
        (ThrWidth.T a r four L target) (12*ThrWidth.T a r four L target+17)
        (8*(12*ThrWidth.T a r four L target+17)+12) (bD (ThrWidth.T a r four L target))
        (bU (ThrWidth.T a r four L target)) (ThrWidth.T a r four L target) (bF (ThrWidth.T a r four L target)) ∧
      4*(12*ThrWidth.T a r four L target+19)+3 ≤ bU (ThrWidth.T a r four L target) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec RowsInit.BaseParams.base_numeric_explicit)))))

/-! ## 2. The base worker's bank: census -/

section Census
set_option linter.unnecessarySeqFocus false in
/-- Off the accumulator (9) and the four digit ports (73–76) the base worker's bank depends on neither. -/
theorem bank_other (source : List Bool) (dg dg' : Fin 4 → Nat) (N v w C U a a' : Nat) (k : Fin 82)
    (h9 : k ≠ 9) (hd : ¬ (73 ≤ k.val ∧ k.val < 77)) :
    PCJ45bee56da9f34d5a_FourfoldBaseCell.bank source dg N v w C U a k =
      PCJ45bee56da9f34d5a_FourfoldBaseCell.bank source dg' N v w C U a' k := by
  fin_cases k <;> first
    | exact (h9 (by decide)).elim
    | exact (hd ⟨by decide, by decide⟩).elim
    | (bank_nf PCJ45bee56da9f34d5a_FourfoldBaseCell.bank <;>
        bank_nf PCJ45bee56da9f34d5a_FourfoldBaseCell.bank <;> rfl)

/-- Digit port `73+c` of the base worker's bank. -/
def dk (c : Fin 4) : Fin 82 := ⟨73 + c.val, by omega⟩

theorem bank_digit (source : List Bool) (dg : Fin 4 → Nat) (N v w C U a : Nat) (c : Fin 4) :
    PCJ45bee56da9f34d5a_FourfoldBaseCell.bank source dg N v w C U a (dk c) =
      frame (SignedSortKey.binary v (dg c)) := by
  fin_cases c <;> rfl

theorem heads_one (k : Fin 82) :
    PCJ45bee56da9f34d5a_FourfoldBaseCell.heads 1 k = if 77 ≤ k.val then 1 else 0 := by
  unfold PCJ45bee56da9f34d5a_FourfoldBaseCell.heads
  have := k.isLt
  by_cases h81 : k = 81
  · subst h81; rfl
  · rw [if_neg h81]
    have hk : k.val ≠ 81 := fun e => h81 (Fin.ext e)
    by_cases h77 : 77 ≤ k.val
    · rw [if_pos ⟨h77, by omega⟩, if_pos h77]
    · rw [if_neg (by omega), if_neg h77]

end Census

/-! ## 3. Ports -/

section Ports
variable (NI : Nat) (ib : Fin 82 → Fin NI) (iOne : Fin NI)

/-- The base worker's slot map: digit ports 73–76 on the child-digit masters, everything else on `init`. -/
def bS (k : Fin 82) : Fin (2+rowsWork NI) :=
  if h : 73 ≤ k.val ∧ k.val < 77 then masterPort NI (dPort ⟨k.val - 73, by omega⟩) else initPort NI (ib k)

theorem bS_digit (c : Fin 4) : bS NI ib (dk c) = masterPort NI (dPort c) := by
  unfold bS dk
  rw [dif_pos (by simp; omega)]
  congr 2
  apply Fin.ext
  simp

theorem bS_init (k : Fin 82) (hk : ¬ (73 ≤ k.val ∧ k.val < 77)) : bS NI ib k = initPort NI (ib k) := by
  unfold bS
  rw [dif_neg hk]

theorem bS_injective (hib : Function.Injective ib) : Function.Injective (bS NI ib) := by
  intro x y h
  unfold bS at h
  split_ifs at h with hx hy hy
  · have hv := (masterPort_inj NI _ _).mp h
    have hv' := congrArg Fin.val hv
    rw [dPort_val, dPort_val] at hv'
    simp only at hv'
    exact Fin.ext (by omega)
  · exact absurd h.symm (initPort_ne_master NI _ _)
  · exact absurd h (initPort_ne_master NI _ _)
  · have hv := congrArg Fin.val h
    rw [initPort_val, initPort_val] at hv
    exact hib (Fin.ext (by omega))

/-- The ports that must sit at head 1 for the base worker (its count/cursor ports 77–81). -/
def hot (p : Fin (2+rowsWork NI)) : Prop := ∃ k : Fin 82, 77 ≤ k.val ∧ initPort NI (ib k) = p

instance (p : Fin (2+rowsWork NI)) : Decidable (hot NI ib p) := by
  unfold hot; infer_instance

def mv (dir : HeadMove) : Machine (2+rowsWork NI) 2 :=
  DecompositionCountPosition.move (fun p => if hot NI ib p then dir else HeadMove.stay)

def H1 (p : Fin (2+rowsWork NI)) : ℕ := if hot NI ib p then 1 else 0

theorem mv_right (A : Fin (2+rowsWork NI) → List Bool) :
    Step (mv NI ib HeadMove.right) 1 (fun _ => 0) A (H1 NI ib) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run
    (fun p => if hot NI ib p then HeadMove.right else HeadMove.stay) (fun _ => 0) A
  refine Step.of_run hr ?_ (by rw [hf])
  rw [hf]
  funext p
  show (if hot NI ib p then HeadMove.right else HeadMove.stay).apply 0 = H1 NI ib p
  unfold H1
  split <;> rfl

theorem mv_left (A : Fin (2+rowsWork NI) → List Bool) :
    Step (mv NI ib HeadMove.left) 1 (H1 NI ib) A (fun _ => 0) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run
    (fun p => if hot NI ib p then HeadMove.left else HeadMove.stay) (H1 NI ib) A
  refine Step.of_run hr ?_ (by rw [hf])
  rw [hf]
  funext p
  show (if hot NI ib p then HeadMove.left else HeadMove.stay).apply (H1 NI ib p) = 0
  unfold H1
  split <;> rfl

theorem H1_bS (hib : Function.Injective ib) (k : Fin 82) :
    H1 NI ib (bS NI ib k) = PCJ45bee56da9f34d5a_FourfoldBaseCell.heads 1 k := by
  rw [heads_one]
  unfold H1
  by_cases hd : 73 ≤ k.val ∧ k.val < 77
  · have hnot : ¬ hot NI ib (bS NI ib k) := by
      intro hx
      obtain ⟨k', _, e⟩ := hx
      unfold bS at e
      rw [dif_pos hd] at e
      exact initPort_ne_master NI _ _ e
    rw [if_neg hnot, if_neg (show ¬ 77 ≤ k.val by omega)]
  · rw [bS_init NI ib k hd]
    by_cases h77 : 77 ≤ k.val
    · rw [if_pos (show hot NI ib (initPort NI (ib k)) from ⟨k, h77, rfl⟩), if_pos h77]
    · have hnot : ¬ hot NI ib (initPort NI (ib k)) := by
        intro hx
        obtain ⟨k', hk', e⟩ := hx
        have hv := congrArg Fin.val e
        rw [initPort_val, initPort_val] at hv
        have hkk : k' = k := hib (Fin.ext (by omega))
        rw [hkk] at hk'
        exact h77 hk'
      rw [if_neg hnot, if_neg h77]

/-- The docked base worker. -/
def dockB := RecoveryFocus.machine (bS NI ib) PCJ45bee56da9f34d5a_FourfoldBaseRun.machine

/-- The scalar copy, docked by a 4-slot map (source, destination, two blank scratch tapes). -/
def srM (s : Fin 4 → Fin (2+rowsWork NI)) := RecoveryFocus.machine s MatrixFrameCopy.machine

def cpS : Fin 4 → Fin (2+rowsWork NI) :=
  ![initPort NI (ib 9), masterPort NI 220, cellPort NI 0, cellPort NI 1]
def rsS : Fin 4 → Fin (2+rowsWork NI) :=
  ![initPort NI iOne, initPort NI (ib 9), cellPort NI 0, cellPort NI 1]

/-- **The base stage** (one fixed machine). -/
def baseW := Composition.machine (mv NI ib HeadMove.right) (Composition.machine (dockB NI ib)
  (Composition.machine (mv NI ib HeadMove.left) (Composition.machine (srM NI (cpS NI ib)) (srM NI (rsS NI ib iOne)))))

end Ports

/-! ## 4. The scalar copy on the work block -/

theorem pad_pad (m n : Nat) (l : List Bool) (h : m ≤ n) : ZeroPadding.pad n (ZeroPadding.pad m l) = ZeroPadding.pad n l := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate, List.append_assoc,
    List.replicate_append_replicate]
  congr 2
  omega

theorem pad_rep (m n : Nat) (h : m ≤ n) : ZeroPadding.pad n (List.replicate m false) = List.replicate n false := by
  simp only [ZeroPadding.pad, List.length_replicate, List.replicate_append_replicate]
  congr 1
  omega

theorem sr_step {NI : Nat} (s : Fin 4 → Fin (2+rowsWork NI)) (hs : Function.Injective s)
    (bits backing : List Bool) (U0 P0 P1 R : Nat) (hb : backing.length ≤ 2*bits.length+1) (hU : 4*bits.length+3 ≤ U0)
    (h0 : U0 ≤ P0) (h1 : U0 ≤ P1) (hR : U0 ≤ R) (A : Fin (2+rowsWork NI) → List Bool)
    (a0 : A (s 0) = ZeroPadding.pad P0 (frame bits)) (a1 : A (s 1) = ZeroPadding.pad P1 backing)
    (a2 : A (s 2) = List.replicate R false) (a3 : A (s 3) = List.replicate R false) :
    Step (RecoveryFocus.machine s MatrixFrameCopy.machine) (8*bits.length+8) (fun _ => 0) A (fun _ => 0)
      (Function.update A (s 1) (ZeroPadding.pad P1 (frame bits))) := by
  have base := (PCJ45bee56da9f34d5a_ScalarReplace.run bits backing U0 hb hU).pad ![P0, P1, R, R]
  have ein : (fun i => ZeroPadding.pad (![P0, P1, R, R] i)
      ((![ZeroPadding.pad U0 (frame bits), ZeroPadding.pad U0 backing, List.replicate U0 false,
        List.replicate U0 false] : Fin 4 → List Bool) i)) = fun i => A (s i) := by
    funext i
    fin_cases i
    · show ZeroPadding.pad P0 (ZeroPadding.pad U0 (frame bits)) = A (s 0)
      rw [pad_pad _ _ _ h0, a0]
    · show ZeroPadding.pad P1 (ZeroPadding.pad U0 backing) = A (s 1)
      rw [pad_pad _ _ _ h1, a1]
    · show ZeroPadding.pad R (List.replicate U0 false) = A (s 2)
      rw [pad_rep _ _ hR, a2]
    · show ZeroPadding.pad R (List.replicate U0 false) = A (s 3)
      rw [pad_rep _ _ hR, a3]
  have eout : (fun i => ZeroPadding.pad (![P0, P1, R, R] i)
      ((![ZeroPadding.pad U0 (frame bits), ZeroPadding.pad U0 (frame bits), List.replicate U0 false,
        List.replicate U0 false] : Fin 4 → List Bool) i)) =
      fun i => Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) i := by
    funext i
    fin_cases i
    · show ZeroPadding.pad P0 (ZeroPadding.pad U0 (frame bits)) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 0
      rw [Function.update_of_ne (by decide), pad_pad _ _ _ h0, a0]
    · show ZeroPadding.pad P1 (ZeroPadding.pad U0 (frame bits)) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 1
      rw [Function.update_self, pad_pad _ _ _ h1]
    · show ZeroPadding.pad R (List.replicate U0 false) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 2
      rw [Function.update_of_ne (by decide), pad_rep _ _ hR, a2]
    · show ZeroPadding.pad R (List.replicate U0 false) =
        Function.update (fun i => A (s i)) 1 (ZeroPadding.pad P1 (frame bits)) 3
      rw [Function.update_of_ne (by decide), pad_rep _ _ hR, a3]
  rw [ein, eout] at base
  have d := wdock NI base s hs A (fun _ => rfl)
  rw [SymVerdict.install_update _ hs A _ 1 (fun j hj => by rw [Function.update_of_ne hj])] at d
  rw [Function.update_self] at d
  exact d

/-! ## 5. The base stage on the work block -/

section Base
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- The request's TOP payload stream (the base worker's source; selection-independent). -/
def srcB : List Bool :=
  (r.circuits.map (fun c => PCJ45bee56da9f34d5a_TopChildCursor.payload (ThresholdRows.children a c))).flatMap frame

/-- **The base worker's resident words** (request constants; `init (ib k)` for the 78 non-digit ports). -/
def baseInit (k : Fin 82) : List Bool :=
  PCJ45bee56da9f34d5a_FourfoldBaseCell.bank (srcB a r) (fun _ => 0) r.circuits.length (ThrWidth.T a r four L target)
    (12*ThrWidth.T a r four L target+17) (8*(12*ThrWidth.T a r four L target+17)+12) (bU (ThrWidth.T a r four L target))
    1 k

/-- The cost of the base stage. -/
def baseCost (F w : Nat) : Nat := 1+1+((4*F+27)+1+(1+1+((8*w+8)+1+(8*w+8))))

theorem cpS_injective (NI : Nat) (ib : Fin 82 → Fin NI) : Function.Injective (cpS NI ib) := by
  intro x y h
  have hv := congrArg Fin.val h
  have := (ib 9).isLt
  fin_cases x <;> fin_cases y <;> simp [cpS, masterPort_val, cellPort_val, initPort_val] at hv ⊢ <;> omega

theorem rsS_injective (NI : Nat) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hone : ib 9 ≠ iOne) :
    Function.Injective (rsS NI ib iOne) := by
  intro x y h
  have hv := congrArg Fin.val h
  have := (ib 9).isLt
  have := iOne.isLt
  have hne : (ib 9).val ≠ iOne.val := fun e => hone (Fin.ext e)
  fin_cases x <;> fin_cases y <;> simp [rsS, cellPort_val, initPort_val] at hv ⊢ <;> omega

theorem data_src (sel : ThresholdRows.Selection a r) :
    (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words.flatMap frame = srcB a r := by
  rw [ThrBounds.words_eq a r four sel]
  rfl

/-- **The base stage.** On any work bank carrying the selection's child digits on 228–231, the base worker's resident
words on `init`, the constant `scalar U (w+2) 1` at `init iOne`, any framed base at master 220 and blank cells 0–1, the
fixed machine `baseW` writes the canonical base `B(sel)` onto master 220 and changes nothing else. -/
theorem base_step (NI : Nat) (ib : Fin 82 → Fin NI) (iOne : Fin NI) (hib : Function.Injective ib)
    (hone : ib 9 ≠ iOne) (sel : ThresholdRows.Selection a r) (Uf R B0 : Nat) (A : Fin (2+rowsWork NI) → List Bool)
    (hdig : ∀ c, A (masterPort NI (dPort c)) =
      fb (ThrWidth.T a r four L target) ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).digits c))
    (hini : ∀ k : Fin 82, ¬ (73 ≤ k.val ∧ k.val < 77) → A (initPort NI (ib k)) = baseInit a r four L target k)
    (hon : A (initPort NI iOne) = ZeroPadding.pad (bU (ThrWidth.T a r four L target)) (fb (wT a r four L target) 1))
    (h220 : A (masterPort NI 220) = ZeroPadding.pad Uf (fb (wT a r four L target) B0))
    (hc0 : A (cellPort NI 0) = List.replicate R false) (hc1 : A (cellPort NI 1) = List.replicate R false)
    (hUf : 4*wT a r four L target+3 ≤ Uf) (hR : 4*wT a r four L target+3 ≤ R) :
    Step (baseW NI ib iOne) (baseCost (bF (ThrWidth.T a r four L target)) (wT a r four L target)) (fun _ => 0) A
      (fun _ => 0) (Function.update A (masterPort NI 220)
        (ZeroPadding.pad Uf (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel)))) := by
  set T := ThrWidth.T a r four L target with hT
  set d := PCJ45bee56da9f34d5a_StreamPair.data a r four sel with hd
  set Ub := bU T with hUb
  obtain ⟨hbnd, hfit⟩ := b_spec a r four L target sel
  -- the base worker's entry bank, read from `A`
  have hbank : ∀ k : Fin 82, A (bS NI ib k) =
      PCJ45bee56da9f34d5a_FourfoldBaseCell.bank (d.words.flatMap frame) d.digits d.count T (12*T+17)
        (8*(12*T+17)+12) Ub 1 k := by
    intro k
    by_cases hk : 73 ≤ k.val ∧ k.val < 77
    · obtain ⟨c, hc⟩ : ∃ c : Fin 4, k = dk c := ⟨⟨k.val - 73, by omega⟩, Fin.ext (by simp [dk]; omega)⟩
      subst hc
      rw [bS_digit, bank_digit, hdig]
    · rw [bS_init NI ib k hk, hini k hk, baseInit, ← data_src a r four sel]
      by_cases h9 : k = 9
      · subst h9
        rw [RowsConstruction.BaseJoin.base_port9, RowsConstruction.BaseJoin.base_port9]
      · exact bank_other _ _ _ _ _ _ _ _ _ _ k h9 hk
  -- (1) heads of the count/cursor ports to 1
  have s1 := mv_right NI ib A
  -- (2) the docked base worker
  have run := PCJ45bee56da9f34d5a_FourfoldBaseRun.run d T (12*T+17) (8*(12*T+17)+12) (bD T) Ub T (bF T) hbnd
  have s2 := SymVerdict.focus_at run (bS NI ib) (bS_injective NI ib hib) (H1 NI ib) A (H1_bS NI ib hib) hbank
  rw [dockH_existing _ _ _ (H1_bS NI ib hib)] at s2
  set Bv := 1 + d.values.sum with hBv
  have hrad : Bv = PCJ45bee56da9f34d5a_StreamPair.radix a r four sel := rfl
  rw [SymVerdict.install_update _ (bS_injective NI ib hib) A _ 9 (fun k hk9 => by
    rw [hbank k]
    by_cases hk : 73 ≤ k.val ∧ k.val < 77
    · obtain ⟨c, hc⟩ : ∃ c : Fin 4, k = dk c := ⟨⟨k.val - 73, by omega⟩, Fin.ext (by simp [dk]; omega)⟩
      subst hc
      rw [bank_digit, bank_digit]
    · exact bank_other _ _ _ _ _ _ _ _ _ _ k hk9 hk)] at s2
  rw [bS_init NI ib 9 (by decide), RowsConstruction.BaseJoin.base_port9] at s2
  set A2 := Function.update A (initPort NI (ib 9)) (MatrixScoreWeight.scalar Ub (12*T+17+2) Bv) with hA2
  -- (3) heads back
  have s3 := mv_left NI ib A2
  -- (4) accumulator onto master 220
  have hB : Bv < 2^(wT a r four L target) := by
    rw [hrad]; exact ThrWidth.base_fit a r four L target sel
  have cellA2 : ∀ c : Fin 257, A2 (cellPort NI c) = A (cellPort NI c) := fun c =>
    Function.update_of_ne (fun e => by
      have hv := congrArg Fin.val e
      rw [cellPort_val, initPort_val] at hv
      have := (ib 9).isLt
      omega) _ _
  have s4 := sr_step (cpS NI ib) (cpS_injective NI ib) (SignedSortKey.binary (wT a r four L target) Bv)
    (frame (SignedSortKey.binary (wT a r four L target) B0)) (4*wT a r four L target+3) Ub Uf R
    (by rw [frame_length, SignedSortKey.binary_length, SignedSortKey.binary_length])
    (by rw [SignedSortKey.binary_length]) (by omega) hUf hR A2
    (by show A2 (initPort NI (ib 9)) = _; rw [hA2, Function.update_self]; rfl)
    (by show A2 (masterPort NI 220) = _; rw [hA2, Function.update_of_ne (initPort_ne_master NI _ _).symm, h220])
    (by show A2 (cellPort NI 0) = _; rw [cellA2, hc0])
    (by show A2 (cellPort NI 1) = _; rw [cellA2, hc1])
  rw [show cpS NI ib 1 = masterPort NI 220 from rfl, SignedSortKey.binary_length] at s4
  set A3 := Function.update A2 (masterPort NI 220)
    (ZeroPadding.pad Uf (frame (SignedSortKey.binary (wT a r four L target) Bv))) with hA3
  -- (5) accumulator reset from the resident constant
  have cellA3 : ∀ c : Fin 257, A3 (cellPort NI c) = A (cellPort NI c) := fun c => by
    rw [hA3, Function.update_of_ne (cell_ne_master NI c 220), cellA2]
  have s5 := sr_step (rsS NI ib iOne) (rsS_injective NI ib iOne hone) (SignedSortKey.binary (wT a r four L target) 1)
    (frame (SignedSortKey.binary (wT a r four L target) Bv)) (4*wT a r four L target+3) Ub Ub R
    (by rw [frame_length, SignedSortKey.binary_length, SignedSortKey.binary_length])
    (by rw [SignedSortKey.binary_length]) (by omega) (by omega) hR A3
    (by show A3 (initPort NI iOne) = _
        rw [hA3, Function.update_of_ne (initPort_ne_master NI _ _), hA2,
          Function.update_of_ne (fun e => hone (Fin.ext (by
            have := congrArg Fin.val e; rw [initPort_val, initPort_val] at this; omega))), hon])
    (by show A3 (initPort NI (ib 9)) = _
        rw [hA3, Function.update_of_ne (initPort_ne_master NI _ _), hA2, Function.update_self]; rfl)
    (by show A3 (cellPort NI 0) = _; rw [cellA3, hc0])
    (by show A3 (cellPort NI 1) = _; rw [cellA3, hc1])
  rw [show rsS NI ib iOne 1 = initPort NI (ib 9) from rfl, SignedSortKey.binary_length] at s5
  -- the final bank
  have hA9 : A (initPort NI (ib 9)) = ZeroPadding.pad Ub (frame (SignedSortKey.binary (wT a r four L target) 1)) := by
    rw [hini 9 (by decide), baseInit, RowsConstruction.BaseJoin.base_port9]; rfl
  have efin : Function.update A3 (initPort NI (ib 9))
      (ZeroPadding.pad Ub (frame (SignedSortKey.binary (wT a r four L target) 1))) =
      Function.update A (masterPort NI 220)
        (ZeroPadding.pad Uf (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four sel))) := by
    rw [hA3, hA2, Function.update_comm (initPort_ne_master NI _ _), Function.update_idem]
    rw [Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne (initPort_ne_master NI _ _), hA9])]
    rfl
  rw [efin] at s5
  have all := s1.seq (s2.seq (s3.seq (s4.seq s5)))
  exact all.enlarge (by unfold baseCost; omega)

end Base

/-! ## 6. `K'`: the whole selection level on the work block -/

section Sel
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

theorem digit_master (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) (c : Fin 4) :
    thrMasters a r four L target R k (dPort c) =
      fb (ThrWidth.T a r four L target) (KeySucc.dig a r L target k (c4 c)) := by
  rw [← data_digits a r four L target k c]
  have hc : dPort c = ⟨228 + c.val, by omega⟩ := Fin.ext (dPort_val c)
  have h109 : dPort c ≠ 109 := by
    intro e
    have := congrArg Fin.val e
    rw [dPort_val] at this
    simp at this
    omega
  have hkey : dPort c ∈ thrKeySet := by fin_cases c <;> decide
  rw [masters_at a r four L target R k _ h109, keyPad_key _ hkey, hc]
  exact KeySucc.thr_digit_ports a r four _ _ L target _ _ _ _ _ _ _ _ c

theorem master_220 (R : Nat) (k : RCFive.RowKeys.ThrKey a r L target) :
    thrMasters a r four L target R k 220 = ZeroPadding.pad (Uf r.q (ThrWidth.T a r four L target))
      (fb (wT a r four L target) (PCJ45bee56da9f34d5a_StreamPair.radix a r four k.selection)) := by
  rw [masters_at a r four L target R k 220 (by decide), keyPad_key _ (by decide)]
  exact KeySucc.thr_220 a r four _ _ L target _ _ _ _ _ _ _ _

end Sel

end
end RowsConstruction.ThrSelBase
