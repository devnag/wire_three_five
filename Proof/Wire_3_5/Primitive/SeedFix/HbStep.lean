import Proof.Wire_3_5.Primitive.SeedFix.HbCons
import Proof.Wire_3_5.UnionMachine.LoopWhile

/-! # C4.Hb, machine part 14: the cell's bank and its docked stages (`filt:soft`, P3:2253-2290)

"After fixing `p`, Gaussian elimination finds its conditional probability" (P3:2268-2269). A cell of the Hb machine
runs on one bank of 94 tapes: the word state's 65 tapes (`wenc`), the masked reset's log, and the 28 tapes the
elimination block keeps for itself (`ex28`: its registers, its row, pass-output and pivot tapes, its constants). A
word program runs docked on the first 66 tapes (**`wmStep`**, through `wm_mask`); the elimination runs docked on its
28 tapes and the word state's constraint, flag and exponent streams (**`elimDock`**).

Paper quantity of the main type: the elimination's flag and count exponent, left on the word state's streams
(`elimDock`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)

section Bank
variable (cap capL : ℕ)

/-- **The Hb bank**: the word state's tapes, the masked reset's log, the elimination's own tapes. -/
def hbBank (σ : HS) (E : Fin 28 → List Bool) : Fin 94 → List Bool :=
  Fin.addCases (m := 66) (n := 28) (Fin.addCases (m := 65) (n := 1) (wenc cap σ).A
    (fun _ => List.replicate capL false)) E

theorem hbBank_lt (σ : HS) (E : Fin 28 → List Bool) (v : ℕ) (h : v < 65) :
    hbBank cap capL σ E ⟨v, by omega⟩ = (wenc cap σ).A ⟨v, h⟩ := by
  show Fin.addCases (m := 66) (n := 28) (motive := fun _ => List Bool) (Fin.addCases (m := 65) (n := 1)
    (motive := fun _ => List Bool) (wenc cap σ).A (fun _ => List.replicate capL false)) E
    (Fin.castAdd 28 (Fin.castAdd 1 ⟨v, h⟩)) = _
  simp only [Fin.addCases_left]

theorem hbBank_log (σ : HS) (E : Fin 28 → List Bool) :
    hbBank cap capL σ E ⟨65, by omega⟩ = List.replicate capL false := by
  show Fin.addCases (m := 66) (n := 28) (motive := fun _ => List Bool) (Fin.addCases (m := 65) (n := 1)
    (motive := fun _ => List Bool) (wenc cap σ).A (fun _ => List.replicate capL false)) E
    (Fin.castAdd 28 (Fin.natAdd 65 (0 : Fin 1))) = _
  simp only [Fin.addCases_left, Fin.addCases_right]

/-- The word programs' slots: the first 66 tapes. -/
def slW : Fin 66 → Fin 94 := Fin.castAdd 28

theorem slW_inj : Function.Injective slW := Fin.castAdd_injective 66 28

theorem install_slW (σ τ : HS) (E : Fin 28 → List Bool) :
    RecoveryRootRound.install slW (hbBank cap capL σ E)
      (Fin.addCases (m := 65) (n := 1) (wenc cap τ).A (fun _ => List.replicate capL false)) = hbBank cap capL τ E := by
  funext i
  refine Fin.addCases (m := 66) (n := 28)
    (motive := fun i => RecoveryRootRound.install slW (hbBank cap capL σ E)
      (Fin.addCases (m := 65) (n := 1) (wenc cap τ).A (fun _ => List.replicate capL false)) i = hbBank cap capL τ E i)
    (fun j => ?_) (fun j => ?_) i
  · rw [show (Fin.castAdd 28 j : Fin 94) = slW j from rfl, RecoveryRootRound.install_slot slW slW_inj]
    simp only [hbBank, slW, Fin.addCases_left]
  · rw [RecoveryRootRound.install_other slW _ _ _ (fun k hk => by
      have := congrArg Fin.val hk; simp [slW] at this; omega)]
    simp only [hbBank, Fin.addCases_right]

/-- A masked word program docked on the word state's tapes. -/
noncomputable def wmM (P : HW) := RecoveryFocus.machine slW (MaskedReset.machine P.toProg.compile (fun _ => true))

/-- **A word program as a step of the Hb bank.** -/
theorem wmStep (P : HW) (σ τ : HS) (n : ℕ) (hw : WExec cap P σ τ n) (hsh : ∀ i, σ.sh i = 0)
    (hv : ∀ r, σ.val r = 0) (hn : n ≤ capL) (E : Fin 28 → List Bool) :
    Step (wmM P) (2 * n + 2) (fun _ => 0) (hbBank cap capL σ E) (fun _ => 0) (hbBank cap capL τ E) := by
  have hm := wm_mask cap capL P σ τ n hw (wenc_H_zero' cap σ hsh hv) hn
  have hd := Block.dockKeep hm slW slW_inj (fun _ => 0) (hbBank cap capL σ E) (fun _ => rfl)
    (fun j => by simp only [hbBank, slW, Fin.addCases_left])
  rw [install_slW] at hd
  exact hd

theorem wenc_A_sets (σ : HS) (s : Fin 24) (l : List Bool) (j : Fin (23 + 2 + 40)) (hj : j ≠ sTape s) :
    (wenc cap (σ.sets s l)).A j = (wenc cap σ).A j := by
  simp only [wenc]
  cases hr : role j with
  | stream i =>
    have hi : i ≠ s := fun h => hj (by subst h; exact role_stream hr)
    simp [Function.update_of_ne hi]
  | cell => rfl
  | reg r => rfl

theorem wenc_A_congr (σ τ : HS) (hst : σ.st = τ.st) (hv : σ.val = τ.val) (hc : σ.cell = τ.cell) :
    (wenc cap σ).A = (wenc cap τ).A := by
  funext j; simp only [wenc]; rw [hst, hv, hc]

end Bank

section Elim
variable (cap capL : ℕ)

/-- The elimination's slots: its own 28 tapes, and the word state's `CONS`, `GF`, `XE` tapes. -/
def slE (j : Fin 31) : Fin 94 :=
  if h : j.val < 22 then ⟨66 + j.val, by omega⟩ else if j.val = 22 then ⟨11, by omega⟩
  else if h' : j.val < 29 then ⟨65 + j.val, by omega⟩ else if j.val = 29 then ⟨12, by omega⟩ else ⟨13, by omega⟩

theorem slE_inj : Function.Injective slE := by
  intro a b h
  have := congrArg Fin.val h
  apply Fin.ext
  simp only [slE] at this
  have ha := a.isLt; have hb := b.isLt
  split_ifs at this <;> simp_all <;> omega

def e28 (j : Fin 28) : Fin 31 := if h : j.val < 22 then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩

/-- **The elimination's own tapes**: its bank (`bank31`) without the constraint, flag and exponent tapes. -/
def ex28 (p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC : ℕ) (R : SeedFix.Regs) (O W P : List Bool) :
    Fin 28 → List Bool :=
  fun j => SeedFix.bank31 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE R O [] W P (pad cK [])
    (pad cC (List.replicate (twoH * ℓ - plen) true)) [] [] (e28 j)

theorem install_eq' {k u : ℕ} (slots : Fin k → Fin u) (hi : Function.Injective slots) (A B : Fin u → List Bool)
    (v : Fin k → List Bool) (h1 : ∀ j, B (slots j) = v j) (h2 : ∀ i, (∀ j, slots j ≠ i) → B i = A i) :
    RecoveryRootRound.install slots A v = B := by
  funext i
  by_cases h : ∃ j, slots j = i
  · obtain ⟨j, rfl⟩ := h
    rw [RecoveryRootRound.install_slot slots hi]
    exact (h1 j).symm
  · have h' : ∀ j, slots j ≠ i := fun j hj => h ⟨j, hj⟩
    rw [RecoveryRootRound.install_other slots A v i h']
    exact (h2 i h').symm

theorem hbBank_slE (p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC : ℕ) (R : SeedFix.Regs)
    (O W P X : List Bool) (g : Bool) (σ : HS) (hG : σ.st sGF = [g]) (hX : σ.st sXE = X) :
    ∀ j : Fin 31, hbBank cap capL σ (ex28 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC R O W P) (slE j) =
      SeedFix.bank31 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE R O (σ.st sCONS) W P (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g] X j := by
  intro j
  fin_cases j <;> first | rfl | exact hG | exact hX

/-- **The elimination docked on the Hb bank.** -/
theorem elimDock (p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC n : ℕ) (R R' : SeedFix.Regs)
    (O O' W W' P P' X X' : List Bool) (g g' : Bool) (σ : HS) (hG : σ.st sGF = [g]) (hX : σ.st sXE = X)
    (h : Step SeedFix.elimM n (fun _ => 0)
      (SeedFix.bank31 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE R O (σ.st sCONS) W P (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g] X) (fun _ => 0)
      (SeedFix.bank31 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE R' O' (σ.st sCONS) W' P' (pad cK [])
        (pad cC (List.replicate (twoH * ℓ - plen) true)) [g'] X')) :
    Step (RecoveryFocus.machine slE SeedFix.elimM) n (fun _ => 0)
      (hbBank cap capL σ (ex28 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC R O W P)) (fun _ => 0)
      (hbBank cap capL ((σ.sets sGF [g']).sets sXE X') (ex28 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC R' O' W' P'))
      := by
  have hd := Block.dockKeep h slE slE_inj (fun _ => 0) _ (fun _ => rfl)
    (hbBank_slE cap capL p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC R O W P X g σ hG hX)
  have hG' : ((σ.sets sGF [g']).sets sXE X').st sGF = [g'] := by simp
  have hX' : ((σ.sets sGF [g']).sets sXE X').st sXE = X' := by simp
  have hC' : ((σ.sets sGF [g']).sets sXE X').st sCONS = σ.st sCONS := by simp
  rw [install_eq' slE slE_inj _ (hbBank cap capL ((σ.sets sGF [g']).sets sXE X')
      (ex28 p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC R' O' W' P')) _ (fun j => by
      rw [hbBank_slE cap capL p ℓ twoH plen pfx m c1 c2 c3 c4 RV cL cE cK cC R' O' W' P' X' g'
        ((σ.sets sGF [g']).sets sXE X') hG' hX' j, hC'])
    (fun i hi => by
      by_cases h66 : 66 ≤ i.val
      · exfalso
        obtain ⟨v, hv⟩ := i
        simp only at h66
        have : v < 94 := hv
        interval_cases v <;> first
          | exact hi 0 rfl | exact hi 1 rfl | exact hi 2 rfl | exact hi 3 rfl | exact hi 4 rfl | exact hi 5 rfl
          | exact hi 6 rfl | exact hi 7 rfl | exact hi 8 rfl | exact hi 9 rfl | exact hi 10 rfl | exact hi 11 rfl
          | exact hi 12 rfl | exact hi 13 rfl | exact hi 14 rfl | exact hi 15 rfl | exact hi 16 rfl | exact hi 17 rfl
          | exact hi 18 rfl | exact hi 19 rfl | exact hi 20 rfl | exact hi 21 rfl | exact hi 23 rfl | exact hi 24 rfl
          | exact hi 25 rfl | exact hi 26 rfl | exact hi 27 rfl | exact hi 28 rfl
      · obtain ⟨v, hv⟩ := i
        simp only at h66
        by_cases h65 : v = 65
        · subst h65
          rw [hbBank_log, hbBank_log]
        · have hlt : v < 65 := by omega
          rw [hbBank_lt cap capL _ _ v hlt, hbBank_lt cap capL _ _ v hlt]
          have h11 : (⟨v, hlt⟩ : Fin (23 + 2 + 40)) ≠ sTape (11 : Fin 24) := by
            intro he
            have h12' : v = 12 := by have := congrArg Fin.val he; simpa [sTape] using this
            subst h12'; exact hi 29 rfl
          have h12 : (⟨v, hlt⟩ : Fin (23 + 2 + 40)) ≠ sTape (12 : Fin 24) := by
            intro he
            have h13' : v = 13 := by have := congrArg Fin.val he; simpa [sTape] using this
            subst h13'; exact hi 30 rfl
          rw [wenc_A_sets cap _ _ _ _ h12, wenc_A_sets cap _ _ _ _ h11])] at hd
  exact hd

end Elim

end NearCubicWires.WireExponent3_5.PrimT.HbM
