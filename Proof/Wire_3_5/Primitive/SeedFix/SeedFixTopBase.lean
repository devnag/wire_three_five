import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase
import Proof.Wire_3_5.Primitive.Writers.ComposeEnvBase
import Proof.Wire_3_5.MachineModel.BlockBranch
import Proof.Wire_3_5.MachineModel.BlockJoin

/-! # SEEDFIX: the enclosing term 

Paper: "There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact printer calls. Under the
displayed allowances the printer applies, and the explicit descriptions and their construction give the middle term in
`prim:runtime`" (P3:3170-3173).

`SeedFixAt` is assembled from PA's writers (`WritersAtJ`, verified interface v2) and the C4 part (`C4At`,
`WireExponent3_5PrimTSeedFixTypes`) on one bank:
* tapes `0` the request (framed), `1` the seed word, `2` the mode flag, `3` the THR writer's input, `4` blank;
  then the four stages' scratch and the three writers' tapes (`Dims`, the slot maps `frontSl`, …, `thrWSl`);
* the machine: `front`, then a branch on the flag (S5's `Block.branchM`): THR runs `hashW ; hash ; thrW ; thr`,
  SYM runs `symW ; sym` (`topM`);
* **`seedFixAt_of`**: the word blocks (`WordBlocks.toRewound`) within `(3c₄ + 2c_W + 6)·seedClasses E` for any `E`
  above both floors; **`seedFixLeaf_of`**: `WriterLeafJ l → C4Leaf l → SeedFixLeaf l` with `E₄ := envMax E_W E₄'`.

Paper quantity of the main type: the fixed seeds `seedWord` (`SeedFixAt`, `SeedFixLeaf`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.SeedFixTop
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Slot maps by tape number -/

/-- A stage's tape `i` in the bank: its ports at `q0 q1 q2`, its scratch from `b`. -/
def stVal (q0 q1 q2 b i : ℕ) : ℕ := if i = 0 then q0 else if i = 1 then q1 else if i = 2 then q2 else b + (i - 3)

/-- A stage's slot map. -/
def stSl {T x : ℕ} (q0 q1 q2 b : ℕ) (h : q0 < T ∧ q1 < T ∧ q2 < T ∧ b + x ≤ T) : Fin (3 + x) → Fin T :=
  fun i => ⟨stVal q0 q1 q2 b i.val, by have := i.isLt; unfold stVal; split_ifs <;> omega⟩

theorem stSl_inj {T x : ℕ} (q0 q1 q2 b : ℕ) (h : q0 < T ∧ q1 < T ∧ q2 < T ∧ b + x ≤ T)
    (hq : q0 ≠ q1 ∧ q0 ≠ q2 ∧ q1 ≠ q2) (h0 : q0 < b ∨ b + x ≤ q0) (h1 : q1 < b ∨ b + x ≤ q1)
    (h2 : q2 < b ∨ b + x ≤ q2) : Function.Injective (stSl (x := x) q0 q1 q2 b h) := by
  intro i j e
  have e' := congrArg Fin.val e
  have hi := i.isLt
  have hj := j.isLt
  simp only [stSl, stVal] at e'
  apply Fin.ext
  split_ifs at e' <;> omega

theorem stSl_ne {T x : ℕ} (q0 q1 q2 b : ℕ) (h : q0 < T ∧ q1 < T ∧ q2 < T ∧ b + x ≤ T) (i : Fin T)
    (h0 : i.val ≠ q0) (h1 : i.val ≠ q1) (h2 : i.val ≠ q2) (hr : i.val < b ∨ b + x ≤ i.val) :
    ∀ j, stSl (x := x) q0 q1 q2 b h j ≠ i := by
  intro j e
  have e' := congrArg Fin.val e
  have hj := j.isLt
  simp only [stSl, stVal] at e'
  split_ifs at e' <;> omega

/-- A writer's tape `j` in the bank: its input tape at `p`, the others from `b`. -/
def wVal (p inS b j : ℕ) : ℕ := if j = inS then p else b + j

/-- A writer's slot map. -/
def wSl {T t : ℕ} (p b : ℕ) (inS : Fin t) (h : p < T ∧ b + t ≤ T) : Fin t → Fin T :=
  fun j => ⟨wVal p inS.val b j.val, by have := j.isLt; unfold wVal; split_ifs <;> omega⟩

theorem wSl_inj {T t : ℕ} (p b : ℕ) (inS : Fin t) (h : p < T ∧ b + t ≤ T) (hp : p < b ∨ b + t ≤ p) :
    Function.Injective (wSl p b inS h) := by
  intro i j e
  have e' := congrArg Fin.val e
  have hi := i.isLt
  have hj := j.isLt
  simp only [wSl, wVal] at e'
  apply Fin.ext
  split_ifs at e' with h1 h2 h2 <;> omega

theorem wSl_ne {T t : ℕ} (p b : ℕ) (inS : Fin t) (h : p < T ∧ b + t ≤ T) (i : Fin T) (hp : i.val ≠ p)
    (hr : i.val < b ∨ b + t ≤ i.val) : ∀ j, wSl p b inS h j ≠ i := by
  intro j e
  have e' := congrArg Fin.val e
  have hj := j.isLt
  simp only [wSl, wVal] at e'
  split_ifs at e' <;> omega

/-! ## Bank facts -/


theorem inBank_self {t : ℕ} (i : Fin t) (w : List Bool) : inBank i w i = frame w := by simp [inBank]
theorem inBank_other {t : ℕ} (i j : Fin t) (w : List Bool) (h : j ≠ i) : inBank i w j = [] := by simp [inBank, h]

/-- The entry bank of the word blocks: the framed request on tape `0`. -/
def entryBank (T : ℕ) (w : List Bool) : Fin T → List Bool := fun i => if i.val = 0 then frame w else []

theorem entryBank_zero {T : ℕ} (w : List Bool) (i : Fin T) (h : i.val = 0) : entryBank T w i = frame w := by
  simp [entryBank, h]
theorem entryBank_other {T : ℕ} (w : List Bool) (i : Fin T) (h : i.val ≠ 0) : entryBank T w i = [] := by
  simp [entryBank, h]

/-! ## The layout -/

/-- The bank's dimensions: the four stages' scratch counts and the three writers' tape counts. -/
structure Dims where
  fx : ℕ
  sx : ℕ
  hx : ℕ
  tx : ℕ
  ws : ℕ
  wh : ℕ
  wt : ℕ

namespace Dims
variable (D : Dims)
def bS : ℕ := 5 + D.fx
def bH : ℕ := D.bS + D.sx
def bT : ℕ := D.bH + D.hx
def bWS : ℕ := D.bT + D.tx
def bWH : ℕ := D.bWS + D.ws
def bWT : ℕ := D.bWH + D.wh
def T : ℕ := D.bWT + D.wt
theorem five_le : 5 ≤ D.T := by unfold T bWT bWH bWS bT bH bS; omega
end Dims

section Layout
variable (D : Dims)

theorem frontH : 0 < D.T ∧ 4 < D.T ∧ 2 < D.T ∧ 5 + D.fx ≤ D.T := by
  unfold Dims.T Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega
theorem symH (oS : ℕ) (hoS : oS < D.ws) : 0 < D.T ∧ D.bWS + oS < D.T ∧ 1 < D.T ∧ D.bS + D.sx ≤ D.T := by
  unfold Dims.T Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS at *; omega
theorem hashH (oH : ℕ) (hoH : oH < D.wh) : 0 < D.T ∧ D.bWH + oH < D.T ∧ 3 < D.T ∧ D.bH + D.hx ≤ D.T := by
  unfold Dims.T Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS at *; omega
theorem thrH (oT : ℕ) (hoT : oT < D.wt) : 3 < D.T ∧ D.bWT + oT < D.T ∧ 1 < D.T ∧ D.bT + D.tx ≤ D.T := by
  unfold Dims.T Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS at *; omega
theorem symWH : 0 < D.T ∧ D.bWS + D.ws ≤ D.T := by
  unfold Dims.T Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega
theorem hashWH : 0 < D.T ∧ D.bWH + D.wh ≤ D.T := by
  unfold Dims.T Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega
theorem thrWH : 3 < D.T ∧ D.bWT + D.wt ≤ D.T := by
  unfold Dims.T Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega

/-- The front stage: request on `0`, the blank tape `4`, the flag `2`; scratch from `5`. -/
def frontSl : Fin (3 + D.fx) → Fin D.T := stSl 0 4 2 5 (frontH D)
/-- The SYM stage: request on `0`, the SYM writer's output, the seed word `1`. -/
def symSl (oS : ℕ) (hoS : oS < D.ws) : Fin (3 + D.sx) → Fin D.T := stSl 0 (D.bWS + oS) 1 D.bS (symH D oS hoS)
/-- The hash stage: request on `0`, the hash writer's output, the THR writer's input `3`. -/
def hashSl (oH : ℕ) (hoH : oH < D.wh) : Fin (3 + D.hx) → Fin D.T := stSl 0 (D.bWH + oH) 3 D.bH (hashH D oH hoH)
/-- The THR stage: the THR writer's input `3`, the THR writer's output, the seed word `1`. -/
def thrSl (oT : ℕ) (hoT : oT < D.wt) : Fin (3 + D.tx) → Fin D.T := stSl 3 (D.bWT + oT) 1 D.bT (thrH D oT hoT)
/-- The SYM writer: input tape `0`, the rest from `bWS`. -/
def symWSl (inS : Fin D.ws) : Fin D.ws → Fin D.T := wSl 0 D.bWS inS (symWH D)
/-- The hash writer: input tape `0`, the rest from `bWH`. -/
def hashWSl (inS : Fin D.wh) : Fin D.wh → Fin D.T := wSl 0 D.bWH inS (hashWH D)
/-- The THR writer: input tape `3`, the rest from `bWT`. -/
def thrWSl (inS : Fin D.wt) : Fin D.wt → Fin D.T := wSl 3 D.bWT inS (thrWH D)

end Layout

/-! ## The banks along the two paths -/

section Banks
variable (D : Dims)

theorem inst_val {t u : ℕ} (slots : Fin t → Fin u) (hi : Function.Injective slots) (A : Fin u → List Bool)
    (v : Fin t → List Bool) (i : Fin u) (j : Fin t) (h : i.val = (slots j).val) : install slots A v i = v j := by
  rw [show i = slots j from Fin.ext h, install_slot _ hi]

/-- Tape-number side conditions of the slot maps. -/
macro "slv" : tactic => `(tactic| (simp [frontSl, symSl, hashSl, thrSl, symWSl, hashWSl, thrWSl, stSl, stVal, wSl,
  wVal, Dims.bWT, Dims.bWH, Dims.bWS, Dims.bT, Dims.bH, Dims.bS] at * <;> (try split_ifs) <;> omega))

/-- Close the side conditions (tape numbers) and the stage-bank equations left by a `refine` chain. -/
macro "bankc" : tactic => `(tactic| (all_goals first | slv | simp [stageIn, inBank]))

theorem frontSl_inj : Function.Injective (frontSl D) := stSl_inj 0 4 2 5 _ (by omega) (by omega) (by omega) (by omega)

theorem symSl_inj (oS : ℕ) (hoS : oS < D.ws) : Function.Injective (symSl D oS hoS) :=
  stSl_inj _ _ _ _ _ (by unfold Dims.bWS Dims.bT Dims.bH Dims.bS; omega) (by unfold Dims.bS; omega)
    (by unfold Dims.bWS Dims.bT Dims.bH Dims.bS; omega) (by unfold Dims.bS; omega)

theorem hashSl_inj (oH : ℕ) (hoH : oH < D.wh) : Function.Injective (hashSl D oH hoH) :=
  stSl_inj _ _ _ _ _ (by unfold Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega) (by unfold Dims.bH Dims.bS; omega)
    (by unfold Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega) (by unfold Dims.bH Dims.bS; omega)

theorem thrSl_inj (oT : ℕ) (hoT : oT < D.wt) : Function.Injective (thrSl D oT hoT) :=
  stSl_inj _ _ _ _ _ (by unfold Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega)
    (by unfold Dims.bT Dims.bH Dims.bS; omega) (by unfold Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega)
    (by unfold Dims.bT Dims.bH Dims.bS; omega)

theorem symWSl_inj (inS : Fin D.ws) : Function.Injective (symWSl D inS) :=
  wSl_inj _ _ _ _ (by unfold Dims.bWS Dims.bT Dims.bH Dims.bS; omega)
theorem hashWSl_inj (inS : Fin D.wh) : Function.Injective (hashWSl D inS) :=
  wSl_inj _ _ _ _ (by unfold Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega)
theorem thrWSl_inj (inS : Fin D.wt) : Function.Injective (thrWSl D inS) :=
  wSl_inj _ _ _ _ (by unfold Dims.bWT Dims.bWH Dims.bWS Dims.bT Dims.bH Dims.bS; omega)

variable (w : List Bool) (mb : Bool) (Jf : Fin D.fx → List Bool)

/-- After the front stage. -/
noncomputable def A1 : Fin D.T → List Bool := install (frontSl D) (entryBank D.T w) (stageOut D.fx w [] [mb] Jf)

theorem front_in : ∀ j, entryBank D.T w (frontSl D j) = stageIn D.fx w [] j := by
  intro j
  induction j using Fin.addCases with
  | left k =>
    rcases k with ⟨_ | _ | _ | k, hk⟩
    · refine (entryBank_zero _ _ ?_).trans ?_ <;> bankc
    · refine (entryBank_other _ _ ?_).trans ?_ <;> bankc
    · refine (entryBank_other _ _ ?_).trans ?_ <;> bankc
    · omega
  | right k =>
    have hk := k.isLt
    refine (entryBank_other _ _ ?_).trans ?_ <;> bankc

theorem A1_at0 (i : Fin D.T) (hi : i.val = 0) : A1 D w mb Jf i = frame w := by
  unfold A1
  rw [inst_val _ (frontSl_inj D) _ _ i (Fin.castAdd D.fx 0) (by slv)]
  simp [stageOut]

theorem A1_at2 (i : Fin D.T) (hi : i.val = 2) : A1 D w mb Jf i = [mb] := by
  unfold A1
  rw [inst_val _ (frontSl_inj D) _ _ i (Fin.castAdd D.fx 2) (by slv)]
  simp [stageOut]

theorem A1_off (i : Fin D.T) (h0 : i.val ≠ 0) (h4 : i.val ≠ 4) (h2 : i.val ≠ 2) (hr : i.val < 5 ∨ 5 + D.fx ≤ i.val) :
    A1 D w mb Jf i = [] := by
  unfold A1
  rw [install_other (frontSl D) _ _ i (stSl_ne _ _ _ _ _ i h0 h4 h2 hr)]
  exact entryBank_other w i h0

section Thr
variable (iH oH : Fin D.wh) (vh : List Bool) (Jh : Fin D.wh → List Bool)
  (w' : List Bool) (Jhs : Fin D.hx → List Bool)
  (iT oT : Fin D.wt) (vt : List Bool) (Jt : Fin D.wt → List Bool) (y : List Bool) (Jts : Fin D.tx → List Bool)

/-- After the hash writer. -/
noncomputable def A2 : Fin D.T → List Bool := install (hashWSl D iH) (A1 D w mb Jf) (outBankJ iH oH w vh Jh)
/-- After the hash stage. -/
noncomputable def A3 : Fin D.T → List Bool :=
  install (hashSl D oH.val oH.isLt) (A2 D w mb Jf iH oH vh Jh) (stageOut D.hx w vh (frame w') Jhs)
/-- After the THR writer. -/
noncomputable def A4 : Fin D.T → List Bool :=
  install (thrWSl D iT) (A3 D w mb Jf iH oH vh Jh w' Jhs) (outBankJ iT oT w' vt Jt)
/-- After the THR stage. -/
noncomputable def A5 : Fin D.T → List Bool :=
  install (thrSl D oT.val oT.isLt) (A4 D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt) (stageOut D.tx w' vt y Jts)

theorem hashW_in : ∀ j, A1 D w mb Jf (hashWSl D iH j) = inBank iH w j := by
  intro j
  have hj0 := j.isLt
  by_cases hj : j = iH
  · subst hj
    refine (A1_at0 D w mb Jf _ ?_).trans (inBank_self _ _).symm
    slv
  · have hjv := Fin.val_ne_of_ne hj
    refine (A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans (inBank_other _ _ _ hj).symm <;> slv

theorem A2_at0 (i : Fin D.T) (hi : i.val = 0) : A2 D w mb Jf iH oH vh Jh i = frame w := by
  unfold A2
  rw [inst_val _ (hashWSl_inj D iH) _ _ i iH (by slv), outBankJ_in]

theorem A2_atO (hio : iH ≠ oH) (i : Fin D.T) (hi : i.val = D.bWH + oH.val) : A2 D w mb Jf iH oH vh Jh i = vh := by
  unfold A2
  have hne := Fin.val_ne_of_ne (Ne.symm hio)
  rw [inst_val _ (hashWSl_inj D iH) _ _ i oH (by slv), outBankJ_out _ _ hio]

theorem A2_off (i : Fin D.T) (h0 : i.val ≠ 0) (hr : i.val < D.bWH ∨ D.bWH + D.wh ≤ i.val) :
    A2 D w mb Jf iH oH vh Jh i = A1 D w mb Jf i := by
  unfold A2
  exact install_other (hashWSl D iH) _ _ i (wSl_ne _ _ _ _ i h0 hr)

theorem hashS_in (hio : iH ≠ oH) : ∀ j, A2 D w mb Jf iH oH vh Jh (hashSl D oH.val oH.isLt j) = stageIn D.hx w vh j := by
  intro j
  have hoH := oH.isLt
  induction j using Fin.addCases with
  | left k =>
    rcases k with ⟨_ | _ | _ | k, hk⟩
    · refine (A2_at0 D w mb Jf iH oH vh Jh _ ?_).trans ?_ <;> bankc
    · refine (A2_atO D w mb Jf iH oH vh Jh hio _ ?_).trans ?_ <;> bankc
    · refine (A2_off D w mb Jf iH oH vh Jh _ ?_ ?_).trans ((A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans ?_) <;> bankc
    · omega
  | right k =>
    have hk := k.isLt
    refine (A2_off D w mb Jf iH oH vh Jh _ ?_ ?_).trans ((A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans ?_) <;> bankc

theorem A3_at3 (i : Fin D.T) (hi : i.val = 3) : A3 D w mb Jf iH oH vh Jh w' Jhs i = frame w' := by
  unfold A3
  rw [inst_val _ (hashSl_inj D oH.val oH.isLt) _ _ i (Fin.castAdd D.hx 2) (by slv)]
  simp [stageOut]

theorem A3_off (i : Fin D.T) (h0 : i.val ≠ 0) (h1 : i.val ≠ D.bWH + oH.val) (h3 : i.val ≠ 3)
    (hr : i.val < D.bH ∨ D.bH + D.hx ≤ i.val) : A3 D w mb Jf iH oH vh Jh w' Jhs i = A2 D w mb Jf iH oH vh Jh i := by
  unfold A3
  exact install_other (hashSl D oH.val oH.isLt) _ _ i (stSl_ne _ _ _ _ _ i h0 h1 h3 hr)

theorem thrW_in : ∀ j, A3 D w mb Jf iH oH vh Jh w' Jhs (thrWSl D iT j) = inBank iT w' j := by
  intro j
  have hj0 := j.isLt
  have hoH := oH.isLt
  by_cases hj : j = iT
  · subst hj
    refine (A3_at3 D w mb Jf iH oH vh Jh w' Jhs _ ?_).trans (inBank_self _ _).symm
    slv
  · have hjv := Fin.val_ne_of_ne hj
    refine (A3_off D w mb Jf iH oH vh Jh w' Jhs _ ?_ ?_ ?_ ?_).trans ((A2_off D w mb Jf iH oH vh Jh _ ?_ ?_).trans
      ((A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans (inBank_other _ _ _ hj).symm)) <;> slv

theorem A4_at3 (i : Fin D.T) (hi : i.val = 3) : A4 D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt i = frame w' := by
  unfold A4
  rw [inst_val _ (thrWSl_inj D iT) _ _ i iT (by slv), outBankJ_in]

theorem A4_atO (hio : iT ≠ oT) (i : Fin D.T) (hi : i.val = D.bWT + oT.val) :
    A4 D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt i = vt := by
  unfold A4
  have hne := Fin.val_ne_of_ne (Ne.symm hio)
  rw [inst_val _ (thrWSl_inj D iT) _ _ i oT (by slv), outBankJ_out _ _ hio]

theorem A4_off (i : Fin D.T) (h3 : i.val ≠ 3) (hr : i.val < D.bWT ∨ D.bWT + D.wt ≤ i.val) :
    A4 D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt i = A3 D w mb Jf iH oH vh Jh w' Jhs i := by
  unfold A4
  exact install_other (thrWSl D iT) _ _ i (wSl_ne _ _ _ _ i h3 hr)

theorem thrS_in (hio : iT ≠ oT) :
    ∀ j, A4 D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt (thrSl D oT.val oT.isLt j) = stageIn D.tx w' vt j := by
  intro j
  have hoH := oH.isLt
  have hoT := oT.isLt
  induction j using Fin.addCases with
  | left k =>
    rcases k with ⟨_ | _ | _ | k, hk⟩
    · refine (A4_at3 D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt _ ?_).trans ?_ <;> bankc
    · refine (A4_atO D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt hio _ ?_).trans ?_ <;> bankc
    · refine (A4_off D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt _ ?_ ?_).trans
        ((A3_off D w mb Jf iH oH vh Jh w' Jhs _ ?_ ?_ ?_ ?_).trans ((A2_off D w mb Jf iH oH vh Jh _ ?_ ?_).trans
          ((A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans ?_))) <;> bankc
    · omega
  | right k =>
    have hk := k.isLt
    refine (A4_off D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt _ ?_ ?_).trans
      ((A3_off D w mb Jf iH oH vh Jh w' Jhs _ ?_ ?_ ?_ ?_).trans ((A2_off D w mb Jf iH oH vh Jh _ ?_ ?_).trans
        ((A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans ?_))) <;> bankc

theorem A5_at1 (i : Fin D.T) (hi : i.val = 1) : A5 D w mb Jf iH oH vh Jh w' Jhs iT oT vt Jt y Jts i = y := by
  unfold A5
  rw [inst_val _ (thrSl_inj D oT.val oT.isLt) _ _ i (Fin.castAdd D.tx 2) (by slv)]
  simp [stageOut]

end Thr

section Sym
variable (iS oS : Fin D.ws) (vs : List Bool) (Js : Fin D.ws → List Bool) (y : List Bool) (Jss : Fin D.sx → List Bool)

/-- After the SYM writer. -/
noncomputable def B2 : Fin D.T → List Bool := install (symWSl D iS) (A1 D w mb Jf) (outBankJ iS oS w vs Js)
/-- After the SYM stage. -/
noncomputable def B3 : Fin D.T → List Bool :=
  install (symSl D oS.val oS.isLt) (B2 D w mb Jf iS oS vs Js) (stageOut D.sx w vs y Jss)

theorem symW_in : ∀ j, A1 D w mb Jf (symWSl D iS j) = inBank iS w j := by
  intro j
  have hj0 := j.isLt
  by_cases hj : j = iS
  · subst hj
    refine (A1_at0 D w mb Jf _ ?_).trans (inBank_self _ _).symm
    slv
  · have hjv := Fin.val_ne_of_ne hj
    refine (A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans (inBank_other _ _ _ hj).symm <;> slv

theorem B2_at0 (i : Fin D.T) (hi : i.val = 0) : B2 D w mb Jf iS oS vs Js i = frame w := by
  unfold B2
  rw [inst_val _ (symWSl_inj D iS) _ _ i iS (by slv), outBankJ_in]

theorem B2_atO (hio : iS ≠ oS) (i : Fin D.T) (hi : i.val = D.bWS + oS.val) : B2 D w mb Jf iS oS vs Js i = vs := by
  unfold B2
  have hne := Fin.val_ne_of_ne (Ne.symm hio)
  rw [inst_val _ (symWSl_inj D iS) _ _ i oS (by slv), outBankJ_out _ _ hio]

theorem B2_off (i : Fin D.T) (h0 : i.val ≠ 0) (hr : i.val < D.bWS ∨ D.bWS + D.ws ≤ i.val) :
    B2 D w mb Jf iS oS vs Js i = A1 D w mb Jf i := by
  unfold B2
  exact install_other (symWSl D iS) _ _ i (wSl_ne _ _ _ _ i h0 hr)

theorem symS_in (hio : iS ≠ oS) : ∀ j, B2 D w mb Jf iS oS vs Js (symSl D oS.val oS.isLt j) = stageIn D.sx w vs j := by
  intro j
  have hoS := oS.isLt
  induction j using Fin.addCases with
  | left k =>
    rcases k with ⟨_ | _ | _ | k, hk⟩
    · refine (B2_at0 D w mb Jf iS oS vs Js _ ?_).trans ?_ <;> bankc
    · refine (B2_atO D w mb Jf iS oS vs Js hio _ ?_).trans ?_ <;> bankc
    · refine (B2_off D w mb Jf iS oS vs Js _ ?_ ?_).trans ((A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans ?_) <;> bankc
    · omega
  | right k =>
    have hk := k.isLt
    refine (B2_off D w mb Jf iS oS vs Js _ ?_ ?_).trans ((A1_off D w mb Jf _ ?_ ?_ ?_ ?_).trans ?_) <;> bankc

theorem B3_at1 (i : Fin D.T) (hi : i.val = 1) : B3 D w mb Jf iS oS vs Js y Jss i = y := by
  unfold B3
  rw [inst_val _ (symSl_inj D oS.val oS.isLt) _ _ i (Fin.castAdd D.sx 2) (by slv)]
  simp [stageOut]

end Sym

end Banks

/-! ## The machine -/

section Machine
variable {l : Literals} {EW E₄ : Envelope} {cW c₄ kclk coef A a : ℕ} {ha : a ≤ kclk + 1}

theorem readyStep {t s : ℕ} {p : Machine t s} {b : ℕ} {inp out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p b inp out) : Step p b (fun _ => 0) inp (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact Step.of_run hr (funext hh) ht

end Machine

/-! ## The class inequality and the leaf -/

section Leaf

/-- **The cost inequality**: the machine's time bound is within `(3c₄ + 2c_W + 6)·seedClasses E` for
any envelope `E` above the writers' and the C4 part's floors, at every `q ≥ 1`. -/
theorem cost_fits {EW E₄ E : Envelope} (hEW : ClassLE EW E) (hE4 : ClassLE E₄ E) (cW c₄ q k psi : ℕ) (hq : 1 ≤ q) :
    3 * (c₄ * seedClasses E₄ q k psi) + 2 * (cW * classBound EW .preprocessing q k psi) + 6 ≤
      (3 * c₄ + 2 * cW + 6) * seedClasses E q k psi := by
  have h1 : seedClasses E₄ q k psi ≤ seedClasses E q k psi := by
    have a1 := PrimAsm.ComposeEnv.classBound_mono hE4 .selection q k psi hq (by decide)
    have a2 := PrimAsm.ComposeEnv.classBound_mono hE4 .preprocessing q k psi hq (by decide)
    have a3 := PrimAsm.ComposeEnv.classBound_mono hE4 .table q k psi hq (by decide)
    unfold seedClasses; omega
  have h2 : classBound EW .preprocessing q k psi ≤ seedClasses E q k psi := by
    have a2 := PrimAsm.ComposeEnv.classBound_mono hEW .preprocessing q k psi hq (by decide)
    unfold seedClasses; omega
  have h3 : 1 ≤ seedClasses E q k psi := by
    have ht : 1 ≤ classBound E .table q k psi := by
      show 1 ≤ 2 ^ (q - k) * q ^ E.Atable
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity))
    unfold seedClasses; omega
  have e1 := Nat.mul_le_mul_left (3 * c₄) h1
  have e2 := Nat.mul_le_mul_left (2 * cW) h2
  nlinarith

end Leaf

end NearCubicWires.WireExponent3_5.PrimT.SeedFixTop
