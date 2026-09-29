import Proof.Wire_3_5.Primitive.SeedFix.W6C
import Proof.Wire_3_5.Primitive.ThresholdWriter.W6Meta

/-! # W6, part 4: the words and the first numbers

P3:2543-2558: the numbers machine reads, from the request word `reqW n true (thrCodes Cs) codes tl` (framed), the
width `n` and the tuple size `a'`; it writes the top word `frame tw` and the program's native word `frame nw0` twice
(one block per program run: `|𝒢|`, the envelope), reads the occurrence count `M = Σᵢ |supp(topᵢ)|` from the payloads'
first fields, and `ncar`, `cap_T` from their unary ports:
* registers `rN, rA, rM, rNc, rCap` and the temporaries;
* **`readReq`** / `readReq_spec` (`n`, `a'` by `ParseNat.readNatM`), **`nwW`** (a constant framed word), `gM`/`readM`
  (the four guarded payload fields).

Paper quantities of the main types: `n`, `a'`, `M = |occs|`, `ncar`, `cap_T`; the top word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell
  appendO_nil appendO_append appendO_setv)

variable (cap : ℕ)

/-! ## Registers -/

def rN : Fin 80 := 48
def rA : Fin 80 := 49
def rM : Fin 80 := 50
def rNc : Fin 80 := 51
def rCap : Fin 80 := 52
def qa : Fin 80 := 67
def qOP : Fin 80 := 68
def qSP : Fin 80 := 69
def qf : Fin 80 := 70
def qc : Fin 80 := 71
def qp : Fin 80 := 72
def qt : Fin 80 := 73

/-! ## `n` and `a'` from the request -/

/-- Read `n`, skip the mode bit, read `a'`. -/
def readReq : WP :=
  .seq (ParseNat.readNatM true sReq qf qc rN qp qt)
    (.seq (.fwd sReq) (.seq (.fwd sReq) (ParseNat.readNatM true sReq qf qc rA qp qt)))

theorem readReq_spec (σ : WL) (n a' : ℕ) (rest : List Bool)
    (hst : σ.st sReq = frameP (natWord n) ++ ([true, true] ++ (frameP (natWord a') ++ rest)))
    (hsh : σ.sh sReq = 0) (hf : σ.val qf = 0) (hc : σ.val qc = 0) (hp : σ.val qp = 0) (ht : σ.val qt = 0)
    (hN : σ.val rN = 0) (hA : σ.val rA = 0) (c1 : 2 ^ (natBitLength n + 1) ≤ cap)
    (c2 : 2 ^ (natBitLength a' + 1) ≤ cap) :
    ∃ τ, WExec cap readReq σ τ ((natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 +
        (1 + 1 + (1 + 1 + (natBitLength a' + 2) * (40 * 2 ^ natBitLength a' + 40)))) ∧
      τ = ((σ.seth sReq (2 * (natWord n).length + 2 + 2 * (natWord a').length)).setv rN n).setv rA a' := by
  have e1 := ParseNat.readNatM_spec cap true sReq qf qc rN qp qt (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n []
    ([true, true] ++ (frameP (natWord a') ++ rest)) σ (by rw [hst]; rfl) (by rw [hsh]; rfl) hf hc hp ht
    (by rw [hN]; omega)
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = (σ.seth sReq (([] : List Bool).length + ParseNat.stp true * (natWord n).length)).setv rN
      (σ.val rN + n) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have e2 := WExec.fwd (cap := cap) sReq σ1
  have e3 := WExec.fwd (cap := cap) sReq (σ1.seth sReq (σ1.sh sReq + 1))
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = (σ1.seth sReq (σ1.sh sReq + 1)).seth sReq
      ((σ1.seth sReq (σ1.sh sReq + 1)).sh sReq + 1) := ⟨_, rfl⟩
  rw [← hσ3] at e3
  have h3sh : σ3.sh sReq = 2 * (natWord n).length + 2 := by
    rw [hσ3, hσ1]; simp [ParseNat.stp] <;> omega
  have v3 : ∀ r, r ≠ rN → σ3.val r = σ.val r := by
    intro r hr; rw [hσ3, hσ1]; simp [Function.update_of_ne hr]
  have v3N : σ3.val rN = n := by rw [hσ3, hσ1]; simp [hN]
  have s3 : σ3.st = σ.st := by rw [hσ3, hσ1]; rfl
  have e4 := ParseNat.readNatM_spec cap true sReq qf qc rA qp qt (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a' (frameP (natWord n) ++ [true, true])
    rest σ3 (by rw [s3, hst]; simp; rfl) (by rw [h3sh]; simp [frameP_length])
    (by rw [v3 _ (by decide)]; exact hf) (by rw [v3 _ (by decide)]; exact hc) (by rw [v3 _ (by decide)]; exact hp)
    (by rw [v3 _ (by decide)]; exact ht) (by rw [v3 _ (by decide), hA]; omega)
  refine ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), ?_⟩
  apply WState.eq
  · funext j; by_cases h : j = sReq
    · subst h; simp [frameP_length, ParseNat.stp] <;> omega
    · simp [Function.update_of_ne h, hσ3, hσ1]
  · simp [s3]
  · funext r; by_cases h : r = rA
    · subst h; simp [v3 _ (show rA ≠ rN by decide), hA]
    · by_cases h2 : r = rN
      · subst h2; simp [Function.update_of_ne h, v3N]
      · simp [Function.update_of_ne h, Function.update_of_ne h2, v3 _ h2]
  · simp [hσ3, hσ1]

/-! ## A constant framed word -/

/-- Write the constant word `u` on the empty stream `O`, then rewind it. -/
def nwW (O : Fin 192) (u : List Bool) : WP := .seq (PrimAsm.Emit.emitW O qOP u) (WM.rewind O qOP)

theorem nwW_spec (O : Fin 192) (u : List Bool) (σ : WL) (hst : σ.st O = []) (hsh : σ.sh O = 0)
    (hop : σ.val qOP = 0) (hc : u.length ≤ cap) :
    WExec cap (nwW O u) σ (σ.sets O u) (8 * u.length + 1 + (5 * u.length + 1)) := by
  have e1 := PrimAsm.Emit.emitW_spec cap O qOP u σ (by rw [hsh, hst]; rfl) (by rw [hop]; omega)
  have e2 := wrewind_spec cap O qOP u.length (appendO σ O qOP u) (by simp [hop]) (by simp [hop]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext j; by_cases h : j = O
    · subst h; simp [hsh]
    · simp [Function.update_of_ne h]
  · funext j; by_cases h : j = O
    · subst h; simp [hst]
    · simp [Function.update_of_ne h]
  · funext r; by_cases h : r = qOP
    · subst h; simp [hop]
    · simp [Function.update_of_ne h]
  · simp

/-! ## `M` from the payloads -/

/-- Circuit `i`'s guarded field `|supp(topᵢ)|` into `rM`. -/
def gM (i : Fin 4) : WP := .ifr qa (.seq (ParseNat.readNatM true (sPay i) qf qc rM qp qt) (.dec qa)) .skip

theorem gM_spec (i : Fin 4) (a : ℕ) (s : ℕ) (rest : List Bool) (σ : WL)
    (hst : i.val < a → σ.st (sPay i) = frameP (natWord s) ++ rest) (hsh : σ.sh (sPay i) = 0)
    (hq : σ.val qa = a - i.val) (hf : σ.val qf = 0) (hc : σ.val qc = 0) (hp : σ.val qp = 0) (ht : σ.val qt = 0)
    (hcap : σ.val rM + 2 ^ (natBitLength s + 1) ≤ cap) (hqc : σ.val qa ≤ cap) :
    ∃ τ, WExec cap (gM i) σ τ ((natBitLength s + 2) * (40 * 2 ^ natBitLength s + 40) + 3) ∧
      τ.val rM = σ.val rM + (if i.val < a then s else 0) ∧ τ.val qa = a - (i.val + 1) ∧
      (∀ r, r ≠ rM → r ≠ qa → τ.val r = σ.val r) ∧ τ.st = σ.st ∧
      (∀ j, j ≠ sPay i → τ.sh j = σ.sh j) ∧ τ.cell = σ.cell := by
  by_cases hi : i.val < a
  · have e1 := ParseNat.readNatM_spec cap true (sPay i) qf qc rM qp qt (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s [] rest σ
      (by rw [hst hi]; rfl) (by rw [hsh]; rfl) hf hc hp ht hcap
    have e2 := WExec.dec (cap := cap) qa ((σ.seth (sPay i) (([] : List Bool).length + ParseNat.stp true * (natWord s).length)).setv rM
      (σ.val rM + s)) (by simp [Function.update_of_ne (show qa ≠ rM by decide)]; omega)
    refine ⟨_, WExec.mono (WExec.ifrT (Q := WM.skip) (by rw [hq]; omega) (WExec.seq e1 e2)) (by omega), ?_, ?_,
      fun r h1 h2 => ?_, by simp, fun j hj => by simp [Function.update_of_ne hj], by simp⟩
    · simp [Function.update_of_ne (show rM ≠ qa by decide), if_pos hi]
    · simp [Function.update_of_ne (show qa ≠ rM by decide), hq]; omega
    · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  · have hq0 : σ.val qa = 0 := by rw [hq]; omega
    refine ⟨σ, WExec.mono (WExec.ifrF (P := WM.seq (ParseNat.readNatM true (sPay i) qf qc rM qp qt) (WM.dec qa))
      hq0 (WExec.skip σ)) (by omega), by rw [if_neg hi]; simp, by rw [hq0]; omega, fun _ _ _ => rfl, rfl,
      fun _ _ => rfl, rfl⟩

/-- The four guarded payload fields. -/
def readM : WP := .seq (gM 0) (.seq (gM 1) (.seq (gM 2) (gM 3)))

end NearCubicWires.WireExponent3_5.PrimT.W6
