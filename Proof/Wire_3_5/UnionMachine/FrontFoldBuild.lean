import Proof.Wire_3_5.UnionMachine.FrontTWKit
import Proof.Wire_3_5.UnionMachine.FrontEntriesRef

/-! # C6 front, U5: the writers' inputs, built in the register language (precompute (b))

The code writers (FP's `CWIface.WritersJ`, `EnvWritersJ`) read framed words: the support bitmap of a variable
(the parity writer), the codes of its atoms (the carrier writer), `natWord q` before them (the envelope writer), `1^q`
(the constant writer). These programs build those words on the writers' input streams from the PCPP output and the
guess rest, and move the writers' outputs into the table writer's dictionaries.
* **`rowP`**: `K` bits of a raw stream (or `K` zeros), marked, then the end mark: the framed bitmap row.
Paper quantity: the writers' input words (P3:3672-3674). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## A bitmap row -/

/-- One bit of the row: the raw stream's bit (then step) if the flag is set, else `0`. -/
def rowBody (Pr I : Fin (ns + 1)) (F OP : Fin nr) : WM ns nr :=
  .ifr F (.seq (.ifs Pr (emitPair I OP true) (emitPair I OP false)) (.fwd Pr)) (emitPair I OP false)

/-- **The framed row**: `K` bits (or zeros), marked, then the end mark. -/
def rowP (Pr I : Fin (ns + 1)) (F K T OP : Fin nr) : WM ns nr := .seq (cloop K T (rowBody Pr I F OP)) (emitC I OP false)

/-- The row's bits: the stream's `n` bits from its head if the flag is set, else `n` zeros. -/
def rowOf (f : Bool) (bits : List Bool) (n : ℕ) : List Bool := if f then bits else List.replicate n false

theorem marks_snoc (l : List Bool) (b : Bool) : marks (l ++ [b]) = marks l ++ [true, b] := by
  simp [marks]

theorem marks_take_succ (l : List Bool) (j : ℕ) (hj : j < l.length) :
    marks (l.take (j + 1)) = marks (l.take j) ++ [true, l.getD j false] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, marks_snoc,
    List.getD_eq_getElem _ _ hj]

theorem rd_shift' (pre l : List Bool) (j : ℕ) : readTapeBit (pre ++ l) (pre.length + j) = readTapeBit l j := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

/-- The row's state after `j` of its `n` bits. -/
def rowFam (σ : WState ns nr) (Pr I : Fin (ns + 1)) (OP : Fin nr) (row : List Bool) (f : Bool) (j : ℕ) :
    WState ns nr :=
  (appendO σ I OP (marks (row.take j))).seth Pr (σ.sh Pr + if f then j else 0)

section Row
variable (Pr I : Fin (ns + 1)) (hPI : Pr ≠ I) (OP : Fin nr) (row : List Bool) (f : Bool) (σ : WState ns nr)
include hPI

theorem rowFam_step (j : ℕ) (hj : j < row.length) (b : Bool) (hb : row.getD j false = b) :
    (appendO (rowFam σ Pr I OP row f j) I OP [true, b]).seth Pr
        ((appendO (rowFam σ Pr I OP row f j) I OP [true, b]).sh Pr + if f then 1 else 0) =
      rowFam σ Pr I OP row f (j + 1) := by
  unfold rowFam
  rw [marks_take_succ _ _ hj, hb]
  apply WState.eq
  · funext x; by_cases hx : x = Pr
    · subst hx; simp [hPI]; split_ifs <;> omega
    · by_cases hxI : x = I
      · subst hxI; simp [hx]; omega
      · simp [hx, hxI]
  · funext x; by_cases hxI : x = I
    · subst hxI; simp [hPI.symm]
    · simp [hxI]
  · funext x; by_cases hxO : x = OP
    · subst hxO; simp; omega
    · simp [hxO]
  · simp

end Row

theorem rowP_spec (Pr I : Fin (ns + 1)) (hPI : Pr ≠ I) (F K T OP : Fin nr) (hKT : K ≠ T) (hKF : K ≠ F) (hKO : K ≠ OP)
    (hTF : T ≠ F) (hTO : T ≠ OP) (hFO : F ≠ OP) (f : Bool) (pre bits rest : List Bool) (n : ℕ)
    (hbits : f = true → bits.length = n) (σ : WState ns nr)
    (hP : f = true → σ.st Pr = pre ++ bits ++ rest) (hPh : f = true → σ.sh Pr = pre.length)
    (hI : σ.sh I = (σ.st I).length) (hF : σ.val F = f.toNat) (hK : σ.val K = n) (hT : σ.val T = 0)
    (hcap : σ.val OP + 2 * n + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap (rowP Pr I F K T OP) σ
      ((appendO σ I OP (marks (rowOf f bits n) ++ [false])).seth Pr (σ.sh Pr + if f then n else 0))
      (n * (19 + 8) + 1 + 1 + (7 * n + 1) + 1 + 7) := by
  set row := rowOf f bits n with hrow
  have hlen : row.length = n := by
    simp only [hrow, rowOf]; cases f
    · simp
    · simp [hbits rfl]
  -- the fields of the family
  have fI : ∀ j, (rowFam σ Pr I OP row f j).st I = σ.st I ++ marks (row.take j) := fun j => by simp [rowFam, hPI.symm]
  have fIh : ∀ j, (rowFam σ Pr I OP row f j).sh I = ((rowFam σ Pr I OP row f j).st I).length := fun j => by
    simp [rowFam, hPI.symm, hI, marks]
  have fOP : ∀ j, j ≤ n → (rowFam σ Pr I OP row f j).val OP = σ.val OP + 2 * j := fun j hj => by
    simp [rowFam, marks, hlen]; omega
  have fF : ∀ j, (rowFam σ Pr I OP row f j).val F = f.toNat := fun j => by simp [rowFam, hFO, hF]
  have fPst : ∀ j, (rowFam σ Pr I OP row f j).st Pr = σ.st Pr := fun j => by simp [rowFam, hPI]
  have fPh : ∀ j, (rowFam σ Pr I OP row f j).sh Pr = σ.sh Pr + if f then j else 0 := fun j => by simp [rowFam]
  have hF0 : ((rowFam σ Pr I OP row f 0).setv K n).setv T 0 = σ := by
    apply WState.eq
    · funext x; by_cases hx : x = Pr
      · subst hx; simp [rowFam]
      · by_cases hxI : x = I
        · subst hxI; simp [rowFam, hx]
        · simp [rowFam, hx, hxI]
    · funext x; by_cases hxI : x = I
      · subst hxI; simp [rowFam, hPI.symm, marks]
      · simp [rowFam, hxI]
    · funext x
      by_cases hxT : x = T
      · subst hxT; simp [rowFam, hT]
      · by_cases hxK : x = K
        · subst hxK; simp [rowFam, hxT, hK]
        · by_cases hxO : x = OP
          · subst hxO; simp [rowFam, hxT, hxK]
          · simp [rowFam, hxT, hxK, hxO]
    · simp [rowFam]
  have hloop := cloop_spec cap K T hKT (rowBody Pr I F OP) n 19 (rowFam σ Pr I OP row f) hn (by
    intro j hj
    set τ := ((rowFam σ Pr I OP row f j).setv K (n - j - 1)).setv T (j + 1) with hτ
    have hτI : τ.sh I = (τ.st I).length := by simp [τ]; exact fIh j
    have hτF : τ.val F = f.toNat := by simp [τ, Function.update_apply, hKF.symm, hTF.symm, fF]
    have hτO : τ.val OP + 2 ≤ cap := by
      simp [τ, Function.update_apply, hKO.symm, hTO.symm, fOP j (by omega)]; omega
    have hjl : j < row.length := by rw [hlen]; exact hj
    have eFin : ∀ b : Bool, row.getD j false = b →
        (appendO τ I OP [true, b]).seth Pr ((appendO τ I OP [true, b]).sh Pr + if f then 1 else 0) =
          ((rowFam σ Pr I OP row f (j + 1)).setv K (n - j - 1)).setv T (j + 1) := by
      intro b hb
      rw [hτ, appendO_setv _ _ _ _ hTO, appendO_setv _ _ _ _ hKO]
      rw [← rowFam_step Pr I hPI OP row f σ j hjl b hb]
      apply WState.eq <;> simp [Function.update_apply] <;> (try funext x) <;> simp [Function.update_apply] <;>
        split_ifs <;> simp_all
    cases f with
    | false =>
      have hb : row.getD j false = false := by
        simp [hrow, rowOf, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      have h1 := emitPair_spec cap I OP false τ hτI hτO
      refine WExec.mono (WExec.cast cap (WExec.ifrF (by simpa using hτF) h1) ?_ le_rfl) (by omega)
      rw [← eFin false hb]
      simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact (wseth_same _ _).symm
    | true =>
      have hbl := hbits rfl
      have hbit : wbit τ Pr = row.getD j false := by
        simp only [wbit, τ, WState.setv_st, WState.setv_sh, fPst, fPh, if_true, hP rfl, hPh rfl]
        rw [List.append_assoc, rd_shift']
        simp only [hrow, rowOf, if_true, readTapeBit]
        rw [List.getD_append _ _ _ _ (by omega)]
      have hstep : ∀ b : Bool, row.getD j false = b →
          WExec cap (.seq (.ifs Pr (emitPair I OP true) (emitPair I OP false)) (.fwd Pr)) τ
            ((appendO τ I OP [true, b]).seth Pr ((appendO τ I OP [true, b]).sh Pr + 1)) (15 + 1 + 1 + 1) := by
        intro b hb
        cases b
        · exact WExec.seq (WExec.ifsF (by rw [hbit, hb]) (emitPair_spec cap I OP false τ hτI hτO)) (WExec.fwd _ _)
        · exact WExec.seq (WExec.ifsT (by rw [hbit, hb]) (emitPair_spec cap I OP true τ hτI hτO)) (WExec.fwd _ _)
      have h2 := hstep _ rfl
      refine WExec.mono (WExec.cast cap (WExec.ifrT (by simp [hτF]) h2) ?_ le_rfl) (by omega)
      rw [← eFin _ rfl]
      simp only [if_true])
  rw [hF0] at hloop
  set τ := ((rowFam σ Pr I OP row f n).setv K n).setv T 0 with hτ
  have hτ' : τ = rowFam σ Pr I OP row f n := by
    refine WState.eq (by simp [τ]) (by simp [τ]) ?_ (by simp [τ])
    funext x
    by_cases hxT : x = T
    · subst hxT; simp [τ, rowFam, Function.update_apply, hTO, hT]
    · by_cases hxK : x = K
      · subst hxK; simp [τ, rowFam, Function.update_apply, hxT, hKO, hK]
      · simp [τ, rowFam, Function.update_apply, hxT, hxK]
  have hτI : τ.sh I = (τ.st I).length := by rw [hτ']; exact fIh n
  have hτO : τ.val OP < cap := by rw [hτ', fOP n le_rfl]; omega
  have h2 := emitC_spec cap I OP false τ hτI hτO
  refine WExec.cast cap (WExec.seq hloop h2) ?_ (by omega)
  rw [hτ']
  simp only [rowFam, List.take_of_length_le (le_of_eq hlen)]
  apply WState.eq
  · funext x; by_cases hx : x = Pr
    · subst hx; simp [hPI]
    · by_cases hxI : x = I
      · subst hxI; simp [hx]; omega
      · simp [hx, hxI]
  · funext x; by_cases hxI : x = I
    · subst hxI; simp [hPI.symm]
    · simp [hxI]
  · funext x; by_cases hxO : x = OP
    · subst hxO; simp; omega
    · simp [hxO]
  · simp

/-! ## The carrier writer's input: the codes of a variable's atoms (and of its parity) -/

section Car
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

/-- Eight cells forward (one marked grid word). -/
def skip8 (R : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd R) (.seq (.fwd R) (.seq (.fwd R) (.seq (.fwd R) (.seq (.fwd R) (.seq (.fwd R) (.seq (.fwd R) (.fwd R)))))))

theorem skip8_spec (R : Fin (ns + 1)) (σ : WState ns nr) : WExec cap (skip8 R) σ (σ.seth R (σ.sh R + 8)) 15 := by
  unfold skip8
  refine WExec.cast cap ((WExec.fwd _ _).seq ((WExec.fwd _ _).seq ((WExec.fwd _ _).seq ((WExec.fwd _ _).seq
    ((WExec.fwd _ _).seq ((WExec.fwd _ _).seq ((WExec.fwd _ _).seq (WExec.fwd _ _)))))))) ?_ le_rfl
  simp only [WState.seth_sh, Function.update_self, wseth_seth]

/-- One entry: skip its grid word, copy its code's field. -/
def entBody (R I : Fin (ns + 1)) (f c OP : Fin nr) : WM ns nr := .seq (skip8 R) (copyNatM true R I f c OP)

/-- The codes of the first `a` entries. -/
def codesOf (code : ℕ → ℕ) (a : ℕ) : List Bool := (List.range a).flatMap fun k => RepairRepresentation.natWord (code k)

theorem codesOf_succ (code : ℕ → ℕ) (a : ℕ) :
    codesOf code (a + 1) = codesOf code a ++ RepairRepresentation.natWord (code a) := by
  simp [codesOf, List.range_succ, List.flatMap_append]

/-- The carrier input's state after `a` entries. -/
def carFam (σ : WState ns nr) (R I : Fin (ns + 1)) (OP : Fin nr) (code pos : ℕ → ℕ) (a : ℕ) : WState ns nr :=
  (appendO σ I OP (marks (codesOf code a))).seth R (2 * pos a)

theorem marks_length (l : List Bool) : (marks l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [marks] at ih ⊢; omega

theorem codesOf_length (code : ℕ → ℕ) (a : ℕ) (W : ℕ) (hW : ∀ k < a, (RepairRepresentation.natWord (code k)).length ≤ W) :
    (codesOf code a).length ≤ a * W := by
  induction a with
  | zero => simp [codesOf]
  | succ a ih =>
    rw [codesOf_succ, List.length_append]
    have := ih (fun k hk => hW k (by omega))
    have := hW a (by omega)
    rw [Nat.succ_mul]; omega

/-- **The entries' loop** of the carrier input. -/
theorem carLoop_spec (R I : Fin (ns + 1)) (hRI : R ≠ I) (S T f c OP : Fin nr) (hST : S ≠ T) (hSf : S ≠ f) (hSc : S ≠ c)
    (hSO : S ≠ OP) (hTf : T ≠ f) (hTc : T ≠ c) (hTO : T ≠ OP) (hfc : f ≠ c) (hfO : f ≠ OP) (hcO : c ≠ OP)
    (σ : WState ns nr) (s Wn : ℕ) (code pos : ℕ → ℕ) (bs xs : ℕ → Bool)
    (hR : ∀ a < s, ∃ pre rest, σ.st R = pre ++ marks (FrontEntriesRef.gridWord (bs a) (xs a)) ++
      marks (RepairRepresentation.natWord (code a)) ++ rest ∧ pre.length = 2 * pos a)
    (hpos : ∀ a < s, pos (a + 1) = pos a + 4 + (RepairRepresentation.natWord (code a)).length)
    (hW : ∀ a < s, (RepairRepresentation.natWord (code a)).length ≤ Wn)
    (hRh : σ.sh R = 2 * pos 0) (hI : σ.sh I = (σ.st I).length) (hS : σ.val S = s) (hT : σ.val T = 0)
    (hf : σ.val f = 0) (hc : σ.val c = 0) (hcap : σ.val OP + 2 * (s * Wn) + 2 * Wn + 2 ≤ cap) (hs : s ≤ cap) :
    WExec cap (cloop S T (entBody R I f c OP)) σ (carFam σ R I OP code pos s)
      (s * ((15 + 1 + (60 * Wn + 60)) + 8) + 1 + 1 + (7 * s + 1)) := by
  have fam0 : ((carFam σ R I OP code pos 0).setv S s).setv T 0 = σ := by
    apply WState.eq
    · funext x; by_cases hx : x = R
      · subst hx; simp [carFam, hRh]
      · by_cases hxI : x = I
        · subst hxI; simp [carFam, hx, codesOf, marks]
        · simp [carFam, hx, hxI]
    · funext x; by_cases hxI : x = I
      · subst hxI; simp [carFam, codesOf, marks]
      · simp [carFam, hxI]
    · funext x
      by_cases hxT : x = T
      · subst hxT; simp [carFam, hT]
      · by_cases hxS : x = S
        · subst hxS; simp [carFam, hxT, hS]
        · by_cases hxO : x = OP
          · subst hxO; simp [carFam, hxT, hxS, codesOf, marks]
          · simp [carFam, hxT, hxS, hxO]
    · simp [carFam]
  have h := cloop_spec cap S T hST (entBody R I f c OP) s (15 + 1 + (60 * Wn + 60)) (carFam σ R I OP code pos) hs (by
    intro a ha
    set τ := ((carFam σ R I OP code pos a).setv S (s - a - 1)).setv T (a + 1) with hτ
    obtain ⟨pre, rest, hst, hpl⟩ := hR a ha
    have hτR : τ.st R = σ.st R := by simp [τ, carFam, hRI]
    have hτRh : τ.sh R = 2 * pos a := by simp [τ, carFam]
    have h1 := skip8_spec cap R τ
    set τ1 := τ.seth R (τ.sh R + 8) with hτ1
    have hlenW := hW a ha
    have hOPa : (carFam σ R I OP code pos a).val OP = σ.val OP + 2 * (codesOf code a).length := by
      simp [carFam, marks_length]
    have hca := codesOf_length code a Wn (fun k hk => hW k (by omega))
    have h2 := copyNatM_spec cap true R I hRI f c OP hfc hfO hcO (code a)
      (pre ++ marks (FrontEntriesRef.gridWord (bs a) (xs a))) rest τ1
      (by rw [hτ1, WState.seth_st, hτR, hst]; simp [PrimAsm.ParseNat.enc])
      (by rw [hτ1]; simp [hτRh, hpl, FrontEntriesRef.gridWord, marks])
      (by simp [τ1, τ, carFam, hRI.symm, hI, marks_length])
      (by simp [τ1, τ, carFam, Function.update_apply, hSf.symm, hTf.symm, hfO, hf])
      (by simp [τ1, τ, carFam, Function.update_apply, hSc.symm, hTc.symm, hcO, hc])
      (by
        have hτ1OP : τ1.val OP = σ.val OP + 2 * (codesOf code a).length := by
          simp [τ1, τ, carFam, Function.update_apply, hSO.symm, hTO.symm, marks_length]
        have : a * Wn + Wn ≤ s * Wn := by
          have := Nat.mul_le_mul_right Wn (show a + 1 ≤ s by omega); rw [Nat.succ_mul] at this; exact this
        rw [hτ1OP]; omega)
    refine WExec.mono (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl) (by omega)
    rw [hτ1, hτ]
    apply WState.eq
    · funext x; by_cases hx : x = R
      · subst hx; simp [carFam, hRI, hpl, hpos a ha, FrontEntriesRef.gridWord, marks, PrimAsm.ParseNat.stp]; omega
      · by_cases hxI : x = I
        · subst hxI; simp [carFam, hx, codesOf_succ, marks, List.flatMap_append]; omega
        · simp [carFam, hx, hxI]
    · funext x; by_cases hxI : x = I
      · subst hxI; simp [carFam, hRI.symm, codesOf_succ, marks, List.flatMap_append]
      · simp [carFam, hxI]
    · funext x
      by_cases hxT : x = T
      · subst hxT; simp [carFam, hTO]
      · by_cases hxS : x = S
        · subst hxS; simp [carFam, hxT, hSO]
        · by_cases hxO : x = OP
          · subst hxO; simp [carFam, hxT, hxS, codesOf_succ, marks, List.flatMap_append]; omega
          · simp [carFam, hxT, hxS, hxO]
    · simp [carFam])
  rw [fam0] at h
  refine WExec.cast cap h ?_ le_rfl
  refine WState.eq (by simp) (by simp) ?_ (by simp)
  funext x
  by_cases hxT : x = T
  · subst hxT; simp [carFam, Function.update_apply, hTO, hT]
  · by_cases hxS : x = S
    · subst hxS; simp [carFam, Function.update_apply, hxT, hSO, hS]
    · simp [carFam, Function.update_apply, hxT, hxS]

end Car

/-! ## Outputs into the dictionaries -/

section Dict

end Dict

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFold
