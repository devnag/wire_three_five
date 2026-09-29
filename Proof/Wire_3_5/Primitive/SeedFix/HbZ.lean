import Proof.Wire_3_5.Primitive.SeedFix.HbLayout

/-! # C4.Hb, machine part 2: the factor `Z^±` of a pool gate at a star row (P3:1233-1235, 2253-2262)

"Expanding a discrepancy power gives `δ_{a,j}^{2t} = Σ Z_{a,i_1}⋯Z_{a,i_{2t}} A_{i_1,j}⋯A_{i_{2t},j}`" (P3:2255-2258): each
factor `Z_i` of a printed term is the population bit of pool gate `gi` at star row `q`, the degree-3 form
`Z^±` in the gate's four corners (`zPlusF2`/`zMinusF2`, P3:1233-1235) on the atoms `(4q + k)·G + gi`. This
module writes that factor's polynomial word (`polyWord (zPoly G q sgn gi)`) on the output stream, with the program
helpers of PA's library: each atom code `1^a 0` is framed as `(TT)^a TF` (`atomE`), its value
`a = gi + (4q + k)·G` computed in registers (`ParseNat.addTo`, `UnaryArith.mulAddW`) and emitted by `Emit.repW`.

Registers: `0` the output length, `1` `4q`, `2` `G`, `3` `gi`, `4` the sign, `5 … 8` scratch (zero at entry and exit).

Paper quantity of the main type: the factor `Z^{sgn}` of gate `gi` at row `q` (**`zW_spec`**). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord recW monoBits atomCode)

/-! ## The words -/

/-- An atom code `1^a 0`, framed: `(TT)^a TF`. -/
def atomE (a : ℕ) : List Bool := reps a [true, true] ++ [true, false]

theorem reps_length (n : ℕ) (u : List Bool) : (reps n u).length = n * u.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [reps_succ, List.length_append, ih]; ring

theorem frameP_atomCode (a : ℕ) : frameP (atomCode a) = atomE a := by
  unfold atomE atomCode frameP
  rw [List.flatMap_append, flatMap_replicate]
  rfl

theorem frameP_append' (u v : List Bool) : frameP (u ++ v) = frameP u ++ frameP v := by
  simp [frameP, List.flatMap_append]

theorem frameP_flatMap (as : List ℕ) : frameP (as.flatMap atomCode) = as.flatMap atomE := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [List.flatMap_cons, frameP_append', ih, frameP_atomCode, List.flatMap_cons]

/-- A monomial record: `T`, its atoms framed, the frame's end. -/
theorem recW_eq (as : List ℕ) : recW as = [true] ++ as.flatMap atomE ++ [false] := by
  unfold recW monoBits
  rw [frame_eq_frameP, frameP_flatMap]
  rfl

/-- The polynomial word of a monomial list. -/
theorem polyWord_eq (ms : List (List ℕ)) :
    polyWord ms = ms.flatMap (fun m => [true] ++ m.flatMap atomE ++ [false]) ++ [false] := by
  unfold polyWord
  congr 1
  exact List.flatMap_congr fun m _ => recW_eq m

/-! ## The programs -/

variable (cap : ℕ)

/-- `mulAddW`'s registers: `a = 6` (`4q + k`), `b = 2` (`G`), `c = 5` (the atom), `t = 7`, `w = 8`. -/
def mR : Fin 5 ↪ Fin 40 := ⟨![6, 2, 5, 7, 8], by decide⟩

/-- One atom `gi + (4q + k)·G`, framed, appended to the output. -/
def atomW (k : ℕ) : HW :=
  .seq (PrimAsm.ParseNat.addTo 3 5 7) (.seq (FinalPass.Hash4.wcopyR 1 6 7) (.seq (incN 6 k)
    (.seq (PrimAsm.UnaryArith.mulAddW mR) (.seq (WM.clear 6) (.seq (repW sOUT 0 5 [true, true])
      (emitW sOUT 0 [true, false]))))))

/-- The cost of one atom. -/
def atomCost (q4 G gi k : ℕ) : ℕ :=
  (18 * gi + 3) + 1 + ((18 * q4 + 3) + 1 + (4 * k + 1 + ((G * (18 * (q4 + k) + 8) + 18 * G + 10) + 1 +
    ((3 * (q4 + k) + 1) + 1 + (((gi + (q4 + k) * G) * (8 * 2 + 4) + 1) + 1 + 8 * 2)))))

theorem atomW_spec (k q4 G gi : ℕ) (σ : HS) (h1 : σ.val 1 = q4) (h2 : σ.val 2 = G) (h3 : σ.val 3 = gi)
    (h5 : σ.val 5 = 0) (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0) (h8 : σ.val 8 = 0)
    (ho : σ.sh sOUT = (σ.st sOUT).length)
    (hcap : σ.val 0 + 3 * (gi + (q4 + k) * G) + 2 + q4 + k + G ≤ cap) :
    WExec cap (atomW k) σ (appendO σ sOUT 0 (atomE (gi + (q4 + k) * G))) (atomCost q4 G gi k) := by
  have hle : gi ≤ gi + (q4 + k) * G := Nat.le_add_right _ _
  have s1 := PrimAsm.ParseNat.addTo_spec cap 3 5 7 (by decide) (by decide) (by decide) σ h7 (by omega)
    (by rw [h5, h3]; omega)
  rw [h5, h3, Nat.zero_add] at s1
  set σ1 := σ.setv 5 gi with hσ1
  have s2 := FinalPass.Hash4.wcopyR_spec cap 1 6 7 (by decide) (by decide) (by decide) σ1
    (by simp [σ1, h6]) (by simp [σ1, h7]) (by simp [σ1, h1]; omega)
  have e2 : σ1.val 1 = q4 := by simp [σ1, h1]
  rw [e2] at s2
  set σ2 := σ1.setv 6 q4 with hσ2
  have s3 := incN_spec cap 6 k σ2 (by simp [σ2]; omega)
  have e3 : σ2.val 6 = q4 := by simp [σ2]
  rw [e3] at s3
  set σ3 := σ2.setv 6 (q4 + k) with hσ3
  have v3a : σ3.val (mR 0) = q4 + k := by simp [σ3, mR]
  have v3b : σ3.val (mR 1) = G := by simp [σ3, σ2, σ1, mR, h2]
  have v3c : σ3.val (mR 2) = gi := by simp [σ3, σ2, σ1, mR]
  have s4 := PrimAsm.UnaryArith.mulAddW_spec cap mR σ3 (by simp [σ3, σ2, σ1, mR, h7]) (by simp [σ3, σ2, σ1, mR, h8])
    (by rw [v3b]; omega) (by rw [v3c, v3a, v3b]; omega) (by rw [v3a]; omega)
  rw [v3a, v3b, v3c] at s4
  set σ4 := σ3.setv (mR 2) (gi + (q4 + k) * G) with hσ4
  have s5 := wclear_spec cap 6 (q4 + k) σ4 (by simp [σ4, σ3, mR]) (by simp [σ4, σ3, mR]; omega)
  set σ5 := σ4.setv 6 0 with hσ5
  have v5 : σ5.val 5 = gi + (q4 + k) * G := by simp [σ5, σ4, mR]
  have o5 : σ5.sh sOUT = (σ5.st sOUT).length := by simp [σ5, σ4, σ3, σ2, σ1, ho]
  have p5 : σ5.val 0 = σ.val 0 := by simp [σ5, σ4, σ3, σ2, σ1, mR]
  have s6 := repW_spec cap sOUT 0 5 (by decide) [true, true] (gi + (q4 + k) * G) σ5 v5 o5
    (by rw [p5]; simp; omega) (by omega)
  set σ6 := (appendO σ5 sOUT 0 (reps (gi + (q4 + k) * G) [true, true])).setv 5 0 with hσ6
  have s7 := emitW_spec cap sOUT 0 [true, false] σ6 (by simp [σ6, appendO]; omega)
    (by simp [σ6, appendO, p5, reps_length]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))))
    ?_ (by unfold atomCost; simp)
  have hm2 : (mR 2 : Fin 40) = 5 := rfl
  have v5all : ∀ x, σ5.val x = if x = 5 then gi + (q4 + k) * G else σ.val x := by
    intro x
    rw [hσ5, hσ4, hσ3, hσ2, hσ1, hm2]
    simp only [WState.setv_val, Function.update_apply]
    split_ifs with hx5 hx6 <;> subst_vars <;> simp_all
  rw [hσ6, atomE, ← appendO_append]
  simp only [appendO]
  apply WState.eq
  · rw [hσ5, hσ4, hσ3, hσ2, hσ1]; simp
  · rw [hσ5, hσ4, hσ3, hσ2, hσ1]; simp
  · funext x
    simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs with hx0 hx5 <;> subst_vars <;> simp_all
  · rw [hσ5, hσ4, hσ3, hσ2, hσ1]; simp

/-- A list of programs in sequence. -/
def seqL : List HW → HW
  | [] => .skip
  | P :: Ps => .seq P (seqL Ps)

/-- The atoms of a monomial (its corners `k`), in order. -/
def atomsCost (q4 G gi : ℕ) : List ℕ → ℕ
  | [] => 0
  | k :: m => atomCost q4 G gi k + 1 + atomsCost q4 G gi m

/-- The uniform room one atom needs: its framed code and the register values (`k ≤ 3`). -/
def atomRoom (q4 G gi : ℕ) : ℕ := 3 * (gi + (q4 + 3) * G) + q4 + G + 8

theorem sum_map_const' {α : Type} (l : List α) (c : ℕ) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem atomE_length (a : ℕ) : (atomE a).length = 2 * a + 2 := by
  simp [atomE, reps_length]; ring

theorem atomsW_spec (q4 G gi : ℕ) : ∀ (m : List ℕ) (σ : HS), (∀ k ∈ m, k ≤ 3) → σ.val 1 = q4 → σ.val 2 = G →
    σ.val 3 = gi → σ.val 5 = 0 → σ.val 6 = 0 → σ.val 7 = 0 → σ.val 8 = 0 → σ.sh sOUT = (σ.st sOUT).length →
    σ.val 0 + m.length * atomRoom q4 G gi ≤ cap →
    WExec cap (seqL (m.map atomW)) σ (appendO σ sOUT 0 (m.flatMap fun k => atomE (gi + (q4 + k) * G)))
      (atomsCost q4 G gi m)
  | [], σ, _, _, _, _, _, _, _, _, _, _ => by
    rw [List.flatMap_nil, appendO_nil]; exact WExec.skip σ
  | k :: m, σ, hk, h1, h2, h3, h5, h6, h7, h8, ho, hcap => by
    have hk3 : k ≤ 3 := hk k List.mem_cons_self
    have hmono : (q4 + k) * G ≤ (q4 + 3) * G := Nat.mul_le_mul_right _ (by omega)
    have hR : (k :: m).length * atomRoom q4 G gi = m.length * atomRoom q4 G gi + atomRoom q4 G gi := by
      simp only [List.length_cons]; ring
    have hA : 3 * (gi + (q4 + k) * G) + 2 + q4 + k + G ≤ atomRoom q4 G gi := by unfold atomRoom; omega
    have hA2 : 2 * (gi + (q4 + k) * G) + 2 ≤ atomRoom q4 G gi := by unfold atomRoom; omega
    have s1 := atomW_spec cap k q4 G gi σ h1 h2 h3 h5 h6 h7 h8 ho (by omega)
    set σ' := appendO σ sOUT 0 (atomE (gi + (q4 + k) * G)) with hσ'
    have s2 := atomsW_spec q4 G gi m σ' (fun k' hk' => hk k' (List.mem_cons_of_mem _ hk'))
      (by simp [σ', appendO, h1]) (by simp [σ', appendO, h2]) (by simp [σ', appendO, h3])
      (by simp [σ', appendO, h5]) (by simp [σ', appendO, h6]) (by simp [σ', appendO, h7])
      (by simp [σ', appendO, h8]) (by simp [σ', appendO, ho])
      (by
        simp only [σ', appendO, WState.setv_val, Function.update_self, atomE_length]
        omega)
    refine WExec.cast cap (WExec.seq s1 s2) ?_ (by simp [atomsCost])
    rw [hσ', appendO_append, List.flatMap_cons]

/-- One monomial record: `T`, its atoms, `F`. -/
def monoW (m : List ℕ) : HW := .seq (emitW sOUT 0 [true]) (.seq (seqL (m.map atomW)) (emitW sOUT 0 [false]))

def monoCost (q4 G gi : ℕ) (m : List ℕ) : ℕ := 8 * 1 + 1 + (atomsCost q4 G gi m + 1 + 8 * 1)

/-- The room one monomial needs (`≤ 3` atoms). -/
def monoRoom (q4 G gi : ℕ) : ℕ := 3 * atomRoom q4 G gi + 4

theorem monoW_spec (q4 G gi : ℕ) (m : List ℕ) (σ : HS) (hk : ∀ k ∈ m, k ≤ 3) (hm : m.length ≤ 3) (h1 : σ.val 1 = q4)
    (h2 : σ.val 2 = G) (h3 : σ.val 3 = gi) (h5 : σ.val 5 = 0) (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0) (h8 : σ.val 8 = 0)
    (ho : σ.sh sOUT = (σ.st sOUT).length) (hcap : σ.val 0 + monoRoom q4 G gi ≤ cap) :
    WExec cap (monoW m) σ (appendO σ sOUT 0 ([true] ++ m.flatMap (fun k => atomE (gi + (q4 + k) * G)) ++ [false]))
      (monoCost q4 G gi m) := by
  have hroom : m.length * atomRoom q4 G gi ≤ 3 * atomRoom q4 G gi := Nat.mul_le_mul_right _ hm
  have s1 := emitW_spec cap sOUT 0 [true] σ ho (by unfold monoRoom at hcap; simp; omega)
  set σ1 := appendO σ sOUT 0 [true] with hσ1
  have s2 := atomsW_spec cap q4 G gi m σ1 hk (by simp [σ1, appendO, h1]) (by simp [σ1, appendO, h2])
    (by simp [σ1, appendO, h3]) (by simp [σ1, appendO, h5]) (by simp [σ1, appendO, h6]) (by simp [σ1, appendO, h7])
    (by simp [σ1, appendO, h8]) (by simp [σ1, appendO, ho]) (by simp [σ1, appendO]; unfold monoRoom at hcap; omega)
  set σ2 := appendO σ1 sOUT 0 (m.flatMap fun k => atomE (gi + (q4 + k) * G)) with hσ2
  have hlen : (m.flatMap fun k => atomE (gi + (q4 + k) * G)).length ≤ m.length * atomRoom q4 G gi := by
    have : ∀ k ∈ m, (atomE (gi + (q4 + k) * G)).length ≤ atomRoom q4 G gi := by
      intro k hkm
      have hk3 := hk k hkm
      have hmono : (q4 + k) * G ≤ (q4 + 3) * G := Nat.mul_le_mul_right _ (by omega)
      rw [atomE_length]; unfold atomRoom; omega
    rw [List.length_flatMap]
    calc (m.map fun k => (atomE (gi + (q4 + k) * G)).length).sum ≤ (m.map fun _ => atomRoom q4 G gi).sum :=
          List.sum_le_sum (fun k hkm => this k hkm)
      _ = m.length * atomRoom q4 G gi := by simp [sum_map_const']
  rw [List.length_flatMap] at hlen
  have s3 := emitW_spec cap sOUT 0 [false] σ2 (by simp [σ2, σ1, appendO, ho]; omega)
    (by simp [σ2, σ1, appendO]; unfold monoRoom at hcap; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by simp [monoCost])
  rw [hσ2, hσ1, appendO_append, appendO_append, List.append_assoc]

/-- The monomial records of a polynomial, then `F`. -/
def monosW : List (List ℕ) → HW
  | [] => .skip
  | m :: ms => .seq (monoW m) (monosW ms)

def monosCost (q4 G gi : ℕ) : List (List ℕ) → ℕ
  | [] => 0
  | m :: ms => monoCost q4 G gi m + 1 + monosCost q4 G gi ms

/-- The word of one monomial record. -/
def monoE (q4 G gi : ℕ) (m : List ℕ) : List Bool := [true] ++ m.flatMap (fun k => atomE (gi + (q4 + k) * G)) ++ [false]

theorem monoE_length_le (q4 G gi : ℕ) (m : List ℕ) (hk : ∀ k ∈ m, k ≤ 3) (hm : m.length ≤ 3) :
    (monoE q4 G gi m).length ≤ monoRoom q4 G gi := by
  have : ∀ k ∈ m, (atomE (gi + (q4 + k) * G)).length ≤ atomRoom q4 G gi := by
    intro k hkm
    have hk3 := hk k hkm
    have hmono : (q4 + k) * G ≤ (q4 + 3) * G := Nat.mul_le_mul_right _ (by omega)
    rw [atomE_length]; unfold atomRoom; omega
  have hs : (m.map fun k => (atomE (gi + (q4 + k) * G)).length).sum ≤ m.length * atomRoom q4 G gi := by
    calc (m.map fun k => (atomE (gi + (q4 + k) * G)).length).sum ≤ (m.map fun _ => atomRoom q4 G gi).sum :=
          List.sum_le_sum (fun k hkm => this k hkm)
      _ = m.length * atomRoom q4 G gi := by simp [sum_map_const']
  have hroom : m.length * atomRoom q4 G gi ≤ 3 * atomRoom q4 G gi := Nat.mul_le_mul_right _ hm
  simp only [monoE, List.length_append, List.length_flatMap, List.length_singleton]
  unfold monoRoom; omega

theorem monosW_spec (q4 G gi : ℕ) : ∀ (ms : List (List ℕ)) (σ : HS), (∀ m ∈ ms, (∀ k ∈ m, k ≤ 3) ∧ m.length ≤ 3) →
    σ.val 1 = q4 → σ.val 2 = G → σ.val 3 = gi → σ.val 5 = 0 → σ.val 6 = 0 → σ.val 7 = 0 → σ.val 8 = 0 →
    σ.sh sOUT = (σ.st sOUT).length → σ.val 0 + ms.length * monoRoom q4 G gi ≤ cap →
    WExec cap (monosW ms) σ (appendO σ sOUT 0 (ms.flatMap (monoE q4 G gi))) (monosCost q4 G gi ms)
  | [], σ, _, _, _, _, _, _, _, _, _, _ => by
    rw [List.flatMap_nil, appendO_nil]; exact WExec.skip σ
  | m :: ms, σ, hm, h1, h2, h3, h5, h6, h7, h8, ho, hcap => by
    obtain ⟨hk, hl⟩ := hm m List.mem_cons_self
    have hR : (m :: ms).length * monoRoom q4 G gi = ms.length * monoRoom q4 G gi + monoRoom q4 G gi := by
      simp only [List.length_cons]; ring
    have s1 := monoW_spec cap q4 G gi m σ hk hl h1 h2 h3 h5 h6 h7 h8 ho (by omega)
    set σ' := appendO σ sOUT 0 (monoE q4 G gi m) with hσ'
    have hle := monoE_length_le q4 G gi m hk hl
    have s2 := monosW_spec q4 G gi ms σ' (fun m' hm' => hm m' (List.mem_cons_of_mem _ hm'))
      (by simp [σ', appendO, h1]) (by simp [σ', appendO, h2]) (by simp [σ', appendO, h3])
      (by simp [σ', appendO, h5]) (by simp [σ', appendO, h6]) (by simp [σ', appendO, h7])
      (by simp [σ', appendO, h8]) (by simp [σ', appendO, ho])
      (by simp only [σ', appendO, WState.setv_val, Function.update_self]; omega)
    refine WExec.cast cap (WExec.seq s1 s2) ?_ (by simp [monosCost])
    rw [hσ', appendO_append, List.flatMap_cons]

/-- A polynomial word: its monomial records, then `F`. -/
def polyW (ms : List (List ℕ)) : HW := .seq (monosW ms) (emitW sOUT 0 [false])

/-- `Z⁺`'s and `Z⁻`'s monomials as corner lists. -/
def zPlusL : List (List ℕ) := Stars.zPlusF2.map fun m => m.map Fin.val
def zMinusL : List (List ℕ) := Stars.zMinusF2.map fun m => m.map Fin.val

theorem zL_ok (sgn : Bool) : ∀ m ∈ (if sgn then zPlusL else zMinusL), (∀ k ∈ m, k ≤ 3) ∧ m.length ≤ 3 := by
  cases sgn <;> decide

theorem zL_length (sgn : Bool) : (if sgn then zPlusL else zMinusL).length = 10 := by cases sgn <;> decide

/-- **The factor `Z^{sgn}` of gate `gi` at row `q`**: `Z⁺` when register `4` is set, else `Z⁻`. -/
def zW : HW := .ifr 4 (polyW zPlusL) (polyW zMinusL)

/-- The factor's cost (the larger branch). -/
def zCost (q4 G gi : ℕ) : ℕ := monosCost q4 G gi zPlusL + monosCost q4 G gi zMinusL + 1 + 8 + 1

theorem liftMap (f : ℕ → ℕ) (m : List (Fin 4)) :
    (List.flatMap (fun a : Fin 4 => [(a : ℕ)]) m).map f = m.map (fun a => f a.val) := by
  induction m with
  | nil => rfl
  | cons a m ih => simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, ih]; rfl

theorem zPoly_word (G q gi : ℕ) (sgn : Bool) :
    polyWord (HashB.zPoly G q sgn gi) = (if sgn then zPlusL else zMinusL).flatMap (monoE (4 * q) G gi) ++ [false] := by
  rw [polyWord_eq]
  congr 1
  have hconv : ∀ m : List (Fin 4), (m.map fun k => CompilerMachine.Pool.poolIndex G q k gi) =
      (m.map Fin.val).map (fun k => CompilerMachine.Pool.poolIndex G q k gi) := by
    intro m; simp only [List.map_map]; simp; exact liftMap _ m
  have key : ∀ p : Shared.F2Poly (Fin 4),
      (p.map fun m => m.map fun k => CompilerMachine.Pool.poolIndex G q k gi).flatMap
          (fun m => [true] ++ m.flatMap atomE ++ [false]) =
        (p.map fun m => m.map Fin.val).flatMap (monoE (4 * q) G gi) := by
    intro p
    induction p with
    | nil => rfl
    | cons m p ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      rw [hconv m]
      congr 1
      unfold monoE
      congr 2
      generalize m.map Fin.val = l
      induction l with
      | nil => rfl
      | cons k l ihl =>
        simp only [List.map_cons, List.flatMap_cons, ihl]
        congr 1
        unfold CompilerMachine.Pool.poolIndex
        rw [Nat.add_comm]
  unfold HashB.zPoly zPlusL zMinusL
  cases sgn <;> simp only [Bool.false_eq_true, if_false, if_true] <;> exact key _

theorem zW_spec (q G gi : ℕ) (sgn : Bool) (σ : HS) (h1 : σ.val 1 = 4 * q) (h2 : σ.val 2 = G) (h3 : σ.val 3 = gi)
    (h4 : σ.val 4 = if sgn then 1 else 0) (h5 : σ.val 5 = 0) (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0)
    (h8 : σ.val 8 = 0) (ho : σ.sh sOUT = (σ.st sOUT).length) (hcap : σ.val 0 + 11 * monoRoom (4 * q) G gi ≤ cap) :
    WExec cap zW σ (appendO σ sOUT 0 (polyWord (HashB.zPoly G q sgn gi))) (zCost (4 * q) G gi) := by
  rw [zPoly_word, ← appendO_append]
  have hms := monosW_spec cap (4 * q) G gi (if sgn then zPlusL else zMinusL) σ (zL_ok sgn) h1 h2 h3 h5 h6 h7 h8 ho
    (by rw [zL_length]; omega)
  set σ' := appendO σ sOUT 0 ((if sgn then zPlusL else zMinusL).flatMap (monoE (4 * q) G gi)) with hσ'
  have hlen : ((if sgn then zPlusL else zMinusL).flatMap (monoE (4 * q) G gi)).length ≤ 10 * monoRoom (4 * q) G gi := by
    rw [List.length_flatMap]
    calc (((if sgn then zPlusL else zMinusL).map fun m => (monoE (4 * q) G gi m).length)).sum
        ≤ (((if sgn then zPlusL else zMinusL).map fun _ => monoRoom (4 * q) G gi)).sum :=
          List.sum_le_sum (fun m hm => monoE_length_le _ _ _ m (zL_ok sgn m hm).1 (zL_ok sgn m hm).2)
      _ = 10 * monoRoom (4 * q) G gi := by rw [sum_map_const', zL_length]
  rw [List.length_flatMap] at hlen
  have h1r : 1 ≤ monoRoom (4 * q) G gi := by unfold monoRoom; omega
  have he := emitW_spec cap sOUT 0 [false] σ' (by simp [σ', appendO, ho])
    (by simp [σ', appendO]; omega)
  cases sgn
  · have hb := WExec.ifrF (P := polyW zPlusL) (h4.trans (by simp)) (WExec.seq hms he)
    exact WExec.mono hb (by unfold zCost; simp only [Bool.false_eq_true, if_false, if_true, List.length_singleton]; omega)
  · have hb := WExec.ifrT (Q := polyW zMinusL) (by rw [h4]; simp) (WExec.seq hms he)
    exact WExec.mono hb (by unfold zCost; simp only [Bool.false_eq_true, if_false, if_true, List.length_singleton]; omega)

end NearCubicWires.WireExponent3_5.PrimT.HbM
