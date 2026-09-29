import Proof.Wire_3_5.UnionMachine.FrontFoldDock

/-! # C6 front, U5, the writers' fold (b): one variable's round

Per variable `X` the union front writes the code of its encoding parity (P3:3092-3094), the code of its carrier
(P3:3409-3410, 3432-3433) and the carrier's envelope bit (P3:3083-3094). The round, on a bank of `1220 + tP + tC`
tapes (the fixed tapes `fx k`, then the parity writer's and the carrier writer's own tapes):
cell ; FP's crop of the bitmap `ys[X]` ; the parity writer (any machine with a ready run) ; FP's append of its output
`p` to the parity codes ; FP's crop of the atoms' codes `as[X]` ; the carrier input `catW` ; the carrier writer ; the
append of its output `natWord x` to the carrier codes ; the envelope stage (`envCodeM`) ; the envelope bit `efW`.
**`round_run`**: the kept tapes `0..9` (bitmaps, counter, atoms' codes, counter, `1^sys`, parity codes, carrier codes,
flags, ruler, capacity) go from round `X` to round `X + 1`.

Paper quantity of the main type: the per-variable codes and envelope bits the table writer reads. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (cropBW cropBCost appendBW appendBCost)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldCat (catW catCost efW efCost)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldDock
open NearCubicWires.WireExponent3_5.UnionMachine.CWEnvCode (envCodeM envCodeIn)
open NearCubicWires.WireExponent3_5.UnionMachine.CodeWriters (inBank)
open NearCubicWires.WireExponent3_5.UnionMachine.CWIface (outBankJ outBankJ_in outBankJ_out)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## The layout -/

section Layout
variable (tP tC : ℕ)

/-- A fixed tape of the round's bank. -/
def fx (k : Fin 1220) : Fin (1220 + tP + tC) := (k.castAdd tP).castAdd tC

theorem fx_val (k : Fin 1220) : (fx tP tC k).val = k.val := rfl

theorem fx_inj : Function.Injective (fx tP tC) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; rwa [fx_val, fx_val] at this)

def cropS1 : Fin 9 → Fin 1220 := ![0, 10, 1, 11, 12, 13, 14, 15, 16]
def appS1 : Fin 4 → Fin 1220 := ![17, 10, 5, 18]
def cropS2 : Fin 9 → Fin 1220 := ![2, 10, 3, 19, 20, 21, 22, 23, 24]
def catS : Fin 7 → Fin 1220 := ![19, 10, 17, 3, 4, 25, 26]
def appS2 : Fin 4 → Fin 1220 := ![27, 10, 6, 28]
def envS (j : Fin 1192) : Fin 1220 :=
  ⟨if j.val = 0 then 27 else if j.val = 1 then 8 else if j.val = 2 then 29 else if j.val = 1189 then 9 else j.val + 28,
    by split_ifs <;> omega⟩
def efS : Fin 5 → Fin 1220 := ![29, 10, 3, 7, 30]

theorem cropS1_inj : Function.Injective cropS1 := by decide
theorem appS1_inj : Function.Injective appS1 := by decide
theorem cropS2_inj : Function.Injective cropS2 := by decide
theorem catS_inj : Function.Injective catS := by decide
theorem appS2_inj : Function.Injective appS2 := by decide
theorem efS_inj : Function.Injective efS := by decide
theorem envS_inj : Function.Injective envS := by
  intro a b h; have hv := congrArg Fin.val h; simp only [envS] at hv; apply Fin.ext
  have := a.isLt; have := b.isLt; split_ifs at hv <;> omega

theorem envS_val (j : Fin 1192) (h0 : j.val ≠ 0) (h1 : j.val ≠ 1) (h2 : j.val ≠ 2) (h3 : j.val ≠ 1189) :
    31 ≤ (envS j).val := by
  simp only [envS]; rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3]; have := j.isLt; omega

theorem cropS1_ge : ∀ j : Fin 9, 3 ≤ j.val → 11 ≤ (cropS1 j).val := by decide
theorem cropS2_ge : ∀ j : Fin 9, 3 ≤ j.val → 19 ≤ (cropS2 j).val := by decide
theorem cropS1_lt : ∀ j : Fin 9, (cropS1 j).val < 17 := by decide
theorem appS1_lt : ∀ j : Fin 4, (appS1 j).val < 19 := by decide
theorem cropS2_lt : ∀ j : Fin 9, (cropS2 j).val < 25 := by decide
theorem catS_lt : ∀ j : Fin 7, (catS j).val < 27 := by decide
theorem appS2_lt : ∀ j : Fin 4, (appS2 j).val < 29 := by decide

theorem comp_inj {a : ℕ} (S : Fin a → Fin 1220) (hS : Function.Injective S) :
    Function.Injective (fun j => fx tP tC (S j)) := fun _ _ h => hS (fx_inj tP tC h)

/-- The parity writer's slots: its input on `11`, its output on `17`, its other tapes after the fixed ones. -/
def slP (inS outS : Fin tP) (j : Fin tP) : Fin (1220 + tP + tC) :=
  if j = inS then fx tP tC 11 else if j = outS then fx tP tC 17 else ⟨1220 + j.val, by omega⟩

/-- The carrier writer's slots: its input on `25`, its output on `27`, its other tapes after the parity writer's. -/
def slC (inS outS : Fin tC) (j : Fin tC) : Fin (1220 + tP + tC) :=
  if j = inS then fx tP tC 25 else if j = outS then fx tP tC 27 else ⟨1220 + tP + j.val, by omega⟩

theorem slP_val (inS outS : Fin tP) (j : Fin tP) :
    (slP tP tC inS outS j).val = if j = inS then 11 else if j = outS then 17 else 1220 + j.val := by
  unfold slP; split_ifs <;> rfl

theorem slC_val (inS outS : Fin tC) (j : Fin tC) :
    (slC tP tC inS outS j).val = if j = inS then 25 else if j = outS then 27 else 1220 + tP + j.val := by
  unfold slC; split_ifs <;> rfl

theorem slP_inj (inS outS : Fin tP) : Function.Injective (slP tP tC inS outS) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [slP_val, slP_val] at hv
  by_cases ha : a = inS
  · by_cases hb : b = inS
    · rw [ha, hb]
    · rw [if_pos ha, if_neg hb] at hv; split_ifs at hv <;> omega
  · by_cases hb : b = inS
    · rw [if_neg ha, if_pos hb] at hv; split_ifs at hv <;> omega
    · rw [if_neg ha, if_neg hb] at hv
      by_cases ha' : a = outS
      · by_cases hb' : b = outS
        · rw [ha', hb']
        · rw [if_pos ha', if_neg hb'] at hv; omega
      · by_cases hb' : b = outS
        · rw [if_neg ha', if_pos hb'] at hv; omega
        · rw [if_neg ha', if_neg hb'] at hv; exact Fin.ext (by omega)

theorem slC_inj (inS outS : Fin tC) : Function.Injective (slC tP tC inS outS) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [slC_val, slC_val] at hv
  by_cases ha : a = inS
  · by_cases hb : b = inS
    · rw [ha, hb]
    · rw [if_pos ha, if_neg hb] at hv; split_ifs at hv <;> omega
  · by_cases hb : b = inS
    · rw [if_neg ha, if_pos hb] at hv; split_ifs at hv <;> omega
    · rw [if_neg ha, if_neg hb] at hv
      by_cases ha' : a = outS
      · by_cases hb' : b = outS
        · rw [ha', hb']
        · rw [if_pos ha', if_neg hb'] at hv; omega
      · by_cases hb' : b = outS
        · rw [if_neg ha', if_pos hb'] at hv; omega
        · rw [if_neg ha', if_neg hb'] at hv; exact Fin.ext (by omega)

end Layout

/-! ## Bank bookkeeping -/

section Book
variable {tP tC : ℕ}

theorem inst_fx {a : ℕ} (S : Fin a → Fin 1220) (B : Fin (1220 + tP + tC) → List Bool) (o : Fin a → List Bool)
    (k : Fin 1220) (hk : ∀ j, S j ≠ k) : install (fun j => fx tP tC (S j)) B o (fx tP tC k) = B (fx tP tC k) :=
  install_other _ _ _ _ (fun j e => hk j (fx_inj tP tC e))

theorem inst_fx_hi {a : ℕ} (S : Fin a → Fin 1220) (B : Fin (1220 + tP + tC) → List Bool) (o : Fin a → List Bool)
    (t : Fin (1220 + tP + tC)) (ht : 1220 ≤ t.val) : install (fun j => fx tP tC (S j)) B o t = B t :=
  install_other _ _ _ _ (fun j e => by have := congrArg Fin.val e; rw [fx_val] at this; have := (S j).isLt; omega)

theorem inst_fx_hit {a : ℕ} (S : Fin a → Fin 1220) (hS : Function.Injective S) (B : Fin (1220 + tP + tC) → List Bool)
    (o : Fin a → List Bool) (j : Fin a) : install (fun j => fx tP tC (S j)) B o (fx tP tC (S j)) = o j :=
  install_slot _ (comp_inj tP tC S hS) _ _ _

theorem inst_P_fx (inS outS : Fin tP) (B : Fin (1220 + tP + tC) → List Bool) (o : Fin tP → List Bool) (k : Fin 1220)
    (h11 : k.val ≠ 11) (h17 : k.val ≠ 17) : install (slP tP tC inS outS) B o (fx tP tC k) = B (fx tP tC k) :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [slP_val, fx_val] at hv; have := k.isLt; split_ifs at hv <;> omega)

theorem inst_P_hi (inS outS : Fin tP) (B : Fin (1220 + tP + tC) → List Bool) (o : Fin tP → List Bool)
    (t : Fin (1220 + tP + tC)) (ht : 1220 + tP ≤ t.val) : install (slP tP tC inS outS) B o t = B t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [slP_val] at hv; have := j.isLt; split_ifs at hv <;> omega)

theorem inst_C_fx (inS outS : Fin tC) (B : Fin (1220 + tP + tC) → List Bool) (o : Fin tC → List Bool) (k : Fin 1220)
    (h25 : k.val ≠ 25) (h27 : k.val ≠ 27) : install (slC tP tC inS outS) B o (fx tP tC k) = B (fx tP tC k) :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [slC_val, fx_val] at hv; have := k.isLt; split_ifs at hv <;> omega)

theorem inst_fx_ge {a : ℕ} (S : Fin a → Fin 1220) (m : ℕ) (hS : ∀ j, (S j).val < m)
    (B : Fin (1220 + tP + tC) → List Bool) (o : Fin a → List Bool) (k : Fin 1220) (hk : m ≤ k.val) :
    install (fun j => fx tP tC (S j)) B o (fx tP tC k) = B (fx tP tC k) :=
  inst_fx S B o k (fun j e => by have := hS j; rw [e] at this; omega)

theorem envS_ne (k : Fin 1220) (hk : k.val < 31) (h27 : k.val ≠ 27) (h8 : k.val ≠ 8) (h29 : k.val ≠ 29)
    (h9 : k.val ≠ 9) : ∀ j, envS j ≠ k := by
  intro j e; have := congrArg Fin.val e; simp only [envS] at this; split_ifs at this <;> omega

end Book

/-! ## The round -/

section Round
variable {tP tC sP sC : ℕ}

/-- The round's second half: the carrier's code and envelope bit. -/
noncomputable def restM (MC : Machine tC sC) (inC outC : Fin tC) :=
  Composition.machine (RecoveryFocus.machine (fun j => fx tP tC (cropS2 j)) (Rewind.machine cropBW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine (fun j => fx tP tC (catS j)) (Rewind.machine catW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine (slC tP tC inC outC) MC)
  (Composition.machine (RecoveryFocus.machine (fun j => fx tP tC (appS2 j)) (Rewind.machine appendBW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine (fun j => fx tP tC (envS j)) envCodeM)
    (RecoveryFocus.machine (fun j => fx tP tC (efS j)) (Rewind.machine efW.toProg.compile))))))

/-- **The round's machine.** -/
noncomputable def roundM (MP : Machine tP sP) (inP outP : Fin tP) (MC : Machine tC sC) (inC outC : Fin tC) :=
  Composition.machine
    (RecoveryFocus.machine (fun _ : Fin 1 => fx tP tC 10) NearCubicWires.WireExponent3_5.PrimT.cellM)
  (Composition.machine (RecoveryFocus.machine (fun j => fx tP tC (cropS1 j)) (Rewind.machine cropBW.toProg.compile))
  (Composition.machine (RecoveryFocus.machine (slP tP tC inP outP) MP)
  (Composition.machine (RecoveryFocus.machine (fun j => fx tP tC (appS1 j)) (Rewind.machine appendBW.toProg.compile))
    (restM (tP := tP) MC inC outC))))

/-- The round's kept tapes `0..9` from a list; every other tape blank. -/
def Qf (ks : List (List Bool)) : Fin (1220 + tP + tC) → List Bool := fun t => ks.getD t.val []

/-- The round counter at `X`, with `Z` free cells. -/
def ctr (X Z : ℕ) : List Bool := List.replicate X true ++ List.replicate Z false

theorem ctr_cons (X Z : ℕ) (hZ : 1 ≤ Z) : ctr X Z = List.replicate X true ++ (false :: List.replicate (Z - 1) false) := by
  unfold ctr; obtain ⟨z, rfl⟩ : ∃ z, Z = z + 1 := ⟨Z - 1, by omega⟩; simp [List.replicate_succ]

theorem rep_getD (Z : ℕ) : (List.replicate Z false).getD 0 false = false := by
  cases Z <;> simp [List.replicate_succ]

/-- The round's fuel. -/
def roundCost (Wb Wa X cP cC cE : ℕ) (pcs crs : List (List Bool)) (a p y : List Bool) : ℕ :=
  1 + 1 + ((2 * cropBCost X Wb + 2) + 1 + (cP + 1 + ((2 * appendBCost pcs p + 2) + 1 + ((2 * cropBCost X Wa + 2) + 1 +
    ((2 * catCost a.length p.length X + 2) + 1 + (cC + 1 + ((2 * appendBCost crs y + 2) + 1 + (cE + 1 +
    (2 * efCost X + 2)))))))))

end Round

/-! ## The round's run -/

section Run
variable {tP tC sP sC : ℕ}

/-- The second half's fuel. -/
def restCost (Wa X cC cE : ℕ) (crs : List (List Bool)) (a p y : List Bool) : ℕ :=
  (2 * cropBCost X Wa + 2) + 1 + ((2 * catCost a.length p.length X + 2) + 1 + (cC + 1 +
    ((2 * appendBCost crs y + 2) + 1 + (cE + 1 + (2 * efCost X + 2)))))

theorem envS0 : envS 0 = 27 := by decide
theorem envS1 : envS 1 = 8 := by decide
theorem envS2 : envS 2 = 29 := by decide
theorem envS1189 : envS 1189 = 9 := by decide

/-- **The round's second half**: the atoms' codes of `X`, the carrier input, the carrier writer, its code joins the
carrier codes, the envelope stage, the envelope bit joins the flags. -/
theorem rest_run (MC : Machine tC sC) (inC outC : Fin tC) (hioC : inC ≠ outC)
    (as : List (List Bool)) (Wa : ℕ) (has : ∀ a ∈ as, a.length ≤ Wa) (X Z sys : ℕ) (hXa : X < as.length)
    (hZ : 1 ≤ Z) (crs : List (List Bool)) (hcrs : ∀ g ∈ crs, g ≠ []) (efs : List Bool) (hefs : efs.length = X)
    (L T : ℕ) (p rP : List Bool) (a : List Bool) (ha : as[X] = a) (w : List Bool)
    (hw : w = a ++ if X < sys then p else []) (x : ℕ) (JC : Fin tC → List Bool) (cC : ℕ)
    (hC : ClockJoin.ReadyRun MC cC (inBank inC w) (outBankJ inC outC w (natWord x) JC))
    (b : Bool) (cE : ℕ) (outE : Fin 1192 → List Bool)
    (hE : Step envCodeM cE (fun _ => 0) (envCodeIn x L T) (fun _ => 0) outE)
    (hE1 : outE 1 = List.replicate L true) (hE2 : outE 1189 = List.replicate T true) (hE3 : outE 2 = frame [b])
    (B : Fin (1220 + tP + tC) → List Bool)
    (hB2 : B (fx tP tC 2) = as.flatMap frame) (hB3 : B (fx tP tC 3) = ctr X Z)
    (hB4 : B (fx tP tC 4) = List.replicate sys true) (hB6 : B (fx tP tC 6) = crs.flatMap frame)
    (hB7 : B (fx tP tC 7) = efs) (hB8 : B (fx tP tC 8) = List.replicate L true)
    (hB9 : B (fx tP tC 9) = List.replicate T true) (hB10 : B (fx tP tC 10) = [false])
    (hB17 : B (fx tP tC 17) = frame p ++ rP) (hBz : ∀ k : Fin 1220, 19 ≤ k.val → B (fx tP tC k) = [])
    (hBr : ∀ t : Fin (1220 + tP + tC), 1220 + tP ≤ t.val → B t = []) :
    ∃ out : Fin (1220 + tP + tC) → List Bool,
      Step (restM (tP := tP) MC inC outC) (restCost Wa X cC cE crs a p (natWord x)) (fun _ => 0) B (fun _ => 0)
        out ∧
      out (fx tP tC 0) = B (fx tP tC 0) ∧ out (fx tP tC 1) = B (fx tP tC 1) ∧ out (fx tP tC 5) = B (fx tP tC 5) ∧
      out (fx tP tC 2) = as.flatMap frame ∧ out (fx tP tC 3) = ctr (X + 1) (Z - 1) ∧
      out (fx tP tC 4) = List.replicate sys true ∧ out (fx tP tC 6) = (crs ++ [natWord x]).flatMap frame ∧
      out (fx tP tC 7) = efs ++ [b] ∧ out (fx tP tC 8) = List.replicate L true ∧
      out (fx tP tC 9) = List.replicate T true := by
  have hrc := rep_getD (Z - 1)
  -- 5: the atoms' codes of `X`
  obtain ⟨o5, d5, e50, e51, e52, e53⟩ := cropD (fun j => fx tP tC (cropS2 j)) (comp_inj tP tC cropS2 cropS2_inj) Wa
    as has [] X hXa (List.replicate (Z - 1) false) B (by show B (fx tP tC 2) = _; rw [hB2, List.append_nil])
    (by show B (fx tP tC 10) = _; exact hB10) (by show B (fx tP tC 3) = _; rw [hB3, ctr_cons X Z hZ])
    (fun j hj => hBz _ (cropS2_ge j hj))
  set B5 := install (fun j => fx tP tC (cropS2 j)) B o5 with hB5d
  have c5 : ∀ k : Fin 1220, (∀ j, cropS2 j ≠ k) → B5 (fx tP tC k) = B (fx tP tC k) :=
    fun k hk => inst_fx cropS2 B o5 k hk
  have c5r : ∀ t : Fin (1220 + tP + tC), 1220 ≤ t.val → B5 t = B t := fun t ht => inst_fx_hi cropS2 B o5 t ht
  have c5ge : ∀ k : Fin 1220, 25 ≤ k.val → B5 (fx tP tC k) = B (fx tP tC k) :=
    fun k hk => inst_fx_ge cropS2 25 cropS2_lt B o5 k hk
  have g5_2 : B5 (fx tP tC 2) = as.flatMap frame := by
    have h : B5 (fx tP tC 2) = o5 0 := inst_fx_hit cropS2 cropS2_inj B o5 0
    rw [h, e50, List.append_nil]
  have g5_3 : B5 (fx tP tC 3) = List.replicate (X + 1) true ++ List.replicate (Z - 1) false := by
    have h : B5 (fx tP tC 3) = o5 2 := inst_fx_hit cropS2 cropS2_inj B o5 2
    rw [h, e52]
  have g5_10 : B5 (fx tP tC 10) = [false] := by
    have h : B5 (fx tP tC 10) = o5 1 := inst_fx_hit cropS2 cropS2_inj B o5 1
    rw [h, e51]
  have g5_19 : B5 (fx tP tC 19) = frame a := by
    have h : B5 (fx tP tC 19) = o5 3 := inst_fx_hit cropS2 cropS2_inj B o5 3
    rw [h, e53, ha]
  -- 6: the carrier input
  obtain ⟨o6, d6, e60, e61, e62, e63, e64, e65⟩ := catD (fun j => fx tP tC (catS j)) (comp_inj tP tC catS catS_inj)
    a p [] rP (List.replicate (Z - 1) false) X sys hrc B5
    (by show B5 (fx tP tC 19) = _; rw [g5_19, List.append_nil])
    (by show B5 (fx tP tC 10) = _; exact g5_10)
    (by show B5 (fx tP tC 17) = _; rw [c5 17 (by decide), hB17])
    (by show B5 (fx tP tC 3) = _; exact g5_3)
    (by show B5 (fx tP tC 4) = _; rw [c5 4 (by decide), hB4])
    (by show B5 (fx tP tC 25) = _; rw [c5ge 25 (by decide), hBz 25 (by decide)])
    (by show B5 (fx tP tC 26) = _; rw [c5ge 26 (by decide), hBz 26 (by decide)])
  set B6 := install (fun j => fx tP tC (catS j)) B5 o6 with hB6d
  have c6 : ∀ k : Fin 1220, (∀ j, catS j ≠ k) → B6 (fx tP tC k) = B5 (fx tP tC k) :=
    fun k hk => inst_fx catS B5 o6 k hk
  have c6r : ∀ t : Fin (1220 + tP + tC), 1220 ≤ t.val → B6 t = B5 t := fun t ht => inst_fx_hi catS B5 o6 t ht
  have c6ge : ∀ k : Fin 1220, 27 ≤ k.val → B6 (fx tP tC k) = B5 (fx tP tC k) :=
    fun k hk => inst_fx_ge catS 27 catS_lt B5 o6 k hk
  have g6_25 : B6 (fx tP tC 25) = frame w := by
    have h : B6 (fx tP tC 25) = o6 5 := inst_fx_hit catS catS_inj B5 o6 5
    rw [h, e65, hw]
  have g6_3 : B6 (fx tP tC 3) = List.replicate (X + 1) true ++ List.replicate (Z - 1) false := by
    have h : B6 (fx tP tC 3) = o6 3 := inst_fx_hit catS catS_inj B5 o6 3
    rw [h, e63]
  have g6_4 : B6 (fx tP tC 4) = List.replicate sys true := by
    have h : B6 (fx tP tC 4) = o6 4 := inst_fx_hit catS catS_inj B5 o6 4
    rw [h, e64]
  have g6_10 : B6 (fx tP tC 10) = [false] := by
    have h : B6 (fx tP tC 10) = o6 1 := inst_fx_hit catS catS_inj B5 o6 1
    rw [h, e61]
  -- 7: the carrier writer
  have sIn : slC tP tC inC outC inC = fx tP tC 25 := by unfold slC; rw [if_pos rfl]
  have sOut : slC tP tC inC outC outC = fx tP tC 27 := by unfold slC; rw [if_neg (Ne.symm hioC), if_pos rfl]
  have d7 := writerD (slC tP tC inC outC) (slC_inj tP tC inC outC) MC inC outC _ (natWord x) JC cC hC B6
    (by rw [sIn, g6_25])
    (by
      intro k hk
      unfold slC; rw [if_neg hk]
      split_ifs with hko
      · rw [c6ge 27 (by decide), c5ge 27 (by decide), hBz 27 (by decide)]
      · rw [c6r _ (by show 1220 ≤ 1220 + tP + k.val; omega), c5r _ (by show 1220 ≤ 1220 + tP + k.val; omega),
          hBr _ (by show 1220 + tP ≤ 1220 + tP + k.val; omega)])
  set B7 := install (slC tP tC inC outC) B6 (outBankJ inC outC w (natWord x) JC) with hB7d
  have c7 : ∀ k : Fin 1220, k.val ≠ 25 → k.val ≠ 27 → B7 (fx tP tC k) = B6 (fx tP tC k) :=
    fun k h1 h2 => inst_C_fx inC outC B6 _ k h1 h2
  have g7_27 : B7 (fx tP tC 27) = frame (natWord x) := by
    have h : B7 (slC tP tC inC outC outC) = outBankJ inC outC w (natWord x) JC outC :=
      install_slot _ (slC_inj tP tC inC outC) _ _ outC
    rw [sOut] at h; rw [h]; exact outBankJ_out inC outC hioC _ _ _
  -- 8: the carrier code joins the carrier codes
  obtain ⟨o8, d8, e80, e81, e82⟩ := appD (fun j => fx tP tC (appS2 j)) (comp_inj tP tC appS2 appS2_inj) crs hcrs
    (natWord x) [] B7
    (by show B7 (fx tP tC 27) = _; rw [g7_27, List.append_nil])
    (by show B7 (fx tP tC 10) = _; rw [c7 10 (by decide) (by decide), g6_10])
    (by show B7 (fx tP tC 6) = _; rw [c7 6 (by decide) (by decide), c6 6 (by decide), c5 6 (by decide), hB6])
    (by show B7 (fx tP tC 28) = _
        rw [c7 28 (by decide) (by decide), c6ge 28 (by decide), c5ge 28 (by decide), hBz 28 (by decide)])
  set B8 := install (fun j => fx tP tC (appS2 j)) B7 o8 with hB8d
  have c8 : ∀ k : Fin 1220, (∀ j, appS2 j ≠ k) → B8 (fx tP tC k) = B7 (fx tP tC k) :=
    fun k hk => inst_fx appS2 B7 o8 k hk
  have c8ge : ∀ k : Fin 1220, 29 ≤ k.val → B8 (fx tP tC k) = B7 (fx tP tC k) :=
    fun k hk => inst_fx_ge appS2 29 appS2_lt B7 o8 k hk
  have g8_6 : B8 (fx tP tC 6) = (crs ++ [natWord x]).flatMap frame := by
    have h : B8 (fx tP tC 6) = o8 2 := inst_fx_hit appS2 appS2_inj B7 o8 2
    rw [h, e82]
  have g8_27 : B8 (fx tP tC 27) = frame (natWord x) := by
    have h : B8 (fx tP tC 27) = o8 0 := inst_fx_hit appS2 appS2_inj B7 o8 0
    rw [h, e80, List.append_nil]
  have g8_10 : B8 (fx tP tC 10) = [false] := by
    have h : B8 (fx tP tC 10) = o8 1 := inst_fx_hit appS2 appS2_inj B7 o8 1
    rw [h, e81]
  have z8 : ∀ k : Fin 1220, 29 ≤ k.val → B8 (fx tP tC k) = [] := fun k hk => by
    rw [c8ge k hk, c7 k (by omega) (by omega), c6ge k (by omega), c5ge k (by omega), hBz k (by omega)]
  -- 9: the envelope stage
  have d9 := envD (fun j => fx tP tC (envS j)) (comp_inj tP tC envS envS_inj) x L T cE outE hE B8
    (by show B8 (fx tP tC (envS 0)) = _; rw [envS0]; exact g8_27)
    (by show B8 (fx tP tC (envS 1)) = _
        rw [envS1, c8 8 (by decide), c7 8 (by decide) (by decide), c6 8 (by decide), c5 8 (by decide), hB8])
    (by show B8 (fx tP tC (envS 1189)) = _
        rw [envS1189, c8 9 (by decide), c7 9 (by decide) (by decide), c6 9 (by decide), c5 9 (by decide), hB9])
    (fun j h0 h1 h2 => by
      show B8 (fx tP tC (envS j)) = []
      by_cases j2 : j.val = 2
      · rw [show envS j = 29 from Fin.ext (by simp only [envS]; rw [if_neg h0, if_neg h1, if_pos j2]; rfl)]
        exact z8 29 (by decide)
      · exact z8 _ (by have := envS_val j h0 h1 j2 h2; omega))
  set B9 := install (fun j => fx tP tC (envS j)) B8 outE with hB9d
  have c9 : ∀ k : Fin 1220, k.val < 31 → k.val ≠ 27 → k.val ≠ 8 → k.val ≠ 29 → k.val ≠ 9 →
      B9 (fx tP tC k) = B8 (fx tP tC k) :=
    fun k h1 h2 h3 h4 h5 => inst_fx envS B8 outE k (envS_ne k h1 h2 h3 h4 h5)
  have g9_29 : B9 (fx tP tC 29) = frame [b] := by
    have h : B9 (fx tP tC (envS 2)) = outE 2 := inst_fx_hit envS envS_inj B8 outE 2
    rw [envS2] at h; rw [h, hE3]
  have g9_8 : B9 (fx tP tC 8) = List.replicate L true := by
    have h : B9 (fx tP tC (envS 1)) = outE 1 := inst_fx_hit envS envS_inj B8 outE 1
    rw [envS1] at h; rw [h, hE1]
  have g9_9 : B9 (fx tP tC 9) = List.replicate T true := by
    have h : B9 (fx tP tC (envS 1189)) = outE 1189 := inst_fx_hit envS envS_inj B8 outE 1189
    rw [envS1189] at h; rw [h, hE2]
  -- 10: the envelope bit joins the flags
  obtain ⟨o10, d10, e100, e101, e102, e103⟩ := efD (fun j => fx tP tC (efS j)) (comp_inj tP tC efS efS_inj) b []
    (List.replicate (Z - 1) false) efs X hrc hefs B9
    (by show B9 (fx tP tC 29) = _; rw [g9_29, List.append_nil])
    (by show B9 (fx tP tC 10) = _
        rw [c9 10 (by decide) (by decide) (by decide) (by decide) (by decide), g8_10])
    (by show B9 (fx tP tC 3) = _
        rw [c9 3 (by decide) (by decide) (by decide) (by decide) (by decide), c8 3 (by decide),
          c7 3 (by decide) (by decide), g6_3])
    (by show B9 (fx tP tC 7) = _
        rw [c9 7 (by decide) (by decide) (by decide) (by decide) (by decide), c8 7 (by decide),
          c7 7 (by decide) (by decide), c6 7 (by decide), c5 7 (by decide), hB7])
    (by show B9 (fx tP tC 30) = _
        rw [c9 30 (by decide) (by decide) (by decide) (by decide) (by decide), z8 30 (by decide)])
  set B10 := install (fun j => fx tP tC (efS j)) B9 o10 with hB10d
  have c10 : ∀ k : Fin 1220, (∀ j, efS j ≠ k) → B10 (fx tP tC k) = B9 (fx tP tC k) :=
    fun k hk => inst_fx efS B9 o10 k hk
  have back : ∀ k : Fin 1220, (∀ j, efS j ≠ k) → k.val < 31 → k.val ≠ 27 → k.val ≠ 8 → k.val ≠ 29 →
      k.val ≠ 9 → (∀ j, appS2 j ≠ k) → k.val ≠ 25 → k.val ≠ 27 → (∀ j, catS j ≠ k) → (∀ j, cropS2 j ≠ k) →
      B10 (fx tP tC k) = B (fx tP tC k) := fun k a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 => by
    rw [c10 k a1, c9 k a2 a3 a4 a5 a6, c8 k a7, c7 k a8 a9, c6 k a10, c5 k a11]
  refine ⟨B10, d5.seq (d6.seq (d7.seq (d8.seq (d9.seq d10)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact back 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact back 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact back 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · rw [c10 2 (by decide), c9 2 (by decide) (by decide) (by decide) (by decide) (by decide), c8 2 (by decide),
      c7 2 (by decide) (by decide), c6 2 (by decide), g5_2]
  · have h : B10 (fx tP tC 3) = o10 2 := inst_fx_hit efS efS_inj B9 o10 2
    rw [h, e102]; rfl
  · rw [c10 4 (by decide), c9 4 (by decide) (by decide) (by decide) (by decide) (by decide), c8 4 (by decide),
      c7 4 (by decide) (by decide), g6_4]
  · rw [c10 6 (by decide), c9 6 (by decide) (by decide) (by decide) (by decide) (by decide), g8_6]
  · have h : B10 (fx tP tC 7) = o10 3 := inst_fx_hit efS efS_inj B9 o10 3
    rw [h, e103]
  · rw [c10 8 (by decide), g9_8]
  · rw [c10 9 (by decide), g9_9]

/-- **One variable's round**: from round `X`'s kept tapes to round `X + 1`'s: the parity writer's output `p` (on the
bitmap `ys[X]`) joins the parity codes; the carrier writer's output `natWord x` (on the atoms' codes `as[X]`, then `p`
if `X < sys`) joins the carrier codes; the envelope bit `b` (of `x`) joins the flags; both counters advance. -/
theorem round_run (MP : Machine tP sP) (inP outP : Fin tP) (hioP : inP ≠ outP) (MC : Machine tC sC)
    (inC outC : Fin tC) (hioC : inC ≠ outC) (ys as : List (List Bool)) (Wb Wa : ℕ) (hys : ∀ y ∈ ys, y.length ≤ Wb)
    (has : ∀ a ∈ as, a.length ≤ Wa) (X Z sys : ℕ) (hXy : X < ys.length) (hXa : X < as.length) (hZ : 1 ≤ Z)
    (pcs crs : List (List Bool)) (hpcs : ∀ g ∈ pcs, g ≠ []) (hcrs : ∀ g ∈ crs, g ≠ []) (efs : List Bool)
    (hefs : efs.length = X) (L T : ℕ) (p : List Bool) (JP : Fin tP → List Bool) (cP : ℕ)
    (hP : ClockJoin.ReadyRun MP cP (inBank inP ys[X]) (outBankJ inP outP ys[X] p JP))
    (a : List Bool) (ha : as[X] = a) (w : List Bool) (hw : w = a ++ if X < sys then p else [])
    (x : ℕ) (JC : Fin tC → List Bool) (cC : ℕ)
    (hC : ClockJoin.ReadyRun MC cC (inBank inC w) (outBankJ inC outC w (natWord x) JC))
    (b : Bool) (cE : ℕ) (outE : Fin 1192 → List Bool)
    (hE : Step envCodeM cE (fun _ => 0) (envCodeIn x L T) (fun _ => 0) outE)
    (hE1 : outE 1 = List.replicate L true) (hE2 : outE 1189 = List.replicate T true) (hE3 : outE 2 = frame [b]) :
    ∃ out : Fin (1220 + tP + tC) → List Bool,
      Step (roundM MP inP outP MC inC outC) (roundCost Wb Wa X cP cC cE pcs crs a p (natWord x)) (fun _ => 0)
        (Qf [ys.flatMap frame, ctr X Z, as.flatMap frame, ctr X Z, List.replicate sys true, pcs.flatMap frame,
          crs.flatMap frame, efs, List.replicate L true, List.replicate T true]) (fun _ => 0) out ∧
      out (fx tP tC 0) = ys.flatMap frame ∧ out (fx tP tC 1) = ctr (X + 1) (Z - 1) ∧
      out (fx tP tC 2) = as.flatMap frame ∧ out (fx tP tC 3) = ctr (X + 1) (Z - 1) ∧
      out (fx tP tC 4) = List.replicate sys true ∧ out (fx tP tC 5) = (pcs ++ [p]).flatMap frame ∧
      out (fx tP tC 6) = (crs ++ [natWord x]).flatMap frame ∧ out (fx tP tC 7) = efs ++ [b] ∧
      out (fx tP tC 8) = List.replicate L true ∧ out (fx tP tC 9) = List.replicate T true := by
  set B0 : Fin (1220 + tP + tC) → List Bool := Qf [ys.flatMap frame, ctr X Z, as.flatMap frame, ctr X Z,
    List.replicate sys true, pcs.flatMap frame, crs.flatMap frame, efs, List.replicate L true,
    List.replicate T true] with hB0
  have q0 : ∀ t : Fin (1220 + tP + tC), 10 ≤ t.val → B0 t = [] := fun t ht => by
    simp only [hB0, Qf]; exact List.getD_eq_default _ _ (by simp; omega)
  have q0z : ∀ k : Fin 1220, 10 ≤ k.val → B0 (fx tP tC k) = [] := fun k hk => q0 _ (by rw [fx_val]; exact hk)
  -- 1: the cell
  have d1 := cellD (fx tP tC 10) B0 (q0z 10 (by decide))
  set B1 := install (fun _ : Fin 1 => fx tP tC 10) B0 (fun _ => [false]) with hB1d
  have c1 : ∀ t : Fin (1220 + tP + tC), t.val ≠ 10 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have c1z : ∀ k : Fin 1220, k.val ≠ 10 → B1 (fx tP tC k) = B0 (fx tP tC k) := fun k hk =>
    c1 _ (by rw [fx_val]; exact hk)
  have g1_10 : B1 (fx tP tC 10) = [false] :=
    install_slot (fun _ : Fin 1 => fx tP tC 10) (fun a b _ => Subsingleton.elim a b) _ _ 0
  -- 2: the bitmap of `X`
  obtain ⟨o2, d2, e20, e21, e22, e23⟩ := cropD (fun j => fx tP tC (cropS1 j)) (comp_inj tP tC cropS1 cropS1_inj) Wb
    ys hys [] X hXy (List.replicate (Z - 1) false) B1
    (by show B1 (fx tP tC 0) = _; rw [c1z 0 (by decide), List.append_nil]; rfl)
    (by show B1 (fx tP tC 10) = _; exact g1_10)
    (by show B1 (fx tP tC 1) = _; rw [c1z 1 (by decide), ← ctr_cons X Z hZ]; rfl)
    (fun j hj => by
      show B1 (fx tP tC (cropS1 j)) = []
      have := cropS1_ge j hj
      rw [c1z _ (by omega)]; exact q0z _ (by omega))
  set B2 := install (fun j => fx tP tC (cropS1 j)) B1 o2 with hB2d
  have c2 : ∀ k : Fin 1220, (∀ j, cropS1 j ≠ k) → B2 (fx tP tC k) = B1 (fx tP tC k) :=
    fun k hk => inst_fx cropS1 B1 o2 k hk
  have c2r : ∀ t : Fin (1220 + tP + tC), 1220 ≤ t.val → B2 t = B1 t := fun t ht => inst_fx_hi cropS1 B1 o2 t ht
  have c2ge : ∀ k : Fin 1220, 17 ≤ k.val → B2 (fx tP tC k) = B1 (fx tP tC k) :=
    fun k hk => inst_fx_ge cropS1 17 cropS1_lt B1 o2 k hk
  have g2_0 : B2 (fx tP tC 0) = ys.flatMap frame := by
    have h : B2 (fx tP tC 0) = o2 0 := inst_fx_hit cropS1 cropS1_inj B1 o2 0
    rw [h, e20, List.append_nil]
  have g2_1 : B2 (fx tP tC 1) = ctr (X + 1) (Z - 1) := by
    have h : B2 (fx tP tC 1) = o2 2 := inst_fx_hit cropS1 cropS1_inj B1 o2 2
    rw [h, e22]; rfl
  have g2_10 : B2 (fx tP tC 10) = [false] := by
    have h : B2 (fx tP tC 10) = o2 1 := inst_fx_hit cropS1 cropS1_inj B1 o2 1
    rw [h, e21]
  have g2_11 : B2 (fx tP tC 11) = frame ys[X] := by
    have h : B2 (fx tP tC 11) = o2 3 := inst_fx_hit cropS1 cropS1_inj B1 o2 3
    rw [h, e23]
  -- 3: the parity writer
  have sIn : slP tP tC inP outP inP = fx tP tC 11 := by unfold slP; rw [if_pos rfl]
  have sOut : slP tP tC inP outP outP = fx tP tC 17 := by unfold slP; rw [if_neg (Ne.symm hioP), if_pos rfl]
  have d3 := writerD (slP tP tC inP outP) (slP_inj tP tC inP outP) MP inP outP ys[X] p JP cP hP B2
    (by rw [sIn, g2_11])
    (by
      intro k hk
      unfold slP; rw [if_neg hk]
      split_ifs with hko
      · rw [c2ge 17 (by decide), c1z 17 (by decide), q0z 17 (by decide)]
      · rw [c2r _ (by show 1220 ≤ 1220 + k.val; omega), c1 _ (by show 1220 + k.val ≠ 10; omega),
          q0 _ (by show 10 ≤ 1220 + k.val; omega)])
  set B3 := install (slP tP tC inP outP) B2 (outBankJ inP outP ys[X] p JP) with hB3d
  have c3 : ∀ k : Fin 1220, k.val ≠ 11 → k.val ≠ 17 → B3 (fx tP tC k) = B2 (fx tP tC k) :=
    fun k h1 h2 => inst_P_fx inP outP B2 _ k h1 h2
  have c3r : ∀ t : Fin (1220 + tP + tC), 1220 + tP ≤ t.val → B3 t = B2 t := fun t ht => inst_P_hi inP outP B2 _ t ht
  have g3_17 : B3 (fx tP tC 17) = frame p := by
    have h : B3 (slP tP tC inP outP outP) = outBankJ inP outP ys[X] p JP outP :=
      install_slot _ (slP_inj tP tC inP outP) _ _ outP
    rw [sOut] at h; rw [h]; exact outBankJ_out inP outP hioP _ _ _
  -- 4: the parity code joins the parity codes
  obtain ⟨o4, d4, e40, e41, e42⟩ := appD (fun j => fx tP tC (appS1 j)) (comp_inj tP tC appS1 appS1_inj) pcs hpcs p []
    B3
    (by show B3 (fx tP tC 17) = _; rw [g3_17, List.append_nil])
    (by show B3 (fx tP tC 10) = _; rw [c3 10 (by decide) (by decide), g2_10])
    (by show B3 (fx tP tC 5) = _; rw [c3 5 (by decide) (by decide), c2 5 (by decide), c1z 5 (by decide)]; rfl)
    (by show B3 (fx tP tC 18) = _
        rw [c3 18 (by decide) (by decide), c2ge 18 (by decide), c1z 18 (by decide), q0z 18 (by decide)])
  set B4 := install (fun j => fx tP tC (appS1 j)) B3 o4 with hB4d
  have c4 : ∀ k : Fin 1220, (∀ j, appS1 j ≠ k) → B4 (fx tP tC k) = B3 (fx tP tC k) :=
    fun k hk => inst_fx appS1 B3 o4 k hk
  have c4r : ∀ t : Fin (1220 + tP + tC), 1220 ≤ t.val → B4 t = B3 t := fun t ht => inst_fx_hi appS1 B3 o4 t ht
  have c4ge : ∀ k : Fin 1220, 19 ≤ k.val → B4 (fx tP tC k) = B3 (fx tP tC k) :=
    fun k hk => inst_fx_ge appS1 19 appS1_lt B3 o4 k hk
  have g4_5 : B4 (fx tP tC 5) = (pcs ++ [p]).flatMap frame := by
    have h : B4 (fx tP tC 5) = o4 2 := inst_fx_hit appS1 appS1_inj B3 o4 2
    rw [h, e42]
  have g4_17 : B4 (fx tP tC 17) = frame p ++ [] := by
    have h : B4 (fx tP tC 17) = o4 0 := inst_fx_hit appS1 appS1_inj B3 o4 0
    rw [h, e40]
  have g4_10 : B4 (fx tP tC 10) = [false] := by
    have h : B4 (fx tP tC 10) = o4 1 := inst_fx_hit appS1 appS1_inj B3 o4 1
    rw [h, e41]
  have back : ∀ k : Fin 1220, (∀ j, appS1 j ≠ k) → k.val ≠ 11 → k.val ≠ 17 → (∀ j, cropS1 j ≠ k) → k.val ≠ 10 →
      B4 (fx tP tC k) = B0 (fx tP tC k) := fun k a1 a2 a3 a4 a5 => by
    rw [c4 k a1, c3 k a2 a3, c2 k a4, c1z k a5]
  -- 5–10: the second half
  obtain ⟨out, d5, r0, r1, r5, r2, r3, r4, r6, r7, r8, r9⟩ := rest_run MC inC outC hioC as Wa has X Z sys hXa hZ crs hcrs
    efs hefs L T p [] a ha w hw x JC cC hC b cE outE hE hE1 hE2 hE3 B4
    (by rw [back 2 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [back 3 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [back 4 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [back 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [back 7 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [back 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    (by rw [back 9 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    g4_10 g4_17
    (fun k hk => by
      rw [c4ge k hk, c3 k (by omega) (by omega), c2ge k (by omega), c1z k (by omega), q0z k (by omega)])
    (fun t ht => by
      rw [c4r t (by omega), c3r t ht, c2r t (by omega), c1 t (by omega), q0 t (by omega)])
  refine ⟨out, d1.seq (d2.seq (d3.seq (d4.seq d5))), ?_, ?_, r2, r3, r4, ?_, r6, r7, r8, r9⟩
  · rw [r0, c4 0 (by decide), c3 0 (by decide) (by decide), g2_0]
  · rw [r1, c4 1 (by decide), c3 1 (by decide) (by decide), g2_1]
  · rw [r5, g4_5]

end Run

end NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldRound
