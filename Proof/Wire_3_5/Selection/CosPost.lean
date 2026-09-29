import Proof.Wire_3_5.Selection.CosParse5

/-! # C1.5 parse: the coset loop's entry state (P3:1356-1360)

Paper: "There are 2^k candidate cosets [...] Select a minimum objective" (P3:1358-1360). The parse's end state `stC`
is the coset loop's entry state before the first coset: `PPost` (the loop invariant `LInv` at the counter `0` with the
sentinel best key `(1, 0)` and `BEST = 0`, the register file `pvP`, the output stream empty). Main declarations:
`stC_st`, `stC_sh`, `stC_val`, **`pPost_stC`**. Paper quantity: the coset loop's entry state. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (selWord)

@[simp] theorem Sm_w1 : Sm 1 = 3 := by decide

@[simp] theorem Qm_v0 : Qm 0 = 0 := rfl
@[simp] theorem Qm_v1 : Qm 1 = 1 := rfl
@[simp] theorem Qm_v2 : Qm 2 = 2 := rfl
@[simp] theorem Qm_v3 : Qm 3 = 3 := rfl
@[simp] theorem Qm_v4 : Qm 4 = 4 := rfl
@[simp] theorem Qm_v5 : Qm 5 = 5 := rfl
@[simp] theorem Qm_v6 : Qm 6 = 6 := rfl
@[simp] theorem Qm_v7 : Qm 7 = 7 := rfl
@[simp] theorem Qm_v8 : Qm 8 = 8 := rfl
@[simp] theorem Qm_v9 : Qm 9 = 9 := rfl
@[simp] theorem Qm_v10 : Qm 10 = 10 := rfl
@[simp] theorem Qm_v11 : Qm 11 = 11 := rfl
@[simp] theorem Qm_v12 : Qm 12 = 12 := rfl
@[simp] theorem Qm_v13 : Qm 13 = 13 := rfl
@[simp] theorem Qm_v14 : Qm 14 = 14 := rfl
@[simp] theorem Qm_v15 : Qm 15 = 15 := rfl
@[simp] theorem Qm_v16 : Qm 16 = 16 := rfl
@[simp] theorem Qm_v17 : Qm 17 = 17 := rfl
@[simp] theorem Qm_v18 : Qm 18 = 18 := rfl
@[simp] theorem Qm_v19 : Qm 19 = 19 := rfl
@[simp] theorem Qm_v20 : Qm 20 = 20 := rfl
@[simp] theorem Qm_v21 : Qm 21 = 21 := rfl
@[simp] theorem Qm_v22 : Qm 22 = 22 := rfl
@[simp] theorem Qm_v23 : Qm 23 = 23 := rfl
@[simp] theorem Qm_v24 : Qm 24 = 24 := rfl
@[simp] theorem Qm_v25 : Qm 25 = 25 := rfl
@[simp] theorem Qm_v26 : Qm 26 = 26 := rfl
@[simp] theorem Qm_v27 : Qm 27 = 27 := rfl
@[simp] theorem Qm_v28 : Qm 28 = 28 := rfl
@[simp] theorem Qm_v29 : Qm 29 = 29 := rfl
@[simp] theorem Qm_v30 : Qm 30 = 30 := rfl
@[simp] theorem Qm_v31 : Qm 31 = 31 := rfl
@[simp] theorem Qm_v32 : Qm 32 = 32 := rfl
@[simp] theorem Qm_v33 : Qm 33 = 33 := rfl
@[simp] theorem Qm_v34 : Qm 34 = 34 := rfl
@[simp] theorem Qm_v35 : Qm 35 = 35 := rfl
@[simp] theorem Qm_v36 : Qm 36 = 36 := rfl
@[simp] theorem Qm_v37 : Qm 37 = 37 := rfl
@[simp] theorem Qm_v38 : Qm 38 = 38 := rfl
@[simp] theorem Qm_v39 : Qm 39 = 39 := rfl
@[simp] theorem Qm_v40 : Qm 40 = 40 := rfl
@[simp] theorem Qm_v41 : Qm 41 = 41 := rfl
@[simp] theorem Qm_v42 : Qm 42 = 42 := rfl
@[simp] theorem Qm_v43 : Qm 43 = 43 := rfl
@[simp] theorem Qm_v44 : Qm 44 = 44 := rfl
@[simp] theorem Qm_v45 : Qm 45 = 45 := rfl
@[simp] theorem Qm_v46 : Qm 46 = 46 := rfl
@[simp] theorem Qm_v47 : Qm 47 = 47 := rfl
@[simp] theorem Qm_v48 : Qm 48 = 48 := rfl
@[simp] theorem Qm_v49 : Qm 49 = 49 := rfl
@[simp] theorem Qm_v50 : Qm 50 = 50 := rfl
@[simp] theorem Qm_v51 : Qm 51 = 51 := rfl
@[simp] theorem Qm_v52 : Qm 52 = 52 := rfl
@[simp] theorem Qm_v53 : Qm 53 = 53 := rfl
@[simp] theorem Qm_v54 : Qm 54 = 54 := rfl
@[simp] theorem Qm_v55 : Qm 55 = 55 := rfl
@[simp] theorem Qm_v56 : Qm 56 = 56 := rfl
@[simp] theorem Qm_v57 : Qm 57 = 57 := rfl
@[simp] theorem Qm_v58 : Qm 58 = 58 := rfl
@[simp] theorem Qm_v59 : Qm 59 = 59 := rfl
@[simp] theorem Qm_v60 : Qm 60 = 60 := rfl
@[simp] theorem Qm_v61 : Qm 61 = 61 := rfl
@[simp] theorem Qm_v62 : Qm 62 = 62 := rfl
@[simp] theorem Qm_v63 : Qm 63 = 63 := rfl

theorem stC_st (R : SelectionReq) (h : ParamsOk R) (i : Fin 50) :
    (stC R h).st i = if i = Sm 31 then popTable (Wof R) R else if i = Sm 30 then gateTable (Wof R) R
      else if i = Sm 32 then frame (binary (Wof R) R.gates.length) else (stB R h).st i := by
  simp only [stC, WState.setv_st, WState.sets_st, WState.seth_st, Function.update_apply]

theorem stC_sh (R : SelectionReq) (h : ParamsOk R) (i : Fin 50) :
    (stC R h).sh i = if i = 0 then 2 * (selWord R).length else 0 := by
  simp only [stC, WState.setv_sh, WState.sets_sh, WState.seth_sh, Function.update_apply, stB_sh]
  rw [stA_sh]
  by_cases hi : i = 0 <;> simp [hi]

theorem stC_val_eq (R : SelectionReq) (h : ParamsOk R) (r : Fin 112) :
    (stC R h).val r = if r = 84 then 2 ^ (R.r * R.s) else if r = 58 then (popTable (Wof R) R).length
      else if r = 59 then R.pops.length else if r = 88 then R.gates.length else (stA R h).val r := by
  simp only [stC, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply, stB_val]

theorem stC_val (R : SelectionReq) (h : ParamsOk R) : (stC R h).val = pvP R h := by
  funext r
  rw [stC_val_eq, stA_val]
  unfold pvP
  by_cases h0 : r = 0
  · subst h0; simp [hh, starParamsOf]
  by_cases h1 : r = 1
  · subst h1; simp
  by_cases h2 : r = 2
  · subst h2; simp
  by_cases h3 : r = 3
  · subst h3; simp [fL, starParamsOf]
  by_cases h4 : r = 4
  · subst h4; simp [fR, starParamsOf]
  by_cases h5 : r = 5
  · subst h5; simp
  by_cases h58 : r = 58
  · subst h58; simp
  by_cases h59 : r = 59
  · subst h59; simp
  by_cases h60 : r = 60
  · subst h60; simp
  by_cases h64 : r = 64
  · subst h64; simp
  by_cases h67 : r = 67
  · subst h67; simp
  by_cases h68 : r = 68
  · subst h68; simp
  by_cases h69 : r = 69
  · subst h69; simp
  by_cases h70 : r = 70
  · subst h70; simp
  by_cases h71 : r = 71
  · subst h71; simp
  by_cases h72 : r = 72
  · subst h72; simp
  by_cases h73 : r = 73
  · subst h73; simp
  by_cases h84 : r = 84
  · subst h84; simp
  by_cases h85 : r = 85
  · subst h85; simp
  by_cases h86 : r = 86
  · subst h86; simp
  by_cases h87 : r = 87
  · subst h87; simp
  by_cases h88 : r = 88
  · subst h88; simp
  by_cases h95 : r = 95
  · subst h95; simp
  simp [h0, h1, h2, h3, h4, h5, h58, h59, h60, h64, h67, h68, h69, h70, h71, h72, h73, h84, h85, h86, h87, h88, h95]

/-- A stream the parse leaves empty. -/
theorem stC_free (R : SelectionReq) (h : ParamsOk R) (k : Fin 50) (hk : 4 ≤ k.val ∧ k.val < 30) :
    (stC R h).st (Sm k) = [] := by
  have hv : (Sm k).val = k.val + 2 := by simp [Sm]; omega
  have ne : ∀ m : Fin 50, (m.val < 6 ∨ 32 ≤ m.val) → Sm k ≠ m := fun m hm e => by
    have := congrArg Fin.val e; omega
  have ne' : ∀ m : Fin 50, (m.val < 6 ∨ 32 ≤ m.val) → ¬ Sm k = m := ne
  rw [stC_st, if_neg (ne' (Sm 31) (by decide)), if_neg (ne' (Sm 30) (by decide)), if_neg (ne' (Sm 32) (by decide)),
    stB_st, if_neg (by rintro (e | e) <;> [exact ne' (Sm 43) (by decide) e; exact ne' (Sm 0) (by decide) e]),
    if_neg (ne' (Sm 32) (by decide)), if_neg (ne' (Sm 2) (by decide)), if_neg (ne' (Sm 41) (by decide))]
  have hz : Sm k ∉ zs13 := by
    intro hm
    simp only [zs13, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e | e | e | e | e | e | e | e | e | e | e <;> exact ne' _ (by decide) e
  rw [if_neg hz, if_neg (ne' (Sm 45) (by decide)), stA_st, if_neg (ne' 0 (by decide))]

theorem stC_sm (R : SelectionReq) (h : ParamsOk R) (k : Fin 50) (hk : k.val < 48) : (stC R h).sh (Sm k) = 0 := by
  rw [stC_sh, if_neg]
  intro e; have := congrArg Fin.val e; simp [Sm] at this; omega

/-- **The coset loop's entry state.** -/
theorem pPost_stC (R : SelectionReq) (h : ParamsOk R) (hLB : 2 * Lof R ≤ Bof R) : PPost R h (stC R h) := by
  have hv := stC_val R h
  have v : ∀ r, (stC R h).val r = pvP R h r := fun r => by rw [hv]
  have sh0 : ∀ k : Fin 50, k.val < 48 → (stC R h).sh (Sm k) = 0 := stC_sm R h
  have nw : ∀ k : Fin 50, k.val < 48 → ∀ W' x, (stC R h).st (Sm k) = frame (binary W' x) → NumOn (stC R h) (Sm k) W' x :=
    fun k hk W' x e => ⟨e, sh0 k hk⟩
  have st : ∀ i, (stC R h).st i = _ := stC_st R h
  refine ⟨⟨⟨?_, sh0 30 (by decide), ?_, nw 32 (by decide) _ _ ?_, nw 2 (by decide) _ _ ?_, nw 0 (by decide) _ _ ?_,
    ?_, sh0 1 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, sh0 31 (by decide), ?_,
    ⟨0, nw 35 (by decide) _ _ ?_⟩, ⟨0, nw 36 (by decide) _ _ ?_⟩, nw 41 (by decide) _ _ ?_, nw 42 (by decide) _ _ ?_,
    nw 43 (by decide) _ _ ?_, ?_, ?_, ?_, ?_⟩, hv, ?_, ?_, ?_, ?_⟩
  · rw [stC_st]; simp
  · rw [stC_st]; simp
  · rw [stC_st]; simp
  · rw [stC_st, stB_st]; simp
  · rw [stC_st, stB_st]; simp
  · rw [stC_st, stB_st]; simp [zs13, stA_st]
  · intro j hj
    have e := stC_free R h ⟨j.val, by omega⟩ ⟨hj, show j.val < 30 by omega⟩
    refine ⟨Or.inl e, sh0 ⟨j.val, by omega⟩ (show j.val < 48 by omega)⟩
  · rw [v]; simp [pvP, hh, starParamsOf]
  · rw [v]; simp [pvP]
  · rw [v]; simp [pvP]; rfl
  · rw [v]; simp [pvP, fL, starParamsOf]
  · rw [v]; simp [pvP, fR, starParamsOf]
  · rw [v]; simp [pvP]
  · intro j hj
    rw [v]
    have hjv : (gR Qm j).val = j.val := rfl
    unfold pvP
    have ne : ∀ m : Fin 112, (m.val < 6 ∨ 48 ≤ m.val) → gR Qm j ≠ m := fun m hm e => by
      have := congrArg Fin.val e; omega
    simp [ne 0 (by decide), ne 1 (by decide), ne 2 (by decide), ne 3 (by decide), ne 4 (by decide), ne 5 (by decide),
      ne 58 (by decide), ne 59 (by decide), ne 60 (by decide), ne 64 (by decide), ne 67 (by decide), ne 68 (by decide),
      ne 69 (by decide), ne 70 (by decide), ne 71 (by decide), ne 72 (by decide), ne 73 (by decide), ne 84 (by decide),
      ne 85 (by decide), ne 86 (by decide), ne 87 (by decide), ne 88 (by decide), ne 95 (by decide)]
  · rw [v]; simp [pvP, Qm]
  · rw [v]; simp [pvP, Qm]
  · rw [v]; simp [pvP, Qm]
  · intro j hj
    rw [v]
    rcases hj with e | e | e | e | e | e | e | e | e <;> (subst e; simp [pvP, Qm])
  · intro k hk
    refine ⟨0, nw k (by rcases hk with e | e | e | e | e | e | e | e | e <;> (subst e; decide)) _ _ ?_⟩
    rw [stC_st, stB_st]
    rcases hk with e | e | e | e | e | e | e | e | e <;> (subst e; simp [zs13])
  · rw [stC_st, stB_st]; simp [zs13]
  · rw [stC_st, stB_st]; simp [zs13]
  · rw [stC_st, stB_st]; simp [bestKey]
  · rw [stC_st, stB_st]; simp [zs13, bestKey]
  · rw [stC_st, stB_st]; simp [argminIdx]
  · rw [v]; simp [pvP, Qm]
  · rw [v]; simp [pvP, Qm]
  · rw [v]; simp [pvP, Qm]
  · rw [v]; simp [pvP]
  · rw [stC_st, stB_st]; simp [zs13, stA_st]
  · rw [stC_sh]; simp
  · rw [stC_sh]; simp; unfold Lof at hLB; omega
  · intro k hk
    rcases hk with e | e | e | e <;> (subst e; exact sh0 _ (by decide))

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
