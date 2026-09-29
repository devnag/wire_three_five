import Proof.Wire_3_5.Primitive.SeedFix.C4SL

/-! # C4 per-call setup (item 3), part 13: the SYM setup's modulus words, big unary words and compiler fields

P3:2929-2941 ("`ℓ ≥ max(k, ⌈log₂(Q+1)⌉)` … the defining irreducible polynomial … can be found and implemented in
`2^{O(ℓ)}` elementary preprocessing time"), P3:1886-1906 (the compiler request's fields `PRE`, `POST`), P3:3034-3037
(the printer child's mask `1^{2^{2·dRow}}` and the loop's pads): from the words `gW`, PA's modulus machine twice (the
enumeration's constant and the finisher's modulus word), base `CapReader` twice (`1^{2^{d₂}}` and the driver
`1^{2^ρ}`), and the C3 request writer (C3ReqIface) from the request and its four numbers.

* `extC3`, `modsM`, `c3M`, `tailM`, **`mods_run`**, **`c3_run`**, **`tail_run`**.

Paper quantities of the main type: the modulus word `frame (binary ℓ (firstPrimitive ℓ))`, the compiler fields
`frame pre`, `frame post`, the unary words `1^{2^{d₂}}`, `1^{2^ρ}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem s31 : (symO 31).val = 152 := by decide
theorem s32 : (symO 32).val = 153 := by decide
theorem s33 : (symO 33).val = 154 := by decide
theorem s34 : (symO 34).val = 155 := by decide
theorem s35 : (symO 35).val = 156 := by decide
theorem s36 : (symO 36).val = 157 := by decide
theorem s37 : (symO 37).val = 158 := by decide
theorem s38 : (symO 38).val = 159 := by decide

namespace Lay
variable (L : Lay)

/-- The C3 request writer's inputs: the request and its four numbers `1^h`, `1^{Q'}`, `1^m`, `1^{pr}`. -/
def extC3 (j : Fin L.S3.t) : Option (Fin L.N) :=
  if j = L.S3.inS then some L.gP0 else if j = L.S3.hS then some (L.gW 33) else if j = L.S3.qS then some (L.gW 34)
  else if j = L.S3.mS then some (L.gW 35) else if j = L.S3.pS then some (L.gW 36) else none

/-- The two modulus words and the two big unary words. -/
noncomputable def modsM :=
  Composition.machine (RecoveryFocus.machine (slx L.oM1 (by unfold oM1; rw [N_eq]; omega) (ext0 (L.gW 31))) Modulus.modM)
  (Composition.machine (RecoveryFocus.machine (slx L.oM2 (by unfold oM2; rw [N_eq]; omega) (ext0 (L.gW 32))) Modulus.modM)
  (Composition.machine (RecoveryFocus.machine (slx L.oCU (by unfold oCU; rw [N_eq]; omega) (ext0 (L.gW 37))) crM)
    (RecoveryFocus.machine (slx L.oCR2 (by unfold oCR2; rw [N_eq]; omega) (ext0 (L.gW 38))) crM)))

/-- The C3 request writer, docked. -/
noncomputable def c3M := RecoveryFocus.machine (slx L.oC3 (by unfold oC3; rw [N_eq]; omega) L.extC3) L.S3.M

/-- **The tail**: the two modulus words, the two big unary words, the compiler fields. -/
noncomputable def tailM := Composition.machine L.modsM L.c3M

/-- The modulus and big-word part's step bound. -/
def modsCost (ell d2 ρ : ℕ) : ℕ :=
  Modulus.modCost ell + 1 + (Modulus.modCost ell + 1 + (srcCost d2 + 1 + srcCost ρ))

/-- The tail's step bound. -/
def tailCost (ell d2 ρ B3 : ℕ) : ℕ := modsCost ell d2 ρ + 1 + B3

/-- **The modulus words and the big unary words**: from the words `wd` on `gW` (`1^ℓ` twice, `srcWord d₂`,
`srcWord ρ`) and a bank blank from the modulus region up: the modulus word twice, `1^{2^{d₂}}`, `1^{2^ρ}`; the words
and the request kept, the other ports unchanged, the bank blank from the writer's region up. -/
theorem mods_run (w : List Bool) (wd : Fin 39 → List Bool) (ell d2 ρ : ℕ) (hell : 1 ≤ ell)
    (h31 : wd 31 = List.replicate ell true) (h32 : wd 32 = List.replicate ell true)
    (h37 : wd 37 = NumsX.srcWord d2) (h38 : wd 38 = NumsX.srcWord ρ)
    (B : Fin L.N → List Bool) (hP0 : B L.gP0 = frame w) (hW : ∀ j, B (L.gW j) = wd j)
    (hbl : ∀ i : Fin L.N, L.oM1 ≤ i.val → B i = []) :
    ∃ B' : Fin L.N → List Bool, Step L.modsM (modsCost ell d2 ρ) (fun _ => 0) B (fun _ => 0) B' ∧
      B' L.gP0 = frame w ∧ (∀ j, B' (L.gW j) = wd j) ∧
      B' L.gMA = frame (binary ell (GF.firstPrimitive ell)) ∧ B' L.gMB = frame (binary ell (GF.firstPrimitive ell)) ∧
      B' L.gUU = List.replicate (2 ^ d2) true ∧ B' L.gRR = List.replicate (2 ^ ρ) true ∧
      (∀ i : Fin L.N, i.val < 3 → i ≠ L.gP0 → B' i = B i) ∧ (∀ i : Fin L.N, L.oC3 ≤ i.val → B' i = []) := by
  have e31 := s31
  have e32 := s32
  have e33 := s33
  have e34 := s34
  have e35 := s35
  have e36 := s36
  have e37 := s37
  have e38 := s38
  have wlt : ∀ j, (L.gW j).val < L.oM1 := fun j => by have := Lay.symO_le j; lv
  have wge : ∀ j, 3 ≤ (L.gW j).val := fun j => by lv
  -- 9: the enumeration's modulus word
  obtain ⟨t9, h9, e90, e912⟩ := Modulus.modulus_step ell hell
  obtain ⟨B9, s9, bl9, un9, pv9, ex9⟩ := stage0 h9 (by norm_num) L.oM1 (by unfold oM1; rw [N_eq]; omega) (L.gW 31)
    (wlt 31) B ((hW 31).trans h31) hbl
  have f9W : ∀ j, B9 (L.gW j) = wd j := by
    intro j
    by_cases hj : j = 31
    · subst hj; exact (ex9.trans e90).trans h31.symm
    · exact (un9 _ (wlt j) (fun e => hj (L.gW_inj e))).trans (hW j)
  have f9P0 : B9 L.gP0 = frame w := (un9 _ (by lv) (by lv)).trans hP0
  have f9A : B9 L.gMA = frame (binary ell (GF.firstPrimitive ell)) :=
    (pv9 ⟨12, by norm_num⟩ L.gMA (by norm_num) (by lv)).trans e912
  -- 10: the finisher's modulus word
  obtain ⟨t10, h10, e100, e1012⟩ := Modulus.modulus_step ell hell
  obtain ⟨B10, s10, bl10, un10, pv10, ex10⟩ := stage0 h10 (by norm_num) L.oM2 (by unfold oM2; rw [N_eq]; omega)
    (L.gW 32) (by have := wlt 32; unfold oM2; unfold oM1 at this; omega) B9 ((f9W 32).trans h32)
    (fun i hi => bl9 i (by unfold oM2 at hi; unfold oM1; omega))
  have f10W : ∀ j, B10 (L.gW j) = wd j := by
    intro j
    by_cases hj : j = 32
    · subst hj; exact (ex10.trans e100).trans h32.symm
    · exact (un10 _ (by have := wlt j; unfold oM2; unfold oM1 at this; omega) (fun e => hj (L.gW_inj e))).trans (f9W j)
  have f10P0 : B10 L.gP0 = frame w := (un10 _ (by lv) (by lv)).trans f9P0
  have f10A : B10 L.gMA = frame (binary ell (GF.firstPrimitive ell)) := (un10 _ (by lv) (by lv)).trans f9A
  have f10B : B10 L.gMB = frame (binary ell (GF.firstPrimitive ell)) :=
    (pv10 ⟨12, by norm_num⟩ L.gMB (by norm_num) (by lv)).trans e1012
  -- 11: `1^{2^{d₂}}`
  obtain ⟨t11, h11, e110, e118, -⟩ := srcS d2
  obtain ⟨B11, s11, bl11, un11, pv11, ex11⟩ := stage0 h11 (by norm_num) L.oCU (by unfold oCU; rw [N_eq]; omega)
    (L.gW 37) (by have := wlt 37; unfold oCU; unfold oM1 at this; omega) B10 ((f10W 37).trans h37)
    (fun i hi => bl10 i (by unfold oCU at hi; unfold oM2; omega))
  have f11W : ∀ j, B11 (L.gW j) = wd j := by
    intro j
    by_cases hj : j = 37
    · subst hj; exact (ex11.trans e110).trans h37.symm
    · exact (un11 _ (by have := wlt j; unfold oCU; unfold oM1 at this; omega) (fun e => hj (L.gW_inj e))).trans (f10W j)
  have f11P0 : B11 L.gP0 = frame w := (un11 _ (by lv) (by lv)).trans f10P0
  have f11A : B11 L.gMA = frame (binary ell (GF.firstPrimitive ell)) := (un11 _ (by lv) (by lv)).trans f10A
  have f11B : B11 L.gMB = frame (binary ell (GF.firstPrimitive ell)) := (un11 _ (by lv) (by lv)).trans f10B
  have f11U : B11 L.gUU = List.replicate (2 ^ d2) true := (pv11 ⟨8, by norm_num⟩ L.gUU (by norm_num) (by lv)).trans e118
  -- 12: the driver `1^{2^ρ}`
  obtain ⟨t12, h12, e120, e128, -⟩ := srcS ρ
  obtain ⟨B12, s12, bl12, un12, pv12, ex12⟩ := stage0 h12 (by norm_num) L.oCR2 (by unfold oCR2; rw [N_eq]; omega)
    (L.gW 38) (by have := wlt 38; unfold oCR2; unfold oM1 at this; omega) B11 ((f11W 38).trans h38)
    (fun i hi => bl11 i (by unfold oCR2 at hi; unfold oCU; omega))
  have f12W : ∀ j, B12 (L.gW j) = wd j := by
    intro j
    by_cases hj : j = 38
    · subst hj; exact (ex12.trans e120).trans h38.symm
    · exact (un12 _ (by have := wlt j; unfold oCR2; unfold oM1 at this; omega) (fun e => hj (L.gW_inj e))).trans (f11W j)
  have f12P0 : B12 L.gP0 = frame w := (un12 _ (by lv) (by lv)).trans f11P0
  have f12A : B12 L.gMA = frame (binary ell (GF.firstPrimitive ell)) := (un12 _ (by lv) (by lv)).trans f11A
  have f12B : B12 L.gMB = frame (binary ell (GF.firstPrimitive ell)) := (un12 _ (by lv) (by lv)).trans f11B
  have f12U : B12 L.gUU = List.replicate (2 ^ d2) true := (un12 _ (by lv) (by lv)).trans f11U
  have f12R : B12 L.gRR = List.replicate (2 ^ ρ) true := (pv12 ⟨8, by norm_num⟩ L.gRR (by norm_num) (by lv)).trans e128
  refine ⟨B12, s9.seq (s10.seq (s11.seq s12)), f12P0, f12W, f12A, f12B, f12U, f12R, ?_, ?_⟩
  · intro i hi hne
    have nw : ∀ k, i ≠ L.gW k := fun k e => by have := wge k; rw [← e] at this; omega
    rw [un12 i (by unfold oCR2; omega) (nw _), un11 i (by unfold oCU; omega) (nw _), un10 i (by unfold oM2; omega) (nw _),
      un9 i (by unfold oM1; omega) (nw _)]
  · intro i hi
    exact bl12 i (by unfold oC3 at hi; unfold oCR2; omega)

theorem extC3_ne (g : Fin L.N) (a : g ≠ L.gP0) (b : g ≠ L.gW 33) (c : g ≠ L.gW 34) (d : g ≠ L.gW 35)
    (e : g ≠ L.gW 36) : ∀ k, L.extC3 k ≠ some g := by
  intro k hk
  unfold extC3 at hk
  split_ifs at hk <;> simp at hk <;> simp_all

theorem extC3_inj : ∀ i j g, L.extC3 i = some g → L.extC3 j = some g → i = j := by
  have e33 := s33
  have e34 := s34
  have e35 := s35
  have e36 := s36
  intro i j g hi hj
  unfold extC3 at hi hj
  split_ifs at hi hj <;> simp at hi hj <;> subst_vars <;>
    first
    | rfl
    | (exfalso; revert hj; lv)

theorem extC3_lt : ∀ i g, L.extC3 i = some g → g.val < L.oC3 := by
  have e33 := s33
  have e34 := s34
  have e35 := s35
  have e36 := s36
  intro i g hi
  unfold extC3 at hi
  split_ifs at hi <;> simp at hi <;> subst hi <;> lv

/-- **The compiler fields**: the C3 request writer from the request and the words `1^h`, `1^{Q'}`, `1^m`, `1^{pr}`
on `gW`, the bank blank from its region up: `frame pre`, `frame post` on `gPRE`, `gPOST`; every word and the request
kept, every other tape below the region unchanged. -/
theorem c3_run (w : List Bool) (wd : Fin 39 → List Bool) (h Q' mm pr : ℕ)
    (h33 : wd 33 = List.replicate h true) (h34 : wd 34 = List.replicate Q' true)
    (h35 : wd 35 = List.replicate mm true) (h36 : wd 36 = List.replicate pr true) (B3 : ℕ) (pre post : List Bool)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS w h Q' mm pr
      pre post)
    (B12 : Fin L.N → List Bool) (f12P0 : B12 L.gP0 = frame w) (f12W : ∀ j, B12 (L.gW j) = wd j)
    (bl12 : ∀ i : Fin L.N, L.oC3 ≤ i.val → B12 i = []) :
    ∃ B' : Fin L.N → List Bool, Step L.c3M B3 (fun _ => 0) B12 (fun _ => 0) B' ∧
      B' L.gP0 = frame w ∧ (∀ j, B' (L.gW j) = wd j) ∧ B' L.gPRE = frame pre ∧ B' L.gPOST = frame post ∧
      (∀ i : Fin L.N, i.val < L.oC3 → i ≠ L.gP0 → (∀ j, i ≠ L.gW j) → B' i = B12 i) ∧
      (∀ i : Fin L.N, L.oC3 + L.S3.t ≤ i.val → B' i = []) := by
  have e33 := s33
  have e34 := s34
  have e35 := s35
  have e36 := s36
  have wlt : ∀ j, (L.gW j).val < L.oM1 := fun j => by have := Lay.symO_le j; lv
  have wge : ∀ j, 3 ≤ (L.gW j).val := fun j => by lv
  -- 13: the compiler fields
  obtain ⟨J, hJ, hrr⟩ := hc3
  have h13 := cjStep hrr
  have hd := L.S3.distinct
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨d01, d02, d03, d04, d05, d06⟩, ⟨d12, d13, d14, d15, d16⟩, ⟨d23, d24, d25, d26⟩, ⟨d34, d35, d36⟩,
    ⟨d45, d46⟩, d56⟩ := hd
  have hnone : ∀ j, j ≠ L.S3.inS → j ≠ L.S3.hS → j ≠ L.S3.qS → j ≠ L.S3.mS → j ≠ L.S3.pS → L.extC3 j = none := by
    intro j a b c d e
    simp [extC3, a, b, c, d, e]
  obtain ⟨B13, s13, bl13, un13, pv13, ex13⟩ := stageE h13 L.oC3 (by unfold oC3; rw [N_eq]; omega) L.extC3
    L.extC3_inj L.extC3_lt B12
    (fun j g hj => by
      unfold extC3 at hj
      split_ifs at hj with a0 a1 a2 a3 a4 <;> simp at hj <;> subst hj <;> subst_vars
      · rw [f12P0]; simp [C3ReqIface.c3In]
      · rw [f12W, h33]; simp [C3ReqIface.c3In, Ne.symm d01]
      · rw [f12W, h34]; simp [C3ReqIface.c3In, Ne.symm d02, Ne.symm d12]
      · rw [f12W, h35]; simp [C3ReqIface.c3In, Ne.symm d03, Ne.symm d13, Ne.symm d23]
      · rw [f12W, h36]; simp [C3ReqIface.c3In, Ne.symm d04, Ne.symm d14, Ne.symm d24, Ne.symm d34])
    bl12
    (fun j hj => by
      unfold extC3 at hj
      split_ifs at hj with a0 a1 a2 a3 a4 <;> simp at hj
      simp [C3ReqIface.c3In, a0, a1, a2, a3, a4])
  have c3ne := L.extC3_ne
  have oc3 : ∀ j, j = L.S3.inS ∨ j = L.S3.hS ∨ j = L.S3.qS ∨ j = L.S3.mS ∨ j = L.S3.pS →
      C3ReqIface.c3Out L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS w h Q' mm pr pre post J j =
        C3ReqIface.c3In L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS w h Q' mm pr j := by
    intro j hj
    have n5 : j ≠ L.S3.preS := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> assumption
    have n6 : j ≠ L.S3.postS := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> assumption
    simp [C3ReqIface.c3Out, n5, n6, hj]
  have wP0 : ∀ j, L.gW j ≠ L.gP0 := fun j e => by have := wge j; rw [e] at this; revert this; lv
  have wne : ∀ j k, j ≠ k → L.gW j ≠ L.gW k := fun j k h e => h (L.gW_inj e)
  refine ⟨B13, s13, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ex13 L.S3.inS L.gP0 (by simp [extC3]), oc3 _ (Or.inl rfl)]
    simp [C3ReqIface.c3In]
  · intro j
    by_cases j33 : j = 33
    · subst j33
      rw [ex13 L.S3.hS (L.gW 33) (by simp [extC3, Ne.symm d01]), oc3 _ (Or.inr (Or.inl rfl)), h33]
      simp [C3ReqIface.c3In, Ne.symm d01]
    by_cases j34 : j = 34
    · subst j34
      rw [ex13 L.S3.qS (L.gW 34) (by simp [extC3, Ne.symm d02, Ne.symm d12]), oc3 _ (Or.inr (Or.inr (Or.inl rfl))), h34]
      simp [C3ReqIface.c3In, Ne.symm d02, Ne.symm d12]
    by_cases j35 : j = 35
    · subst j35
      rw [ex13 L.S3.mS (L.gW 35) (by simp [extC3, Ne.symm d03, Ne.symm d13, Ne.symm d23]),
        oc3 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h35]
      simp [C3ReqIface.c3In, Ne.symm d03, Ne.symm d13, Ne.symm d23]
    by_cases j36 : j = 36
    · subst j36
      rw [ex13 L.S3.pS (L.gW 36) (by simp [extC3, Ne.symm d04, Ne.symm d14, Ne.symm d24, Ne.symm d34]),
        oc3 _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), h36]
      simp [C3ReqIface.c3In, Ne.symm d04, Ne.symm d14, Ne.symm d24, Ne.symm d34]
    exact (un13 _ (by have := wlt j; unfold oC3; unfold oM1 at this; omega)
      (c3ne _ (wP0 j) (wne _ _ j33) (wne _ _ j34) (wne _ _ j35) (wne _ _ j36))).trans (f12W j)
  · rw [pv13 L.S3.preS L.gPRE (hnone _ (Ne.symm d05) (Ne.symm d15) (Ne.symm d25) (Ne.symm d35) (Ne.symm d45)) (by lv)]
    simp [C3ReqIface.c3Out]
  · rw [pv13 L.S3.postS L.gPOST (hnone _ (Ne.symm d06) (Ne.symm d16) (Ne.symm d26) (Ne.symm d36) (Ne.symm d46)) (by lv)]
    simp [C3ReqIface.c3Out, Ne.symm d56.1]
  · intro i hi hne hw
    exact un13 i hi (c3ne _ hne (hw _) (hw _) (hw _) (hw _))
  · intro i hi
    exact bl13 i hi

/-- **The tail's run**: from the words `wd` on `gW` (`1^ℓ` twice, `1^h`, `1^{Q'}`, `1^m`, `1^{pr}`, `srcWord d₂`,
`srcWord ρ`), the request on port `0` and a bank blank from the modulus region up: the modulus word twice,
`1^{2^{d₂}}`, `1^{2^ρ}`, the compiler fields `frame pre`, `frame post`; the words and the request kept, the other
ports unchanged, the bank blank above the writer's region. -/
theorem tail_run (w : List Bool) (wd : Fin 39 → List Bool) (ell h Q' mm pr d2 ρ : ℕ) (hell : 1 ≤ ell)
    (h31 : wd 31 = List.replicate ell true) (h32 : wd 32 = List.replicate ell true)
    (h33 : wd 33 = List.replicate h true) (h34 : wd 34 = List.replicate Q' true)
    (h35 : wd 35 = List.replicate mm true) (h36 : wd 36 = List.replicate pr true)
    (h37 : wd 37 = NumsX.srcWord d2) (h38 : wd 38 = NumsX.srcWord ρ) (B3 : ℕ) (pre post : List Bool)
    (hc3 : C3ReqIface.C3Run L.S3.M B3 L.S3.inS L.S3.hS L.S3.qS L.S3.mS L.S3.pS L.S3.preS L.S3.postS w h Q' mm pr
      pre post)
    (B : Fin L.N → List Bool) (hP0 : B L.gP0 = frame w) (hW : ∀ j, B (L.gW j) = wd j)
    (hbl : ∀ i : Fin L.N, L.oM1 ≤ i.val → B i = []) :
    ∃ B' : Fin L.N → List Bool, Step L.tailM (tailCost ell d2 ρ B3) (fun _ => 0) B (fun _ => 0) B' ∧
      B' L.gP0 = frame w ∧ (∀ j, B' (L.gW j) = wd j) ∧
      B' L.gMA = frame (binary ell (GF.firstPrimitive ell)) ∧ B' L.gMB = frame (binary ell (GF.firstPrimitive ell)) ∧
      B' L.gUU = List.replicate (2 ^ d2) true ∧ B' L.gRR = List.replicate (2 ^ ρ) true ∧
      B' L.gPRE = frame pre ∧ B' L.gPOST = frame post ∧
      (∀ i : Fin L.N, i.val < 3 → i ≠ L.gP0 → B' i = B i) ∧ (∀ i : Fin L.N, L.oC3 + L.S3.t ≤ i.val → B' i = []) := by
  obtain ⟨B12, s12, f12P0, f12W, f12A, f12B, f12U, f12R, un12, bl12⟩ :=
    L.mods_run w wd ell d2 ρ hell h31 h32 h37 h38 B hP0 hW hbl
  obtain ⟨B13, s13, f13P0, f13W, f13PRE, f13POST, un13, bl13⟩ :=
    L.c3_run w wd h Q' mm pr h33 h34 h35 h36 B3 pre post hc3 B12 f12P0 f12W bl12
  have wge : ∀ j, 3 ≤ (L.gW j).val := fun j => by lv
  refine ⟨B13, s12.seq s13, f13P0, f13W, ?_, ?_, ?_, ?_, f13PRE, f13POST, ?_, bl13⟩
  · exact (un13 _ (by lv) (by lv) (fun j e => by have := Lay.symO_le j; revert e; lv)).trans f12A
  · exact (un13 _ (by lv) (by lv) (fun j e => by have := Lay.symO_le j; revert e; lv)).trans f12B
  · exact (un13 _ (by lv) (by lv) (fun j e => by have := Lay.symO_le j; revert e; lv)).trans f12U
  · exact (un13 _ (by lv) (by lv) (fun j e => by have := Lay.symO_le j; revert e; lv)).trans f12R
  · intro i hi hne
    rw [un13 i (by unfold oC3; omega) hne (fun k e => by have := wge k; rw [← e] at this; omega), un12 i hi hne]

end Lay

end NearCubicWires.WireExponent3_5.PrimT.C4Set
