import Proof.Wire_3_5.FinalPass.SdI3Base

/-! # S4 (the seeds phase), part 53: the register capacity's side conditions from the sizes (P3:3170-3178)

From the sizes below `X` (`AtomsX`), the counters' width `T ≤ X`, the per-point values `Vm ≤ X`, and the sample
list's length `|ps| ≤ Fn` with `n ≤ Fn`, every capacity condition of S4's run (`run_symG`, `run_thrG`) holds at any
capacity `cap ≥ capNeed X Fn = 10⁴·X³ + 100 + Fn·(4Fn² + 2)`: **`qnum_of`** (the seed loop's `QNum`), **`prep_caps`**
(the prep's capacity and the small numbers' registers), **`hHT_of`** (the tables' registers).

Paper quantity of the main type: the seeds phase's space, polynomial in the input (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.FinalPass.Corner
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL)
open NearCubicWires.SupplierWalk (majorityThreshold)

/-- **The capacity the seeds phase needs** at the sizes' bound `X` and the input length `Fn`. -/
def capNeed (X Fn : ℕ) : ℕ := 10000 * (X * X * X) + 100 + Fn * (4 * (Fn * Fn) + 2)

theorem ul_le (X : ℕ) : ∀ (L : List ℕ), (∀ x ∈ L, x ≤ X) → (PrimAsm.Data.unaryList L).length ≤ L.length * (X + 1)
  | [], _ => by simp [PrimAsm.Data.unaryList]
  | x :: L, h => by
    have ih := ul_le X L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (List.mem_cons_self)
    rw [ThrPt.unaryList_length] at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.succ_mul]
    omega

theorem getD_le (X : ℕ) : ∀ (L : List ℕ), (∀ x ∈ L, x ≤ X) → ∀ j, L.getD j 0 ≤ X
  | [], _, j => by simp
  | x :: L, h, 0 => by simpa using h x (List.mem_cons_self)
  | x :: L, h, j + 1 => by
    simpa using getD_le X L (fun y hy => h y (List.mem_cons_of_mem _ hy)) j

theorem esOf_length (FP : GapParams) : (esOf FP).length = Fintype.card (GapSeed FP) := by simp [esOf]

section Caps
variable (P : StarParams) (carriers : List (Carrier P.n)) (FP : GapParams) (X : ℕ)

/-- S4's small numbers are at most `X`. -/
theorem vs_le (H : AtomsX P carriers FP X) : ∀ x ∈ Seams.s4Small2 P carriers FP, x ≤ X := by
  obtain ⟨hb, hs, hr, h2s, hhL, hdRow, hdR, h1, h2, _⟩ := star_le P
  have hsw := sw_lt FP
  have hG := H.G
  have hn := H.n2
  have c0 := H.cl 0
  have c1 := H.cl 1
  have hc2 := H.car2
  have hl := H.len
  have hc := H.cap
  have he := H.err
  intro x hx
  simp only [Seams.s4Small2, Seams.s4Small, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (h | h | h | h | h | h | h | h | h | h | h | h | h) | (h | h | h) <;> subst h <;> omega

theorem prep_caps (H : AtomsX P carriers FP X) (cap : ℕ) (hcap : 10000 * (X * X * X) + 100 ≤ cap) :
    (PrimAsm.Data.unaryList (Seams.s4Small2 P carriers FP)).length + ppN (Seams.s4Small2 P carriers FP) +
      2 ^ ((Seams.s4Small2 P carriers FP).getD 11 0 + 1) + 4 * (ppReq (Seams.s4Small2 P carriers FP)).length +
      10 ≤ cap ∧
    (∀ j : ℕ, 8 * (Seams.s4Small2 P carriers FP).getD j 0 + 1 ≤ cap) ∧
    8 * P.n + 1 ≤ cap ∧ 8 * 2 ^ (Seams.s4Small2 P carriers FP).getD 11 0 + 1 ≤ cap := by
  have hv := vs_le P carriers FP X H
  have hul := ul_le X _ hv
  have hlen : (Seams.s4Small2 P carriers FP).length = 16 := rfl
  rw [hlen] at hul
  have hn := H.n2
  have hG := H.G
  have hreq := TabW.reqT_le P.n FP.len FP.cap FP.errExp (Seams.carLen carriers 0) (Seams.carLen carriers 1)
    (Fintype.card (GapSeed FP)) X hn H.len H.cap (by have := H.err; omega) (H.cl 0) (H.cl 1) hG
  have hX2 : 2 ≤ X := by omega
  have hx2 : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hx3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  rw [ppN_s4, ppReq_s4, pow_succ, nE_s4]
  refine ⟨by omega, fun j => ?_, by omega, by omega⟩
  have := getD_le X _ hv j
  omega

theorem hHT_of (H : AtomsX P carriers FP X) (cap : ℕ) (hcap : 10000 * (X * X * X) + 100 ≤ cap) :
    8 * Hof carriers 0 + 8 * Hof carriers 1 +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) + 1) +
      8 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) + 1) + 10 ≤ cap := by
  have hw : FP.walkLen ≤ X := by have := walkLen_le FP; have := H.err; omega
  have hn := H.n2
  have w0 : FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) ≤ X * (258 + 256 * X) :=
    Nat.mul_le_mul hw (by have := H.cl 0; omega)
  have w1 : FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) ≤ X * (258 + 256 * X) :=
    Nat.mul_le_mul hw (by have := H.cl 1; omega)
  have e : X * (258 + 256 * X) = 258 * X + 256 * (X * X) := by ring
  have hx2 : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hx3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  have := H.hof 0
  have := H.hof 1
  omega

theorem twW_le (H : AtomsX P carriers FP X) :
    (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length + 1 < 2100 * (X * X * X) + 2 := by
  rw [twW_len, esOf_length]
  have hw : FP.walkLen ≤ X := by have := walkLen_le FP; have := H.err; omega
  have hn := H.n2
  have w0 : FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) ≤ X * (258 + 256 * X) :=
    Nat.mul_le_mul hw (by have := H.cl 0; omega)
  have w1 : FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) ≤ X * (258 + 256 * X) :=
    Nat.mul_le_mul hw (by have := H.cl 1; omega)
  have e : X * (258 + 256 * X) = 258 * X + 256 * (X * X) := by ring
  have hin : 2 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 0 + 2)) + 1) + 1 +
      (2 * (FP.walkLen * (2 + 128 * (2 * Seams.carLen carriers 1 + 2)) + 1) + 1) ≤ 1032 * X + 1024 * (X * X) + 6 := by
    omega
  have hG := Nat.mul_le_mul H.G hin
  have e2 : X * (1032 * X + 1024 * (X * X) + 6) = 1032 * (X * X) + 1024 * (X * X * X) + 6 * X := by ring
  have hx2 : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hx3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem mkc_of (H : AtomsX P carriers FP X) (cap : ℕ) (hcap : 10000 * (X * X * X) + 100 ≤ cap) (e : GapSeed FP)
    (k : Fin 2) (hk : k.val < carriers.length) :
    MkCap cap (PrimT.tabH (carriers.get ⟨k.val, hk⟩)) P.n (maskGates (carriers.get ⟨k.val, hk⟩)).length
      (filterTable FP e (maskGates (carriers.get ⟨k.val, hk⟩)).length) (majorityThreshold FP.walkLen) := by
  have hh := H.tabH k.val hk
  have hg := H.mask k.val hk
  have ht := H.tbl e k.val hk
  have hn := H.n2
  have hthr : majorityThreshold FP.walkLen ≤ X := by
    have := thr_le FP; have := walkLen_le FP; have := H.err; omega
  have hx2 : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hx3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  have hkk : (maskGates (carriers.get ⟨k.val, hk⟩)).length *
      (1 + (P.n + 1) * (2 * (2 * PrimT.tabH (carriers.get ⟨k.val, hk⟩) + 1))) ≤ X * (1 + X * (4 * X + 2)) :=
    Nat.mul_le_mul hg (by
      have := Nat.mul_le_mul (show P.n + 1 ≤ X by omega)
        (show 2 * (2 * PrimT.tabH (carriers.get ⟨k.val, hk⟩) + 1) ≤ 4 * X + 2 by omega)
      omega)
  have e1 : X * (1 + X * (4 * X + 2)) = X + 2 * (X * X) + 4 * (X * X * X) := by ring
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  unfold capOf7
  omega

/-- **The seed loop's numeric hypotheses** at the sizes' bound. -/
theorem qnum_of (H : AtomsX P carriers FP X) {N : ℕ} (ps : List (Fin N × Fin N)) (T Vm Fn cap : ℕ)
    (hT1 : dR P ≤ T) (hT2 : dRow P ≤ T) (hTX : T ≤ X) (hV : Vm ≤ X) (hps : ps.length ≤ Fn) (hnF : P.n ≤ Fn)
    (hcap : capNeed X Fn ≤ cap) :
    QNum cap FP P carriers ps T Vm (twW FP (esOf FP) (Seams.carLen carriers 0) (Seams.carLen carriers 1)).length := by
  obtain ⟨hb, hs, hr, h2s, hhL, hdRow, hdR, h1, h2, hsr⟩ := star_le P
  unfold capNeed at hcap
  have hn := H.n2
  have hx2 : X ≤ X * X := Nat.le_mul_of_pos_left X (by omega)
  have hx3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  have hc0 : 10000 * (X * X * X) + 100 ≤ cap := by omega
  have h8 : 8 * X + 3 < cap := by
    generalize X * X * X = x3 at hx3 hc0
    generalize X * X = x2 at hx2 hx3
    omega
  have hp : ps.length * (2 * (2 * (P.s * (P.r / 2)) + 1)) ≤ Fn * (4 * (Fn * Fn) + 2) :=
    Nat.mul_le_mul hps (by have := Nat.mul_le_mul hnF hnF; omega)
  have htw := twW_le P carriers FP X H
  refine ⟨by omega, by omega, ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, by omega, by omega,
    ⟨hT1, hT2⟩, ⟨by omega, by omega⟩, fun e k hk => mkc_of P carriers FP X H cap hc0 e k hk, by omega, by omega⟩

end Caps

end NearCubicWires.WireExponent3_5.FinalPass.Sd

