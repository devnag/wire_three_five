import Proof.Wire_3_5.Primitive.Writers.HashPops5

/-! # HASH setup (C), P2a part 6: the generic loop over the rows `(g, p)` (built once)

A row program is any word program meeting **`RowOK`** (from a tracked state at selection index `gi` and prime `p`,
blank digit stream, zero counters: the row's records `(f gi pi).flatMap recsOf` appended, the digit stream blank
again). The loop:

* `pBodyW`, `pLoopW`, **`pLoop_spec`**: the primes `1^p 0` read from `PR` into `R 2` (their position in `PH`), the row
  run, `p` cleared — over every prime of the list;
* `gBodyW`, `gLoopW`, **`gLoop_spec`**: the primes loop at every selection index `gi < G` (counted down in `GR`,
  `R 1` counting up), `PR` rewound;
* `popsW`, **`pops_spec`**: the loop, then the closing `0`: the output `rowsAll G ++ [false]`.

Paper quantity of the main type: the HASH call's populations stream, row by row (P3:2253-2293, 2596-2599). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashPops
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-- The records of the rows `(gi, 0) … (gi, k − 1)`. -/
def rowsG (f : ℕ → ℕ → List (List ℕ)) (gi k : ℕ) : List Bool := (List.range k).flatMap fun pi => (f gi pi).flatMap recsOf

/-- The records of the selections `0 … j − 1`, each over the `m` primes. -/
def rowsAll (f : ℕ → ℕ → List (List ℕ)) (m j : ℕ) : List Bool := (List.range j).flatMap fun gi => rowsG f gi m

theorem rowsG_succ (f : ℕ → ℕ → List (List ℕ)) (gi k : ℕ) :
    rowsG f gi (k + 1) = rowsG f gi k ++ (f gi k).flatMap recsOf := by
  simp [rowsG, List.range_succ]

theorem rowsAll_succ (f : ℕ → ℕ → List (List ℕ)) (m j : ℕ) :
    rowsAll f m (j + 1) = rowsAll f m j ++ rowsG f j m := by
  simp [rowsAll, List.range_succ]

theorem rowsG_le (f : ℕ → ℕ → List (List ℕ)) (gi k m : ℕ) (hk : k ≤ m) :
    (rowsG f gi k).length ≤ (rowsG f gi m).length := by
  induction m with
  | zero => rw [Nat.le_zero.mp hk]
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hk with h1 | h1
    · have := ih (by omega); rw [rowsG_succ, List.length_append]; omega
    · rw [h1]

theorem rowsAll_le (f : ℕ → ℕ → List (List ℕ)) (m j G : ℕ) (hj : j ≤ G) :
    (rowsAll f m j).length ≤ (rowsAll f m G).length := by
  induction G with
  | zero => rw [Nat.le_zero.mp hj]
  | succ G ih =>
    rcases Nat.lt_or_eq_of_le hj with h1 | h1
    · have := ih (by omega); rw [rowsAll_succ, List.length_append]; omega
    · rw [h1]

theorem unary_take_succ (ps : List ℕ) (k : ℕ) (hk : k < ps.length) :
    PrimAsm.Data.unaryList (ps.take (k + 1)) =
      PrimAsm.Data.unaryList (ps.take k) ++ (List.replicate ps[k] true ++ [false]) := by
  unfold PrimAsm.Data.unaryList
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]
  simp

theorem unary_split (ps : List ℕ) (k : ℕ) (hk : k < ps.length) :
    PrimAsm.Data.unaryList ps = PrimAsm.Data.unaryList (ps.take k) ++
      (List.replicate ps[k] true ++ false :: PrimAsm.Data.unaryList (ps.drop (k + 1))) := by
  have e : PrimAsm.Data.unaryList ps =
      PrimAsm.Data.unaryList (ps.take (k + 1)) ++ PrimAsm.Data.unaryList (ps.drop (k + 1)) := by
    unfold PrimAsm.Data.unaryList
    rw [← List.flatMap_append, List.take_append_drop]
  rw [e, unary_take_succ ps k hk]
  simp

theorem unary_take_le (ps : List ℕ) (k : ℕ) :
    (PrimAsm.Data.unaryList (ps.take k)).length ≤ (PrimAsm.Data.unaryList ps).length := by
  have e : PrimAsm.Data.unaryList ps = PrimAsm.Data.unaryList (ps.take k) ++ PrimAsm.Data.unaryList (ps.drop k) := by
    unfold PrimAsm.Data.unaryList
    rw [← List.flatMap_append, List.take_append_drop]
  rw [e, List.length_append]
  omega

section Defs
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (σB : WState ns nr)

/-- **The row contract**: from a tracked state at selection index `gi < G` and the prime `ps[pi]`, blank digit stream
and zero counters, an output within `U` after the row, the row program appends the row's records and leaves the
digit stream blank. -/
def RowOK (rowW : WM ns nr) (G : ℕ) (ps : List ℕ) (f : ℕ → ℕ → List (List ℕ)) (U c : ℕ) : Prop :=
  ∀ gi < G, ∀ pi < ps.length, ∀ (t : LS) (kD : ℕ), t.dg = List.replicate kD false → t.dh = 0 → t.k = 0 →
    t.dl = 0 → t.dc = 0 → t.gi = gi → t.p = ps.getD pi 0 → t.out.length + ((f gi pi).flatMap recsOf).length ≤ U →
    ∃ kD', WExec cap rowW (t.w L σB)
      ({ t with out := t.out ++ (f gi pi).flatMap recsOf, dg := List.replicate kD' false }.w L σB) c

/-- One prime: read `1^p 0` into `R 2`, the row, `p` cleared. -/
def pBodyW (rowW : WM ns nr) : WM ns nr := .seq (WM.readU L.PR L.PH (L.R 2)) (.seq rowW (WM.clear (L.R 2)))

/-- **The primes loop.** -/
def pLoopW (rowW : WM ns nr) : WM ns nr := .whs L.PR (pBodyW L rowW)

end Defs

section Loop
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (h : L.Ok) (σB : WState ns nr)
include h

/-- The primes loop's state before prime `k`. -/
def pSt (t : LS) (f : ℕ → ℕ → List (List ℕ)) (gi : ℕ) (ps : List ℕ) (k kD : ℕ) : LS :=
  { t with
    out := t.out ++ rowsG f gi k
    dg := List.replicate kD false
    ph := (PrimAsm.Data.unaryList (ps.take k)).length }

theorem pLoop_spec (rowW : WM ns nr) (G : ℕ) (ps : List ℕ) (f : ℕ → ℕ → List (List ℕ)) (U c : ℕ)
    (hrow : RowOK cap L σB rowW G ps f U c) (hpos : ∀ q ∈ ps, 1 ≤ q)
    (hPR : σB.st L.PR = PrimAsm.Data.unaryList ps) (hcP : (PrimAsm.Data.unaryList ps).length + 1 ≤ cap)
    (gi : ℕ) (hgi : gi < G) (t : LS) (kD : ℕ) (hdg : t.dg = List.replicate kD false) (hdh : t.dh = 0)
    (hk : t.k = 0) (hdl : t.dl = 0) (hdc : t.dc = 0) (hg : t.gi = gi) (hp : t.p = 0) (hph : t.ph = 0)
    (hU : t.out.length + (rowsG f gi ps.length).length ≤ U) :
    ∃ kD', WExec cap (pLoopW L rowW) (t.w L σB) ((pSt t f gi ps ps.length kD').w L σB)
      (ps.length * ((11 * (PrimAsm.Data.unaryList ps).length + 7) + 1 +
        (c + 1 + (3 * (PrimAsm.Data.unaryList ps).length + 1)) + 2) + 1) := by
  set Inv : ℕ → WState ns nr → Prop := fun k σ => ∃ kD', σ = (pSt t f gi ps k kD').w L σB with hInv
  have i0 : Inv (ps.length - ps.length) (t.w L σB) := by
    refine ⟨kD, ?_⟩
    rw [Nat.sub_self]
    congr 1
    apply LS.ext <;> simp [pSt, rowsG, hdg, hph, PrimAsm.Data.unaryList]
  obtain ⟨τ, e, kD', hτ⟩ := ws_loop cap L.PR (pBodyW L rowW)
    ((11 * (PrimAsm.Data.unaryList ps).length + 7) + 1 + (c + 1 + (3 * (PrimAsm.Data.unaryList ps).length + 1)))
    Inv ps.length
    (fun k hk σ ⟨kD1, hσ⟩ => by
      rw [hσ]; unfold wbit; rw [w_st_PR L h, w_sh_PR L h, hPR, unary_split ps k hk]
      simp only [pSt]
      rw [rd_app0]
      exact rd_ones _ 0 _ (by have := hpos ps[k] (List.getElem_mem hk); omega))
    (fun σ ⟨kD1, hσ⟩ => by
      rw [hσ]; unfold wbit; rw [w_st_PR L h, w_sh_PR L h, hPR]
      simp [pSt, readTapeBit])
    (fun k hkl σ ⟨kD1, hσ⟩ => by
      subst hσ
      have hsplit := unary_split ps k hkl
      have hlk := unary_take_le ps (k + 1)
      rw [unary_take_succ ps k hkl] at hlk
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hlk
      set tk := pSt t f gi ps k kD1 with htk
      have tph : tk.ph = (PrimAsm.Data.unaryList (ps.take k)).length := by simp [htk, pSt]
      have tp : tk.p = 0 := by simp [htk, pSt, hp]
      have r1 := wreadU_spec cap L.PR L.PH (L.R 2) (ne2_PH L h).symm ps[k] (tk.w L σB)
        (fun i hi => by rw [w_st_PR L h, w_sh_PR L h, hPR, hsplit, tph, rd_app]; exact rd_ones _ i _ hi)
        (by rw [w_st_PR L h, w_sh_PR L h, hPR, hsplit, tph, rd_app]; exact rd_zero _ _)
        (by rw [w_PH L h, tph]; omega) (by rw [w_2 L h, tp]; omega)
      rw [w_sh_PR L h, w_PH L h, w_2 L h, seth_PR_setv_PH_w L h, setv_2_w L h] at r1
      set t1 : LS := { ({ tk with ph := tk.ph + ps[k] + 1 } : LS) with p := tk.p + ps[k] } with ht1
      obtain ⟨kD2, r2⟩ := hrow gi hgi k hkl t1 kD1 (by simp [ht1, htk, pSt]) (by simp [ht1, htk, pSt, hdh])
        (by simp [ht1, htk, pSt, hk]) (by simp [ht1, htk, pSt, hdl]) (by simp [ht1, htk, pSt, hdc])
        (by simp [ht1, htk, pSt, hg]) (by simp [ht1, tp, List.getElem?_eq_getElem hkl])
        (by
          have := rowsG_le f gi (k + 1) ps.length (by omega)
          rw [rowsG_succ, List.length_append] at this
          simp only [ht1, htk, pSt, List.length_append]
          omega)
      have r3 := wclear_spec cap (L.R 2) ps[k]
        (({ t1 with out := t1.out ++ (f gi k).flatMap recsOf, dg := List.replicate kD2 false } : LS).w L σB)
        (by rw [w_2 L h]; simp [ht1, tp]) (by rw [w_2 L h]; simp [ht1, tp]; omega)
      rw [setv_2_w L h] at r3
      refine ⟨_, WExec.cast cap (WExec.seq r1 (WExec.seq r2 r3)) rfl (by omega), kD2, ?_⟩
      congr 1
      apply LS.ext <;> simp [ht1, htk, pSt, rowsG_succ, unary_take_succ ps k hkl, hp] <;> omega)
    ps.length le_rfl (t.w L σB) i0
  exact ⟨kD', by rw [hτ] at e; exact e⟩

end Loop

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
