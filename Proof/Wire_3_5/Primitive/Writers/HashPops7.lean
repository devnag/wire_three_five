import Proof.Wire_3_5.Primitive.Writers.HashPops6

/-! # HASH setup (C), P2a part 7: the loop over the selections and the populations stream

* `gBodyW`, `gLoopW`, **`gLoop_spec`**: at every selection index `gi < G` (counted down in `GR`, `R 1` counting up)
  the primes loop, then `PR` rewound;
* `popsW`, **`pops_spec`**: the loop, then the closing `0`: the output gains `rowsAll f |ps| G ++ [false]`.

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

section Defs
variable {ns nr : ℕ} (L : PL ns nr)

/-- One selection: the primes loop, `PR` rewound, `R 1` up. -/
def gBodyW (rowW : WM ns nr) : WM ns nr := .seq (pLoopW L rowW) (.seq (WM.rewind L.PR L.PH) (.inc (L.R 1)))

/-- **The selections loop.** -/
def gLoopW (rowW : WM ns nr) : WM ns nr := FinalPass.ThrArith.countW L.GR (gBodyW L rowW)

/-- **The populations program**: the selections loop, then the closing `0`. -/
def popsW (rowW : WM ns nr) : WM ns nr := .seq (gLoopW L rowW) (emitC L.O L.OP false)

end Defs

/-- The selections loop's state before selection `j`. -/
def gSt (t : LS) (f : ℕ → ℕ → List (List ℕ)) (m G j kD : ℕ) : LS :=
  { t with
    out := t.out ++ rowsAll f m j
    dg := List.replicate kD false
    gi := j
    gr := G - j }

section Loop
variable {ns nr : ℕ} (cap : ℕ) (L : PL ns nr) (h : L.Ok) (σB : WState ns nr)
include h

/-- The primes loop's cost bound. -/
def pCost (m u c : ℕ) : ℕ := m * ((11 * u + 7) + 1 + (c + 1 + (3 * u + 1)) + 2) + 1

theorem gLoop_spec (rowW : WM ns nr) (G : ℕ) (ps : List ℕ) (f : ℕ → ℕ → List (List ℕ)) (U c : ℕ)
    (hrow : RowOK cap L σB rowW G ps f U c) (hpos : ∀ q ∈ ps, 1 ≤ q)
    (hPR : σB.st L.PR = PrimAsm.Data.unaryList ps) (hcP : (PrimAsm.Data.unaryList ps).length + 1 ≤ cap)
    (hG : G + 1 ≤ cap) (t : LS) (kD : ℕ) (hdg : t.dg = List.replicate kD false) (hdh : t.dh = 0)
    (hk : t.k = 0) (hdl : t.dl = 0) (hdc : t.dc = 0) (hg : t.gi = 0) (hgr : t.gr = G) (hp : t.p = 0) (hph : t.ph = 0)
    (hU : t.out.length + (rowsAll f ps.length G).length ≤ U) :
    ∃ kD', WExec cap (gLoopW L rowW) (t.w L σB) ((gSt t f ps.length G G kD').w L σB)
      (G * (pCost ps.length (PrimAsm.Data.unaryList ps).length c + 1 +
        (5 * (PrimAsm.Data.unaryList ps).length + 1 + 1 + 3) + 4) + 1) := by
  set Inv : ℕ → WState ns nr → Prop := fun j σ => ∃ kD', σ = (gSt t f ps.length G j kD').w L σB with hInv
  have i0 : Inv (G - G) (t.w L σB) := by
    refine ⟨kD, ?_⟩
    rw [Nat.sub_self]
    congr 1
    apply LS.ext <;> simp [gSt, rowsAll, hdg, hg, hgr]
  obtain ⟨τ, e, kD', hτ⟩ := cd_loop cap L.GR (gBodyW L rowW)
    (pCost ps.length (PrimAsm.Data.unaryList ps).length c + 1 + (5 * (PrimAsm.Data.unaryList ps).length + 1 + 1 + 3))
    Inv G (by omega)
    (fun j _ σ ⟨kD1, hσ⟩ => by rw [hσ, w_GR L h]; simp [gSt])
    (fun j hj σ ⟨kD1, hσ⟩ => by
      subst hσ
      rw [setv_GR_w L h]
      set tj : LS := { gSt t f ps.length G j kD1 with gr := G - j - 1 } with htj
      obtain ⟨kD2, p1⟩ := pLoop_spec cap L h σB rowW G ps f U c hrow hpos hPR hcP j hj tj kD1
        (by simp [htj, gSt]) (by simp [htj, gSt, hdh]) (by simp [htj, gSt, hk]) (by simp [htj, gSt, hdl])
        (by simp [htj, gSt, hdc]) (by simp [htj, gSt]) (by simp [htj, gSt, hp]) (by simp [htj, gSt, hph])
        (by
          have := rowsAll_le f ps.length (j + 1) G (by omega)
          rw [rowsAll_succ, List.length_append] at this
          simp only [htj, gSt, List.length_append]
          omega)
      have hu := unary_take_le ps ps.length
      rw [List.take_length] at hu
      have p2 := wrewind_spec cap L.PR L.PH (PrimAsm.Data.unaryList ps).length
        ((pSt tj f j ps ps.length kD2).w L σB) (by rw [w_PH L h]; simp [pSt]) (by rw [w_PH L h]; simp [pSt]; omega)
      rw [w_sh_PR L h, show (pSt tj f j ps ps.length kD2).ph - (PrimAsm.Data.unaryList ps).length = 0 by
        simp [pSt], setv_PH_seth_PR_w L h] at p2
      have p3 := WExec.inc (cap := cap) (L.R 1) (({ pSt tj f j ps ps.length kD2 with ph := 0 } : LS).w L σB)
        (by rw [w_1 L h]; simp [pSt, htj, gSt]; omega)
      rw [w_1 L h, setv_1_w L h] at p3
      refine ⟨_, WExec.cast cap (WExec.seq p1 (WExec.seq p2 p3)) rfl (by unfold pCost; omega), kD2, ?_⟩
      congr 1
      apply LS.ext <;> simp [pSt, htj, gSt, rowsAll_succ, hph] <;> omega)
    G le_rfl (t.w L σB) i0
  exact ⟨kD', by rw [hτ] at e; exact e⟩

theorem pops_spec (rowW : WM ns nr) (G : ℕ) (ps : List ℕ) (f : ℕ → ℕ → List (List ℕ)) (U c : ℕ)
    (hrow : RowOK cap L σB rowW G ps f U c) (hpos : ∀ q ∈ ps, 1 ≤ q)
    (hPR : σB.st L.PR = PrimAsm.Data.unaryList ps) (hcP : (PrimAsm.Data.unaryList ps).length + 1 ≤ cap)
    (hG : G + 1 ≤ cap) (t : LS) (kD : ℕ) (hdg : t.dg = List.replicate kD false) (hdh : t.dh = 0)
    (hk : t.k = 0) (hdl : t.dl = 0) (hdc : t.dc = 0) (hg : t.gi = 0) (hgr : t.gr = G) (hp : t.p = 0) (hph : t.ph = 0)
    (hU : t.out.length + (rowsAll f ps.length G).length + 1 ≤ U) (hUc : U ≤ cap) :
    ∃ kD', WExec cap (popsW L rowW) (t.w L σB)
      (({ gSt t f ps.length G G kD' with out := t.out ++ (rowsAll f ps.length G ++ [false]) } : LS).w L σB)
      (G * (pCost ps.length (PrimAsm.Data.unaryList ps).length c + 1 +
        (5 * (PrimAsm.Data.unaryList ps).length + 1 + 1 + 3) + 4) + 1 + 1 + 7) := by
  obtain ⟨kD', e1⟩ := gLoop_spec cap L h σB rowW G ps f U c hrow hpos hPR hcP hG t kD hdg hdh hk hdl hdc hg hgr hp hph
    (by omega)
  have e2 := emitC_spec cap L.O L.OP false ((gSt t f ps.length G G kD').w L σB) (by rw [w_sh_O L h, w_st_O L h])
    (by rw [w_OP L h]; simp [gSt]; omega)
  rw [show ((((gSt t f ps.length G G kD').w L σB).sets L.O (((gSt t f ps.length G G kD').w L σB).st L.O ++ [false])).seth
      L.O (((gSt t f ps.length G G kD').w L σB).sh L.O + 1)).setv L.OP
      (((gSt t f ps.length G G kD').w L σB).val L.OP + 1) =
      appendO ((gSt t f ps.length G G kD').w L σB) L.O L.OP [false] from rfl, appendO_w L h] at e2
  refine ⟨kD', WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl⟩
  congr 1
  apply LS.ext <;> simp [gSt]

end Loop

end NearCubicWires.WireExponent3_5.PrimAsm.HashPops
