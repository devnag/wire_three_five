import Proof.Wire_3_5.Selection.CosParse4

/-! # C1.5 parse, part 5: the whole parse (P3:1326-1330, 1356-1360)

Paper: the request (P3:1326-1330) becomes the coset loop's entry state (P3:1356-1360). `parseP` runs the stages
`lenP ; numsP ; shapeP ; widthP ; rulerP ; wordsP ; gatesP ; popsP ; powP` from the word function's entry state. Their
side conditions (widths, capacities, the request's bit lengths) are the structure `ParseOK`. The run's end state is
`stC`, the stage outputs composed. Main declarations: `ParseOK`, `stA`, `stB`, `stC`, `parseA_spec`, `parseB_spec`,
`parseC_spec`, `parseCost`, **`parse_run`**. Paper quantity: the request's data in the machine's working form. -/

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
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (selWord)
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)
open NearCubicWires.WireExponent3_5 (ratWord)
open NearCubicWires.WireExponent3_5.SelectionMachine.Gate (zwCost)

/-- The parse's side conditions at capacity `cap`. -/
structure ParseOK (R : SelectionReq) (h : ParamsOk R) (cap : ℕ) : Prop where
  c0 : 2 * Lof R + 1 ≤ cap
  c1 : 2 ^ (natBitLength R.n + 1) ≤ cap
  c2 : 2 ^ (natBitLength R.r + 1) ≤ cap
  c3 : R.n + 4 ≤ cap
  c4 : 2 ^ (R.s + 1) ≤ cap
  c5 : R.n + R.r * (starParamsOf R h).b + R.r + (starParamsOf R h).b + 1 ≤ cap
  c6 : R.s * (R.r / 2) + R.s + R.r / 2 ≤ cap
  c7 : R.r * R.s + R.r + R.s ≤ cap
  c8 : R.r / 2 + (starParamsOf R h).b + R.s + (R.n - R.r * (starParamsOf R h).b) + Lof R + R.n + 3 ≤ cap
  c9 : 8 * (Wof R * Wof R) + 2 * Wof R + 1 ≤ cap
  c10 : Bof R + Wof R ≤ cap
  c11 : 2 * Wof R + 2 * (R.r * R.s) + Lof R + 2 ≤ cap
  c12 : 2 ^ (R.gates.length + 2) + R.gates.length * (R.n + 1) + 2 * Wof R + Bof R + R.n + 2 ≤ cap
  c13 : 2 ^ (R.pops.length + 2) + R.pops.length + Bof R + 1 ≤ cap
  c14 : 2 ^ (R.r * R.s + 1) ≤ cap
  wB : Wof R + 1 ≤ Bof R
  w1 : 1 ≤ Wof R
  bits : ∀ z ∈ gInts R, natBitLength z.natAbs ≤ Wof R
  gB : (gateTable (Wof R) R).length ≤ Bof R
  pB : (popTable (Wof R) R).length ≤ Bof R
  gW : R.gates.length < 2 ^ Wof R
  pops : PopsOK R (Wof R) cap

/-! ## The stages composed -/

/-- The state after the numbers (`lenP ; numsP ; shapeP ; widthP`). -/
def stA (R : SelectionReq) (h : ParamsOk R) : WState 49 112 :=
  ((((((((((numsSt R h ((Top.entrySt (selWord R) : WState 49 112).setv 85 (Lof R))).setv 0 (R.r / 2)).setv 1
    (starParamsOf R h).b).setv 2 R.s).setv 3 ((R.n - R.r * (starParamsOf R h).b + 1) / 2)).setv 4
      ((R.n - R.r * (starParamsOf R h).b) / 2)).setv 5 (Lof R + 1)).setv 60 (R.n + 1)).setv 86 (Wof R)).setv 95
        (2 * Wof R + 1)).setv 87 (Bof R)

/-- The numbers' cost. -/
def costA (R : SelectionReq) (h : ParamsOk R) : ℕ :=
  lenCost (Lof R) + 1 + (numsCost R h + 1 + (shapeCost (R.r / 2) (starParamsOf R h).b R.s
    (R.n - R.r * (starParamsOf R h).b) (Lof R) R.n + 1 + (widthCost (Lof R) R.n + 1)))

theorem parseA_spec (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (hc : ParseOK R h cap) (k : WM 49 112)
    (τ : WState 49 112) (c : ℕ) (hk : WExec cap k (stA R h) τ c) :
    WExec cap (.seq lenP (.seq numsP (.seq shapeP (.seq widthP k)))) (Top.entrySt (selWord R)) τ (costA R h + c) := by
  set σ0 : WState 49 112 := Top.entrySt (selWord R) with hσ0
  have x1 := lenP_spec cap (selWord R) σ0 (by simp [hσ0, Top.entrySt]) (by simp [hσ0, Top.entrySt])
    (by simp [hσ0, Top.entrySt]) (by simp [hσ0, Top.entrySt]) (by simp [hσ0, Top.entrySt]) hc.c0
  have x2 := numsP_spec cap R h (σ0.setv 85 (selWord R).length) (by simp [hσ0, Top.entrySt])
    (by simp [hσ0, Top.entrySt])
    (fun r hr => by
      have h85 : r ≠ 85 := by rintro rfl; rcases hr with ⟨_, e⟩ | e | e | e | e <;> simp_all
      simp [hσ0, Top.entrySt, Function.update_of_ne h85])
    hc.c1 hc.c2 hc.c3 hc.c4 hc.c5 hc.c6 hc.c7
  set σB := numsSt R h (σ0.setv 85 (selWord R).length) with hσB
  have x3 := shapeP_spec cap σB (R.r / 2) (starParamsOf R h).b R.s (R.n - R.r * (starParamsOf R h).b) (Lof R) R.n
    (by simp [hσB, numsSt]) (by simp [hσB, numsSt]) (by simp [hσB, numsSt]) (by simp [hσB, numsSt])
    (by simp [hσB, numsSt, Lof]) (by simp [hσB, numsSt])
    (fun r hr => by
      have n1 : r ≠ 64 ∧ r ≠ 67 ∧ r ≠ 68 ∧ r ≠ 69 ∧ r ≠ 70 ∧ r ≠ 71 ∧ r ≠ 72 ∧ r ≠ 73 ∧ r ≠ 85 := by
        rcases hr with e | e | e | e | e
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; simp at e)
        all_goals (subst e; decide)
      simp [hσB, numsSt, hσ0, Top.entrySt, Function.update_apply, n1.1, n1.2.1, n1.2.2.1, n1.2.2.2.1,
        n1.2.2.2.2.1, n1.2.2.2.2.2.1, n1.2.2.2.2.2.2.1, n1.2.2.2.2.2.2.2.1, n1.2.2.2.2.2.2.2.2])
    hc.c8
  set σC := (((((((σB.setv 0 (R.r / 2)).setv 1 (starParamsOf R h).b).setv 2 R.s).setv 3
    ((R.n - R.r * (starParamsOf R h).b + 1) / 2)).setv 4 ((R.n - R.r * (starParamsOf R h).b) / 2)).setv 5
      (Lof R + 1)).setv 60 (R.n + 1)) with hσC
  have x4 := widthP_spec cap σC (Lof R) R.n (by simp [hσC, hσB, numsSt, Lof]) (by simp [hσC, hσB, numsSt])
    (fun r hr => by
      rcases hr with e | e | e | e | e | e <;> (subst e; simp [hσC, hσB, numsSt, hσ0, Top.entrySt]))
    (by have := hc.c9; unfold Wof at this; exact this)
  have e4 : (((σC.setv 86 (8 * (Lof R + R.n + 2))).setv 95 (2 * (8 * (Lof R + R.n + 2)) + 1)).setv 87
      (8 * (8 * (Lof R + R.n + 2) * (8 * (Lof R + R.n + 2))))) = stA R h := by
    simp only [stA, hσC, hσB, hσ0, Wof, Bof, Lof]
  rw [e4] at x4
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 hk)))) rfl ?_
  unfold costA Lof; omega

/-- The state after the ruler and the words. -/
def stB (R : SelectionReq) (h : ParamsOk R) : WState 49 112 :=
  wordsSt ((stA R h).sets (Sm 45) (false :: List.replicate (Wof R) true)) (Wof R) (Lof R) (R.r * R.s)

/-- The ruler's and the words' cost. -/
def costB (R : SelectionReq) : ℕ :=
  3 + 1 + (18 * Wof R + 3 + 1 + (7 * Wof R + 1 + 1 + (Bof R * (1 + 8) + 1 + 1 + (7 * Bof R + 1)))) + 1 +
    (wordsCost (Wof R) (Lof R) (R.r * R.s) + 1)

theorem stA_val (R : SelectionReq) (h : ParamsOk R) (r : Fin 112) :
    (stA R h).val r = if r = 87 then Bof R else if r = 95 then 2 * Wof R + 1 else if r = 86 then Wof R
      else if r = 60 then R.n + 1 else if r = 5 then Lof R + 1 else if r = 4 then (R.n - R.r * (starParamsOf R h).b) / 2
      else if r = 3 then (R.n - R.r * (starParamsOf R h).b + 1) / 2 else if r = 2 then R.s
      else if r = 1 then (starParamsOf R h).b else if r = 0 then R.r / 2 else if r = 73 then R.r * R.s
      else if r = 72 then R.s * (R.r / 2) else if r = 71 then R.n - R.r * (starParamsOf R h).b else if r = 70 then R.r / 2
      else if r = 69 then (starParamsOf R h).b else if r = 68 then R.s else if r = 67 then R.r else if r = 64 then R.n
      else if r = 85 then Lof R else 0 := by
  simp only [stA, numsSt, WState.setv_val, WState.seth_val, Function.update_apply, Top.entrySt]

theorem stA_sh (R : SelectionReq) (h : ParamsOk R) (i : Fin 50) :
    (stA R h).sh i = if i = 0 then 2 * ((natWord R.n).length + (natWord R.r).length) else 0 := by
  simp only [stA, numsSt, WState.setv_sh, WState.seth_sh, Function.update_apply, Top.entrySt]

theorem stA_st (R : SelectionReq) (h : ParamsOk R) (i : Fin 50) :
    (stA R h).st i = if i = 0 then frame (selWord R) else [] := by
  simp only [stA, numsSt, WState.setv_st, WState.seth_st, Top.entrySt]
  by_cases hi : i = 0
  · subst hi; simp
  · have hv : i.val ≠ 0 := fun e => hi (Fin.ext e)
    simp [hi, hv]

theorem parseB_spec (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (hc : ParseOK R h cap) (k : WM 49 112)
    (τ : WState 49 112) (c : ℕ) (hk : WExec cap k (stB R h) τ c) :
    WExec cap (.seq rulerP (.seq wordsP k)) (stA R h) τ (costB R + c) := by
  have x1 := rulerP_spec cap (stA R h) (Wof R) (Bof R) (by rw [stA_st]; simp) (by rw [stA_sh]; simp)
    (by rw [stA_val]; simp) (by rw [stA_val]; simp) (by rw [stA_val]; simp) (by rw [stA_val]; simp) hc.wB hc.c10
  set σ := (stA R h).sets (Sm 45) (false :: List.replicate (Wof R) true) with hσ
  have x2 := wordsP_spec cap σ (Wof R) (Lof R) (R.r * R.s) (by simp [hσ, stA_val]) (by simp [hσ, stA_val])
    (by simp [hσ, stA_val])
    (fun r hr => by rcases hr with e | e | e | e | e | e <;> (subst e; simp [hσ, stA_val]))
    (fun Z hZ => by
      have h0 : Z ≠ 0 := by rcases hZ with hZ | e | e | e | e <;> [skip; subst e; subst e; subst e; subst e] <;>
        first | decide | (simp [zs13] at hZ; rcases hZ with e | e | e | e | e | e | e | e | e | e | e | e | e <;>
          (subst e; decide))
      have h45 : Z ≠ Sm 45 := by rcases hZ with hZ | e | e | e | e <;> [skip; subst e; subst e; subst e; subst e] <;>
        first | decide | (simp [zs13] at hZ; rcases hZ with e | e | e | e | e | e | e | e | e | e | e | e | e <;>
          (subst e; decide))
      refine ⟨?_, ?_⟩
      · simp only [hσ, WState.sets_st, Function.update_of_ne h45]; rw [stA_st, if_neg h0]
      · simp only [hσ, WState.sets_sh]; rw [stA_sh, if_neg h0])
    (by simp only [hσ, WState.sets_sh]; rw [stA_sh]; simp) hc.w1 hc.c11
  exact WExec.cast cap (WExec.seq x1 (WExec.seq x2 hk)) rfl (by unfold costB; omega)

theorem stB_val (R : SelectionReq) (h : ParamsOk R) : (stB R h).val = (stA R h).val := by
  simp only [stB, wordsSt, WState.sets_val, setsAll_val]

theorem stB_sh (R : SelectionReq) (h : ParamsOk R) : (stB R h).sh = (stA R h).sh := by
  simp only [stB, wordsSt, WState.sets_sh, setsAll_sh]

theorem stB_st (R : SelectionReq) (h : ParamsOk R) (i : Fin 50) :
    (stB R h).st i = if i = Sm 43 ∨ i = Sm 0 then frame (binary (R.r * R.s) 0)
      else if i = Sm 32 then frame (binary (Wof R) 0) else if i = Sm 2 then frame (binary (Wof R) (2 ^ Lof R))
      else if i = Sm 41 then frame (binary (Wof R) 1) else if i ∈ zs13 then frame (binary (Wof R) 0)
      else if i = Sm 45 then false :: List.replicate (Wof R) true else (stA R h).st i := by
  simp only [stB, wordsSt, WState.sets_st, setsAll_st, Function.update_apply]
  by_cases h43 : i = Sm 43
  · subst h43; simp
  by_cases h0 : i = Sm 0
  · subst h0; simp
  by_cases h32 : i = Sm 32
  · subst h32; simp
  by_cases h2 : i = Sm 2
  · subst h2; simp
  by_cases h41 : i = Sm 41
  · subst h41; simp
  have e43 : i ≠ 45 := by simpa using h43
  have e0 : i ≠ 2 := by simpa using h0
  have e32 : i ≠ 34 := by simpa using h32
  have e2 : i ≠ 4 := by simpa using h2
  have e41 : i ≠ 43 := by simpa using h41
  simp [e43, e0, e32, e2, e41]

/-- The end state of the parse. -/
def stC (R : SelectionReq) (h : ParamsOk R) : WState 49 112 :=
  ((((((((((stB R h).seth 0 (2 * ((natWord R.n ++ natWord R.r).length +
    (natWord R.gates.length ++ (gInts R).flatMap intWord).length))).setv 88 R.gates.length).sets (Sm 32)
      (frame (binary (Wof R) R.gates.length))).sets (Sm 30) (gateTable (Wof R) R)).seth 0 (2 * (selWord R).length)).setv 59
        R.pops.length).sets (Sm 31) (popTable (Wof R) R)).setv 58 (popTable (Wof R) R).length).setv 84 (2 ^ (R.r * R.s)))

/-- The tables' cost. -/
def costC (R : SelectionReq) : ℕ :=
  gatesCost R (Wof R) (Bof R) + 1 + ((natBitLength R.pops.length + 2) * (40 * 2 ^ natBitLength R.pops.length + 40) + 1 +
    (18 * R.pops.length + 3 + 1 + (popsTCost (Wof R) R.pops + 1 + (Bof R * (1 + 8) + 1 + 1 + (7 * Bof R + 1)))) + 1 +
      ((R.r * R.s) * (18 * 2 ^ (R.r * R.s) + 7) + 18 * (R.r * R.s) + 20))

theorem frame_selWord (R : SelectionReq) : frame (selWord R) =
    frameP (natWord R.n ++ natWord R.r) ++ (frameP (natWord R.gates.length ++ (gInts R).flatMap intWord) ++
      (frameP (natWord R.pops.length ++ R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2) ++ [false])) := by
  rw [frame_eq_frameP, selWord_eq, tailG]
  simp only [frameP_append', List.append_assoc]

theorem parseC_spec (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (hc : ParseOK R h cap) :
    WExec cap (.seq gatesP (.seq popsP (PrimAsm.UnaryArith.pow2W zPow))) (stB R h) (stC R h) (costC R) := by
  have v := stB_val R h
  have x1 := gatesP_spec cap R (Wof R) (Bof R) (stB R h) (frameP (natWord R.n ++ natWord R.r))
    (frameP (natWord R.pops.length ++ R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2) ++ [false])
    (by rw [stB_st]; simp only [show ¬((0 : Fin 50) = Sm 43 ∨ (0 : Fin 50) = Sm 0) by decide,
      show (0 : Fin 50) ≠ Sm 32 by decide, show (0 : Fin 50) ≠ Sm 2 by decide, show (0 : Fin 50) ≠ Sm 41 by decide,
      show (0 : Fin 50) ∉ zs13 by decide, show (0 : Fin 50) ≠ Sm 45 by decide, if_false]
        rw [stA_st, if_pos rfl, frame_selWord])
    (by rw [stB_sh, stA_sh, if_pos rfl, frameP_length', List.length_append])
    (by rw [v, stA_val]; simp) (by rw [v, stA_val]; simp)
    (fun r hr => by rw [v, stA_val]; rcases hr with e | e | e | e | e | e | e <;> (subst e; simp))
    ⟨by rw [stB_st]; simp, by rw [stB_sh, stA_sh]; simp⟩ ⟨by rw [stB_st]; simp [zs13], by rw [stB_sh, stA_sh]; simp⟩
    (by rw [stB_st]; simp [zs13, stA_st]) (by rw [stB_sh, stA_sh]; simp) (by rw [stB_st]; simp [zs13])
    (by rw [stB_sh, stA_sh]; simp) hc.bits hc.gB hc.gW hc.c12
  set σG := ((((stB R h).seth 0 ((frameP (natWord R.n ++ natWord R.r)).length +
    2 * (natWord R.gates.length ++ (gInts R).flatMap intWord).length)).setv 88 R.gates.length).sets (Sm 32)
      (frame (binary (Wof R) R.gates.length))).sets (Sm 30) (gateTable (Wof R) R) with hσG
  have vG : ∀ r : Fin 112, r ≠ 88 → σG.val r = (stA R h).val r := fun r hr => by
    simp [hσG, v, Function.update_of_ne hr]
  have x2 := popsP_spec cap R (Wof R) (Bof R) σG
    (frameP (natWord R.n ++ natWord R.r) ++ frameP (natWord R.gates.length ++ (gInts R).flatMap intWord)) [false]
    (by simp only [hσG, WState.sets_st, WState.setv_st, WState.seth_st, Function.update_of_ne
        (show (0 : Fin 50) ≠ Sm 30 by decide), Function.update_of_ne (show (0 : Fin 50) ≠ Sm 32 by decide)]
        rw [stB_st]; simp only [show ¬((0 : Fin 50) = Sm 43 ∨ (0 : Fin 50) = Sm 0) by decide,
          show (0 : Fin 50) ≠ Sm 32 by decide, show (0 : Fin 50) ≠ Sm 2 by decide, show (0 : Fin 50) ≠ Sm 41 by decide,
          show (0 : Fin 50) ∉ zs13 by decide, show (0 : Fin 50) ≠ Sm 45 by decide, if_false]
        rw [stA_st, if_pos rfl, frame_selWord, List.append_assoc])
    (by simp [hσG, frameP_length'])
    (fun r hr => by
      have h88 : r ≠ 88 := by rcases hr with e | e | e | e | e | e | e | e | e <;> (subst e; decide)
      rw [vG r h88, stA_val]; rcases hr with e | e | e | e | e | e | e | e | e <;> (subst e; simp))
    (by rw [vG 95 (by decide), stA_val]; simp) (by rw [vG 87 (by decide), stA_val]; simp)
    (by simp [hσG]; rw [stB_st]; simp [zs13, stA_st]) (by simp [hσG, stB_sh, stA_sh])
    (by simp [hσG]; rw [stB_st]; simp [zs13]) (by simp [hσG, stB_sh, stA_sh]) hc.pops hc.pB hc.c13
  set σH := (((σG.seth 0 ((frameP (natWord R.n ++ natWord R.r) ++
    frameP (natWord R.gates.length ++ (gInts R).flatMap intWord)).length + 2 * (natWord R.pops.length ++
      R.pops.flatMap fun X => natListWord X.1 ++ ratWord X.2).length)).setv 59 R.pops.length).sets (Sm 31)
        (popTable (Wof R) R)).setv 58 (popTable (Wof R) R).length with hσH
  have x3 := powP_spec cap σH (R.r * R.s) (by simp [hσH, vG 73 (by decide), stA_val])
    (by simp [hσH, vG 84 (by decide), stA_val]) (by simp [hσH, vG 92 (by decide), stA_val])
    (by simp [hσH, vG 89 (by decide), stA_val]) hc.c14
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 x3)) ?_ (by unfold costC; omega)
  simp only [stC, hσH, hσG, frameP_length', List.length_append]
  congr 3
  · rw [selWord_eq, tailG]; simp; ring

/-- The parse's cost. -/
def parseCost (R : SelectionReq) (h : ParamsOk R) : ℕ := costA R h + (costB R + costC R)

/-- **The parse's run** to `stC`. -/
theorem parse_run (cap : ℕ) (R : SelectionReq) (h : ParamsOk R) (hc : ParseOK R h cap) :
    WExec cap parseP (Top.entrySt (selWord R)) (stC R h) (parseCost R h) := by
  have xC := parseC_spec cap R h hc
  have xB := parseB_spec cap R h hc _ _ _ xC
  have xA := parseA_spec cap R h hc _ _ _ xB
  exact xA

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
