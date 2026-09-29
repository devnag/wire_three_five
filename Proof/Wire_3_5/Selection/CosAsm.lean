import Proof.Wire_3_5.Selection.CosLay

/-! # C1.5: the run from the parse's postcondition (P3:1356-1362, 3673)

Paper: "There are 2^k candidate cosets, so the total is bounded as claimed. Select a minimum objective" (P3:1358-1360);
the union machine reads the selected coset (P3:3673). Consumer backward from Top's residual `C1WM` (one register-machine
run from the framed request word to the selected coset's raw word, every head and register back at `0`): this module
proves `C1WM Pw 1 …` from (i) the parse's postcondition `PPost` (the coset loop's invariant `LInv` at the counter `0`,
the exact register file `pvP`, the output stream empty) and (ii) the request's width and capacity facts `GlobalOK`.
After the parse, the coset loop (`cosetL_spec`) leaves `BEST = argminIdx ratLt keyAt 2^k`; `setOut` hands `r, s` to the
output block; `outW` writes `natListWord (codesOfIdx s r BEST)`, which is `cosetWord (selArgmin R)` by `selArgmin_eq_fold`; `cleanP` rewinds the input and output heads and clears every register. Main declarations: `Lof`,
`Wof`, `Bof`, `pvP`, `PPost`, `GlobalOK`, `clearAll_spec`, `costF`, **`c1WM_of_parse`**. Paper quantity: the selected
coset's word from the request word. -/

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
open NearCubicWires.WireExponent3_5.UnionMachine.RegRat
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (selWord cosetWord)
open NearCubicWires.WireExponent3_5.SelectionMachine.Plan (BasePre)

/-! ## The request's widths -/

/-- The request word's length `L` (the key width `V`). -/
def Lof (R : SelectionReq) : ℕ := (selWord R).length

/-- The word width `W = 8(L + n + 2)`. -/
def Wof (R : SelectionReq) : ℕ := 8 * (Lof R + R.n + 2)

/-- The rewind bound `8·W²`. -/
def Bof (R : SelectionReq) : ℕ := 8 * (Wof R * Wof R)

/-! ## The register file after the parse -/

/-- **The registers after the parse** (every other register `0`). -/
def pvP (R : SelectionReq) (h : ParamsOk R) (r : Fin 112) : ℕ :=
  if r = 0 then hh (starParamsOf R h) else if r = 1 then (starParamsOf R h).b else if r = 2 then R.s
  else if r = 3 then fL (starParamsOf R h) else if r = 4 then fR (starParamsOf R h) else if r = 5 then Lof R + 1
  else if r = 58 then (popTable (Wof R) R).length else if r = 59 then R.pops.length else if r = 60 then R.n + 1
  else if r = 64 then R.n else if r = 67 then R.r else if r = 68 then R.s else if r = 69 then (starParamsOf R h).b
  else if r = 70 then R.r / 2 else if r = 71 then R.n - R.r * (starParamsOf R h).b
  else if r = 72 then R.s * (R.r / 2) else if r = 73 then R.r * R.s else if r = 84 then 2 ^ (R.r * R.s)
  else if r = 85 then Lof R else if r = 86 then Wof R else if r = 87 then Bof R else if r = 88 then R.gates.length
  else if r = 95 then 2 * Wof R + 1 else 0

theorem pvP_zero (R : SelectionReq) (h : ParamsOk R) (r : Fin 112) (hr : r ∉ dirty) (h84 : r ≠ 84) :
    pvP R h r = 0 := by
  unfold pvP
  simp only [dirty, List.mem_cons, List.not_mem_nil, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h4, h5, h58, h59, h60, h64, h67, h68, h69, h70, h71, h72, h73, h85, h86, h87, h88, h95, -, -,
    -⟩ := hr
  simp [h0, h1, h2, h3, h4, h5, h58, h59, h60, h64, h67, h68, h69, h70, h71, h72, h73, h84, h85, h86, h87, h88, h95]

/-- **The parse's postcondition**: the coset loop's invariant before the first round, the register file, the output
stream empty, the input head within the rewind bound, the ruler's and the helper stream's heads home. -/
def PPost (R : SelectionReq) (h : ParamsOk R) (σ : WState 49 112) : Prop :=
  LInv Sm Qm R h (Wof R) (Lof R) 84 0 σ ∧ σ.val = pvP R h ∧ σ.st 1 = [] ∧ σ.sh 1 = 0 ∧ σ.sh 0 ≤ Bof R ∧
    ∀ k : Fin 50, (k = 28 ∨ k = 29 ∨ k = 45 ∨ k = 47) → σ.sh (Sm k) = 0

/-- **The request's width and capacity facts** (at `W = Wof R`, `V = Lof R`, capacity `cap`). -/
structure GlobalOK (R : SelectionReq) (h : ParamsOk R) (cap : ℕ) : Prop where
  ng : R.gates.length < 2 ^ Wof R
  kb : ∀ g ∈ R.gates, KeyBound (gateOf g) (Lof R)
  wv : 2 * Lof R + 3 ≤ Wof R
  nk : R.n + (starParamsOf R h).k + 4 ≤ Wof R
  gneed : gateNeed (starParamsOf R h) (Wof R) (Lof R) ≤ cap
  c2 : 2 * Wof R + 1 ≤ cap
  cG : R.gates.length * (R.n + 1) * (2 * Wof R + 2) + 2 < cap
  ck : 2 * (R.r * R.s) + 1 ≤ cap
  cP : R.pops.length ≤ cap
  cT : (popTable (Wof R) R).length ≤ cap
  cC : 2 ^ (R.r * R.s) ≤ cap
  w1 : 1 ≤ Wof R
  fit : ∀ N < 2 ^ (R.r * R.s), PopsFit R h N (Wof R) cap (0, 1) R.pops
  key : ∀ N < 2 ^ (R.r * R.s), ∀ M < 2 ^ (R.r * R.s),
    (keyAt R h N).1 * (keyAt R h M).2 < 2 ^ Wof R ∧ (keyAt R h M).1 * (keyAt R h N).2 < 2 ^ Wof R
  den : ∀ N < 2 ^ (R.r * R.s), (keyAt R h N).2 < 2 ^ Wof R
  cout : 2 * 2 ^ (R.s + 1) + 2 * R.r + 6 ≤ cap
  cs : R.s ≤ cap
  outB : ∀ N, (RepairRepresentation.natListWord (codesOfIdx R.s R.r N)).length ≤ Bof R
  cB : Bof R ≤ cap
  cv : ∀ r : Fin 112, pvP R h r ≤ cap

/-! ## Clearing registers -/

theorem clearAll_spec (cap : ℕ) :
    ∀ (rs : List (Fin 112)) (σ : WState 49 112), (∀ r ∈ rs, σ.val r ≤ cap) →
      WExec cap (clearAll rs) σ ⟨σ.sh, σ.st, fun r => if r ∈ rs then 0 else σ.val r, σ.cell⟩
        ((rs.map fun r => 3 * σ.val r + 2).sum)
  | [], σ, _ => by
    refine WExec.cast cap (WExec.skip σ) ?_ (by simp)
    apply WState.eq <;> simp
  | r :: rs, σ, hc => by
    have x1 := wclear_spec (cap := cap) r (σ.val r) σ rfl (hc r List.mem_cons_self)
    have x2 := clearAll_spec cap rs (σ.setv r 0) (fun r' hr' => by
      simp only [WState.setv_val, Function.update_apply]; split_ifs
      · omega
      · exact hc r' (List.mem_cons_of_mem _ hr'))
    have hle : ((rs.map fun r' => 3 * (σ.setv r 0).val r' + 2).sum) ≤ ((rs.map fun r' => 3 * σ.val r' + 2).sum) := by
      apply List.sum_le_sum
      intro r' _
      simp only [WState.setv_val, Function.update_apply]; split_ifs <;> omega
    refine WExec.cast cap (WExec.seq x1 x2) ?_ (by simp only [List.map_cons, List.sum_cons]; omega)
    apply WState.eq
    · rfl
    · rfl
    · funext r'
      by_cases h1 : r' = r
      · subst h1; simp
      · by_cases h2 : r' ∈ rs
        · simp [h2]
        · simp [h1, h2, Function.update_apply]
    · rfl

/-! ## The whole run -/

/-- The loop's cost. -/
def loopCost (R : SelectionReq) (h : ParamsOk R) : ℕ :=
  2 ^ (R.r * R.s) * (iterCost (starParamsOf R h) R.n (Wof R) (Lof R) R.gates.length (R.r * R.s) R.pops.length
    (popTable (Wof R) R).length R.pops + 2) + 1

/-- The registers before the cleanup. -/
def vClean (R : SelectionReq) (h : ParamsOk R) (r : Fin 112) : ℕ :=
  if r = 110 then R.r else if r = 111 then R.s else pvP R h r

/-- The cleanup's cost. -/
def cleanCost (R : SelectionReq) (h : ParamsOk R) : ℕ :=
  Bof R * (1 + 8) + 1 + 1 + (7 * Bof R + 1) + 1 + (Bof R * (1 + 8) + 1 + 1 + (7 * Bof R + 1) + 1 +
    (dirty.map fun r => 3 * vClean R h r + 2).sum)

/-- **The machine's cost** from the parse's. -/
def costF (parseCost : SelectionReq → ℕ) (R : SelectionReq) : ℕ :=
  if h : ParamsOk R then
    parseCost R + 1 + (loopCost R h + 1 + (18 * R.r + 3 + 1 + (18 * R.s + 3) + 1 + (outCost R.r R.s + 1 +
      cleanCost R h)))
  else 0

theorem heads_zero (R : SelectionReq) (h : ParamsOk R) (σ : WState 49 112) (hP : PPost R h σ) :
    ∀ k : Fin 50, k.val < 48 → σ.sh (Sm k) = 0 := by
  obtain ⟨inv, -, -, -, -, hfree⟩ := hP
  intro k hk
  have b := inv.base
  have hw : ∀ k : Fin 50, (k.val = 3 ∨ k.val = 33 ∨ k.val = 34 ∨ k.val = 37 ∨ k.val = 38 ∨ k.val = 39 ∨ k.val = 40 ∨
      k.val = 44 ∨ k.val = 46) → σ.sh (Sm k) = 0 := fun k hk => by
    obtain ⟨v, hv⟩ := inv.wd k (by
      rcases hk with e | e | e | e | e | e | e | e | e <;> [exact Or.inl (Fin.ext e);
        exact Or.inr (Or.inl (Fin.ext e)); exact Or.inr (Or.inr (Or.inl (Fin.ext e)));
        exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e)))); exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e)))));
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e))))));
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e)))))));
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext e))))))));
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext e))))))))])
    exact hv.2
  have hf : ∀ k : Fin 50, (k.val = 28 ∨ k.val = 29 ∨ k.val = 45 ∨ k.val = 47) → σ.sh (Sm k) = 0 := fun k hk =>
    hfree k (by rcases hk with e | e | e | e <;> [exact Or.inl (Fin.ext e); exact Or.inr (Or.inl (Fin.ext e));
      exact Or.inr (Or.inr (Or.inl (Fin.ext e))); exact Or.inr (Or.inr (Or.inr (Fin.ext e)))])
  by_cases hsc : 4 ≤ k.val ∧ k.val < 28
  · exact (b.sc ⟨k.val, hsc.2⟩ hsc.1).2
  by_cases hw' : k.val = 3 ∨ k.val = 33 ∨ k.val = 34 ∨ k.val = 37 ∨ k.val = 38 ∨ k.val = 39 ∨ k.val = 40 ∨
      k.val = 44 ∨ k.val = 46
  · exact hw k hw'
  by_cases hf' : k.val = 28 ∨ k.val = 29 ∨ k.val = 45 ∨ k.val = 47
  · exact hf k hf'
  obtain ⟨kv, hkv⟩ := k
  simp only at hsc hw' hf' hk
  interval_cases kv <;> (try simp at hsc hw' hf')
  all_goals first
    | exact b.nsw.2
    | exact b.gah
    | exact b.of.2
    | exact b.gth
    | exact inv.pth
    | exact b.ng.2
    | exact inv.bn.2
    | exact inv.bd.2
    | exact inv.be.2
    | (obtain ⟨v, hv⟩ := inv.an; exact hv.2)
    | (obtain ⟨v, hv⟩ := inv.ad; exact hv.2)

/-- **C1's register-machine run** from the parse (consumer backward: the parse must deliver `PPost`). -/
theorem c1WM_of_parse (capOf parseCost : SelectionReq → ℕ)
    (hparse : ∀ (R : SelectionReq) (h : ParamsOk R), (∀ X ∈ R.pops, 0 ≤ X.2) →
      ∃ σ, WExec (capOf R) parseP (Top.entrySt (selWord R)) σ (parseCost R) ∧ PPost R h σ)
    (hglob : ∀ (R : SelectionReq) (h : ParamsOk R), (∀ X ∈ R.pops, 0 ≤ X.2) → GlobalOK R h (capOf R)) :
    Top.C1WM Pw 1 capOf (costF parseCost) := by
  intro R hR
  obtain ⟨hr2, h2, h4, _, hnn⟩ := hR
  have h : ParamsOk R := ⟨hr2, h2, h4⟩
  obtain ⟨σP, xP, hP⟩ := hparse R h hnn
  have G := hglob R h hnn
  have hP' := hP
  obtain ⟨inv, hval, hO1, hOh, hINh, -⟩ := hP
  set cap := capOf R with hcapdef
  -- the coset loop
  have hpos : 1 ≤ 2 ^ (R.r * R.s) := Nat.one_le_two_pow
  have hC : σP.val 84 = (2 ^ (R.r * R.s) - 1) + 1 := by
    rw [hval, Nat.sub_add_cancel hpos]; simp [pvP]
  obtain ⟨σL, xL, bL, beL, cL, vL, shL, stL, cellL⟩ := cosetL_spec Sm Sm_inj Qm Qm_inj 84 (by decide) cap R h (Wof R)
    (Lof R) G.ng G.kb G.wv G.nk G.gneed G.c2 G.cG G.ck G.cP G.cT G.cC G.w1 G.fit G.key G.den (2 ^ (R.r * R.s) - 1) 0 σP inv hC
  set N := argminIdx ratLt (keyAt R h) (2 ^ (R.r * R.s)) with hN
  have vLP : ∀ r : Fin 112, r ≠ 84 → σL.val r = pvP R h r := fun r hr => by rw [vL r hr, hval]
  -- r, s into the output block
  have x1 := FinalPass.Hash4.wcopyR_spec cap 67 110 89 (by decide) (by decide) (by decide) σL
    (by rw [vLP 110 (by decide)]; simp [pvP]) (by rw [vLP 89 (by decide)]; simp [pvP])
    (by rw [vLP 67 (by decide)]; exact G.cv 67)
  rw [vLP 67 (by decide)] at x1
  set σ1 := σL.setv 110 (pvP R h 67) with hσ1
  have x2 := FinalPass.Hash4.wcopyR_spec cap 68 111 89 (by decide) (by decide) (by decide) σ1
    (by simp [hσ1, vLP 111 (by decide), pvP]) (by simp [hσ1, vLP 89 (by decide), pvP])
    (by simp [hσ1, vLP 68 (by decide)]; exact G.cv 68)
  have h68 : σ1.val 68 = R.s := by simp [hσ1, vLP 68 (by decide), pvP]
  rw [h68] at x2
  set σ2 := σ1.setv 111 R.s with hσ2
  have x12 : WExec cap setOut σL σ2 (18 * R.r + 3 + 1 + (18 * R.s + 3)) := by
    have e : pvP R h 67 = R.r := by simp [pvP]
    rw [e] at x1
    exact WExec.cast cap (WExec.seq x1 x2) (by rw [hσ2, hσ1, e]) le_rfl
  -- the output
  have hst : σ2.st (Sm 43) = frame (binary (R.s * R.r) N) := by
    rw [show σ2.st = σL.st from rfl, beL.1, Nat.mul_comm]
  have hNlt : N < 2 ^ (R.s * R.r) := by
    rw [Nat.mul_comm]
    have := argminIdx_lt ratLt (keyAt R h) (2 ^ (R.r * R.s) - 1)
    rw [Nat.sub_add_cancel hpos] at this
    exact this
  have hO2 : σ2.sh (Sm 49) = (σ2.st (Sm 49)).length := by
    have e1 : σ2.st (Sm 49) = [] := by
      rw [show σ2.st = σL.st from rfl, stL 49 (by decide) (by decide) (Or.inr (by decide))]; exact hO1
    rw [e1, show σ2.sh = σL.sh from rfl, shL 49]; exact hOh
  have x3 := outW_spec cap R.s R.r N (Sm 43) (Sm 49) (by decide) Rout σ2 hst (beL.2)
    hNlt (fun i hi => by
      have h110 : Rout i ≠ 110 := fun e => by have := congrArg Fin.val e; simp [Rout] at this; omega
      have h111 : Rout i ≠ 111 := fun e => by have := congrArg Fin.val e; simp [Rout] at this; omega
      have h84 : Rout i ≠ 84 := fun e => by have := congrArg Fin.val e; simp [Rout] at this; omega
      simp only [hσ2, hσ1, WState.setv_val, Function.update_apply, h110, h111, if_false]
      rw [vLP _ h84]
      have hd : ∀ r ∈ dirty, r.val < 100 ∨ 110 ≤ r.val := by decide
      apply pvP_zero R h _ (fun hm => by have := hd _ hm; simp [Rout] at this; omega) h84)
    (by simp [hσ2, hσ1, Rout, pvP]) (by simp [hσ2, Rout]) hO2 G.cout G.cs
  set σ3 := appS σ2 (Sm 49) (RepairRepresentation.natListWord (codesOfIdx R.s R.r N)) with hσ3
  -- the cleanup
  have v3 : ∀ r : Fin 112, σ3.val r = vClean R h r ∨ r = 84 := by
    intro r
    by_cases h84 : r = 84
    · exact Or.inr h84
    · left
      simp only [hσ3, appS_val, hσ2, hσ1, WState.setv_val, Function.update_apply, vClean]
      by_cases h111 : r = 111
      · subst h111; simp
      · by_cases h110 : r = 110
        · subst h110; simp [pvP]
        · simp only [h111, h110, if_false]; exact vLP r h84
  have h87 : σ3.val 87 = Bof R := by
    rcases v3 87 with e | e
    · rw [e]; simp [vClean, pvP]
    · exact absurd e (by decide)
  have h89 : σ3.val 89 = 0 := by
    rcases v3 89 with e | e
    · rw [e]; simp [vClean, pvP]
    · exact absurd e (by decide)
  have hsh0 : σ3.sh 0 ≤ Bof R := by
    have e : σ3.sh 0 = σP.sh 0 := by
      simp only [hσ3, appS_sh, Function.update_apply, show (0 : Fin 50) ≠ Sm 49 by decide, if_false]
      exact shL 48
    rw [e]; exact hINh
  have x4 := rewS_spec cap 0 87 89 (by decide) σ3 (Bof R) h87 h89 G.cB hsh0
  set σ4 := σ3.seth 0 0 with hσ4
  have hsh1 : σ4.sh 1 ≤ Bof R := by
    simp only [hσ4, WState.seth_sh, Function.update_apply, show (1 : Fin 50) ≠ 0 by decide, if_false, hσ3, appS_sh]
    simp only [show (1 : Fin 50) = Sm 49 by decide, Function.update_self]
    rw [show σ2.st (Sm 49) = [] by
      rw [show σ2.st = σL.st from rfl, stL 49 (by decide) (by decide) (Or.inr (by decide))]; exact hO1]
    simpa using G.outB N
  have x5 := rewS_spec cap 1 87 89 (by decide) σ4 (Bof R) (by simpa [hσ4] using h87) (by simpa [hσ4] using h89) G.cB
    hsh1
  set σ5 := σ4.seth 1 0 with hσ5
  have hv5 : ∀ r : Fin 112, σ5.val r = σ3.val r := fun r => rfl
  have x6 := clearAll_spec cap dirty σ5 (fun r hr => by
    rw [hv5]
    rcases v3 r with e | e
    · rw [e]; unfold vClean; split_ifs
      · exact le_trans (by simp [pvP]) (G.cv 67)
      · exact le_trans (by simp [pvP]) (G.cv 68)
      · exact G.cv r
    · subst e; simp [dirty] at hr)
  set τ := (⟨σ5.sh, σ5.st, fun r => if r ∈ dirty then 0 else σ5.val r, σ5.cell⟩ : WState 49 112) with hτ
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · -- the cost
    unfold Pw costF
    rw [dif_pos h]
    have hcl : (dirty.map fun r => 3 * σ5.val r + 2).sum ≤ (dirty.map fun r => 3 * vClean R h r + 2).sum := by
      apply le_of_eq
      apply congrArg
      apply List.map_congr_left
      intro r hr
      rw [hv5]
      rcases v3 r with e | e
      · rw [e]
      · subst e; simp [dirty] at hr
    refine WExec.seq xP (WExec.seq (WExec.cast cap xL rfl ?_) (WExec.seq x12 (WExec.seq x3
      (WExec.mono (WExec.seq x4 (WExec.seq x5 x6)) ?_))))
    · unfold loopCost; rw [Nat.sub_add_cancel hpos]
    · unfold cleanCost; omega
  · -- the output
    have e : τ.st 1 = σ3.st (Sm 49) := by rfl
    rw [e]
    simp only [hσ3, appS_st, Function.update_self]
    rw [show σ2.st (Sm 49) = [] by
      rw [show σ2.st = σL.st from rfl, stL 49 (by decide) (by decide) (Or.inr (by decide))]; exact hO1,
      List.nil_append]
    rw [selArgmin_eq_fold R h hnn]
    rfl
  · -- the heads
    intro i
    obtain ⟨k, rfl⟩ := Sm_surj i
    by_cases h48 : k = 48
    · subst h48; simp [hτ, hσ5, hσ4, show Sm 48 = 0 by decide]
    · by_cases h49 : k = 49
      · subst h49; simp [hτ, hσ5, show Sm 49 = 1 by decide]
      · have hk : k.val < 48 := by have := k.isLt; omega
        have e0 : Sm k ≠ 0 := fun e => h48 (Sm_inj (e.trans (by decide)))
        have e1 : Sm k ≠ 1 := fun e => h49 (Sm_inj (e.trans (by decide)))
        have e49 : Sm k ≠ Sm 49 := fun e => h49 (Sm_inj e)
        simp only [hτ, hσ5, hσ4, WState.seth_sh, Function.update_apply, e0, e1, if_false, hσ3, appS_sh, e49]
        rw [show σ2.sh = σL.sh from rfl, shL k]
        exact heads_zero R h σP hP' k hk
  · -- the registers
    intro r
    simp only [hτ]
    split_ifs with hr
    · rfl
    · rw [hv5]
      by_cases h84 : r = 84
      · subst h84
        simp only [hσ3, appS_val, hσ2, hσ1, WState.setv_val, Function.update_apply]
        simp; exact cL
      · rcases v3 r with e | e
        · rw [e]; unfold vClean
          have h110 : r ≠ 110 := fun e => hr (by subst e; simp [dirty])
          have h111 : r ≠ 111 := fun e => hr (by subst e; simp [dirty])
          rw [if_neg h110, if_neg h111]
          exact pvP_zero R h r hr h84
        · exact absurd e h84

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
