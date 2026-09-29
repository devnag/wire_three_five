import Proof.Wire_3_5.Primitive.Writers.LevelWordW

/-! # SW parts: the stage-5 template word, raw (P3:1449-1477, 3170-3178)

The SYM words writer's templates (`symWords` word `4·3 + j`, `S3.templJ`) are C5's stage-5 table word of the
base list at blank rows, `levelWord M J W (fun _ => replicate L false)` with `L = |G_j|` (P3:1449-1477: `M`, then the
records of levels `J, …, 0`, record `j` = `true`, `unary (pow W'_j)`, `unary W'_j`, the row; then `false`). `LevelWordW` writes the same word at marks-level 2 inside a POP record; the front's slots hold it raw. Here:

* `tplRec`, `tplWord` (the raw word from `S = natCeilSqrt(64²B)`, `J`, `M`, `L`), **`tplWord_eq`** (it is the template word
  `levelWord P.M P.J P.W (blank rows)` of the base list `P`, through `winAt_eq`, `powAt_eq`);
* `tplBody` / **`tplBody_spec`**: one level (`levelVals` for `W'_j`, `pow W'_j`; the record appended raw);
* `tplW` / **`tplW_spec`**: the whole word, appended to an output stream from the registers `S`, `J`, `M`, `L` (`LevelWordW` register layout: `0 S`, `1 J`, `2 … 23` the level block, `24` the output counter, `25 M`, `26 L`, `27`
  the loop counter, `28`, `29` scratch).

Paper quantity of the main type: the stage-5 template `levelWord M J W (blank rows of length L)` of the base list
(`list:base`/`list:flatten`, P3:1449-1477, P3:1508-1520), the call word `4·3 + j` (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymParts.Tmpl
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.LevelW NearCubicWires.WireExponent3_5.PrimAsm.LevelWordW

/-! ## The raw word -/

/-- Level `j`'s record, raw: its marker, `pow W'_j`, `W'_j` (from `S = natCeilSqrt(64²B)`), the blank row. -/
def tplRec (Sv J j L : ℕ) : List Bool :=
  [true] ++ (reps (2 ^ Nat.clog 2 (2 * winAt Sv J j + 1)) [true] ++ [false]) ++
    (reps (winAt Sv J j) [true] ++ [false]) ++ reps L [false]

/-- **The template word, raw**: `M`, the records of levels `J, …, 0`, the end. -/
def tplWord (M Sv J L : ℕ) : List Bool :=
  (reps M [true] ++ [false]) ++ (FinalPass.ListEval.levels J).flatMap (fun j => tplRec Sv J j L) ++ [false]

theorem repsB_eq (n : ℕ) (b : Bool) : reps n [b] = List.replicate n b := by
  induction n with
  | zero => rfl
  | succ k ih => rw [reps_succ, ih, List.replicate_succ']

/-- **The raw template is the template word** `levelWord P.M P.J P.W (blank rows)` of the base list `P`. -/
theorem tplWord_eq (P : Lists.BaseListParams) (L : ℕ) :
    tplWord P.M (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B)) P.J L =
      FinalPass.ListEval.levelWord P.M P.J P.W (fun _ => List.replicate L false) := by
  unfold tplWord FinalPass.ListEval.levelWord
  rw [repsB_eq, ← unary_eq]
  congr 2
  refine List.flatMap_congr fun j _ => ?_
  unfold tplRec FinalPass.ListEval.record
  rw [repsB_eq, repsB_eq, repsB_eq, powAt_eq, winAt_eq, ← unary_eq, ← unary_eq]
  simp only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append]

theorem tplRec_length (Sv J j L : ℕ) :
    (tplRec Sv J j L).length = 1 + (2 ^ Nat.clog 2 (2 * winAt Sv J j + 1) + 1) + (winAt Sv J j + 1) + L := by
  unfold tplRec
  simp only [List.length_append, repsB_eq, List.length_replicate, List.length_singleton]
  try omega

/-! ## One level -/

section Body
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr)

/-- **One level**: compute `W'_j`, `pow W'_j` (`levelVals`); append the record raw; the blank row from `L`
(register `26`, copied to `28`). -/
def tplBody : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (W 27) (W 2) (W 29))
  (.seq (levelVals (lwV.trans W))
  (.seq (emitW O (W 24) [true])
  (.seq (repW O (W 24) (W 4) [true])
  (.seq (emitW O (W 24) [false])
  (.seq (repW O (W 24) (W 3) [true])
  (.seq (emitW O (W 24) [false])
  (.seq (FinalPass.Hash4.wcopyR (W 26) (W 28) (W 29))
  (.seq (repW O (W 24) (W 28) [false])
  (WM.clear (W 2))))))))))

/-- A bound on one level's cost. -/
def tplBodyBound (cap : ℕ) : ℕ := 4 * phBound cap + 200 * (cap + 10)

theorem tplBody_spec (τ : WState ns nr) (Sv J j L : ℕ)
    (h0 : τ.val (W 0) = Sv) (h1 : τ.val (W 1) = J) (h27 : τ.val (W 27) = j) (hjJ : j ≤ J)
    (hz : ∀ i : Fin 30, 2 ≤ i.val → i.val ≤ 23 → τ.val (W i) = 0) (h28 : τ.val (W 28) = 0)
    (h29 : τ.val (W 29) = 0) (h26 : τ.val (W 26) = L) (ho : τ.sh O = (τ.st O).length)
    (hcap : lvCap Sv J j ≤ cap) (hc : τ.val (W 24) + (tplRec Sv J j L).length ≤ cap)
    (hjc : j ≤ cap) (hLc : L ≤ cap) :
    ∃ n, WExec cap (tplBody O W) τ (appendO τ O (W 24) (tplRec Sv J j L)) n ∧ n ≤ tplBodyBound cap := by
  have hR : ∀ i k : Fin 30, W i = W k ↔ i = k := fun i k => W.injective.eq_iff
  have hne : ∀ {i k : Fin 30}, i ≠ k → W i ≠ W k := fun h => W.injective.ne h
  have hlen := tplRec_length Sv J j L
  generalize hw : winAt Sv J j = w at hlen
  generalize hp : 2 ^ Nat.clog 2 (2 * w + 1) = p at hlen
  have hV : ∀ i : Fin 24, (lwV.trans W) i = W ⟨i.val, by omega⟩ := fun i => rfl
  have hV0 : (lwV.trans W) 0 = W 0 := rfl
  have hV1 : (lwV.trans W) 1 = W 1 := rfl
  have hV2 : (lwV.trans W) 2 = W 2 := rfl
  have hV3 : (lwV.trans W) 3 = W 3 := rfl
  have hV4 : (lwV.trans W) 4 = W 4 := rfl
  have h2z := hz 2 (by decide) (by decide)
  have h3z := hz 3 (by decide) (by decide)
  have h4z := hz 4 (by decide) (by decide)
  -- the level's numbers
  have e1 := FinalPass.Hash4.wcopyR_spec cap (W 27) (W 2) (W 29) (hne (by decide)) (hne (by decide))
    (hne (by decide)) τ h2z h29 (by omega)
  rw [h27] at e1
  obtain ⟨n2, e2, b2⟩ := levelVals_spec cap (lwV.trans W) (τ.setv (W 2) j) Sv J j
    (by rw [hV0]; simp [hR, h0]) (by rw [hV1]; simp [hR, h1]) (by rw [hV2]; simp) hjJ
    (fun i hi => by
      have h2 : (⟨i.val, by omega⟩ : Fin 30) ≠ 2 := Fin.ne_of_val_ne (by show i.val ≠ 2; omega)
      rw [hV i, wsetv_val_ne _ _ (hne h2)]
      exact hz _ (by show 2 ≤ i.val; omega) (by show i.val ≤ 23; omega))
    hcap
  rw [hV3, hV4, hw, hp] at e2
  -- the record
  set ρ2 := ((τ.setv (W 2) j).setv (W 3) w).setv (W 4) p with hρ2
  have hsh2 : ρ2.sh = τ.sh := rfl
  have hst2 : ρ2.st = τ.st := rfl
  have hv2 : ρ2.val (W 24) = τ.val (W 24) := by simp [hρ2, hR]
  have e3 := emitW_spec cap O (W 24) [true] ρ2 (by rw [hsh2, hst2]; exact ho)
    (by rw [hv2]; simp only [List.length_cons, List.length_nil]; omega)
  have e4 := repW_spec cap O (W 24) (W 4) (hne (by decide)) [true] p (appendO ρ2 O (W 24) [true])
    (by simp [hρ2, hR]) (by simp [hsh2, hst2, ho])
    (by simp [hR, hv2]; omega) (by omega)
  rw [appendO_append, ← appendO_setv _ _ _ _ (hne (by decide))] at e4
  set ρ4 := ρ2.setv (W 4) 0 with hρ4
  have e5 := emitW_spec cap O (W 24) [false] (appendO ρ4 O (W 24) ([true] ++ reps p [true]))
    (by simp [hρ4, hsh2, hst2, ho])
    (by simp [hρ4, hR, hv2, PrimAsm.FiltRecW.reps_length]; omega)
  rw [appendO_append] at e5
  have e6 := repW_spec cap O (W 24) (W 3) (hne (by decide)) [true] w
    (appendO ρ4 O (W 24) ([true] ++ reps p [true] ++ [false]))
    (by simp [hρ4, hρ2, hR]) (by simp [hρ4, hsh2, hst2, ho])
    (by simp [hρ4, hR, hv2, PrimAsm.FiltRecW.reps_length]; omega) (by omega)
  rw [appendO_append, ← appendO_setv _ _ _ _ (hne (by decide))] at e6
  set ρ6 := ρ4.setv (W 3) 0 with hρ6
  have e7 := emitW_spec cap O (W 24) [false]
    (appendO ρ6 O (W 24) ([true] ++ reps p [true] ++ [false] ++ reps w [true]))
    (by simp [hρ6, hρ4, hsh2, hst2, ho])
    (by simp [hρ6, hρ4, hR, hv2, PrimAsm.FiltRecW.reps_length]; omega)
  rw [appendO_append] at e7
  -- the blank row
  set u7 := [true] ++ reps p [true] ++ [false] ++ reps w [true] ++ [false] with hu7
  have hu7l : u7.length = p + w + 3 := by
    simp only [hu7, List.length_append, PrimAsm.FiltRecW.reps_length, List.length_cons, List.length_nil]; try omega
  have e8 := FinalPass.Hash4.wcopyR_spec cap (W 26) (W 28) (W 29) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (appendO ρ6 O (W 24) u7) (by simp [hρ6, hρ4, hρ2, hR, h28])
    (by simp [hρ6, hρ4, hρ2, hR, h29]) (by simp [hρ6, hρ4, hρ2, hR, h26]; omega)
  rw [show (appendO ρ6 O (W 24) u7).val (W 26) = L by simp [hρ6, hρ4, hρ2, hR, h26],
    ← appendO_setv _ _ _ _ (hne (by decide))] at e8
  set ρ8 := ρ6.setv (W 28) L with hρ8
  have e9 := repW_spec cap O (W 24) (W 28) (hne (by decide)) [false] L (appendO ρ8 O (W 24) u7)
    (by simp [hρ8, hR]) (by simp [hρ8, hρ6, hρ4, hsh2, hst2, ho])
    (by simp [hρ8, hρ6, hρ4, hR, hv2]; omega) hLc
  rw [appendO_append, ← appendO_setv _ _ _ _ (hne (by decide))] at e9
  set ρ9 := ρ8.setv (W 28) 0 with hρ9
  have e10 := wclear_spec cap (W 2) j (appendO ρ9 O (W 24) (u7 ++ reps L [false]))
    (by simp [hρ9, hρ8, hρ6, hρ4, hρ2, hR]) (by simp [hρ9, hρ8, hρ6, hρ4, hρ2, hR]; omega)
  rw [← appendO_setv _ _ _ _ (hne (by decide))] at e10
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 e10))))))))) ?_ le_rfl, ?_⟩
  · have hρ : ρ9.setv (W 2) 0 = τ := by
      apply WState.eq
      · rfl
      · rfl
      · funext x
        simp only [hρ9, hρ8, hρ6, hρ4, hρ2, WState.setv_val, Function.update_apply]
        by_cases x2 : x = W 2
        · subst x2; simp [hR, h2z]
        · by_cases x28 : x = W 28
          · subst x28; simp [hR, h28]
          · by_cases x3 : x = W 3
            · subst x3; simp [hR, h3z]
            · by_cases x4 : x = W 4
              · subst x4; simp [hR, h4z]
              · simp [x2, x28, x3, x4]
      · rfl
    rw [hρ]
    have hu : u7 ++ reps L [false] = tplRec Sv J j L := by
      rw [hu7]; unfold tplRec; rw [hw, hp]; simp only [List.append_assoc]
    rw [hu]
  · unfold tplBodyBound
    have hF : cap + 2 ≤ phBound cap := by
      unfold phBound
      have : cap + 2 ≤ (cap + 2) * (cap + 2) := Nat.le_mul_self _
      have hE : 2000 * (cap + 2) * (cap + 2) = 2000 * ((cap + 2) * (cap + 2)) := by ring
      omega
    have hpc : p ≤ cap := by omega
    have hwc : w ≤ cap := by omega
    simp only [List.length_cons, List.length_nil]
    omega

end Body

/-! ## The whole word -/

section Word
variable {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr)

/-- **The template word, written**: `M` (register `25`, kept), the levels `J, …, 0` (loop counter `27`), the end. -/
def tplW : WM ns nr :=
  .seq (repRegW O (W 24) (W 25) (W 28) (W 29) [true])
  (.seq (emitW O (W 24) [false])
  (.seq (FinalPass.Hash4.wcopyR (W 1) (W 27) (W 29))
  (.seq (.inc (W 27))
  (.seq (.whr (W 27) (.seq (.dec (W 27)) (tplBody O W)))
  (emitW O (W 24) [false])))))

/-- A bound on the word's cost. -/
def tplWBound (cap J M : ℕ) : ℕ := 30 * M + 18 * J + 100 + (J + 1) * (tplBodyBound cap + 4)

/-- **The raw template word, appended to stream `O`**, from `S = natCeilSqrt(64²B)` in `W 0`, `J` in `W 1`, `M` in
`W 25`, `L` in `W 26` (the level block `2 … 23` and `27 … 29` at `0`); every register as at the entry. -/
theorem tplW_spec (τ : WState ns nr) (M Sv J L : ℕ)
    (h0 : τ.val (W 0) = Sv) (h1 : τ.val (W 1) = J) (h25 : τ.val (W 25) = M) (h26 : τ.val (W 26) = L)
    (hz : ∀ i : Fin 30, 2 ≤ i.val → i.val ≤ 23 → τ.val (W i) = 0) (h27 : τ.val (W 27) = 0)
    (h28 : τ.val (W 28) = 0) (h29 : τ.val (W 29) = 0) (ho : τ.sh O = (τ.st O).length)
    (hcap : lvCap Sv J J ≤ cap) (hc : τ.val (W 24) + (tplWord M Sv J L).length ≤ cap) (hJc : J + 1 ≤ cap)
    (hLc : L ≤ cap) (hMc : M ≤ cap) :
    ∃ n, WExec cap (tplW O W) τ (appendO τ O (W 24) (tplWord M Sv J L)) n ∧ n ≤ tplWBound cap J M := by
  have hR : ∀ i k : Fin 30, W i = W k ↔ i = k := fun i k => W.injective.eq_iff
  have hne : ∀ {i k : Fin 30}, i ≠ k → W i ≠ W k := fun h => W.injective.ne h
  set f : ℕ → List Bool := fun j => tplRec Sv J j L with hf
  set pre := reps M [true] ++ [false] with hpre
  have hlE : tplWord M Sv J L = pre ++ (FinalPass.ListEval.levels J).flatMap f ++ [false] := rfl
  have hpl : pre.length = M + 1 := by simp [hpre, PrimAsm.FiltRecW.reps_length]
  have hEl : (tplWord M Sv J L).length = pre.length + ((FinalPass.ListEval.levels J).flatMap f).length + 1 := by
    rw [hlE, List.length_append, List.length_append]; rfl
  -- the preamble
  have e1 := repRegW_spec cap O (W 24) (W 25) (W 28) (W 29) (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) [true] τ h28 h29 ho (by omega) (by rw [h25]; simp; omega)
  rw [h25] at e1
  have e2 := emitW_spec cap O (W 24) [false] (appendO τ O (W 24) (reps M [true])) (by simp [ho])
    (by simp [PrimAsm.FiltRecW.reps_length]; omega)
  rw [appendO_append, ← hpre] at e2
  have e3 := FinalPass.Hash4.wcopyR_spec cap (W 1) (W 27) (W 29) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (appendO τ O (W 24) pre) (by simp [hR, h27]) (by simp [hR, h29]) (by simp [hR, h1]; omega)
  rw [show (appendO τ O (W 24) pre).val (W 1) = J by simp [hR, h1]] at e3
  have e4 := WExec.inc (cap := cap) (W 27) ((appendO τ O (W 24) pre).setv (W 27) J) (by simp; omega)
  rw [wsetv_setv, show ((appendO τ O (W 24) pre).setv (W 27) J).val (W 27) + 1 = J + 1 by simp] at e4
  -- the loop
  let S' : ℕ → WState ns nr := fun k =>
    appendO (τ.setv (W 27) (J + 1 - k)) O (W 24) (pre ++ ((FinalPass.ListEval.levels J).take k).flatMap f)
  have hS'0 : S' 0 = (appendO τ O (W 24) pre).setv (W 27) (J + 1) := by
    simp only [S', List.take_zero, List.flatMap_nil, List.append_nil, Nat.sub_zero]
    rw [appendO_setv _ _ _ _ (hne (by decide))]
  have hloop := UnionMachine.Round.wloop cap (W 27) (tplBody O W) (tplBodyBound cap) (J + 1) S'
    (fun k _ => by simp only [S']; simp [hR])
    hJc
    (fun k hk => by
      have hkl : k < (FinalPass.ListEval.levels J).length := by rw [levels_length]; exact hk
      have hlk := levels_getElem J k hkl
      set τ' := appendO (τ.setv (W 27) (J + 1 - k - 1)) O (W 24)
        (pre ++ ((FinalPass.ListEval.levels J).take k).flatMap f) with hτ'
      have hτS : (S' k).setv (W 27) (J + 1 - k - 1) = τ' := by
        simp only [S', hτ']
        rw [← appendO_setv _ _ _ _ (hne (by decide)), wsetv_setv]
      rw [hτS]
      have htake : ((FinalPass.ListEval.levels J).take (k + 1)).flatMap f =
          ((FinalPass.ListEval.levels J).take k).flatMap f ++ f (J - k) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hkl, Option.toList_some, List.flatMap_append, hlk]
        simp
      have hpref : pre.length + (((FinalPass.ListEval.levels J).take k).flatMap f).length + (f (J - k)).length ≤
          (tplWord M Sv J L).length := by
        have := flatMap_take_length_le (FinalPass.ListEval.levels J) f (k + 1)
        rw [htake, List.length_append] at this
        omega
      have hcb : τ.val (W 24) + (pre ++ ((FinalPass.ListEval.levels J).take k).flatMap f).length +
          (tplRec Sv J (J - k) L).length ≤ cap := by
        have : (f (J - k)).length = (tplRec Sv J (J - k) L).length := rfl
        rw [List.length_append]
        omega
      obtain ⟨nb, eb, bb⟩ := tplBody_spec cap O W τ' Sv J (J - k) L
        (by rw [hτ']; simp [hR, h0]) (by rw [hτ']; simp [hR, h1])
        (by rw [hτ']; simp [hR]; omega) (by omega)
        (fun i h2 h23 => by
          have hi24 : W i ≠ W 24 := hne (Fin.ne_of_val_ne (by show i.val ≠ 24; omega))
          have hi27 : W i ≠ W 27 := hne (Fin.ne_of_val_ne (by show i.val ≠ 27; omega))
          rw [hτ', appendO_val, Function.update_of_ne hi24, wsetv_val_ne _ _ hi27]
          exact hz i h2 h23)
        (by rw [hτ']; simp [hR, h28]) (by rw [hτ']; simp [hR, h29])
        (by rw [hτ']; simp [hR, h26])
        (by rw [hτ']; simp [ho])
        (le_trans (lvCap_mono Sv J (J - k) (by omega)) hcap)
        (by rw [hτ', appendO_val, Function.update_self,
              wsetv_val_ne _ _ (hne (show (24 : Fin 30) ≠ 27 by decide))]
            exact hcb) (by omega) hLc
      refine WExec.mono (WExec.cast cap eb ?_ le_rfl) bb
      rw [hτ', appendO_append]
      simp only [S']
      rw [htake, List.append_assoc, show J + 1 - k - 1 = J + 1 - (k + 1) by omega])
  rw [hS'0] at hloop
  have hall : ((FinalPass.ListEval.levels J).take (J + 1)).flatMap f = (FinalPass.ListEval.levels J).flatMap f := by
    rw [List.take_of_length_le (by rw [levels_length])]
  simp only [S', Nat.sub_self, hall] at hloop
  have e6 := emitW_spec cap O (W 24) [false]
    (appendO (τ.setv (W 27) 0) O (W 24) (pre ++ (FinalPass.ListEval.levels J).flatMap f))
    (by simp [ho])
    (by rw [appendO_val, Function.update_self, wsetv_val_ne _ _ (hne (show (24 : Fin 30) ≠ 27 by decide)),
          List.length_append]
        simp only [List.length_cons, List.length_nil]
        omega)
  rw [appendO_append] at e6
  refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq hloop e6))))) ?_
    le_rfl, ?_⟩
  · rw [setv_eq_self h27, ← hlE]
  · unfold tplWBound
    simp only [List.length_cons, List.length_nil]
    omega

end Word

end NearCubicWires.WireExponent3_5.FinalPass.SymParts.Tmpl
