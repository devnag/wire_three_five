import Proof.Wire_3_5.Compiler.MachineTopLoad
import Proof.Wire_3_5.Primitive.Writers.C3WMarks
import Proof.Wire_3_5.Primitive.Writers.SparseNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Asm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimT.CarWM NearCubicWires.WireExponent3_5.PrimAsm.C3Marks
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm

/-! ## The twice-framed records -/

theorem frame_eq_marks (x : List Bool) : frame x = marks x ++ [false] := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [frame, marks] at ih ⊢; exact ih

/-- `marks (frame f) = marks (marks f) ++ [true, false]`. -/
theorem marks_frame (f : List Bool) : marks (frame f) = marks (marks f) ++ [true, false] := by
  rw [frame_eq_marks, marks_append]; rfl

theorem mm_unary (k : ℕ) : marks (marks (List.replicate k true)) = List.replicate (4 * k) true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, show 4 * (k + 1) = 4 + 4 * k by ring, List.replicate_add, ← ih]
    simp only [marks, List.flatMap_cons, List.flatMap_append, List.flatMap_nil]
    rfl

theorem mm_frames (ys : List (List Bool)) : marks (marks (ys.flatMap frame)) = ys.flatMap mm := by
  induction ys with
  | nil => rfl
  | cons y ys ih => rw [List.flatMap_cons, marks_append, marks_append, ih, marks_marks_frame, List.flatMap_cons]

theorem mm_stream (ys : List (List Bool)) :
    marks (marks (ys.flatMap frame ++ [false])) = ys.flatMap mm ++ [true, true, true, false] := by
  rw [marks_append, marks_append, mm_frames]; rfl

theorem reps4 (k : ℕ) : (List.replicate k [true, true, true, true]).flatten = List.replicate (4 * k) true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, show 4 * (k + 1) = 4 + 4 * k by ring, List.replicate_add]
    rfl

/-- **The twice-framed load record**: `frame (loadRec f₀ … f₁₀)` field by field. -/
theorem frame_loadRec (f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : List Bool) :
    frame (CompilerMachine.Top.loadRec f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10) =
      marks (marks f0) ++ [true, false] ++ (marks (marks f1) ++ [true, false] ++ (marks (marks f2) ++ [true, false] ++
      (marks (marks f3) ++ [true, false] ++ (marks (marks f4) ++ [true, false] ++ (marks (marks f5) ++ [true, false] ++
      (marks (marks f6) ++ [true, false] ++ (marks (marks f7) ++ [true, false] ++ (marks (marks f8) ++ [true, false] ++
      (marks (marks f9) ++ [true, false] ++ (marks (marks f10) ++ [true, false] ++ [false])))))))))) := by
  simp only [CompilerMachine.Top.loadRec, frame_eq_marks (List.append _ _), marks_append, marks_frame]
  rw [frame_eq_marks]
  simp only [marks_append, marks_frame, List.append_assoc]

/-! ## One field of a twice-framed record -/

variable {ns nr : ℕ} (cap : ℕ)

/-- A unary field from a register: `1^{4v}` then the field's end `[true, false]`. -/
def fieldR (O : Fin (ns + 1)) (r K T : Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR r K T) (.seq (repE O K [true, true, true, true]) (emitL O [true, false]))

theorem fieldR_spec (O : Fin (ns + 1)) (r K T : Fin nr) (hrK : r ≠ K) (hrT : r ≠ T) (hKT : K ≠ T) (v : ℕ)
    (σ : WState ns nr) (hr : σ.val r = v) (hK : σ.val K = 0) (hT : σ.val T = 0) (hv : v ≤ cap)
    (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (fieldR O r K T) σ τ (UnaryPow.sq cap + v * 21 + 20) ∧
      τ.st O = σ.st O ++ (List.replicate (4 * v) true ++ [true, false]) ∧ τ.sh O = (τ.st O).length ∧
      (∀ j, j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have h1 := SparseNum.copy1 cap r K T hrK hrT hKT v σ hr hK hT hv
  obtain ⟨σ2, s2, e2, e2h, o2, k2, r2, c2⟩ := repE_spec cap O K [true, true, true, true] v (σ.setv K v)
    (by simp) hv (by simp [hO])
  obtain ⟨τ, s3, e3, e3h, o3, v3, c3⟩ := emitL_facts cap O [true, false] σ2 e2h
  refine ⟨τ, WExec.mono (WExec.seq h1 (WExec.seq s2 s3)) (by simp; omega), ?_, e3h, ?_, ?_, ?_⟩
  · rw [e3, e2, reps4]; simp
  · intro j hj
    exact ⟨by rw [(o3 j hj).1, (o2 j hj).1]; rfl, by rw [(o3 j hj).2, (o2 j hj).2]; rfl⟩
  · rw [v3]; funext q
    by_cases hq : q = K
    · subst hq; rw [k2, hK]
    · rw [r2 q hq]; simp [Function.update_apply, hq]
  · rw [c3, c2]; rfl

/-- **The C3a′ input assembler**: `frame (c3aInput …)` field by field on the blank `AIN`, from `1^n` (`NT`), the gate
field (`GF`), the halves (`SF`), the flips' stream (`FF`) and the registers `w`, `h`, `Q'`. -/
def asmW (NT GF SF FF AIN : Fin (ns + 1)) (rw rh rQ K T : Fin nr) : WM ns nr :=
  .seq (m2U NT AIN) (.seq (emitL AIN [true, false])
  (.seq (m2F GF AIN) (.seq (emitL AIN [true, false])
  (.seq (m2F SF AIN) (.seq (emitL AIN [true, false])
  (.seq (fieldR AIN rw K T)
  (.seq (m2Fs FF AIN) (.seq (emitL AIN [true, false])
  (.seq (fieldR AIN rh K T)
  (.seq (fieldR AIN rQ K T)
  (emitL AIN [true, false, true, false, true, false, true, false, false])))))))))))

theorem asm_word (n w h Q : ℕ) (gy sy : List Bool) (ys : List (List Bool)) :
    List.replicate (4 * n) true ++ [true, false] ++ mm gy ++ [true, false] ++ mm sy ++ [true, false] ++
      (List.replicate (4 * w) true ++ [true, false]) ++ (ys.flatMap mm ++ [true, true, true, false]) ++
      [true, false] ++ (List.replicate (4 * h) true ++ [true, false]) ++
      (List.replicate (4 * Q) true ++ [true, false]) ++ [true, false, true, false, true, false, true, false, false] =
    frame (CompilerMachine.Top.loadRec (List.replicate n true) (frame gy) (frame sy)
        (List.replicate w true) (ys.flatMap frame ++ [false]) (List.replicate h true) (List.replicate Q true)
        [] [] [] []) := by
  rw [frame_loadRec, mm_unary, marks_marks_frame, marks_marks_frame, mm_unary, mm_stream, mm_unary, mm_unary]
  show _ = _ ++ [true, false] ++ (_ ++ [true, false] ++ (_ ++ [true, false] ++ (_ ++ [true, false] ++
    (_ ++ [true, false] ++ (_ ++ [true, false] ++ (_ ++ [true, false] ++ ([] ++ [true, false] ++
    ([] ++ [true, false] ++ ([] ++ [true, false] ++ ([] ++ [true, false] ++ [false]))))))))))
  simp only [List.append_assoc, List.nil_append, List.cons_append, List.singleton_append]

theorem asmW_spec (NT GF SF FF AIN : Fin (ns + 1)) (rw rh rQ K T : Fin nr)
    (hNA : NT ≠ AIN) (hGA : GF ≠ AIN) (hSA : SF ≠ AIN) (hFA : FF ≠ AIN) (hNG : NT ≠ GF) (hNS : NT ≠ SF)
    (hNF : NT ≠ FF) (hGS : GF ≠ SF) (hGF : GF ≠ FF) (hSF : SF ≠ FF)
    (hwK : rw ≠ K) (hwT : rw ≠ T) (hhK : rh ≠ K) (hhT : rh ≠ T) (hQK : rQ ≠ K) (hQT : rQ ≠ T) (hKT : K ≠ T)
    (n w h Q : ℕ) (gy sy : List Bool) (ys : List (List Bool)) (hne : ∀ y ∈ ys, y ≠ []) (σ : WState ns nr)
    (hN : σ.st NT = List.replicate n true) (hNh : σ.sh NT = 0) (hG : σ.st GF = frame gy) (hGh : σ.sh GF = 0)
    (hS : σ.st SF = frame sy) (hSh : σ.sh SF = 0) (hF : σ.st FF = ys.flatMap frame ++ [false]) (hFh : σ.sh FF = 0)
    (hA : σ.st AIN = []) (hAh : σ.sh AIN = 0) (hw : σ.val rw = w) (hh : σ.val rh = h) (hQ : σ.val rQ = Q)
    (hK : σ.val K = 0) (hT : σ.val T = 0) (hwc : w ≤ cap) (hhc : h ≤ cap) (hQc : Q ≤ cap) :
    ∃ τ, WExec cap (asmW NT GF SF FF AIN rw rh rQ K T) σ τ
        (3 * UnaryPow.sq cap + 25 * n + 50 * gy.length + 50 * sy.length + 60 * (ys.flatMap frame).length +
          21 * (w + h + Q) + 400) ∧
      τ.st AIN = frame (CompilerMachine.Top.loadRec (List.replicate n true) (frame gy) (frame sy)
        (List.replicate w true) (ys.flatMap frame ++ [false]) (List.replicate h true) (List.replicate Q true)
        [] [] [] []) ∧
      τ.sh AIN = (τ.st AIN).length ∧ τ.st NT = σ.st NT ∧ τ.st GF = σ.st GF ∧ τ.st SF = σ.st SF ∧
      τ.st FF = σ.st FF ∧
      (∀ j, j ≠ NT → j ≠ GF → j ≠ SF → j ≠ FF → j ≠ AIN → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hO0 : σ.sh AIN = (σ.st AIN).length := by rw [hAh, hA]; rfl
  obtain ⟨σ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := m2U_spec cap NT AIN hNA [] rfl n [] σ (by rw [hN]; simp)
    (by rw [hNh]; rfl) hO0
  obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap AIN [true, false] σ1 e1h
  have G2 : Same σ σ2 GF := (o1 GF (Ne.symm hNG) hGA).trans' (o2 GF hGA)
  obtain ⟨σ3, s3, e3, e3h, n3, n3h, o3, v3, c3⟩ := m2F_spec cap GF AIN hGA [] gy [] σ2 (by rw [G2.1, hG]; simp)
    (by rw [G2.2, hGh]; rfl) e2h
  obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emitL_facts cap AIN [true, false] σ3 e3h
  have S4 : Same σ σ4 SF := ((((o1 SF (Ne.symm hNS) hSA).trans' (o2 SF hSA)).trans'
    (o3 SF (Ne.symm hGS) hSA)).trans' (o4 SF hSA))
  obtain ⟨σ5, s5, e5, e5h, n5, n5h, o5, v5, c5⟩ := m2F_spec cap SF AIN hSA [] sy [] σ4 (by rw [S4.1, hS]; simp)
    (by rw [S4.2, hSh]; rfl) e4h
  obtain ⟨σ6, s6, e6, e6h, o6, v6, c6⟩ := emitL_facts cap AIN [true, false] σ5 e5h
  have V6 : σ6.val = σ.val := by rw [v6, v5, v4, v3, v2, v1]
  obtain ⟨σ7, s7, e7, e7h, o7, v7, c7⟩ := fieldR_spec cap AIN rw K T hwK hwT hKT w σ6 (by rw [V6, hw])
    (by rw [V6, hK]) (by rw [V6, hT]) hwc e6h
  have F7 : Same σ σ7 FF := ((((((o1 FF (Ne.symm hNF) hFA).trans' (o2 FF hFA)).trans' (o3 FF (Ne.symm hGF) hFA)).trans'
    (o4 FF hFA)).trans' (o5 FF (Ne.symm hSF) hFA)).trans' (o6 FF hFA)).trans' (o7 FF hFA)
  obtain ⟨σ8, s8, e8, e8h, n8, n8h, o8, v8, c8⟩ := m2Fs_spec cap FF AIN hFA ys [] [] σ7 hne
    (by rw [F7.1, hF]; simp) (by rw [F7.2, hFh]; rfl) e7h
  obtain ⟨σ9, s9, e9, e9h, o9, v9, c9⟩ := emitL_facts cap AIN [true, false] σ8 e8h
  have V9 : σ9.val = σ.val := by rw [v9, v8, v7, V6]
  obtain ⟨σ10, s10, e10, e10h, o10, v10, c10⟩ := fieldR_spec cap AIN rh K T hhK hhT hKT h σ9 (by rw [V9, hh])
    (by rw [V9, hK]) (by rw [V9, hT]) hhc e9h
  obtain ⟨σ11, s11, e11, e11h, o11, v11, c11⟩ := fieldR_spec cap AIN rQ K T hQK hQT hKT Q σ10
    (by rw [v10, V9, hQ]) (by rw [v10, V9, hK]) (by rw [v10, V9, hT]) hQc e10h
  obtain ⟨τ, s12, e12, e12h, o12, v12, c12⟩ := emitL_facts cap AIN
    [true, false, true, false, true, false, true, false, false] σ11 e11h
  have hsq := UnaryPow.sq_ge cap
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 s12)))))))))))
    (by simp only [List.length_cons, List.length_nil]; omega), ?_, e12h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, hA, ← asm_word]
    simp only [List.nil_append, List.append_assoc]
  · -- NT
    have := ((((((((((o2 NT hNA).trans' (o3 NT hNG hNA)).trans' (o4 NT hNA)).trans' (o5 NT hNS hNA)).trans'
      (o6 NT hNA)).trans' (o7 NT hNA)).trans' (o8 NT hNF hNA)).trans' (o9 NT hNA)).trans' (o10 NT hNA)).trans'
      (o11 NT hNA)).trans' (o12 NT hNA)
    rw [this.1, n1]
  · -- GF
    have := (((((((o4 GF hGA).trans' (o5 GF hGS hGA)).trans' (o6 GF hGA)).trans' (o7 GF hGA)).trans'
      (o8 GF hGF hGA)).trans' (o9 GF hGA)).trans' ((o10 GF hGA).trans' (o11 GF hGA))).trans' (o12 GF hGA)
    rw [this.1, n3, G2.1]
  · -- SF
    have := (((((o6 SF hSA).trans' (o7 SF hSA)).trans' (o8 SF hSF hSA)).trans' (o9 SF hSA)).trans'
      ((o10 SF hSA).trans' (o11 SF hSA))).trans' (o12 SF hSA)
    rw [this.1, n5, S4.1]
  · -- FF
    have := ((o9 FF hFA).trans' ((o10 FF hFA).trans' (o11 FF hFA))).trans' (o12 FF hFA)
    rw [this.1, n8, F7.1]
  · intro j h1 h2 h3 h4 h5
    exact (((((((((((o1 j h1 h5).trans' (o2 j h5)).trans' (o3 j h2 h5)).trans' (o4 j h5)).trans' (o5 j h3 h5)).trans'
      (o6 j h5)).trans' (o7 j h5)).trans' (o8 j h4 h5)).trans' (o9 j h5)).trans' (o10 j h5)).trans' (o11 j h5)).trans'
      (o12 j h5)
  · rw [v12, v11, v10, V9]
  · rw [c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2, c1]

/-! ## Loops over framed words -/

theorem skip_facts (W : Fin (ns + 1)) (pre rest y : List Bool) (σ : WState ns nr)
    (hW : σ.st W = pre ++ (frame y ++ rest)) (hWh : σ.sh W = pre.length) :
    ∃ τ, WExec cap (skipFrameW W) σ τ (5 * y.length + 3) ∧ τ.st W = σ.st W ∧
      τ.sh W = pre.length + (frame y).length ∧ (∀ j, j ≠ W → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell :=
  ⟨_, skipFrame_spec cap W pre rest y σ hW hWh, rfl, by simp, fun j hj => ⟨rfl, by simp [Function.update_of_ne hj]⟩,
    rfl, rfl⟩

theorem flatten_rep1 (g : ℕ) : (List.replicate g [true]).flatten = List.replicate g true := by
  induction g with
  | zero => rfl
  | succ g ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl

/-- **The atoms' ruler**: `g` ones per flip pattern of the stream `FF` (the pool's atoms, flip-major). -/
def atomsW (FF AT : Fin (ns + 1)) (rg K T : Fin nr) : WM ns nr :=
  .whs FF (.seq (skipFrameW FF) (.seq (FinalPass.Hash4.wcopyR rg K T) (repE AT K [true])))

theorem atomsW_spec (FF AT : Fin (ns + 1)) (rg K T : Fin nr) (hFA : FF ≠ AT) (hgK : rg ≠ K) (hgT : rg ≠ T)
    (hKT : K ≠ T) (g : ℕ) (hgc : g ≤ cap) (rest : List Bool) :
    ∀ (ys : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ y ∈ ys, y ≠ []) →
      σ.st FF = pre ++ (ys.flatMap frame ++ false :: rest) → σ.sh FF = pre.length → σ.sh AT = (σ.st AT).length →
      σ.val rg = g → σ.val K = 0 → σ.val T = 0 →
      ∃ τ, WExec cap (atomsW FF AT rg K T) σ τ
          (5 * (ys.flatMap frame).length + ys.length * (UnaryPow.sq cap + 9 * g + 30) + 1) ∧
        τ.st AT = σ.st AT ++ List.replicate (ys.length * g) true ∧ τ.sh AT = (τ.st AT).length ∧
        τ.st FF = σ.st FF ∧ τ.sh FF = pre.length + (ys.flatMap frame).length ∧
        (∀ j, j ≠ FF → j ≠ AT → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, _, hF, hFh, hA, _, _, _ => by
    have hz : wbit σ FF = false := by simp only [wbit, hF, hFh, List.flatMap_nil, List.nil_append, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hA, rfl, by simp [hFh], fun _ _ _ => ⟨rfl, rfl⟩,
      rfl, rfl⟩
  | y :: ys, pre, σ, hne, hF, hFh, hA, hg, hK, hT => by
    have hy : y ≠ [] := hne y List.mem_cons_self
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hy
    have hAF : AT ≠ FF := fun e => hFA e.symm
    have hw : wbit σ FF = true := by
      simp only [wbit, hF, hFh, List.flatMap_cons, rd_at]; simp [frame]
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := skip_facts cap FF pre (ys.flatMap frame ++ false :: rest) (b :: bs) σ
      (by rw [hF]; simp) hFh
    have h2 := SparseNum.copy1 cap rg K T hgK hgT hKT g σ1 (by rw [v1, hg]) (by rw [v1, hK]) (by rw [v1, hT]) hgc
    have A1 := o1 AT hAF
    obtain ⟨σ3, s3, e3, e3h, o3, k3, r3, c3⟩ := repE_spec cap AT K [true] g (σ1.setv K g) (by simp) hgc
      (by simp [A1.1, A1.2, hA])
    have V3 : σ3.val = σ.val := by
      funext q
      by_cases hq : q = K
      · subst hq; rw [k3, hK]
      · rw [r3 q hq]; simp [Function.update_apply, hq, v1]
    have F3 := o3 FF hFA
    obtain ⟨τ, s4, e4, e4h, n4, n4h, o4, v4, c4⟩ := atomsW_spec FF AT rg K T hFA hgK hgT hKT g hgc rest ys
      (pre ++ frame (b :: bs)) σ3 (fun z hz => hne z (List.mem_cons_of_mem _ hz))
      (by rw [show σ3.st FF = σ1.st FF from F3.1, n1, hF]; simp)
      (by rw [show σ3.sh FF = σ1.sh FF from F3.2, n1h]; simp) e3h (by rw [V3, hg]) (by rw [V3, hK]) (by rw [V3, hT])
    have hsq := UnaryPow.sq_ge cap
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq h2 s3)) s4) ?_, ?_, e4h, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.length_append, frame_length, List.length_cons, List.length_nil]
      have e : (ys.length + 1) * (UnaryPow.sq cap + 9 * g + 30) =
          ys.length * (UnaryPow.sq cap + 9 * g + 30) + (UnaryPow.sq cap + 9 * g + 30) := by ring
      rw [e]
      omega
    · rw [e4, e3, show (σ1.setv K g).st AT = σ.st AT by simp [A1.1], flatten_rep1]
      simp only [List.length_cons, List.append_assoc]
      rw [← List.replicate_add]; congr 1; rw [Nat.succ_mul, Nat.add_comm]
    · rw [n4, F3.1]; exact n1.trans rfl
    · rw [n4h]; simp [List.flatMap_cons]; omega
    · intro j h1 h2
      have := o1 j h1
      exact ((this.trans' ⟨rfl, rfl⟩).trans' (o3 j h2)).trans' (o4 j h1 h2)
    · rw [v4, V3]
    · rw [c4, c3]; exact c1

/-- Skip framed words up to the stream's `false`, emitting one `true` on `SH` per word. -/
def cntW (A SH : Fin (ns + 1)) : WM ns nr := .whs A (.seq (skipFrameW A) (PrimT.emitW SH true))

theorem cntW_spec (A SH : Fin (ns + 1)) (hAS : A ≠ SH) (rest : List Bool) :
    ∀ (ys : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ y ∈ ys, y ≠ []) →
      σ.st A = pre ++ (ys.flatMap frame ++ false :: rest) → σ.sh A = pre.length → σ.sh SH = (σ.st SH).length →
      ∃ τ, WExec cap (cntW A SH) σ τ (10 * (ys.flatMap frame).length + 1) ∧
        τ.st SH = σ.st SH ++ List.replicate ys.length true ∧ τ.sh SH = (τ.st SH).length ∧
        τ.st A = σ.st A ∧ τ.sh A = pre.length + (ys.flatMap frame).length ∧
        (∀ j, j ≠ A → j ≠ SH → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, _, hA, hAh, hS => by
    have hz : wbit σ A = false := by simp only [wbit, hA, hAh, List.flatMap_nil, List.nil_append, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hS, rfl, by simp [hAh], fun _ _ _ => ⟨rfl, rfl⟩,
      rfl, rfl⟩
  | y :: ys, pre, σ, hne, hA, hAh, hS => by
    have hy : y ≠ [] := hne y List.mem_cons_self
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hy
    have hSA : SH ≠ A := fun e => hAS e.symm
    have hw : wbit σ A = true := by simp only [wbit, hA, hAh, List.flatMap_cons, rd_at]; simp [frame]
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := skip_facts cap A pre (ys.flatMap frame ++ false :: rest) (b :: bs) σ
      (by rw [hA]; simp) hAh
    have S1 := o1 SH hSA
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap SH true σ1 (by rw [S1.1, S1.2, hS])
    have A2 := o2 A hAS
    obtain ⟨τ, s3, e3, e3h, n3, n3h, o3, v3, c3⟩ := cntW_spec A SH hAS rest ys (pre ++ frame (b :: bs)) σ2
      (fun z hz => hne z (List.mem_cons_of_mem _ hz)) (by rw [A2.1, n1, hA]; simp) (by rw [A2.2, n1h]; simp) e2h
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, ?_, e3h, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.length_append, frame_length, List.length_cons] at *
      omega
    · rw [e3, e2, S1.1]; simp [List.replicate_succ]
    · rw [n3, A2.1, n1]
    · rw [n3h]; simp [List.flatMap_cons]; omega
    · intro j h1 h2
      exact ((o1 j h1).trans' (o2 j h2)).trans' (o3 j h1 h2)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

/-- The atoms' stream: every atom's framed words, then `false`. -/
def atomsStream (atoms : List (List (List Bool))) : List Bool :=
  atoms.flatMap fun E => E.flatMap frame ++ [false]

/-- **The children's ruler**: one `true` on `SH` per framed word of the atoms' stream at `A`, atom by atom along the
ruler `AT`. -/
def shW (AT A SH : Fin (ns + 1)) : WM ns nr := .whs AT (.seq (.fwd AT) (.seq (cntW A SH) (.fwd A)))

theorem shW_spec (AT A SH : Fin (ns + 1)) (hTA : AT ≠ A) (hTS : AT ≠ SH) (hAS : A ≠ SH) (rest : List Bool) :
    ∀ (atoms : List (List (List Bool))) (preT preA : List Bool) (σ : WState ns nr),
      (∀ E ∈ atoms, ∀ y ∈ E, y ≠ []) →
      σ.st AT = preT ++ List.replicate atoms.length true → σ.sh AT = preT.length →
      σ.st A = preA ++ (atomsStream atoms ++ rest) → σ.sh A = preA.length → σ.sh SH = (σ.st SH).length →
      ∃ τ, WExec cap (shW AT A SH) σ τ (11 * (atomsStream atoms).length + 1) ∧
        τ.st SH = σ.st SH ++ List.replicate (atoms.map List.length).sum true ∧ τ.sh SH = (τ.st SH).length ∧
        τ.st AT = σ.st AT ∧ τ.sh AT = preT.length + atoms.length ∧
        τ.st A = σ.st A ∧ τ.sh A = preA.length + (atomsStream atoms).length ∧
        (∀ j, j ≠ AT → j ≠ A → j ≠ SH → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], preT, preA, σ, _, hT, hTh, hA, hAh, hS => by
    have hz : wbit σ AT = false := by
      simp only [wbit, hT, hTh, List.length_nil, List.replicate_zero, List.append_nil]
      unfold readTapeBit; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hS, rfl, by simp [hTh], rfl, by simp [hAh, atomsStream],
      fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | E :: atoms, preT, preA, σ, hne, hT, hTh, hA, hAh, hS => by
    have hAT : A ≠ AT := fun e => hTA e.symm
    have hST : SH ≠ AT := fun e => hTS e.symm
    have hSA : SH ≠ A := fun e => hAS e.symm
    have hw : wbit σ AT = true := by
      simp only [wbit, hT, hTh, List.length_cons, List.replicate_succ, rd_at]; simp
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap AT σ
    have A1 := o1 A hAT
    have S1 := o1 SH hST
    obtain ⟨σ2, s2, e2, e2h, n2, n2h, o2, v2, c2⟩ := cntW_spec cap A SH hAS (atomsStream atoms ++ rest) E preA σ1
      (hne E List.mem_cons_self) (by rw [A1.1, hA]; simp [atomsStream]) (by rw [A1.2, hAh])
      (by rw [S1.1, S1.2, hS])
    obtain ⟨σ3, s3, n3, n3h, o3, v3, c3⟩ := fwd_facts cap A σ2
    have T3 := (o2 AT hTA hTS).trans' (o3 AT hTA)
    have S3 := o3 SH hSA
    obtain ⟨τ, s4, e4, e4h, t4, t4h, n4, n4h, o4, v4, c4⟩ := shW_spec AT A SH hTA hTS hAS rest atoms (preT ++ [true])
      (preA ++ (E.flatMap frame ++ [false])) σ3 (fun F hF => hne F (List.mem_cons_of_mem _ hF))
      (by rw [T3.1, n1, hT]; simp [List.replicate_succ]) (by rw [T3.2, n1h, hTh]; simp)
      (by rw [n3, n2, A1.1, hA]; simp [atomsStream]) (by rw [n3h, n2h]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      (by rw [S3.1, S3.2, e2h])
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) s4) ?_, ?_, e4h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hl : (atomsStream (E :: atoms)).length = (E.flatMap frame).length + 1 + (atomsStream atoms).length := by
        simp only [atomsStream, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      rw [hl]
      omega
    · rw [e4, S3.1, e2, S1.1, List.append_assoc, ← List.replicate_add]
      simp only [List.map_cons, List.sum_cons]
    · rw [t4, T3.1, n1]
    · rw [t4h]; simp; omega
    · rw [n4, n3, n2, A1.1]
    · rw [n4h]; simp [atomsStream]; omega
    · intro j h1 h2 h3
      exact (((o1 j h1).trans' (o2 j h2 h3)).trans' (o3 j h2)).trans' (o4 j h1 h2 h3)
    · rw [v4, v3, v2, v1]
    · rw [c4, c3, c2, c1]

/-- **The children table, twice framed**: every atom's `marks (marks (E.flatMap frame ++ [false]))` on `O`, atom by
atom along the ruler `AT`. -/
def f7W (AT A O : Fin (ns + 1)) : WM ns nr := .whs AT (.seq (.fwd AT) (m2Fs A O))

theorem f7W_spec (AT A O : Fin (ns + 1)) (hTA : AT ≠ A) (hTO : AT ≠ O) (hAO : A ≠ O) (rest : List Bool) :
    ∀ (atoms : List (List (List Bool))) (preT preA : List Bool) (σ : WState ns nr),
      (∀ E ∈ atoms, ∀ y ∈ E, y ≠ []) →
      σ.st AT = preT ++ List.replicate atoms.length true → σ.sh AT = preT.length →
      σ.st A = preA ++ (atomsStream atoms ++ rest) → σ.sh A = preA.length → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (f7W AT A O) σ τ (70 * (atomsStream atoms).length + 1) ∧
        τ.st O = σ.st O ++ atoms.flatMap (fun E => E.flatMap mm ++ [true, true, true, false]) ∧
        τ.sh O = (τ.st O).length ∧ τ.st AT = σ.st AT ∧ τ.sh AT = preT.length + atoms.length ∧
        τ.st A = σ.st A ∧ τ.sh A = preA.length + (atomsStream atoms).length ∧
        (∀ j, j ≠ AT → j ≠ A → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], preT, preA, σ, _, hT, hTh, hA, hAh, hO => by
    have hz : wbit σ AT = false := by
      simp only [wbit, hT, hTh, List.length_nil, List.replicate_zero, List.append_nil]
      unfold readTapeBit; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hO, rfl, by simp [hTh], rfl, by simp [hAh, atomsStream],
      fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | E :: atoms, preT, preA, σ, hne, hT, hTh, hA, hAh, hO => by
    have hAT : A ≠ AT := fun e => hTA e.symm
    have hOT : O ≠ AT := fun e => hTO e.symm
    have hw : wbit σ AT = true := by
      simp only [wbit, hT, hTh, List.length_cons, List.replicate_succ, rd_at]; simp
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap AT σ
    have A1 := o1 A hAT
    have O1 := o1 O hOT
    obtain ⟨σ2, s2, e2, e2h, n2, n2h, o2, v2, c2⟩ := m2Fs_spec cap A O hAO E preA (atomsStream atoms ++ rest) σ1
      (hne E List.mem_cons_self) (by rw [A1.1, hA]; simp [atomsStream]) (by rw [A1.2, hAh])
      (by rw [O1.1, O1.2, hO])
    have T2 := o2 AT hTA hTO
    obtain ⟨τ, s4, e4, e4h, t4, t4h, n4, n4h, o4, v4, c4⟩ := f7W_spec AT A O hTA hTO hAO rest atoms (preT ++ [true])
      (preA ++ (E.flatMap frame ++ [false])) σ2 (fun F hF => hne F (List.mem_cons_of_mem _ hF))
      (by rw [T2.1, n1, hT]; simp [List.replicate_succ]) (by rw [T2.2, n1h, hTh]; simp)
      (by rw [n2, A1.1, hA]; simp [atomsStream]) (by rw [n2h]; simp only [List.length_append, List.length_cons, List.length_nil]; omega) e2h
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s4) ?_, ?_, e4h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hl : (atomsStream (E :: atoms)).length = (E.flatMap frame).length + 1 + (atomsStream atoms).length := by
        simp only [atomsStream, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      rw [hl]
      omega
    · rw [e4, e2, O1.1]; simp
    · rw [t4, T2.1, n1]
    · rw [t4h]; simp; omega
    · rw [n4, n2, A1.1]
    · rw [n4h]; simp [atomsStream]; omega
    · intro j h1 h2 h3
      exact ((o1 j h1).trans' (o2 j h2 h3)).trans' (o4 j h1 h2 h3)
    · rw [v4, v2, v1]
    · rw [c4, c2, c1]

/-! ## Counting blocks, skipping words, the header's numbers -/

/-- **Count the blocks** of `D` cells (each starting with `true`) before the stream's `false`: `C += #blocks`. -/
def colsW (S : Fin (ns + 1)) (rD K T C : Fin nr) : WM ns nr :=
  .whs S (.seq (FinalPass.Hash4.wcopyR rD K T) (.seq (fwdN S K) (.inc C)))

theorem colsW_spec (S : Fin (ns + 1)) (rD K T C : Fin nr) (hDK : rD ≠ K) (hDT : rD ≠ T) (hKT : K ≠ T) (hDC : rD ≠ C)
    (hKC : K ≠ C) (hTC : T ≠ C) (D : ℕ) (hD : D ≤ cap) (rest : List Bool) :
    ∀ (bl : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ b ∈ bl, b.length = D ∧ b.headD false = true) →
      σ.st S = pre ++ (bl.flatten ++ false :: rest) → σ.sh S = pre.length → σ.val rD = D → σ.val K = 0 →
      σ.val T = 0 → σ.val C + bl.length < cap + 1 →
      ∃ τ, WExec cap (colsW S rD K T C) σ τ (bl.length * (UnaryPow.sq cap + 6 * D + 10) + 1) ∧ τ.st = σ.st ∧
        τ.sh S = pre.length + bl.length * D ∧ (∀ j, j ≠ S → τ.sh j = σ.sh j) ∧ τ.val C = σ.val C + bl.length ∧
        (∀ r, r ≠ C → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | [], pre, σ, _, hS, hSh, _, _, _, _ => by
    have hz : wbit σ S = false := by simp only [wbit, hS, hSh, List.flatten_nil, List.nil_append, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by simp [hSh], fun _ _ => rfl, by simp, fun _ _ => rfl, rfl⟩
  | b :: bl, pre, σ, hbl, hS, hSh, hDv, hK, hT, hC => by
    obtain ⟨hbD, hbh⟩ := hbl b List.mem_cons_self
    have hC' : σ.val C + bl.length + 1 < cap + 1 := by simpa [Nat.add_assoc] using hC
    have hw : wbit σ S = true := by
      simp only [wbit, hS, hSh, List.flatten_cons, rd_at]
      cases b with
      | nil => simp at hbh
      | cons c t => simpa using hbh
    have h1 := SparseNum.copy1 cap rD K T hDK hDT hKT D σ hDv hK hT hD
    obtain ⟨σ2, s2, t2, h2, o2, k2, r2, c2⟩ := fwdN_spec cap S K D (σ.setv K D) (by simp) hD
    have h3 := WExec.inc (cap := cap) C σ2 (by rw [r2 C (Ne.symm hKC)]; simp only [WState.setv_val, Function.update_apply, Ne.symm hKC, if_false]; omega)
    set σ3 := σ2.setv C (σ2.val C + 1) with hσ3
    have hst3 : σ3.st = σ.st := by rw [hσ3]; simp [t2]
    obtain ⟨τ, s4, t4, h4, o4, c4v, r4, c4⟩ := colsW_spec S rD K T C hDK hDT hKT hDC hKC hTC D hD rest bl
      (pre ++ b) σ3 (fun z hz => hbl z (List.mem_cons_of_mem _ hz))
      (by rw [hst3, hS]; simp)
      (by rw [hσ3]; simp [h2, hSh, hbD]) (by rw [hσ3]; simp [Function.update_apply, hDC, r2 rD hDK]; simp [hDv])
      (by rw [hσ3]; simp [Function.update_apply, hKC, k2]) (by rw [hσ3]; simp [Function.update_apply, hTC, r2 T (Ne.symm hKT), Ne.symm hKT, hT])
      (by rw [hσ3]; simp only [WState.setv_val, Function.update_self]; rw [r2 C (Ne.symm hKC)]; simp only [WState.setv_val, Function.update_apply, Ne.symm hKC, if_false]; omega)
    have hsq := UnaryPow.sq_ge cap
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq h1 (WExec.seq s2 h3)) s4) ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      have e : (bl.length + 1) * (UnaryPow.sq cap + 6 * D + 10) =
          bl.length * (UnaryPow.sq cap + 6 * D + 10) + (UnaryPow.sq cap + 6 * D + 10) := by ring
      rw [e]; omega
    · rw [t4, hst3]
    · rw [h4]; simp [hbD]; ring
    · intro j hj
      rw [o4 j hj, hσ3]; simp [o2 j hj]
    · rw [c4v, hσ3]; simp only [WState.setv_val, Function.update_self, List.length_cons]; rw [r2 C (Ne.symm hKC)]
      simp only [WState.setv_val, Function.update_apply, Ne.symm hKC, if_false]; omega
    · intro r hr
      rw [r4 r hr, hσ3]
      simp only [WState.setv_val, Function.update_apply, hr, if_false]
      by_cases hrK : r = K
      · subst hrK; rw [k2, hK]
      · rw [r2 r hrK]; simp [Function.update_apply, hrK]
    · rw [c4, hσ3]; simp [c2]

/-- Skip framed words up to the stream's `false`, then past it. -/
def skipFs (S : Fin (ns + 1)) : WM ns nr := .seq (.whs S (skipFrameW S)) (.fwd S)

theorem skipFsLoop (S : Fin (ns + 1)) (rest : List Bool) :
    ∀ (ys : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ y ∈ ys, y ≠ []) →
      σ.st S = pre ++ (ys.flatMap frame ++ false :: rest) → σ.sh S = pre.length →
      WExec cap (.whs S (skipFrameW S)) σ (σ.seth S (pre.length + (ys.flatMap frame).length))
        (5 * (ys.flatMap frame).length + 1)
  | [], pre, σ, _, hS, hSh => by
    have hz : wbit σ S = false := by simp only [wbit, hS, hSh, List.flatMap_nil, List.nil_append, rd_at]; rfl
    have e : σ.seth S (pre.length + (([] : List (List Bool)).flatMap frame).length) = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, ← hSh, wseth_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
  | y :: ys, pre, σ, hne, hS, hSh => by
    have hy : y ≠ [] := hne y List.mem_cons_self
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hy
    have hw : wbit σ S = true := by simp only [wbit, hS, hSh, List.flatMap_cons, rd_at]; simp [frame]
    have s1 := skipFrame_spec cap S pre (ys.flatMap frame ++ false :: rest) (b :: bs) σ (by rw [hS]; simp) hSh
    have s2 := skipFsLoop S rest ys (pre ++ frame (b :: bs)) (σ.seth S (pre.length + (frame (b :: bs)).length))
      (fun z hz => hne z (List.mem_cons_of_mem _ hz)) (by simp [hS]) (by simp)
    rw [wseth_seth] at s2
    have e : (pre ++ frame (b :: bs)).length + (ys.flatMap frame).length =
        pre.length + (((b :: bs) :: ys).flatMap frame).length := by simp [List.flatMap_cons]; omega
    rw [e] at s2
    refine WExec.mono (WExec.whsT hw s1 s2) ?_
    simp only [List.flatMap_cons, List.length_append, frame_length, List.length_cons]
    omega

theorem skipFs_spec (S : Fin (ns + 1)) (rest : List Bool) (ys : List (List Bool)) (pre : List Bool)
    (σ : WState ns nr) (hne : ∀ y ∈ ys, y ≠ []) (hS : σ.st S = pre ++ (ys.flatMap frame ++ false :: rest))
    (hSh : σ.sh S = pre.length) :
    WExec cap (skipFs S) σ (σ.seth S (pre.length + (ys.flatMap frame).length + 1))
      (5 * (ys.flatMap frame).length + 3) := by
  have s1 := skipFsLoop cap S rest ys pre σ hne hS hSh
  have s2 := WExec.fwd (cap := cap) S (σ.seth S (pre.length + (ys.flatMap frame).length))
  rw [wseth_seth] at s2
  simp only [WState.seth_sh, Function.update_self] at s2
  exact WExec.mono (WExec.seq s1 s2) (by omega)

/-! ## The header's field: `frame (natWord d ++ natWord p)` -/

/-- Write `marks (natWord d)` (`d = R 0`), `marks (natWord p)` (`p = R' 0`) and `false` on `NW` (`R`, `R'` share
their scratch and counter registers `1 … 7`). -/
def nw9W (NW : Fin (ns + 1)) (R R' : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (WriteNat.writeNatM NW R) (.seq (WriteNat.writeNatM NW R') (PrimT.emitW NW false))

theorem nw9W_spec (NW : Fin (ns + 1)) (R R' : Fin 8 ↪ Fin nr) (hsh : ∀ i : Fin 8, i ≠ 0 → R' i = R i)
    (d p : ℕ) (σ : WState ns nr) (hd : σ.val (R 0) = d) (hp : σ.val (R' 0) = p)
    (hR : ∀ i : Fin 8, i ≠ 0 → σ.val (R i) = 0) (hN : σ.sh NW = (σ.st NW).length)
    (hcap : d + p + 20 * (d + p + 2) ≤ cap) :
    ∃ τ, WExec cap (nw9W NW R R') σ τ ((d + p + 12) * (200 * (d + p) + 400) + 10) ∧
      τ.st NW = σ.st NW ++ frame (RepairRepresentation.natWord d ++ RepairRepresentation.natWord p) ∧
      τ.sh NW = (τ.st NW).length ∧ (∀ j, j ≠ NW → Same σ τ j) ∧
      (∀ r, r ≠ R 7 → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hRne : ∀ {i j : Fin 8}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have h0R : ∀ i : Fin 8, i ≠ 0 → R' 0 ≠ R i := by
    intro i hi e
    have := R'.injective (e.trans (hsh i hi).symm)
    exact hi this.symm
  have hnd := CopyNat.natBitLength_le_self_succ d
  have hnp := CopyNat.natBitLength_le_self_succ p
  have h1 := WriteNat.writeNatM_spec cap NW R σ (hR 1 (by decide)) (hR 2 (by decide)) (hR 3 (by decide))
    (hR 4 (by decide)) (hR 5 (by decide)) (hR 6 (by decide)) hN (by rw [hd, hR 7 (by decide)]; omega)
  rw [hd] at h1
  set u := RepairOrdinary.Streaming.marks (RepairRepresentation.natWord d) with hu
  set σ1 := WriteNat.appendO σ NW (R 7) u with hσ1
  have hul : u.length = 2 * (RepairRepresentation.natWord d).length := by simp [hu]
  have hnwd : (RepairRepresentation.natWord d).length ≤ 2 * d + 4 := by
    have := ParseNat.natWord_length d; omega
  have hv1 : ∀ r, r ≠ R 7 → σ1.val r = σ.val r := by
    intro r hr; simp [σ1, Function.update_apply, hr]
  have h2 := WriteNat.writeNatM_spec cap NW R' σ1
    (by rw [hsh 1 (by decide), hv1 _ (hRne (by decide)), hR 1 (by decide)])
    (by rw [hsh 2 (by decide), hv1 _ (hRne (by decide)), hR 2 (by decide)])
    (by rw [hsh 3 (by decide), hv1 _ (hRne (by decide)), hR 3 (by decide)])
    (by rw [hsh 4 (by decide), hv1 _ (hRne (by decide)), hR 4 (by decide)])
    (by rw [hsh 5 (by decide), hv1 _ (hRne (by decide)), hR 5 (by decide)])
    (by rw [hsh 6 (by decide), hv1 _ (hRne (by decide)), hR 6 (by decide)])
    (by simp [σ1, hN])
    (by rw [hv1 _ (h0R 7 (by decide)), hp, hsh 7 (by decide)]; simp [σ1, hR 7 (by decide)]; omega)
  rw [hv1 _ (h0R 7 (by decide)), hp] at h2
  set v := RepairOrdinary.Streaming.marks (RepairRepresentation.natWord p) with hv
  set σ2 := WriteNat.appendO σ1 NW (R' 7) v with hσ2
  obtain ⟨τ, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap NW false σ2 (by simp [σ2, σ1, hN]; omega)
  refine ⟨τ, WExec.mono (WExec.seq h1 (WExec.seq h2 s3)) ?_, ?_, e3h, ?_, ?_, ?_⟩
  · have e1 : (natBitLength d + 10) * (100 * d + 200) ≤ (d + p + 12) * (100 * (d + p) + 200) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e2 : (natBitLength p + 10) * (100 * p + 200) ≤ (d + p + 12) * (100 * (d + p) + 200) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  · rw [e3]; simp [σ2, σ1, hu, hv, frame_eq_marks]
  · intro j hj
    have := o3 j hj
    exact ⟨by rw [this.1]; simp [σ2, σ1, Function.update_apply, hj], by rw [this.2]; simp [σ2, σ1, Function.update_apply, hj]⟩
  · intro r hr
    rw [v3]
    simp only [σ2, σ1, WriteNat.appendO_val, Function.update_apply]
    rw [hsh 7 (by decide)]
    simp [hr]
  · rw [c3]; simp [σ2, σ1]

end NearCubicWires.WireExponent3_5.PrimAsm.C3Asm
