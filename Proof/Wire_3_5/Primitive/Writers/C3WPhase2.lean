import Proof.Wire_3_5.Primitive.Writers.C3WPhase1

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Phase
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimT.CarWM NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.C3Marks NearCubicWires.WireExponent3_5.PrimAsm.C3Asm
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)

/-! ## The words of `frame PRE` and `frame POST` -/

/-- A unary field `1^k`, framed and marked: `marks (frame 1^k)`. -/
def uf (k : ℕ) : List Bool := List.replicate (4 * k) true ++ [true, false]

/-- The children table's stream, marked twice. -/
def atomsMM (atoms : List (List (List Bool))) : List Bool :=
  atoms.flatMap fun E => E.flatMap mm ++ [true, true, true, false]

/-- **`frame PRE`**, field by field. -/
def preOut (Q S m h p wd : ℕ) (ys : List (List Bool)) (atoms : List (List (List Bool))) : List Bool :=
  uf Q ++ uf S ++ uf m ++ uf h ++ uf p ++ uf wd ++
    (ys.flatMap mm ++ [true, false] ++ atomsMM atoms ++ [true, false, false])

/-- **`frame POST`**, field by field. -/
def postOut (y9 y10 : List Bool) : List Bool := mm y9 ++ [true, false] ++ mm y10 ++ [true, false, false]

theorem mm_atoms (atoms : List (List (List Bool))) : marks (marks (atomsStream atoms)) = atomsMM atoms := by
  induction atoms with
  | nil => rfl
  | cons E atoms ih =>
    simp only [atomsStream, atomsMM, List.flatMap_cons, marks_append, mm_frames, List.append_assoc] at ih ⊢
    rw [ih]
    rfl

theorem pre_word (Q S m h p wd : ℕ) (ys : List (List Bool)) (atoms : List (List (List Bool))) :
    frame ([List.replicate Q true, List.replicate S true, List.replicate m true, List.replicate h true,
      List.replicate p true, List.replicate wd true, ys.flatMap frame, atomsStream atoms].flatMap frame) =
      preOut Q S m h p wd ys atoms := by
  rw [frame_eq_marks]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, marks_append, marks_frame, mm_unary, mm_frames,
    mm_atoms, preOut, uf, List.append_assoc, List.cons_append, List.nil_append]

theorem post_word (y9 y10 : List Bool) : frame ([frame y9, frame y10].flatMap frame) = postOut y9 y10 := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [frame_eq_marks (frame (frame y9) ++ frame (frame y10)), marks_append, marks_frame (frame y9),
    marks_frame (frame y10), marks_marks_frame, marks_marks_frame]
  simp only [postOut, List.append_assoc, List.cons_append, List.nil_append]

variable (cap : ℕ)

/-! ## The second program, part b: `frame PRE` and `frame POST` -/

/-- The unary fields of `PRE`: `Q'`, the shape's label count (from `sSH`), `m`, `h`, `p + 1`, the width. -/
def wPre1 : WM CN CR :=
  .seq (fieldR sPRE rQ rK rT) (.seq (m2U sSH sPRE) (.seq (emitL sPRE [true, false]) (.seq (fieldR sPRE rm rK rT)
    (.seq (fieldR sPRE rh rK rT) (.seq (fieldR sPRE rP1 rK rT) (fieldR sPRE rw rK rT))))))

theorem wPre1_spec (σ : WState CN CR) (S Q m h p wd : ℕ) (hS : σ.st sSH = List.replicate S true)
    (hSh : σ.sh sSH = 0) (hO : σ.sh sPRE = (σ.st sPRE).length) (hQ : σ.val rQ = Q) (hm : σ.val rm = m)
    (hh : σ.val rh = h) (hp : σ.val rP1 = p) (hw : σ.val rw = wd) (hK : σ.val rK = 0) (hT : σ.val rT = 0)
    (hcap : Q + m + h + p + wd ≤ cap) :
    ∃ τ, WExec cap wPre1 σ τ (5 * UnaryPow.sq cap + 21 * (Q + m + h + p + wd) + 25 * S + 200) ∧
      τ.st sPRE = σ.st sPRE ++ (uf Q ++ uf S ++ uf m ++ uf h ++ uf p ++ uf wd) ∧
      τ.sh sPRE = (τ.st sPRE).length ∧ (∀ j, j ≠ sPRE → τ.st j = σ.st j) ∧
      (∀ j, j ≠ sPRE → j ≠ sSH → τ.sh j = σ.sh j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hPS : sSH ≠ sPRE := by decide
  obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := fieldR_spec cap sPRE rQ rK rT (by decide) (by decide) (by decide) Q σ hQ
    hK hT (by omega) hO
  have S1 := o1 sSH hPS
  obtain ⟨σ2, s2, e2, e2h, n2, n2h, o2, v2, c2⟩ := m2U_spec cap sSH sPRE hPS [] rfl S [] σ1
    (by rw [S1.1, hS]; simp) (by rw [S1.2, hSh]; rfl) e1h
  obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emitL_facts cap sPRE [true, false] σ2 e2h
  have V3 : σ3.val = σ.val := by rw [v3, v2, v1]
  obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := fieldR_spec cap sPRE rm rK rT (by decide) (by decide) (by decide) m σ3
    (by rw [V3, hm]) (by rw [V3, hK]) (by rw [V3, hT]) (by omega) e3h
  obtain ⟨σ5, s5, e5, e5h, o5, v5, c5⟩ := fieldR_spec cap sPRE rh rK rT (by decide) (by decide) (by decide) h σ4
    (by rw [v4, V3, hh]) (by rw [v4, V3, hK]) (by rw [v4, V3, hT]) (by omega) e4h
  obtain ⟨σ6, s6, e6, e6h, o6, v6, c6⟩ := fieldR_spec cap sPRE rP1 rK rT (by decide) (by decide) (by decide) p σ5
    (by rw [v5, v4, V3, hp]) (by rw [v5, v4, V3, hK]) (by rw [v5, v4, V3, hT]) (by omega) e5h
  obtain ⟨τ, s7, e7, e7h, o7, v7, c7⟩ := fieldR_spec cap sPRE rw rK rT (by decide) (by decide) (by decide) wd σ6
    (by rw [v6, v5, v4, V3, hw]) (by rw [v6, v5, v4, V3, hK]) (by rw [v6, v5, v4, V3, hT]) (by omega) e6h
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 s7))))))
    ?_, ?_, e7h, ?_, ?_, by rw [v7, v6, v5, v4, V3], by rw [c7, c6, c5, c4, c3, c2, c1]⟩
  · simp only [List.length_cons, List.length_nil]
    omega
  · rw [e7, e6, e5, e4, e3, e2, e1]
    simp only [uf, List.append_assoc]
  · intro j hj
    have a1 := (o1 j hj).1
    have a3 := (o3 j hj).1
    have a4 := (o4 j hj).1
    have a5 := (o5 j hj).1
    have a6 := (o6 j hj).1
    have a7 := (o7 j hj).1
    by_cases jS : j = sSH
    · subst jS; rw [a7, a6, a5, a4, a3, n2, a1]
    · rw [a7, a6, a5, a4, a3, (o2 j jS hj).1, a1]
  · intro j a b
    rw [(o7 j a).2, (o6 j a).2, (o5 j a).2, (o4 j a).2, (o3 j a).2, (o2 j b a).2, (o1 j a).2]

/-- The pool's records and the children table of `PRE`, then `PRE`'s frame end. -/
def wPre2 : WM CN CR :=
  .seq (m2F6 sAOUT sPRE) (.seq (emitL sPRE [true, false]) (.seq (f7W sAT sAOUT sPRE)
    (emitL sPRE [true, false, false])))

theorem wPre2_spec (σ : WState CN CR) (ys : List (List Bool)) (atoms : List (List (List Bool)))
    (hys : ∀ y ∈ ys, y ≠ []) (hat : ∀ E ∈ atoms, ∀ y ∈ E, y ≠ [])
    (hA : σ.st sAOUT = ys.flatMap frame ++ false :: atomsStream atoms) (hAh : σ.sh sAOUT = 0)
    (hT : σ.st sAT = List.replicate atoms.length true) (hTh : σ.sh sAT = 0)
    (hO : σ.sh sPRE = (σ.st sPRE).length) :
    ∃ τ, WExec cap wPre2 σ τ (60 * (ys.flatMap frame).length + 70 * (atomsStream atoms).length + 40) ∧
      τ.st sPRE = σ.st sPRE ++ (ys.flatMap mm ++ [true, false] ++ atomsMM atoms ++ [true, false, false]) ∧
      τ.sh sPRE = (τ.st sPRE).length ∧ (∀ j, j ≠ sPRE → τ.st j = σ.st j) ∧
      (∀ j, j ≠ sPRE → j ≠ sAOUT → j ≠ sAT → τ.sh j = σ.sh j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hAP : sAOUT ≠ sPRE := by decide
  obtain ⟨σ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := m2F6_spec cap sAOUT sPRE hAP ys [] (atomsStream atoms) σ hys
    (by rw [hA]; simp) (by rw [hAh]; rfl) hO
  obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap sPRE [true, false] σ1 e1h
  have A2 := o2 sAOUT hAP
  have T1 := o1 sAT (by decide) (by decide)
  have T2 := o2 sAT (by decide)
  obtain ⟨σ3, s3, e3, e3h, t3, t3h, n3, n3h, o3, v3, c3⟩ := f7W_spec cap sAT sAOUT sPRE (by decide) (by decide) hAP
    [] atoms [] (ys.flatMap frame ++ [false]) σ2 hat (by rw [T2.1, T1.1, hT]; simp) (by rw [T2.2, T1.2, hTh]; rfl)
    (by rw [A2.1, n1, hA]; simp) (by rw [A2.2, n1h]; simp) e2h
  obtain ⟨τ, s4, e4, e4h, o4, v4, c4⟩ := emitL_facts cap sPRE [true, false, false] σ3 e3h
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_, ?_, e4h, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil]
    omega
  · rw [e4, e3, e2, e1]
    simp only [atomsMM, List.append_assoc]
  · intro j hj
    by_cases jA : j = sAOUT
    · subst jA; rw [(o4 _ hAP).1, n3, A2.1, n1]
    · by_cases jT : j = sAT
      · subst jT; rw [(o4 _ (by decide)).1, t3, T2.1, T1.1]
      · rw [(o4 j hj).1, (o3 j jT jA hj).1, (o2 j hj).1, (o1 j jA hj).1]
  · intro j a1 a2 a3
    rw [(o4 j a1).2, (o3 j a3 a2 a1).2, (o2 j a1).2, (o1 j a2 a1).2]
  · rw [v4, v3, v2, v1]
  · rw [c4, c3, c2, c1]

/-- **`frame POST`**: the header's field (from `sNW`) and the columns field (from `sCF1`), marked twice. -/
def wPost : WM CN CR :=
  .seq (m2F sNW sPOST) (.seq (emitL sPOST [true, false]) (.seq (m2F sCF1 sPOST) (emitL sPOST [true, false, false])))

theorem wPost_spec (σ : WState CN CR) (y9 y10 : List Bool) (hN : σ.st sNW = frame y9) (hNh : σ.sh sNW = 0)
    (hC : σ.st sCF1 = frame y10) (hCh : σ.sh sCF1 = 0) (hO : σ.sh sPOST = (σ.st sPOST).length) :
    ∃ τ, WExec cap wPost σ τ (50 * (y9.length + y10.length) + 80) ∧
      τ.st sPOST = σ.st sPOST ++ postOut y9 y10 ∧ τ.sh sPOST = (τ.st sPOST).length ∧
      (∀ j, j ≠ sPOST → τ.st j = σ.st j) ∧ (∀ j, j ≠ sPOST → j ≠ sNW → j ≠ sCF1 → τ.sh j = σ.sh j) ∧
      τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := m2F_spec cap sNW sPOST (by decide) [] y9 [] σ
    (by rw [hN]; simp) (by rw [hNh]; rfl) hO
  obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap sPOST [true, false] σ1 e1h
  have C1 := o1 sCF1 (by decide) (by decide)
  have C2 := o2 sCF1 (by decide)
  obtain ⟨σ3, s3, e3, e3h, n3, n3h, o3, v3, c3⟩ := m2F_spec cap sCF1 sPOST (by decide) [] y10 [] σ2
    (by rw [C2.1, C1.1, hC]; simp) (by rw [C2.2, C1.2, hCh]; rfl) e2h
  obtain ⟨τ, s4, e4, e4h, o4, v4, c4⟩ := emitL_facts cap sPOST [true, false, false] σ3 e3h
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_, ?_, e4h, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil]
    omega
  · rw [e4, e3, e2, e1]
    simp only [postOut, List.append_assoc]
  · intro j hj
    by_cases jN : j = sNW
    · subst jN; rw [(o4 _ (by decide)).1, (o3 _ (by decide) (by decide)).1, (o2 _ (by decide)).1, n1]
    · by_cases jC : j = sCF1
      · subst jC; rw [(o4 _ (by decide)).1, n3, C2.1, C1.1]
      · rw [(o4 j hj).1, (o3 j jC hj).1, (o2 j hj).1, (o1 j jN hj).1]
  · intro j a1 a2 a3
    rw [(o4 j a1).2, (o3 j a3 a1).2, (o2 j a1).2, (o1 j a2 a1).2]
  · rw [v4, v3, v2, v1]
  · rw [c4, c3, c2, c1]

/-- **The second program, part b.** -/
def wm2b : WM CN CR := .seq wPre1 (.seq wPre2 wPost)

theorem wm2b_spec (σ : WState CN CR) (S Q m h p wd : ℕ) (ys : List (List Bool)) (atoms : List (List (List Bool)))
    (y9 y10 : List Bool) (hys : ∀ y ∈ ys, y ≠ []) (hat : ∀ E ∈ atoms, ∀ y ∈ E, y ≠ [])
    (hS : σ.st sSH = List.replicate S true) (hSh : σ.sh sSH = 0)
    (hA : σ.st sAOUT = ys.flatMap frame ++ false :: atomsStream atoms) (hAh : σ.sh sAOUT = 0)
    (hT : σ.st sAT = List.replicate atoms.length true) (hTh : σ.sh sAT = 0)
    (hN : σ.st sNW = frame y9) (hNh : σ.sh sNW = 0) (hC : σ.st sCF1 = frame y10) (hCh : σ.sh sCF1 = 0)
    (hO : σ.sh sPRE = (σ.st sPRE).length) (hP : σ.sh sPOST = (σ.st sPOST).length)
    (hQ : σ.val rQ = Q) (hm : σ.val rm = m) (hh : σ.val rh = h) (hp : σ.val rP1 = p) (hw : σ.val rw = wd)
    (hK : σ.val rK = 0) (hT0 : σ.val rT = 0) (hcap : Q + m + h + p + wd ≤ cap) :
    ∃ τ, WExec cap wm2b σ τ (5 * UnaryPow.sq cap + 21 * (Q + m + h + p + wd) + 25 * S +
        60 * (ys.flatMap frame).length + 70 * (atomsStream atoms).length + 50 * (y9.length + y10.length) + 330) ∧
      τ.st sPRE = σ.st sPRE ++ preOut Q S m h p wd ys atoms ∧ τ.st sPOST = σ.st sPOST ++ postOut y9 y10 ∧
      (∀ j, j ≠ sPRE → j ≠ sPOST → τ.st j = σ.st j) ∧
      (∀ j, j ≠ sPRE → j ≠ sPOST → j ≠ sSH → j ≠ sAOUT → j ≠ sAT → j ≠ sNW → j ≠ sCF1 → τ.sh j = σ.sh j) ∧
      τ.sh sPRE = (τ.st sPRE).length ∧ τ.sh sPOST = (τ.st sPOST).length ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  obtain ⟨σ1, s1, e1, e1h, o1, h1, v1, c1⟩ := wPre1_spec cap σ S Q m h p wd hS hSh hO hQ hm hh hp hw hK hT0 hcap
  obtain ⟨σ2, s2, e2, e2h, o2, h2, v2, c2⟩ := wPre2_spec cap σ1 ys atoms hys hat
    (by rw [o1 _ (by decide), hA]) (by rw [h1 _ (by decide) (by decide), hAh])
    (by rw [o1 _ (by decide), hT]) (by rw [h1 _ (by decide) (by decide), hTh]) e1h
  obtain ⟨τ, s3, e3, e3h, o3, h3, v3, c3⟩ := wPost_spec cap σ2 y9 y10
    (by rw [o2 _ (by decide), o1 _ (by decide), hN])
    (by rw [h2 _ (by decide) (by decide) (by decide), h1 _ (by decide) (by decide), hNh])
    (by rw [o2 _ (by decide), o1 _ (by decide), hC])
    (by rw [h2 _ (by decide) (by decide) (by decide), h1 _ (by decide) (by decide), hCh])
    (by rw [o2 _ (by decide), o1 _ (by decide), h2 _ (by decide) (by decide) (by decide),
      h1 _ (by decide) (by decide), hP])
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_, ?_, ?_, ?_, ?_, e3h, ?_, ?_⟩
  · rw [o3 _ (by decide), e2, e1]
    simp only [preOut, List.append_assoc]
  · rw [e3, o2 _ (by decide), o1 _ (by decide)]
  · intro j a1 a2
    rw [o3 j a2, o2 j a1, o1 j a1]
  · intro j a1 a2 a3 a4 a5 a6 a7
    rw [h3 j a2 a6 a7, h2 j a1 a4 a5, h1 j a1 a3]
  · rw [h3 _ (by decide) (by decide) (by decide), o3 _ (by decide)]
    exact e2h
  · rw [v3, v2, v1]
  · rw [c3, c2, c1]

end NearCubicWires.WireExponent3_5.PrimAsm.C3Phase
