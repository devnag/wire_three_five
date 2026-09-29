import Proof.Wire_3_5.Primitive.SeedFix.CarWM

/-! # C3 request writer, part 1: framed copies at the second marking level

The C3 request's fields are framed twice over (`c3In`'s `frame req.word`; `C3Run`'s `frame PRE`, `PRE = Σ frame
field`; C3a′'s `frame (c3aInput …)`, `c3aInput = loadRec …`): `frame (frame f) = marks (marks f) ++ [true, false] ++
[false]`. These word programs append `marks (marks ·)` of a source to the end of an output stream, reading the source
once (every head only moves forward): unary runs (`m2U`), one framed word (`m2F`), a stream of framed words ended by
`false` (`m2Fs`), and constant words (`emitL`).

Paper quantity: none (the framing of the compiler's request fields, alg:compiler P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Marks
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimT.CarWM
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Words -/

/-- `marks (marks f)` for a framed word's content `y` (then the frame's terminal `false`, marked twice). -/
def mm (y : List Bool) : List Bool := y.flatMap (fun b => [true, true, true, true, true, true, true, b]) ++
  [true, true, true, false]

theorem marks_marks_frame (y : List Bool) : marks (marks (frame y)) = mm y := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [frame, marks, mm] at ih ⊢; exact ih

/-! ## Constant words -/

/-- Append the word `w`. -/
def emitL (O : Fin (ns + 1)) : List Bool → WM ns nr
  | [] => .skip
  | b :: w => .seq (PrimT.emitW O b) (emitL O w)

theorem emitL_facts (O : Fin (ns + 1)) : ∀ (w : List Bool) (σ : WState ns nr), σ.sh O = (σ.st O).length →
    ∃ τ, WExec cap (emitL O w) σ τ (4 * w.length + 1) ∧ τ.st O = σ.st O ++ w ∧ τ.sh O = (τ.st O).length ∧
      (∀ j, j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], σ, hO => ⟨σ, WExec.mono (WExec.skip σ) (by omega), by simp, hO, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | b :: w, σ, hO => by
    obtain ⟨τ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap O b σ hO
    obtain ⟨τ, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts O w τ1 e1h
    refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by simp; omega), by rw [e2, e1]; simp, e2h,
      fun j hj => (o1 j hj).trans' (o2 j hj), by rw [v2, v1], by rw [c2, c1]⟩

/-! ## Unary runs -/

/-- `marks (marks 1^k)` of the run of ones at `S`'s head. -/
def m2U (S O : Fin (ns + 1)) : WM ns nr := .whs S (.seq (.fwd S) (emitL O [true, true, true, true]))

theorem m2U_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) (hr : rest.headD false = false) :
    ∀ (k : ℕ) (pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (List.replicate k true ++ rest) →
      σ.sh S = pre.length → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (m2U S O) σ τ (25 * k + 1) ∧ τ.st O = σ.st O ++ List.replicate (4 * k) true ∧
        τ.sh O = (τ.st O).length ∧ τ.st S = σ.st S ∧ τ.sh S = pre.length + k ∧
        (∀ j, j ≠ S → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, pre, σ, hS, hSh, hO => by
    have hz : wbit σ S = false := by
      simp only [wbit, hS, hSh, List.replicate_zero, List.nil_append, rd_at]
      cases rest with
      | nil => rfl
      | cons c t => simp at hr; simp [hr]
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hO, rfl, by simp [hSh], fun _ _ _ => ⟨rfl, rfl⟩,
      rfl, rfl⟩
  | k + 1, pre, σ, hS, hSh, hO => by
    have hOS : O ≠ S := fun e => hSO e.symm
    have hw : wbit σ S = true := by simp only [wbit, hS, hSh, rd_at, List.replicate_succ]; simp
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap S σ
    have O1 := o1 O hOS
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap O [true, true, true, true] σ1 (by rw [O1.1, O1.2, hO])
    have N2 := o2 S hSO
    obtain ⟨τ, s3, e3, e3h, n3, n3h, o3, v3, c3⟩ := m2U_spec S O hSO rest hr k (pre ++ [true]) σ2
      (by rw [N2.1, n1, hS]; simp [List.replicate_succ]) (by rw [N2.2, n1h, hSh]; simp) e2h
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) (by simp; omega), ?_, e3h, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e3, e2, O1.1]
      have : 4 * (k + 1) = 4 + 4 * k := by ring
      rw [this, List.replicate_add]; simp
    · rw [n3, N2.1, n1]
    · rw [n3h]; simp; omega
    · intro j h1 h2
      exact ((o1 j h1).trans' (o2 j h2)).trans' (o3 j h1 h2)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

/-! ## One framed word -/

/-- The pair loop: `marks (marks [true, b])` for every pair `(true, b)` of the framed word at `S`'s head. -/
def m2FLoop (S O : Fin (ns + 1)) : WM ns nr :=
  .whs S (.seq (.fwd S) (.seq (emitL O [true, true, true, true, true, true, true])
    (.seq (.ifs S (PrimT.emitW O true) (PrimT.emitW O false)) (.fwd S))))

/-- **`marks (marks (frame y))`** of the framed word at `S`'s head. -/
def m2F (S O : Fin (ns + 1)) : WM ns nr := .seq (m2FLoop S O) (.seq (emitL O [true, true, true, false]) (.fwd S))

theorem m2FLoop_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) :
    ∀ (y pre : List Bool) (σ : WState ns nr), σ.st S = pre ++ (frame y ++ rest) → σ.sh S = pre.length →
      σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (m2FLoop S O) σ τ (50 * y.length + 1) ∧
        τ.st O = σ.st O ++ y.flatMap (fun b => [true, true, true, true, true, true, true, b]) ∧
        τ.sh O = (τ.st O).length ∧ τ.st S = σ.st S ∧ τ.sh S = pre.length + 2 * y.length ∧
        (∀ j, j ≠ S → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, hS, hSh, hO => by
    have hz : wbit σ S = false := by simp only [wbit, hS, hSh, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hO, rfl, by simp [hSh], fun _ _ _ => ⟨rfl, rfl⟩,
      rfl, rfl⟩
  | b :: bs, pre, σ, hS, hSh, hO => by
    have hOS : O ≠ S := fun e => hSO e.symm
    have hw : wbit σ S = true := by simp only [wbit, hS, hSh, rd_at]; rfl
    obtain ⟨σ1, s1, n1, n1h, o1, v1, c1⟩ := fwd_facts cap S σ
    have O1 := o1 O hOS
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap O [true, true, true, true, true, true, true] σ1
      (by rw [O1.1, O1.2, hO])
    have N2 := o2 S hSO
    have hb : wbit σ2 S = b := by simp only [wbit, N2.1, N2.2, n1, n1h, hS, hSh, rd_at1]; rfl
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap O b σ2 e2h
    have s3' : WExec cap (.ifs S (PrimT.emitW O true) (PrimT.emitW O false)) σ2 σ3 4 := by
      cases b
      · exact WExec.ifsF hb s3
      · exact WExec.ifsT hb s3
    have N3 := o3 S hSO
    obtain ⟨σ4, s4, n4, n4h, o4, v4, c4⟩ := fwd_facts cap S σ3
    have O4 := o4 O hOS
    obtain ⟨τ, s5, eO, eOh, eN, eNh, oth, v5, c5⟩ := m2FLoop_spec S O hSO rest bs (pre ++ [true, b]) σ4
      (by rw [n4, N3.1, N2.1, n1, hS]; simp [frame]) (by rw [n4h, N3.2, N2.2, n1h, hSh]; simp)
      (by rw [O4.1, O4.2, e3h])
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3' s4))) s5) (by simp; omega),
      ?_, eOh, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eO, O4.1, e3, e2, O1.1]; simp
    · rw [eN, n4, N3.1, N2.1, n1]
    · rw [eNh]; simp; omega
    · intro j h1 h2
      exact ((((o1 j h1).trans' (o2 j h2)).trans' (o3 j h2)).trans' (o4 j h1)).trans' (oth j h1 h2)
    · rw [v5, v4, v3, v2, v1]
    · rw [c5, c4, c3, c2, c1]

theorem m2F_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (pre y rest : List Bool) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (frame y ++ rest)) (hSh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (m2F S O) σ τ (50 * y.length + 25) ∧ τ.st O = σ.st O ++ mm y ∧
      τ.sh O = (τ.st O).length ∧ τ.st S = σ.st S ∧ τ.sh S = pre.length + (frame y).length ∧
      (∀ j, j ≠ S → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hOS : O ≠ S := fun e => hSO e.symm
  obtain ⟨τ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := m2FLoop_spec cap S O hSO rest y pre σ hS hSh hO
  obtain ⟨τ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap O [true, true, true, false] τ1 e1h
  have N2 := o2 S hSO
  obtain ⟨τ, s3, n3, n3h, o3, v3, c3⟩ := fwd_facts cap S τ2
  have O3 := o3 O hOS
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by simp only [List.length_cons, List.length_nil]; omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O3.1, e2, e1]; simp [mm]
  · rw [O3.1, O3.2, e2h]
  · rw [n3, N2.1, n1]
  · rw [n3h, N2.2, n1h, frame_length]; ring
  · intro j h1 h2
    exact ((o1 j h1 h2).trans' (o2 j h2)).trans' (o3 j h1)
  · rw [v3, v2, v1]
  · rw [c3, c2, c1]

/-! ## Streams of framed words -/

/-- The frames' loop: `marks (marks (frame y))` for every framed word before the stream's `false`. -/
def m2FsLoop (S O : Fin (ns + 1)) : WM ns nr := .whs S (m2F S O)

theorem m2FsLoop_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (rest : List Bool) :
    ∀ (ys : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ y ∈ ys, y ≠ []) →
      σ.st S = pre ++ (ys.flatMap frame ++ false :: rest) → σ.sh S = pre.length → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (m2FsLoop S O) σ τ (60 * (ys.flatMap frame).length + 1) ∧ τ.st O = σ.st O ++ ys.flatMap mm ∧
        τ.sh O = (τ.st O).length ∧ τ.st S = σ.st S ∧ τ.sh S = pre.length + (ys.flatMap frame).length ∧
        (∀ j, j ≠ S → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, _, hS, hSh, hO => by
    have hz : wbit σ S = false := by simp only [wbit, hS, hSh, List.flatMap_nil, List.nil_append, rd_at]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hO, rfl, by simp [hSh], fun _ _ _ => ⟨rfl, rfl⟩,
      rfl, rfl⟩
  | y :: ys, pre, σ, hne, hS, hSh, hO => by
    have hy : y ≠ [] := hne y List.mem_cons_self
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hy
    have hw : wbit σ S = true := by
      simp only [wbit, hS, hSh, List.flatMap_cons, rd_at]; simp [frame]
    obtain ⟨σ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := m2F_spec cap S O hSO pre (b :: bs)
      (ys.flatMap frame ++ false :: rest) σ (by rw [hS]; simp) hSh hO
    obtain ⟨τ, s2, e2, e2h, n2, n2h, o2, v2, c2⟩ := m2FsLoop_spec S O hSO rest ys (pre ++ frame (b :: bs)) σ1
      (fun z hz => hne z (List.mem_cons_of_mem _ hz)) (by rw [n1, hS]; simp) (by rw [n1h]; simp) e1h
    refine ⟨τ, WExec.mono (WExec.whsT hw s1 s2) ?_, by rw [e2, e1]; simp, e2h, by rw [n2, n1], ?_,
      fun j h1 h2 => (o1 j h1 h2).trans' (o2 j h1 h2), by rw [v2, v1], by rw [c2, c1]⟩
    · simp only [List.flatMap_cons, List.length_append, frame_length, List.length_cons] at *
      omega
    · rw [n2h]; simp [List.flatMap_cons]; omega

/-- **`marks (marks (ys.flatMap frame ++ [false]))`**: a stream of framed words ended by `false`. -/
def m2Fs (S O : Fin (ns + 1)) : WM ns nr := .seq (m2FsLoop S O) (.seq (emitL O [true, true, true, false]) (.fwd S))

theorem m2Fs_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (ys : List (List Bool)) (pre rest : List Bool)
    (σ : WState ns nr) (hne : ∀ y ∈ ys, y ≠ []) (hS : σ.st S = pre ++ (ys.flatMap frame ++ false :: rest))
    (hSh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (m2Fs S O) σ τ (60 * (ys.flatMap frame).length + 25) ∧
      τ.st O = σ.st O ++ (ys.flatMap mm ++ [true, true, true, false]) ∧ τ.sh O = (τ.st O).length ∧
      τ.st S = σ.st S ∧ τ.sh S = pre.length + (ys.flatMap frame).length + 1 ∧
      (∀ j, j ≠ S → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hOS : O ≠ S := fun e => hSO e.symm
  obtain ⟨τ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := m2FsLoop_spec cap S O hSO rest ys pre σ hne hS hSh hO
  obtain ⟨τ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap O [true, true, true, false] τ1 e1h
  have N2 := o2 S hSO
  obtain ⟨τ, s3, n3, n3h, o3, v3, c3⟩ := fwd_facts cap S τ2
  have O3 := o3 O hOS
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by simp only [List.length_cons, List.length_nil]; omega),
    by rw [O3.1, e2, e1]; simp, by rw [O3.1, O3.2, e2h], by rw [n3, N2.1, n1], by rw [n3h, N2.2, n1h],
    fun j h1 h2 => ((o1 j h1 h2).trans' (o2 j h2)).trans' (o3 j h1), by rw [v3, v2, v1], by rw [c3, c2, c1]⟩

/-- **`marks (marks (ys.flatMap frame))`**, then past the stream's `false` (unmarked). -/
def m2F6 (S O : Fin (ns + 1)) : WM ns nr := .seq (m2FsLoop S O) (.fwd S)

theorem m2F6_spec (S O : Fin (ns + 1)) (hSO : S ≠ O) (ys : List (List Bool)) (pre rest : List Bool)
    (σ : WState ns nr) (hne : ∀ y ∈ ys, y ≠ []) (hS : σ.st S = pre ++ (ys.flatMap frame ++ false :: rest))
    (hSh : σ.sh S = pre.length) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (m2F6 S O) σ τ (60 * (ys.flatMap frame).length + 5) ∧ τ.st O = σ.st O ++ ys.flatMap mm ∧
      τ.sh O = (τ.st O).length ∧ τ.st S = σ.st S ∧ τ.sh S = pre.length + (ys.flatMap frame).length + 1 ∧
      (∀ j, j ≠ S → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hOS : O ≠ S := fun e => hSO e.symm
  obtain ⟨τ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := m2FsLoop_spec cap S O hSO rest ys pre σ hne hS hSh hO
  obtain ⟨τ, s3, n3, n3h, o3, v3, c3⟩ := fwd_facts cap S τ1
  have O3 := o3 O hOS
  refine ⟨τ, WExec.mono (WExec.seq s1 s3) (by omega), by rw [O3.1, e1], by rw [O3.1, O3.2, e1h], by rw [n3, n1],
    by rw [n3h, n1h], fun j h1 h2 => (o1 j h1 h2).trans' (o3 j h1), by rw [v3, v1], by rw [c3, c1]⟩

/-! ## Repeated words, counted by a register -/

/-- Append `u` `n` times (`K = n`, back to `0`). -/
def repE (O : Fin (ns + 1)) (K : Fin nr) (u : List Bool) : WM ns nr := .whr K (.seq (.dec K) (emitL O u))

theorem repE_spec (O : Fin (ns + 1)) (K : Fin nr) (u : List Bool) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val K = n → n ≤ cap → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (repE O K u) σ τ (n * (4 * u.length + 5) + 1) ∧
        τ.st O = σ.st O ++ (List.replicate n u).flatten ∧ τ.sh O = (τ.st O).length ∧
        (∀ j, j ≠ O → Same σ τ j) ∧ τ.val K = 0 ∧ (∀ r, r ≠ K → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | 0, σ, hK, _, hO => ⟨σ, WExec.mono (WExec.whrF hK) (by omega), by simp, hO, fun _ _ => ⟨rfl, rfl⟩, hK,
      fun _ _ => rfl, rfl⟩
  | n + 1, σ, hK, hn, hO => by
    have h1 := WExec.dec (cap := cap) K σ (by omega)
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emitL_facts cap O u (σ.setv K (σ.val K - 1)) (by simp [hO])
    have hK2 : σ2.val K = n := by rw [v2]; simp [hK]
    obtain ⟨τ, s3, e3, e3h, o3, k3, r3, c3⟩ := repE_spec O K u n σ2 hK2 (by omega) e2h
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (WExec.seq h1 s2) s3) (by ring_nf; omega), ?_, e3h, ?_, k3, ?_, ?_⟩
    · rw [e3, e2]; simp [List.replicate_succ]
    · intro j hj
      have := o2 j hj
      exact ⟨by rw [(o3 j hj).1, this.1]; rfl, by rw [(o3 j hj).2, this.2]; rfl⟩
    · intro r hr
      rw [r3 r hr, v2]; simp [Function.update_apply, hr]
    · rw [c3, c2]; rfl

/-- Move `S`'s head `n` cells forward (`K = n`, back to `0`). -/
def fwdN (S : Fin (ns + 1)) (K : Fin nr) : WM ns nr := .whr K (.seq (.dec K) (.fwd S))

theorem fwdN_spec (S : Fin (ns + 1)) (K : Fin nr) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val K = n → n ≤ cap →
      ∃ τ, WExec cap (fwdN S K) σ τ (6 * n + 1) ∧ τ.st = σ.st ∧ τ.sh S = σ.sh S + n ∧
        (∀ j, j ≠ S → τ.sh j = σ.sh j) ∧ τ.val K = 0 ∧ (∀ r, r ≠ K → τ.val r = σ.val r) ∧ τ.cell = σ.cell
  | 0, σ, hK, _ => ⟨σ, WExec.mono (WExec.whrF hK) (by omega), rfl, by simp, fun _ _ => rfl, hK, fun _ _ => rfl, rfl⟩
  | n + 1, σ, hK, hn => by
    have h1 := WExec.dec (cap := cap) K σ (by omega)
    obtain ⟨σ2, s2, n2, n2h, o2, v2, c2⟩ := fwd_facts cap S (σ.setv K (σ.val K - 1))
    have hK2 : σ2.val K = n := by rw [v2]; simp [hK]
    obtain ⟨τ, s3, t3, h3, o3, k3, r3, c3⟩ := fwdN_spec S K n σ2 hK2 (by omega)
    refine ⟨τ, WExec.mono (WExec.whrT (by omega) (WExec.seq h1 s2) s3) (by omega), ?_, ?_, ?_, k3, ?_, ?_⟩
    · rw [t3]; funext j
      by_cases hj : j = S
      · subst hj; rw [n2]; rfl
      · rw [(o2 j hj).1]; rfl
    · rw [h3, n2h]; simp; omega
    · intro j hj; rw [o3 j hj, (o2 j hj).2]; rfl
    · intro r hr; rw [r3 r hr, v2]; simp [Function.update_apply, hr]
    · rw [c3, c2]; rfl

end NearCubicWires.WireExponent3_5.PrimAsm.C3Marks
