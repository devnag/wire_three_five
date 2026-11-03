import Proof.Wire_3_5.FinalPass.TabDec1
import Proof.Wire_3_5.Primitive.Writers.FiltSetupIface2
import Proof.Wire_3_5.Primitive.Writers.DataSetup
import Proof.Wire_3_5.Primitive.Writers.DataTabs
import Proof.Wire_3_5.Primitive.Writers.ParseNat

/-! # S4 (f1), the tables writer, part 4: the request's numbers into registers (P3:2036-2101)

The unit's request word is the THR request word of the empty tuple with the unit's numbers as its tail:
`reqT n len cap err L₀ L₁ nE = Data.reqW n true [] [] (unaryList [len, cap, err, L₀, L₁, nE])`
(**`reqT_eq`**: `natWord n ++ [1,1,0,0,1,0,0] ++ unaryList […]`). **`parseW`** reads it on the cell layout (framed
on stream `0`): `natWord n` (its unary length, then its payload), four junk fields, then the six numbers into the
registers `Rg 3 … Rg 8` (any nine distinct registers `Rg`), every head move counted in `Rg 0`, the request
rewound. **`parse_spec`**: the six numbers in their registers, the streams and heads as they were, every register off
`Rg` kept, within `30·|w| + 300`.

Paper quantity of the main type: the unit's numbers (the filter's `len`, `cap`, `errExp`, the two mask lengths, the
seed count) read from its request word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm

/-! ## Reading steps with their facts -/

theorem drop_rep (v : ℕ) (R : List Bool) : (List.replicate v true ++ false :: R).drop (v + 1) = R := by
  induction v with
  | zero => rfl
  | succ v ih => simpa [List.replicate_succ] using ih

theorem dropNext (W R : List Bool) (p v : ℕ) (h : W.drop p = List.replicate v true ++ false :: R) :
    W.drop (p + v + 1) = R := by
  rw [show p + v + 1 = p + (v + 1) by omega, ← List.drop_drop, h, drop_rep]

theorem rstep (cap : ℕ) {ns nr : ℕ} (Q : Fin (ns + 1)) (ps r : Fin nr) (hpr : ps ≠ r) (W R : List Bool) (p v : ℕ)
    (hd : W.drop p = List.replicate v true ++ false :: R) (σ : WState ns nr) (hst : σ.st Q = frameP W ++ [false])
    (hsh : σ.sh Q = 2 * p) (hps : σ.val ps = 2 * p) (hc : σ.val r + v ≤ cap) (hc2 : 2 * (p + v + 1) ≤ cap) :
    ∃ σ' : WState ns nr, WExec cap (readUF Q ps r) σ σ' (17 * v + 13) ∧ σ'.st = σ.st ∧
      σ'.sh Q = 2 * (p + v + 1) ∧ (∀ s, s ≠ Q → σ'.sh s = σ.sh s) ∧ σ'.val ps = 2 * (p + v + 1) ∧
      σ'.val r = σ.val r + v ∧ (∀ q, q ≠ ps → q ≠ r → σ'.val q = σ.val q) ∧ σ'.cell = σ.cell ∧
      W.drop (p + v + 1) = R := by
  refine ⟨_, readUF_spec cap Q ps r hpr W R p v hd σ hst hsh hc (by omega), rfl, by simp, ?_, ?_, by simp, ?_, rfl,
    dropNext W R p v hd⟩
  · intro s hs
    simp [Function.update_of_ne hs]
  · simp [Function.update_of_ne hpr, hps]
    ring
  · intro q hq hr
    simp [Function.update_of_ne hq, Function.update_of_ne hr]

/-! ## The request word -/

/-- **The unit's request word**: the empty tuple's THR request word, the numbers as its tail. -/
def reqT (n len cp err L0 L1 nE : ℕ) : List Bool :=
  Data.reqW n true [] [] (Data.unaryList [len, cp, err, L0, L1, nE])

theorem natWord_zero : RepairRepresentation.natWord 0 = [true, false, false] := by
  simp [RepairRepresentation.natWord, WilliamsPublishedForm.framedNatBits, natBitLength,
    WilliamsPublishedForm.fixedWidthNatBits]

theorem reqT_eq (n len cp err L0 L1 nE : ℕ) :
    reqT n len cp err L0 L1 nE = RepairRepresentation.natWord n ++
      ([true, true, false, false, true, false, false] ++ Data.unaryList [len, cp, err, L0, L1, nE]) := by
  simp [reqT, Data.reqW, RepairRepresentation.natListWord, natWord_zero]

variable (cap x : ℕ) (Rg : Fin 9 ↪ Fin LNR)

/-- **The request's numbers read** into `Rg 3 … Rg 8`: `natWord n`, the junk fields (into `Rg 2`), the six
numbers, the request rewound by the counter `Rg 0`. -/
def parseW : WM (LNS x) LNR :=
  .seq (readUF (sk x 0) (Rg 0) (Rg 1)) (.seq (skipBF (sk x 0) (Rg 0) (Rg 1)) (.seq (readUF (sk x 0) (Rg 0) (Rg 2))
    (.seq (readUF (sk x 0) (Rg 0) (Rg 2)) (.seq (readUF (sk x 0) (Rg 0) (Rg 2)) (.seq (readUF (sk x 0) (Rg 0) (Rg 2))
    (.seq (readUF (sk x 0) (Rg 0) (Rg 3)) (.seq (readUF (sk x 0) (Rg 0) (Rg 4)) (.seq (readUF (sk x 0) (Rg 0) (Rg 5))
    (.seq (readUF (sk x 0) (Rg 0) (Rg 6)) (.seq (readUF (sk x 0) (Rg 0) (Rg 7)) (.seq (readUF (sk x 0) (Rg 0) (Rg 8))
    (WM.rewind (sk x 0) (Rg 0)))))))))))))

theorem parse_spec (n len cp err L0 L1 nE : ℕ) (σ : WState (LNS x) LNR)
    (hst : σ.st (sk x 0) = frame (reqT n len cp err L0 L1 nE)) (hsh : σ.sh (sk x 0) = 0)
    (hz : ∀ k, σ.val (Rg k) = 0) (hc : 2 * (reqT n len cp err L0 L1 nE).length + 2 ≤ cap) :
    ∃ (σA : WState (LNS x) LNR) (m : ℕ), WExec cap (parseW x Rg) σ σA m ∧
      m ≤ 30 * (reqT n len cp err L0 L1 nE).length + 300 ∧ σA.st = σ.st ∧ σA.sh = σ.sh ∧ σA.cell = σ.cell ∧
      σA.val (Rg 3) = len ∧ σA.val (Rg 4) = cp ∧ σA.val (Rg 5) = err ∧ σA.val (Rg 6) = L0 ∧ σA.val (Rg 7) = L1 ∧
      σA.val (Rg 8) = nE ∧ (∀ q : Fin LNR, (∀ k, q ≠ Rg k) → σA.val q = σ.val q) ∧ σA.val (Rg 0) = 0 ∧
      σA.val (Rg 1) = 0 := by
  have d : ∀ a b : Fin 9, a ≠ b → Rg a ≠ Rg b := fun a b h => Rg.injective.ne h
  set W := reqT n len cp err L0 L1 nE with hW
  set L := natBitLength n with hL
  set tl := Data.unaryList [len, cp, err, L0, L1, nE] with htl
  have hWe : W = RepairRepresentation.natWord n ++ ([true, true, false, false, true, false, false] ++ tl) :=
    reqT_eq n len cp err L0 L1 nE
  have hnl : (RepairRepresentation.natWord n).length = 2 * L + 1 := ParseNat.natWord_length n
  have hWl : W.length = 2 * L + 1 + 7 + (len + 1) + (cp + 1) + (err + 1) + (L0 + 1) + (L1 + 1) + (nE + 1) := by
    rw [hWe, List.length_append, hnl, htl]
    simp [Data.unaryList]
    ring
  have hst' : σ.st (sk x 0) = frameP W ++ [false] := by rw [hst, frame_eq_frameP]
  -- natWord n
  have d0 : W.drop 0 = List.replicate L true ++ false ::
      (WilliamsPublishedForm.fixedWidthNatBits L n ++ ([true, true, false, false, true, false, false] ++ tl)) := by
    rw [List.drop_zero, hWe, ParseNat.natWord_eq, ← hL]
    simp
  obtain ⟨σ1, e1, s1, h1, o1, p1, r1, v1, c1, d1⟩ := rstep cap (sk x 0) (Rg 0) (Rg 1) (d 0 1 (by decide)) W _ 0 L d0 σ
    hst' (by rw [hsh]) (by rw [hz 0]) (by rw [hz 1]; omega) (by omega)
  have e2 := skipBF_spec cap (sk x 0) (Rg 0) (Rg 1) (d 0 1 (by decide)) L σ1 (by rw [r1, hz 1]; omega) (by omega)
    (by rw [p1]; omega)
  obtain ⟨σ2, h2⟩ : ∃ y : WState (LNS x) LNR, y = ((σ1.seth (sk x 0) (σ1.sh (sk x 0) + 2 * L)).setv (Rg 0)
      (σ1.val (Rg 0) + 2 * L)).setv (Rg 1) 0 := ⟨_, rfl⟩
  rw [← h2] at e2
  have s2 : σ2.st = σ.st := by rw [h2, ← s1]; rfl
  have hs2 : σ2.sh (sk x 0) = 2 * (2 * L + 1) := by rw [h2]; simp [h1]; ring
  have o2 : ∀ s, s ≠ sk x 0 → σ2.sh s = σ.sh s := fun s hs => by rw [h2]; simp [Function.update_of_ne hs, o1 s hs]
  have p2 : σ2.val (Rg 0) = 2 * (2 * L + 1) := by
    rw [h2, wsetv_val_ne _ _ (d 0 1 (by decide))]; simp [p1]; ring
  have v2 : ∀ q, q ≠ Rg 0 → q ≠ Rg 1 → σ2.val q = σ.val q := fun q h1' h2' => by
    rw [h2]; simp [Function.update_of_ne h1', Function.update_of_ne h2', v1 q h1' h2']
  have c2 : σ2.cell = σ.cell := by rw [h2, ← c1]; rfl
  have dA : W.drop (2 * L + 1) = List.replicate 2 true ++ false :: (false :: true :: false :: false :: tl) := by
    rw [hWe, ← hnl, List.drop_left]
    rfl
  -- the junk fields
  have j2 : σ2.val (Rg 2) = 0 := by rw [v2 _ (d 2 0 (by decide)) (d 2 1 (by decide)), hz 2]
  obtain ⟨σ3, e3, s3, h3, o3, p3, r3, v3, c3, d3⟩ := rstep cap (sk x 0) (Rg 0) (Rg 2) (d 0 2 (by decide)) W _ _ 2 dA
    σ2 (by rw [s2, hst']) hs2 p2 (by rw [j2]; omega) (by omega)
  obtain ⟨σ4, e4, s4, h4, o4, p4, r4, v4, c4, d4⟩ := rstep cap (sk x 0) (Rg 0) (Rg 2) (d 0 2 (by decide)) W _ _ 0 d3
    σ3 (by rw [s3, s2, hst']) h3 p3 (by rw [r3, j2]; omega) (by omega)
  obtain ⟨σ5, e5, s5, h5, o5, p5, r5, v5, c5, d5⟩ := rstep cap (sk x 0) (Rg 0) (Rg 2) (d 0 2 (by decide)) W _ _ 1 d4
    σ4 (by rw [s4, s3, s2, hst']) h4 p4 (by rw [r4, r3, j2]; omega) (by omega)
  obtain ⟨σ6, e6, s6, h6, o6, p6, r6, v6, c6, d6⟩ := rstep cap (sk x 0) (Rg 0) (Rg 2) (d 0 2 (by decide)) W _ _ 0 d5
    σ5 (by rw [s5, s4, s3, s2, hst']) h5 p5 (by rw [r5, r4, r3, j2]; omega) (by omega)
  -- the six numbers
  have dT : W.drop (2 * L + 1 + 2 + 1 + 0 + 1 + 1 + 1 + 0 + 1) = List.replicate len true ++ false ::
      Data.unaryList [cp, err, L0, L1, nE] := by rw [d6, htl]; simp [Data.unaryList]
  have base6 : ∀ k : Fin 9, 3 ≤ k.val → σ6.val (Rg k) = 0 := fun k hk => by
    have n0 : Rg k ≠ Rg 0 := d k 0 (fun e => by rw [e] at hk; simp at hk)
    have n1 : Rg k ≠ Rg 1 := d k 1 (fun e => by rw [e] at hk; simp at hk)
    have n2 : Rg k ≠ Rg 2 := d k 2 (fun e => by rw [e] at hk; simp at hk)
    rw [v6 _ n0 n2, v5 _ n0 n2, v4 _ n0 n2, v3 _ n0 n2, v2 _ n0 n1, hz k]
  obtain ⟨σ7, e7, s7, h7, o7, p7, r7, v7, c7, d7⟩ := rstep cap (sk x 0) (Rg 0) (Rg 3) (d 0 3 (by decide)) W _ _ len dT
    σ6 (by rw [s6, s5, s4, s3, s2, hst']) h6 p6 (by rw [base6 3 (by decide)]; omega) (by omega)
  have dT2 : W.drop (2 * L + 1 + 2 + 1 + 0 + 1 + 1 + 1 + 0 + 1 + len + 1) = List.replicate cp true ++ false ::
      Data.unaryList [err, L0, L1, nE] := by rw [d7]; simp [Data.unaryList]
  obtain ⟨σ8, e8, s8, h8, o8, p8, r8, v8, c8, d8⟩ := rstep cap (sk x 0) (Rg 0) (Rg 4) (d 0 4 (by decide)) W _ _ cp dT2
    σ7 (by rw [s7, s6, s5, s4, s3, s2, hst']) h7 p7
    (by rw [v7 _ (d 4 0 (by decide)) (d 4 3 (by decide)), base6 4 (by decide)]; omega) (by omega)
  have dT3 : W.drop (2 * L + 1 + 2 + 1 + 0 + 1 + 1 + 1 + 0 + 1 + len + 1 + cp + 1) = List.replicate err true ++
      false :: Data.unaryList [L0, L1, nE] := by rw [d8]; simp [Data.unaryList]
  obtain ⟨σ9, e9, s9, h9, o9, p9, r9, v9, c9, d9⟩ := rstep cap (sk x 0) (Rg 0) (Rg 5) (d 0 5 (by decide)) W _ _ err dT3
    σ8 (by rw [s8, s7, s6, s5, s4, s3, s2, hst']) h8 p8
    (by rw [v8 _ (d 5 0 (by decide)) (d 5 4 (by decide)), v7 _ (d 5 0 (by decide)) (d 5 3 (by decide)),
      base6 5 (by decide)]; omega) (by omega)
  have dT4 : W.drop (2 * L + 1 + 2 + 1 + 0 + 1 + 1 + 1 + 0 + 1 + len + 1 + cp + 1 + err + 1) =
      List.replicate L0 true ++ false :: Data.unaryList [L1, nE] := by rw [d9]; simp [Data.unaryList]
  obtain ⟨σ10, e10, s10, h10, o10, p10, r10, v10, c10, d10⟩ := rstep cap (sk x 0) (Rg 0) (Rg 6) (d 0 6 (by decide)) W
    _ _ L0 dT4 σ9 (by rw [s9, s8, s7, s6, s5, s4, s3, s2, hst']) h9 p9
    (by rw [v9 _ (d 6 0 (by decide)) (d 6 5 (by decide)), v8 _ (d 6 0 (by decide)) (d 6 4 (by decide)),
      v7 _ (d 6 0 (by decide)) (d 6 3 (by decide)), base6 6 (by decide)]; omega) (by omega)
  have dT5 : W.drop (2 * L + 1 + 2 + 1 + 0 + 1 + 1 + 1 + 0 + 1 + len + 1 + cp + 1 + err + 1 + L0 + 1) =
      List.replicate L1 true ++ false :: Data.unaryList [nE] := by rw [d10]; simp [Data.unaryList]
  obtain ⟨σ11, e11, s11, h11, o11, p11, r11, v11, c11, d11⟩ := rstep cap (sk x 0) (Rg 0) (Rg 7) (d 0 7 (by decide)) W
    _ _ L1 dT5 σ10 (by rw [s10, s9, s8, s7, s6, s5, s4, s3, s2, hst']) h10 p10
    (by rw [v10 _ (d 7 0 (by decide)) (d 7 6 (by decide)), v9 _ (d 7 0 (by decide)) (d 7 5 (by decide)),
      v8 _ (d 7 0 (by decide)) (d 7 4 (by decide)), v7 _ (d 7 0 (by decide)) (d 7 3 (by decide)),
      base6 7 (by decide)]; omega) (by omega)
  have dT6 : W.drop (2 * L + 1 + 2 + 1 + 0 + 1 + 1 + 1 + 0 + 1 + len + 1 + cp + 1 + err + 1 + L0 + 1 + L1 + 1) =
      List.replicate nE true ++ false :: [] := by rw [d11]; simp [Data.unaryList]
  obtain ⟨σ12, e12, s12, h12, o12, p12, r12, v12, c12, d12⟩ := rstep cap (sk x 0) (Rg 0) (Rg 8) (d 0 8 (by decide)) W
    _ _ nE dT6 σ11 (by rw [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, hst']) h11 p11
    (by rw [v11 _ (d 8 0 (by decide)) (d 8 7 (by decide)), v10 _ (d 8 0 (by decide)) (d 8 6 (by decide)),
      v9 _ (d 8 0 (by decide)) (d 8 5 (by decide)), v8 _ (d 8 0 (by decide)) (d 8 4 (by decide)),
      v7 _ (d 8 0 (by decide)) (d 8 3 (by decide)), base6 8 (by decide)]; omega) (by omega)
  -- the request rewound
  have e13 := wrewind_spec cap (sk x 0) (Rg 0) _ σ12 p12 (by omega)
  have g3 : ∀ k : Fin 9, 3 ≤ k.val → ∀ q, q = Rg k → σ12.val q = if k.val = 3 then len else if k.val = 4 then cp
      else if k.val = 5 then err else if k.val = 6 then L0 else if k.val = 7 then L1 else nE := by
    intro k hk q hq
    subst hq
    have hk9 := k.isLt
    have n0 : Rg k ≠ Rg 0 := d k 0 (fun e => by rw [e] at hk; simp at hk)
    have c3' : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
    rcases c3' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [v12 _ n0 (d 3 8 (by decide)), v11 _ n0 (d 3 7 (by decide)), v10 _ n0 (d 3 6 (by decide)),
        v9 _ n0 (d 3 5 (by decide)), v8 _ n0 (d 3 4 (by decide)), r7, base6 3 (by decide)]
      simp
    · rw [v12 _ n0 (d 4 8 (by decide)), v11 _ n0 (d 4 7 (by decide)), v10 _ n0 (d 4 6 (by decide)),
        v9 _ n0 (d 4 5 (by decide)), r8, v7 _ n0 (d 4 3 (by decide)), base6 4 (by decide)]
      simp
    · rw [v12 _ n0 (d 5 8 (by decide)), v11 _ n0 (d 5 7 (by decide)), v10 _ n0 (d 5 6 (by decide)), r9,
        v8 _ n0 (d 5 4 (by decide)), v7 _ n0 (d 5 3 (by decide)), base6 5 (by decide)]
      simp
    · rw [v12 _ n0 (d 6 8 (by decide)), v11 _ n0 (d 6 7 (by decide)), r10, v9 _ n0 (d 6 5 (by decide)),
        v8 _ n0 (d 6 4 (by decide)), v7 _ n0 (d 6 3 (by decide)), base6 6 (by decide)]
      simp
    · rw [v12 _ n0 (d 7 8 (by decide)), r11, v10 _ n0 (d 7 6 (by decide)), v9 _ n0 (d 7 5 (by decide)),
        v8 _ n0 (d 7 4 (by decide)), v7 _ n0 (d 7 3 (by decide)), base6 7 (by decide)]
      simp
    · rw [r12, v11 _ n0 (d 8 7 (by decide)), v10 _ n0 (d 8 6 (by decide)), v9 _ n0 (d 8 5 (by decide)),
        v8 _ n0 (d 8 4 (by decide)), v7 _ n0 (d 8 3 (by decide)), base6 8 (by decide)]
      simp
  have fin : ∀ k : Fin 9, 3 ≤ k.val → ((σ12.setv (Rg 0) 0).seth (sk x 0) (σ12.sh (sk x 0) -
      2 * (2 * L + 1 + 2 + 1 + 0 + 1 + 1 + 1 + 0 + 1 + len + 1 + cp + 1 + err + 1 + L0 + 1 + L1 + 1 + nE + 1))).val
      (Rg k) = σ12.val (Rg k) := fun k hk => by
    simp only [WState.seth_val]
    exact wsetv_val_ne _ _ (d k 0 (fun e => by rw [e] at hk; simp at hk))
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
    (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 (WExec.seq e12 e13))))))))))), by omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st, WState.setv_st]
    rw [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]
  · funext s
    simp only [WState.seth_sh, WState.setv_sh]
    by_cases hs : s = sk x 0
    · rw [hs, Function.update_self, h12, hsh]
      omega
    · rw [Function.update_of_ne hs, o12 s hs, o11 s hs, o10 s hs, o9 s hs, o8 s hs, o7 s hs, o6 s hs, o5 s hs,
        o4 s hs, o3 s hs, o2 s hs]
  · simp only [WState.seth_cell, WState.setv_cell]
    rw [c12, c11, c10, c9, c8, c7, c6, c5, c4, c3, c2]
  · rw [fin 3 (by decide), g3 3 (by decide) _ rfl]; rfl
  · rw [fin 4 (by decide), g3 4 (by decide) _ rfl]; rfl
  · rw [fin 5 (by decide), g3 5 (by decide) _ rfl]; rfl
  · rw [fin 6 (by decide), g3 6 (by decide) _ rfl]; rfl
  · rw [fin 7 (by decide), g3 7 (by decide) _ rfl]; rfl
  · rw [fin 8 (by decide), g3 8 (by decide) _ rfl]; rfl
  · intro q hq
    simp only [WState.seth_val, WState.setv_val]
    rw [Function.update_of_ne (hq 0), v12 q (hq 0) (hq 8), v11 q (hq 0) (hq 7), v10 q (hq 0) (hq 6),
      v9 q (hq 0) (hq 5), v8 q (hq 0) (hq 4), v7 q (hq 0) (hq 3), v6 q (hq 0) (hq 2), v5 q (hq 0) (hq 2),
      v4 q (hq 0) (hq 2), v3 q (hq 0) (hq 2), v2 q (hq 0) (hq 1)]
  · simp only [WState.seth_val, WState.setv_val, Function.update_self]
  · simp only [WState.seth_val, WState.setv_val]
    have n10 := d 1 0 (by decide)
    rw [Function.update_of_ne n10, v12 _ n10 (d 1 8 (by decide)), v11 _ n10 (d 1 7 (by decide)),
      v10 _ n10 (d 1 6 (by decide)), v9 _ n10 (d 1 5 (by decide)), v8 _ n10 (d 1 4 (by decide)),
      v7 _ n10 (d 1 3 (by decide)), v6 _ n10 (d 1 2 (by decide)), v5 _ n10 (d 1 2 (by decide)),
      v4 _ n10 (d 1 2 (by decide)), v3 _ n10 (d 1 2 (by decide))]
    rw [h2]
    simp

end NearCubicWires.WireExponent3_5.FinalPass.TabW
