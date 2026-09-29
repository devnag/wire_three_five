import Proof.Wire_3_5.Primitive.Writers.HashN1

/-! # HASH setup (A), part 2: `a := t` and the HASH numbers machine's run

**`aTW`** (`dA := Hb 12`, through a zero temporary), **`bigWTH`** (`numsTW`, `aTW`, the free program's words) and
**`bigTH_spec`**: from the THR cell's entry, the thirty-nine loop-entry words at the HASH call's `FreeIn` (`a := t`, the
data word's entry `12`), every other stream as at entry; `hashBigCost` its steps.

Paper quantity of the main type: the HASH stage's free numbers at the HASH call's `FreeIn`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- The temporary of `aTW` (a register of the words' zero region `64 … 249`). -/
def tHs : Fin LNR := ⟨100, by decide⟩

/-- **`a := t`**: clear `dA`, then copy `Hb 12` (the data word's entry `12`, the moment count) into it. -/
def aTW : WM (LNS 0) LNR := .seq (WM.clear dA) (FinalPass.Hash4.wcopyR (Hb 12) dA tHs)

/-- **The HASH numbers machine's program**: the THR numbers, `a := t`, the free program's words. -/
def bigWTH (F : FreeProg) (cr fe : ℕ) : WM (LNS 0) LNR := .seq (numsTW cr fe) (.seq aTW (wordsW F))

/-- The HASH numbers machine's steps. -/
def hashBigCost (cap n a nc Kb t fc : ℕ) : ℕ :=
  numsTCost cap n a nc Kb + 1 + ((3 * a + 1) + 1 + (18 * t + 3) + 1 + (400 * UnaryPow.sq cap + 1 + (fc + 1 +
    (200 * UnaryPow.sq cap + 1 + 400 * UnaryPow.sq cap))))

/-- **The HASH numbers machine's program, run**: `bigT_spec` at `a := t`. -/
theorem bigTH_spec (F : FreeProg) (cap cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n)
    (w : List Bool) (codes cc : List ℕ) (tl : List Bool) (hs xs : List ℕ) (tg Kb : ℕ)
    (hw : w = Data.reqW P.n true codes cc tl) (hhs : hs.length = 16) (hxs : xs.length ≤ 2)
    (h0v : hs.getD 0 0 = xs.length) (hKb : ∀ c ∈ codes, natBitLength c ≤ Kb)
    (cW : 2 * w.length + 2 ≤ cap)
    (cP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      Kb + P.n + codes.length + 1 ≤ cap)
    (hcl : ∀ k, (hs ++ (xs ++ [tg])).getD k 0 ≤ cap) (hcs : xs.sum + tg + 4 ≤ cap)
    (hcS : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (capT err g cu pS I Q kh gs : ℕ) (hT : hs.getD 1 0 = capT) (hg : hs.getD 2 0 = g) (hcu : hs.getD 4 0 = cu)
    (hp : hs.getD 6 0 = pS) (herr : err = fe * Nat.clog 2 (P.n + 2)) (hkh : kh = P.s * (P.r / 2))
    (hgs : gs = 2 ^ (gP P.n capT err).seedBits)
    (cT1 : 1 ≤ capT) (cT : capT * 32 + 2 ≤ cap) (cL : 2 * (P.n + 1) ^ 26 + 8 ≤ cap) (cE : err + 4 ≤ cap)
    (cSB : 2 ^ ((gP P.n capT err).seedBits + 1) ≤ cap)
    (cLB : (gP P.n capT err).labelBits + (gP P.n capT err).fieldBits + (gP P.n capT err).walkLen + 512 ≤ cap)
    (cB : 2 * (g * cu) + 2 ≤ cap)
    (hI : I = g * pS * 2 ^ (gP P.n capT err).seedBits * (2 * (g * cu) + 1) * (2 * (g * cu) + 1) + 1)
    (hQ : Q = 2 ^ ((kh * 5 + 3) / 2 / 2) * (I * 8192 * P.n * P.n)) (hn : 2 ≤ P.n) (cQ2 : 2 * Q ≤ cap)
    (hsc : SeedCap cap Q kh gs g pS P.b P.s (P.r / 2) P.r P.n)
    (x : FreeIn) (hx : x = ⟨P.n, kh, Nat.clog 2 (P.n + 2), capT, hs.getD 12 0, cc.length, hs.getD 7 0, Q,
      max (kh + kh) (Nat.clog 2 Q), gs * g * pS, wOf kh Q, (P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)⟩)
    (hF : F.ok cap x) (hdc : DerCap cap Q kh (F.val x 0) (F.val x 1))
    (cQl : Q - 1 < 2 ^ max (kh + kh) (Nat.clog 2 Q)) (cQ : Q + 1 ≤ cap)
    (cl : 3 * max (kh + kh) (Nat.clog 2 Q) + Q + 3 ≤ cap) (ck : kh + kh + 1 ≤ cap)
    (cfr : ∀ j, F.val x j + F.val x j + 3 ≤ cap)
    (cdd : ∀ i, derVals Q kh (F.val x 0) (F.val x 1) i + derVals Q kh (F.val x 0) (F.val x 1) i + 3 ≤ cap)
    (ccnt : gs * g * pS * 2 ^ wOf kh Q + 1 ≤ cap)
    (cd2 : (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) +
        ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2))) +
      (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) +
        ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2))) + 3 ≤ cap)
    (c17 : 17 ≤ cap) :
    ∃ τ c, WExec cap (bigWTH F cr fe) (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))) τ c ∧
      c ≤ hashBigCost cap P.n codes.length cc.length Kb (hs.getD 12 0) (F.cost cap x) ∧
      (∀ j : Fin 39, τ.st (sk 0 (symO j)) = symClean Q kh (max (kh + kh) (Nat.clog 2 Q)) (gs * g * pS * 2 ^ wOf kh Q)
        (0 + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)) + ((P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2)))
        (F.val x) (derVals Q kh (F.val x 0) (F.val x 1)) j) ∧
      (∀ s, (∀ j : Fin 39, s ≠ sk 0 (symO j)) →
        τ.st s = (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (hs ++ (xs ++ [tg])))).st s) ∧
      τ.cell = false := by
  obtain ⟨τ1, c1, e1, c1le, v1N, v1A, v1NC, v1MS, v1L, v1r, v1s, v1b, v1r2, v1kh, v1k, v1err, v1cap, v1G21, v1G41,
    v1G52, v1KB, v1z, v1st, v1sh, v1cl, v1H12⟩ := numsTH_spec cap cr fe P hrP w codes cc tl hs xs tg Kb hw hhs hxs h0v hKb
      cW cP hcl hcs hcS capT err g cu pS I Q hT hg hcu hp herr cT1 cT cL cE cSB cLB cB hI (by rw [← hkh]; exact hQ) hn cQ2
  have hac : codes.length ≤ cap := by
    have p1 : 1 ≤ 2 ^ (natBitLength P.n + 1) := Nat.one_le_two_pow
    have p2 : 1 ≤ 2 ^ (natBitLength codes.length + 1) := Nat.one_le_two_pow
    have p3 : 1 ≤ 2 ^ (natBitLength cc.length + 1) := Nat.one_le_two_pow
    omega
  have h12 : hs.getD 12 0 ≤ cap := by
    have := hcl 12; rwa [List.getD_append _ _ _ _ (by omega)] at this
  -- `a := t`
  have eA := wclear_spec cap dA codes.length τ1 v1A (by omega)
  have ht0 : (τ1.setv dA 0).val tHs = 0 := by
    rw [WState.setv_val, Function.update_of_ne (show tHs ≠ dA by decide)]; exact v1z tHs (by decide) (by decide)
  have hb0 : (τ1.setv dA 0).val dA = 0 := by simp
  have h12' : (τ1.setv dA 0).val (Hb 12) = hs.getD 12 0 := by
    rw [WState.setv_val, Function.update_of_ne (show (Hb 12 : Fin LNR) ≠ dA by decide)]; exact v1H12
  have eB := FinalPass.Hash4.wcopyR_spec cap (Hb 12) dA tHs (by decide) (by decide) (by decide) (τ1.setv dA 0) hb0 ht0
    (by rw [h12']; exact h12)
  rw [h12'] at eB
  obtain ⟨σ2, hσ2⟩ : ∃ s, s = (τ1.setv dA 0).setv dA (hs.getD 12 0) := ⟨_, rfl⟩
  rw [← hσ2] at eB
  have k2 : ∀ r : Fin LNR, r ≠ dA → σ2.val r = τ1.val r := fun r h => by
    rw [hσ2, WState.setv_val, Function.update_of_ne h, WState.setv_val, Function.update_of_ne h]
  have v2A : σ2.val dA = hs.getD 12 0 := by rw [hσ2]; simp
  have st2 : σ2.st = τ1.st ∧ σ2.sh = τ1.sh ∧ σ2.cell = τ1.cell := by rw [hσ2]; simp
  have hsk : ∀ k : Fin 161, 120 ≤ k.val → σ2.st (sk 0 k) = [] := by
    intro k hk
    have n0 : sk 0 k ≠ sk 0 0 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n1 : sk 0 k ≠ sk 0 1 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n2 : sk 0 k ≠ sk 0 2 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    have n3 : sk 0 k ≠ sk 0 113 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    rw [st2.1, v1st]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply, n0, n1, n2, n3]
  have hsh : ∀ k : Fin 161, 120 ≤ k.val → σ2.sh (sk 0 k) = 0 := by
    intro k hk
    have n3 : sk 0 k ≠ sk 0 113 := fun e => by have := congrArg Fin.val e; simp [sk] at this; omega
    rw [st2.2.1, v1sh _ n3]
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets, Function.update_apply]
  have hz2 : ∀ q : Fin LNR, 64 ≤ q.val → q.val < 250 → σ2.val q = 0 := fun q h1 h2 => by
    rw [k2 q (fun e => by subst e; exact absurd h2 (by decide))]; exact v1z q h1 h2
  obtain ⟨τ, c, e, cle, hwd, hrest, hcl5⟩ := words_spec F cap σ2 Q kh gs g pS P.b P.s (P.r / 2) P.r P.n
    (Nat.clog 2 (P.n + 2)) capT (hs.getD 12 0) cc.length (hs.getD 7 0)
    (by rw [k2 _ (by decide)]; exact v1KB) (by rw [k2 _ (by decide), hkh]; exact v1kh)
    (by rw [k2 _ (by decide), hgs]; exact v1G21) (by rw [k2 _ (by decide)]; exact v1G41)
    (by rw [k2 _ (by decide)]; exact v1G52) (by rw [k2 _ (by decide)]; exact v1b) (by rw [k2 _ (by decide)]; exact v1s)
    (by rw [k2 _ (by decide)]; exact v1r2) (by rw [k2 _ (by decide)]; exact v1r) (by rw [k2 _ (by decide)]; exact v1N)
    (by rw [k2 _ (by decide)]; exact v1L) (by rw [k2 _ (by decide)]; exact v1cap) v2A
    (by rw [k2 _ (by decide)]; exact v1NC) (by rw [k2 _ (by decide)]; exact v1MS) hz2 hsk hsh hsc x hx hF hdc
    cQl cQ cl ck cfr cdd ccnt cd2 c17
  refine ⟨τ, _, WExec.seq e1 (WExec.seq (WExec.seq eA eB) e), ?_, hwd, fun s hs' => ?_, ?_⟩
  · unfold hashBigCost; omega
  · rw [hrest s hs', st2.1, v1st]
  · rw [hcl5, st2.2.2, v1cl]

end NearCubicWires.WireExponent3_5.PrimAsm.ThrNums
