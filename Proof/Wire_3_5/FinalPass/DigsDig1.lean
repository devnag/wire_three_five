import Proof.Wire_3_5.FinalPass.DigsNav2

/-! # `DigsW`'s body, part 4: to the selected child; one weight's digit (P3:2596-2599)

`navW` (header, product, skips) leaves the head at the selected child's first weight. `wBodyW` reads one weight `w`
(`modW2W`, `V = (w mod p).toNat`), forms `a = (B · V) mod p` with the circuit's power `B = base^i mod p` (`mulLoopW`),
takes its digit `d` (`bitOfW`), appends `enc (oOff + o)` when the digit is `1` (`encW`), and counts the occurrence.
`emitW` / `emitList` are the appended words. Main declarations: **`nav_spec`**, `emitW`, `emitList`,
`emitList_append`, **`wBody_spec`**. Paper quantities: the reduced coefficient `a_i = w_i mod p` of `L_g` (as
`(base^i · w) mod p`) and its digit `v_{i,d}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires.RepairRepresentation (natWord intWord)

/-- The word appended for one occurrence `o` with coefficient residue `a` at digit `d`. -/
def emitW (off o d a : ℕ) : List Bool := if a / 2 ^ d % 2 = 1 then enc (off + o) else []

/-- The words appended for the weights `ws` (occurrences `o, o + 1, …`) of a circuit with power `B`. -/
def emitList (off d B p : ℕ) : ℕ → List ℤ → List Bool
  | _, [] => []
  | o, w :: ws => emitW off o d (B * (w % (p : ℤ)).toNat % p) ++ emitList off d B p (o + 1) ws

theorem emitList_append (off d B p : ℕ) :
    ∀ (o : ℕ) (xs ys : List ℤ), emitList off d B p o (xs ++ ys) =
      emitList off d B p o xs ++ emitList off d B p (o + xs.length) ys
  | o, [], ys => by simp [emitList]
  | o, x :: xs, ys => by
    rw [List.cons_append, emitList, emitList, emitList_append off d B p (o + 1) xs ys, List.append_assoc]
    congr 3; simp; ring

theorem emitList_take (off d B p o : ℕ) (ws : List ℤ) (k : ℕ) (hk : k < ws.length) :
    emitList off d B p o (ws.take (k + 1)) =
      emitList off d B p o (ws.take k) ++ emitW off (o + k) d (B * (ws[k] % (p : ℤ)).toNat % p) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, emitList_append,
    List.length_take_of_le hk.le]
  simp [emitList]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

@[simp] theorem mlW0 : mlW R 0 = R 26 := rfl
@[simp] theorem mlW1 : mlW R 1 = R 27 := rfl
@[simp] theorem mlW2 : mlW R 2 = R 5 := rfl
@[simp] theorem mlW3 : mlW R 3 = R 25 := rfl
@[simp] theorem mlW4 : mlW R 4 = R 39 := rfl
@[simp] theorem mlW5 : mlW R 5 = R 40 := rfl
@[simp] theorem btE0 : btE R 0 = R 26 := rfl
@[simp] theorem btE1 : btE R 1 = R 36 := rfl
@[simp] theorem btE2 : btE R 2 = R 29 := rfl
@[simp] theorem btE3 : btE R 3 = R 30 := rfl
@[simp] theorem btE4 : btE R 4 = R 31 := rfl
@[simp] theorem btE5 : btE R 5 = R 32 := rfl
@[simp] theorem btE6 : btE R 6 = R 39 := rfl
@[simp] theorem ecE0 : ecE R 0 = R 4 := rfl
@[simp] theorem ecE1 : ecE R 1 = R 37 := rfl
@[simp] theorem ecE2 : ecE R 2 = R 33 := rfl
@[simp] theorem ecE3 : ecE R 3 = R 39 := rfl
@[simp] theorem ecE4 : ecE R 4 = R 40 := rfl
@[simp] theorem ecE5 : ecE R 5 = R 34 := rfl

/-! ## To the selected child -/

/-- Header, product, skips. -/
def navW (E : Fin (ns + 1)) : WM ns nr := .seq (navHeadW R E) (.seq (prodW R) (skipsW R E))

/-- The navigation's zero registers. -/
def navL : List (Fin digsK) := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 21, 22, 39, 40]

/-- The navigation's step bound. -/
def navCost (S m g n Lm : ℕ) : ℕ := headCost S m g + 1 + (g % m * (25 * S + 13) + 1 + 1 + (n * (24 * Lm + 23) + 1))

theorem nav_spec (E : Fin (ns + 1)) (S m g : ℕ) (zs : List ℤ) (Lm : ℕ) (hLm : ∀ z ∈ zs, natBitLength z.natAbs ≤ Lm)
    (c rest : List Bool) (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 0)
    (hc : c = natWord S ++ (natWord m ++ (zs.flatMap intWord ++ rest))) (hzs : zs.length = g % m * (S + 1))
    (hz : Zs R σ navL) (hg : σ.val (R 17) = g) (hm : 1 ≤ m)
    (hcS : (natWord S).length + (natWord m).length + (zs.flatMap intWord).length ≤ cap) (hS : 2 * S + 2 ≤ cap)
    (hM : 2 * m + 2 ≤ cap) (hgc : g ≤ cap) (hzc : zs.length ≤ cap) :
    WExec cap (navW R E) σ
      (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14)
        ((natWord S).length + (natWord m).length + (zs.flatMap intWord).length))
      (navCost S m g zs.length Lm) := by
  have h18 := hz 18 (by decide)
  have h19 := hz 19 (by decide)
  have h7 := hz 7 (by decide)
  have h39 := hz 39 (by decide)
  have h40 := hz 40 (by decide)
  have d1 := navHead_spec cap R E S m g c (zs.flatMap intWord ++ rest) σ hst hs hc (Zs_sub R _ _ _ (by decide) hz)
    hg hm (by omega) hS hM hgc
  have hmS : g % m * (S + 1) ≤ cap := by omega
  have d2 := prod_spec cap R (g % m) S
    (at2 (((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 18) (g % m)) E (R 14)
      ((natWord S).length + (natWord m).length)) (by simp [at2]) (by simp [at2, h19]) (by simp [at2])
    (by simp [at2, h39]) (by simp [at2, h40]) hmS
    (le_trans (Nat.le_mul_of_pos_right _ (by omega)) hmS) (by omega)
  have d3 := skips_spec cap R E zs Lm hLm c rest ((natWord S).length + (natWord m).length)
    (((at2 (((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 18) (g % m)) E (R 14)
      ((natWord S).length + (natWord m).length)).setv (R 18) 0).setv (R 19) (g % m * (S + 1)))
    (by simp [at2, hst]) (by simp [at2]) (by simp [at2])
    (by rw [hc, ← List.append_assoc, List.drop_left' (by simp)]) (by simp [hzs]) (by simp [at2, h7]) (by omega) hzc
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ (by unfold navCost; omega)
  clear d1 d2 d3 hz
  wst_eq

/-! ## One weight's digit -/

/-- One weight: its residue, times the power, its digit `d`, the occurrence's word if the digit is `1`, `Oc += 1`. -/
def wBodyW (E Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (modW2W E (R 14) (Rg R) false) (.seq (Hash4.wcopyR (R 2) (R 27) (R 39)) (.seq (mulLoopW (mlW R))
    (.seq (WM.clear (R 27)) (.seq (bitOfW (btE R)) (.seq (WM.clear (R 26))
    (.seq (.ifr (R 31) (.seq (.dec (R 31)) (encW Dg (ecE R))) .skip) (.inc (R 37))))))))

/-- One weight's zero registers. -/
def wL : List (Fin digsK) := [5, 6, 7, 8, 9, 10, 11, 12, 13, 26, 27, 29, 30, 31, 32, 33, 39, 40]

/-- One weight's step bound. -/
def wCost (L p d off o : ℕ) : ℕ :=
  modCost2 L p + 1 + (18 * p + 3 + 1 + (p * mulStep p + 1 + 1 + (3 * p + 1 + 1 + (bitOfCost p d + 1 +
    (3 * p + 1 + 1 + (encCost (off + o) o + 3 + 1 + 3))))))

theorem wBody_spec (E Dg : Fin (ns + 1)) (hED : E ≠ Dg) (w : ℤ) (c rest : List Bool) (j p B d off o : ℕ)
    (l : List Bool) (hp : 1 ≤ p) (hpc : p ≤ cap) (hB : B < p) (σ : WState ns nr) (hst : σ.st E = frame c)
    (hs : σ.sh E = 2 * j + 1) (hpj : σ.val (R 14) = j) (hd : c.drop j = intWord w ++ rest)
    (hP : σ.val (R 2) = p) (hBv : σ.val (R 25) = B) (hdv : σ.val (R 36) = d) (hov : σ.val (R 4) = off)
    (hoc : σ.val (R 37) = o) (hlst : σ.st Dg = l) (hlsh : σ.sh Dg = l.length) (hlw : σ.val (R 34) = l.length)
    (hz : Zs R σ wL) (hjc : j + (intWord w).length ≤ cap) (hdc : d ≤ cap)
    (hlc : l.length + off + o + 2 ≤ cap) :
    WExec cap (wBodyW R E Dg) σ
      (at2 (outAt (σ.setv (R 37) (o + 1)) Dg (R 34) (l ++ emitW off o d (B * (w % (p : ℤ)).toNat % p))) E (R 14)
        (j + (intWord w).length)) (wCost (natBitLength w.natAbs) p d off o) := by
  have hPc := Rg_ne_Pc R
  have hpos : 0 < p := by omega
  obtain ⟨V, hVe⟩ : ∃ V, V = (w % (p : ℤ)).toNat := ⟨_, rfl⟩
  have hV : V < p := by
    have h1 : w % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hpos)
    have h2 : 0 ≤ w % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
    omega
  have h5 := hz 5 (by decide)
  have h26 := hz 26 (by decide)
  have h27 := hz 27 (by decide)
  have h29 := hz 29 (by decide)
  have h30 := hz 30 (by decide)
  have h31 := hz 31 (by decide)
  have h32 := hz 32 (by decide)
  have h33 := hz 33 (by decide)
  have h39 := hz 39 (by decide)
  have h40 := hz 40 (by decide)
  obtain ⟨J, hJ⟩ : ∃ J, J = j + (intWord w).length := ⟨_, rfl⟩
  -- the residue
  have d1 := modW2_spec cap E (R 14) (Rg R) hPc false w c rest j p hp hpc σ hst hs hpj hd (by simp [hP])
    (core_zero R _ (Zs_sub R _ _ _ (by decide) hz)) hjc
  rw [show (if false = true then -w else w) = w from rfl, ← hVe, ← hJ, Rg1] at d1
  -- the product
  have d2 := Hash4.wcopyR_spec cap (R 2) (R 27) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (at2 (σ.setv (R 5) V) E (R 14) J)
    (by simp [at2, h27]) (by simp [at2, h39]) (by simp [at2, hP]; omega)
  have e2 : (at2 (σ.setv (R 5) V) E (R 14) J).setv (R 27) ((at2 (σ.setv (R 5) V) E (R 14) J).val (R 2)) =
      at2 ((σ.setv (R 5) V).setv (R 27) p) E (R 14) J := by
    clear d1 d2 hz; wst_eq
  rw [e2, show (at2 (σ.setv (R 5) V) E (R 14) J).val (R 2) = p by simp [at2, hP]] at d2
  have d3 := mulLoop_spec cap (mlW R) p B hpc hB V (at2 ((σ.setv (R 5) V).setv (R 27) p) E (R 14) J) 0
    (by simp [at2]) (by omega) (by simp [at2, h26]) hpos (by simp [at2]) (by simp [at2, hBv])
    (by simp [at2, h39]) (by simp [at2, h40])
  obtain ⟨a, ha⟩ : ∃ a, a = (0 + B * V) % p := ⟨_, rfl⟩
  rw [← ha] at d3
  simp only [mlW0, mlW1, mlW2] at d3
  have hap : a < p := by rw [ha]; exact Nat.mod_lt _ hpos
  have e3 : (((at2 ((σ.setv (R 5) V).setv (R 27) p) E (R 14) J).setv (R 5) 0).setv (R 26) a).setv (R 27) (p - a) =
      at2 ((σ.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J := by
    clear d1 d2 d3 hz e2; wst_eq
  rw [e3] at d3
  have d4 := wclear_spec cap (R 27) (p - a) (at2 ((σ.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J)
    (by simp [at2]) (by simp [at2]; omega)
  have e4 : (at2 ((σ.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J).setv (R 27) 0 = at2 (σ.setv (R 26) a) E (R 14) J := by
    clear d1 d2 d3 d4 hz e2 e3; wst_eq
  rw [e4] at d4
  -- the digit
  have d5 := bitOf_spec cap (btE R) a d (by omega) hdc (by omega) (at2 (σ.setv (R 26) a) E (R 14) J)
    (by simp [at2]) (by simp [at2, hdv]) (by simp [at2, h29]) (by simp [at2, h30])
    (by simp [at2, h31]) (by simp [at2, h32]) (by simp [at2, h39])
  obtain ⟨b, hb⟩ : ∃ b, b = a / 2 ^ d % 2 := ⟨_, rfl⟩
  rw [← hb, btE4] at d5
  have hb2 : b < 2 := by rw [hb]; exact Nat.mod_lt _ (by norm_num)
  have d6 := wclear_spec cap (R 26) a ((at2 (σ.setv (R 26) a) E (R 14) J).setv (R 31) b) (by simp [at2])
    (by simp [at2]; omega)
  have e6 : ((at2 (σ.setv (R 26) a) E (R 14) J).setv (R 31) b).setv (R 26) 0 = at2 (σ.setv (R 31) b) E (R 14) J := by
    clear d1 d2 d3 d4 d5 d6 hz e2 e3 e4; wst_eq
  rw [e6] at d6
  -- the occurrence's word
  have d7 : WExec cap (.ifr (R 31) (.seq (.dec (R 31)) (encW Dg (ecE R))) .skip) (at2 (σ.setv (R 31) b) E (R 14) J)
      (outAt (at2 σ E (R 14) J) Dg (R 34) (l ++ emitW off o d a)) (encCost (off + o) o + 3) := by
    have hv : (at2 (σ.setv (R 31) b) E (R 14) J).val (R 31) = b := by simp [at2]
    by_cases h1 : b = 1
    · have de := enc_spec cap Dg (ecE R) (at2 σ E (R 14) J) off o l (by simp [at2, hov]) (by simp [at2, hoc])
        (by simp [at2, h33]) (by simp [at2, h39]) (by simp [at2, h40]) (by simp [at2, hED.symm, hlst])
        (by simp [at2, hED.symm, hlsh]) (by simp [at2, hlw]) hlc
      have dd := WExec.dec (cap := cap) (R 31) (at2 (σ.setv (R 31) b) E (R 14) J) (by rw [hv, h1]; omega)
      have edd : (at2 (σ.setv (R 31) b) E (R 14) J).setv (R 31)
          ((at2 (σ.setv (R 31) b) E (R 14) J).val (R 31) - 1) = at2 σ E (R 14) J := by
        rw [hv, h1]; clear d1 d2 d3 d4 d5 d6 hz e2 e3 e4 e6 de; wst_eq
      rw [edd] at dd
      unfold emitW; rw [← hb, if_pos h1]
      simp only [ecE5] at de
      exact WExec.cast cap (WExec.ifrT (by rw [hv, h1]; omega) (WExec.seq dd de)) rfl (by omega)
    · have h0 : b = 0 := by omega
      unfold emitW; rw [← hb, if_neg h1, List.append_nil]
      have e : outAt (at2 σ E (R 14) J) Dg (R 34) l = at2 (σ.setv (R 31) b) E (R 14) J := by
        rw [outAt_self _ _ _ _ (by simp [at2, hED.symm, hlst]) (by simp [at2, hED.symm, hlsh]) (by simp [at2, hlw]),
          h0, ThrRead.setv_eq_self σ (R 31) 0 h31]
      rw [e]
      exact WExec.mono (WExec.ifrF (by rw [hv, h0]) (WExec.skip _)) (by omega)
  have d8 := WExec.inc (cap := cap) (R 37) (outAt (at2 σ E (R 14) J) Dg (R 34) (l ++ emitW off o d a))
    (by rw [outAt_val_ne _ _ _ _ _ (R.injective.ne (by decide))]; simp [at2, hoc]; omega)
  have hcost : wCost (natBitLength w.natAbs) p d off o ≥ modCost2 (natBitLength w.natAbs) p + 1 + (18 * p + 3 + 1 +
      (V * mulStep p + 1 + 1 + (3 * (p - a) + 1 + 1 + (bitOfCost a d + 1 + (3 * a + 1 + 1 +
      (encCost (off + o) o + 3 + 1 + 3)))))) := by
    have m1 : V * mulStep p ≤ p * mulStep p := Nat.mul_le_mul_right _ hV.le
    have m2 : bitOfCost a d ≤ bitOfCost p d := by
      unfold bitOfCost halfCost
      have : d * (12 * a + 20) ≤ d * (12 * p + 20) := Nat.mul_le_mul_left _ (by omega)
      omega
    unfold wCost; omega
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6
    (WExec.seq d7 d8))))))) ?_ (by omega)
  rw [show B * (w % (p : ℤ)).toNat % p = a by rw [ha, ← hVe, Nat.zero_add], ← hJ]
  clear d1 d2 d3 d4 d5 d6 d7 d8 hcost hz e2 e3 e4 e6
  wst_eq

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
