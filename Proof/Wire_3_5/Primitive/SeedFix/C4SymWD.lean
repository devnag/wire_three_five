import Proof.Wire_3_5.Primitive.SeedFix.C4SymWC

/-! # C4 SYM stage, part 4: the loop's entry on the SYM setup's bank (`C4Wrap.LoopEntry.entry`)

"The processor writes the pool, the enumeration's rulers and constants, and the compiler request's numbers before the
loop" (P3:3011-3016); "For each candidate child prefix [...] sum the recovered integers" (P3:3034-3036). At the bank the
SYM setup leaves (`C4Cap.setup_run2`'s exit: the thirty-nine words `symClean` on `gW`, the batch on port `1`, the modulus
word, the mask, the driver, the compiler fields, the log, `2^ρ` falses on the loop's cells), every tape of the decision
loop docked by `slx oLP _ (symExt L pd)` carries the loop's bank before its first decision (`C4Wrap.loopBank F R L 0`),
for any child family of the shape `ChShape`, given the numbers' links (the setup's `ℓ`, `kh`, `Q`, the derived numbers,
the counter `n_T·2^w`, the modulus, the mask) (**`SymBank`**).

* `SymBank`, `frame_rep_false`, `binary_one`, `frame_bin1`, one lemma per docked tape (`ent_*`), **`entry_all`**.

Paper quantity of the main type: the loop's entry bank (the kept words of `P3:3011-3016`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimAsm (FiltRec.reps)

/-- **The SYM setup's exit bank and the numbers' links** (at the numbers machine's values `Q, kh, ℓ, cnt, d₂, fr, dd`). -/
structure SymBank (L : Lay) (pd : ℕ) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr)) (TWd Cap nT : ℕ)
    (pre post : List Bool) (q uu : ℕ) (B : Fin L.N → List Bool) (ρ : ℕ) (v : List Bool)
    (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ) : Prop where
  hW : ∀ k, B (L.gW k) = symClean Q kh ell cnt d2 fr dd k
  hP1 : B L.gP1 = v
  hMA : B L.gMA = frame (binary ell (GF.firstPrimitive ell))
  hUU : B L.gUU = List.replicate (2 ^ d2) true
  hRR : B L.gRR = List.replicate (2 ^ ρ) true
  hPRE : B L.gPRE = frame pre
  hPOST : B L.gPOST = frame post
  hLG : B L.gLG = List.replicate (2 ^ ρ + 1) false
  hmask : ∀ i : Fin L.N, L.maskLP i = true → B i = List.replicate (2 ^ ρ) false
  e_ell : P.ell = ell
  e_kh : P.kh = kh
  e_Q : P.Q = Q
  e_ellQ : ell = max (kh + kh) (Nat.clog 2 Q)
  e_TW : fr 0 = TWd
  e_Cap : fr 1 = Cap
  e_q : fr 2 = q
  e_dd : dd = derVals Q kh TWd Cap
  e_cnt : cnt = nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh)
  e_mod : P.modulus = GF.firstPrimitive ell
  e_uu : uu = 2 ^ d2
  e_v : v = SeedFix.blockWord ents
  h_ell1 : 1 ≤ ell

theorem frame_rep_false : ∀ k : ℕ, frame (List.replicate k false) = FiltRec.reps k [true, false] ++ [false]
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ]
    show true :: false :: frame (List.replicate k false) = _
    rw [frame_rep_false k]
    simp [FiltRec.reps, List.replicate_succ]

theorem binary_zero : ∀ k : ℕ, binary k 0 = List.replicate k false
  | 0 => rfl
  | k + 1 => by
    show (0 % 2 == 1) :: binary k (0 / 2) = _
    rw [Nat.zero_div, binary_zero k]
    rfl

theorem frame_bin1 (w : ℕ) (hw : 1 ≤ w) : frame (binary w 1) = [true, true] ++ FiltRec.reps (w - 1) [true, false] ++ [false] := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  show frame ((1 % 2 == 1) :: binary k (1 / 2)) = _
  rw [show (1 : ℕ) / 2 = 0 from rfl, binary_zero]
  show true :: true :: frame (List.replicate k false) = _
  rw [frame_rep_false]
  simp

theorem loopBank_ltV (F : C4Loop.ChildFam) (R L V : ℕ) (hV : V < F.T + 1 + 1 + 1) (h : V < F.T) :
    C4Wrap.loopBank F R L 0 ⟨V, hV⟩ = F.src R 0 ⟨V, h⟩ := loopBank_lt F R L ⟨V, hV⟩ h

theorem src_keptV (F : C4Loop.ChildFam) (R V : ℕ) (hV : V < F.T) (hi : V < F.t) (hk : F.keep ⟨V, hi⟩ = true) :
    F.src R 0 ⟨V, hV⟩ = C4Loop.cin F.PFX F.keep F.K [] ⟨V, hi⟩ := src_kept F R ⟨V, hV⟩ hi hk

theorem cin_kept (F : C4Loop.ChildFam) (V : ℕ) (hi : V < F.t) (hP : V ≠ F.PFX.val) (hk : F.keep ⟨V, hi⟩ = true) :
    C4Loop.cin F.PFX F.keep F.K [] ⟨V, hi⟩ = F.K ⟨V, hi⟩ := by
  unfold C4Loop.cin
  rw [if_neg (fun e => hP (by rw [← e])), if_pos hk]

theorem cin_pfx (F : C4Loop.ChildFam) (V : ℕ) (hi : V < F.t) (hP : V = F.PFX.val) :
    C4Loop.cin F.PFX F.keep F.K [] ⟨V, hi⟩ = frame [] := by
  unfold C4Loop.cin
  rw [if_pos (Fin.ext hP)]

section Entry
variable (L : Lay) (F : C4Loop.ChildFam) (pd : ℕ) (P : Sampler.SeedParams) (ents : List (List SeedFix.SExpr))
  (TWd Cap nT : ℕ) (pre post : List Bool) (q uu : ℕ) (B : Fin L.N → List Bool) (ρ : ℕ) (v : List Bool)
  (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)
  (hS : ChShape F pd P ents TWd Cap nT pre post q uu)
  (hB : SymBank L pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd)
  (hoff : L.oLP + (F.T + 1 + 1 + 1) ≤ L.N)

include hS hB in
theorem ent_6 (h : 6 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨6, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨6, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨6, h⟩ = L.gW ⟨0, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (6) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (6) = (L.gW ⟨0, by decide⟩).val
    rw [tv2 L pd 6 rfl]
    show _ = 9925 + 3 * L.U + (symO ⟨0, by decide⟩).val
    have : (symO ⟨0, by decide⟩).val = 120 := rfl
    omega
  have hkp : F.keep ⟨6, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (6) h (by omega), src_keptV F _ (6) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 6 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate ell true = List.replicate P.ell true
  rw [hB.e_ell]

include hS hB in
theorem ent_8 (h : 8 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨8, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨8, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨8, h⟩ = L.gW ⟨1, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (8) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (8) = (L.gW ⟨1, by decide⟩).val
    rw [tv3 L pd 8 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨1, by decide⟩).val
    have : (symO ⟨1, by decide⟩).val = 121 := rfl
    omega
  have hkp : F.keep ⟨8, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (8) h (by omega), src_keptV F _ (8) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 8 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate kh true = List.replicate P.kh true
  rw [hB.e_kh]

include hS hB in
theorem ent_9 (h : 9 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨9, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨9, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨9, h⟩ = L.gW ⟨2, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (9) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (9) = (L.gW ⟨2, by decide⟩).val
    rw [tv3 L pd 9 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨2, by decide⟩).val
    have : (symO ⟨2, by decide⟩).val = 122 := rfl
    omega
  have hkp : F.keep ⟨9, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (9) h (by omega), src_keptV F _ (9) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 9 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (fr 0) true = List.replicate TWd true
  rw [hB.e_TW]

include hS hB in
theorem ent_10 (h : 10 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨10, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨10, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨10, h⟩ = L.gW ⟨3, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (10) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (10) = (L.gW ⟨3, by decide⟩).val
    rw [tv3 L pd 10 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨3, by decide⟩).val
    have : (symO ⟨3, by decide⟩).val = 123 := rfl
    omega
  have hkp : F.keep ⟨10, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (10) h (by omega), src_keptV F _ (10) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 10 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (fr 1) true = List.replicate Cap true
  rw [hB.e_Cap]

include hS hB in
theorem ent_11 (h : 11 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨11, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨11, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨11, h⟩ = L.gW ⟨4, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (11) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (11) = (L.gW ⟨4, by decide⟩).val
    rw [tv3 L pd 11 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨4, by decide⟩).val
    have : (symO ⟨4, by decide⟩).val = 124 := rfl
    omega
  have hkp : F.keep ⟨11, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (11) h (by omega), src_keptV F _ (11) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 11 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (kh + kh) true = List.replicate (2 * P.kh) true
  rw [hB.e_kh, two_mul]

include hS hB in
theorem ent_12 (h : 12 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨12, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨12, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨12, h⟩ = L.gW ⟨5, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (12) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (12) = (L.gW ⟨5, by decide⟩).val
    rw [tv3 L pd 12 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨5, by decide⟩).val
    have : (symO ⟨5, by decide⟩).val = 125 := rfl
    omega
  have hkp : F.keep ⟨12, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (12) h (by omega), src_keptV F _ (12) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 12 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (dd 0) true = List.replicate (2 * P.kh + TWd) true
  rw [hB.e_dd, hB.e_kh]
  show List.replicate (kh + kh + TWd) true = _
  rw [two_mul]

include hS hB in
theorem ent_13 (h : 13 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨13, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨13, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨13, h⟩ = L.gW ⟨6, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (13) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (13) = (L.gW ⟨6, by decide⟩).val
    rw [tv3 L pd 13 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨6, by decide⟩).val
    have : (symO ⟨6, by decide⟩).val = 126 := rfl
    omega
  have hkp : F.keep ⟨13, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (13) h (by omega), src_keptV F _ (13) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 13 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (dd 1) true = List.replicate (8 * (P.ell * (2 * P.ell + 1)) + Cap) true
  rw [hB.e_dd]
  show List.replicate (max (kh + kh) (Nat.clog 2 Q) * 8 * (max (kh + kh) (Nat.clog 2 Q) + max (kh + kh) (Nat.clog 2 Q) + 1) + Cap) true = _
  rw [← hB.e_ellQ, hB.e_ell]
  congr 1
  ring

include hS hB in
theorem ent_14 (h : 14 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨14, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨14, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨14, h⟩ = L.gW ⟨7, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (14) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (14) = (L.gW ⟨7, by decide⟩).val
    rw [tv3 L pd 14 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨7, by decide⟩).val
    have : (symO ⟨7, by decide⟩).val = 127 := rfl
    omega
  have hkp : F.keep ⟨14, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (14) h (by omega), src_keptV F _ (14) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 14 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (dd 2) true = List.replicate (8 + 8 * P.ell + 8 * P.kh + 1) true
  rw [hB.e_dd]
  show List.replicate (wOf kh Q + 1) true = _
  unfold wOf
  rw [← hB.e_ellQ, hB.e_ell, hB.e_kh]
  congr 1
  ring

include hS hB in
theorem ent_15 (h : 15 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨15, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨15, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨15, h⟩ = L.gW ⟨8, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (15) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (15) = (L.gW ⟨8, by decide⟩).val
    rw [tv3 L pd 15 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨8, by decide⟩).val
    have : (symO ⟨8, by decide⟩).val = 128 := rfl
    omega
  have hkp : F.keep ⟨15, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (15) h (by omega), src_keptV F _ (15) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 15 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (dd 3) true = List.replicate (8 + 8 * P.ell + 8 * P.kh + TWd + 1) true
  rw [hB.e_dd]
  show List.replicate (wOf kh Q + 1 + TWd) true = _
  unfold wOf
  rw [← hB.e_ellQ, hB.e_ell, hB.e_kh]
  congr 1
  ring

include hS hB in
theorem ent_16 (h : 16 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨16, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨16, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨16, h⟩ = L.gW ⟨9, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (16) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (16) = (L.gW ⟨9, by decide⟩).val
    rw [tv3 L pd 16 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨9, by decide⟩).val
    have : (symO ⟨9, by decide⟩).val = 129 := rfl
    omega
  have hkp : F.keep ⟨16, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (16) h (by omega), src_keptV F _ (16) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 16 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (dd 4) true = List.replicate (8 * P.ell) true
  rw [hB.e_dd]
  show List.replicate (max (kh + kh) (Nat.clog 2 Q) * 8) true = _
  rw [← hB.e_ellQ, hB.e_ell]
  congr 1
  ring

include hS hB in
theorem ent_73 (h : 73 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨73, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨73, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨73, h⟩ = L.gW ⟨11, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (73) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (73) = (L.gW ⟨11, by decide⟩).val
    rw [tv5 L pd 73 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨11, by decide⟩).val
    have : (symO ⟨11, by decide⟩).val = 131 := rfl
    omega
  have hkp : F.keep ⟨73, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (73) h (by omega), src_keptV F _ (73) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 73 (by norm_num) (by norm_num) (by omega), hB.hW]
  show Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits ell (Q - 1)) ++ [false] = frame (binary P.ell (P.Q - 1))
  rw [C4Frame.frame_marks, ← CompilerMachine.Pool.fixedWidth_eq_binary, hB.e_ell, hB.e_Q]

include hS hB in
theorem ent_74 (h : 74 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨74, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨74, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨74, h⟩ = L.gW ⟨12, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (74) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (74) = (L.gW ⟨12, by decide⟩).val
    rw [tv5 L pd 74 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨12, by decide⟩).val
    have : (symO ⟨12, by decide⟩).val = 132 := rfl
    omega
  have hkp : F.keep ⟨74, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (74) h (by omega), src_keptV F _ (74) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 74 (by norm_num) (by norm_num) (by omega), hB.hW]
  rfl

include hS hB in
theorem ent_75 (h : 75 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨75, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨75, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨75, h⟩ = L.gW ⟨13, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (75) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (75) = (L.gW ⟨13, by decide⟩).val
    rw [tv5 L pd 75 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨13, by decide⟩).val
    have : (symO ⟨13, by decide⟩).val = 133 := rfl
    omega
  have hkp : F.keep ⟨75, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (75) h (by omega), src_keptV F _ (75) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 75 (by norm_num) (by norm_num) (by omega), hB.hW]
  show Streaming.marks (List.replicate 8 true) ++ [false] = frame (List.replicate 8 true)
  rw [C4Frame.frame_marks]

include hS hB in
theorem ent_77 (h : 77 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨77, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨77, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨77, h⟩ = L.gW ⟨14, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (77) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (77) = (L.gW ⟨14, by decide⟩).val
    rw [tv5 L pd 77 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨14, by decide⟩).val
    have : (symO ⟨14, by decide⟩).val = 135 := rfl
    omega
  have hkp : F.keep ⟨77, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (77) h (by omega), src_keptV F _ (77) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 77 (by norm_num) (by norm_num) (by omega), hB.hW]
  rfl

include hS hB in
theorem ent_78 (h : 78 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨78, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨78, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨78, h⟩ = L.gW ⟨15, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (78) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (78) = (L.gW ⟨15, by decide⟩).val
    rw [tv5 L pd 78 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨15, by decide⟩).val
    have : (symO ⟨15, by decide⟩).val = 136 := rfl
    omega
  have hkp : F.keep ⟨78, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (78) h (by omega), src_keptV F _ (78) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 78 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate ell true ++ [false] = List.replicate P.ell true ++ [false]
  rw [hB.e_ell]

include hS hB in
theorem ent_79 (h : 79 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨79, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨79, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨79, h⟩ = L.gW ⟨16, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (79) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (79) = (L.gW ⟨16, by decide⟩).val
    rw [tv5 L pd 79 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨16, by decide⟩).val
    have : (symO ⟨16, by decide⟩).val = 137 := rfl
    omega
  have hkp : F.keep ⟨79, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (79) h (by omega), src_keptV F _ (79) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 79 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate kh true ++ [false] = List.replicate P.kh true ++ [false]
  rw [hB.e_kh]

include hS hB in
theorem ent_80 (h : 80 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨80, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨80, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨80, h⟩ = L.gW ⟨17, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (80) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (80) = (L.gW ⟨17, by decide⟩).val
    rw [tv5 L pd 80 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨17, by decide⟩).val
    have : (symO ⟨17, by decide⟩).val = 138 := rfl
    omega
  have hkp : F.keep ⟨80, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (80) h (by omega), src_keptV F _ (80) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 80 (by norm_num) (by norm_num) (by omega), hB.hW]
  rfl

include hS hB in
theorem ent_81 (h : 81 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨81, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨81, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨81, h⟩ = L.gW ⟨18, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (81) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (81) = (L.gW ⟨18, by decide⟩).val
    rw [tv5 L pd 81 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨18, by decide⟩).val
    have : (symO ⟨18, by decide⟩).val = 139 := rfl
    omega
  have hkp : F.keep ⟨81, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (81) h (by omega), src_keptV F _ (81) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 81 (by norm_num) (by norm_num) (by omega), hB.hW]
  rfl

include hS hB in
theorem ent_82 (h : 82 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨82, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨82, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨82, h⟩ = L.gW ⟨19, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (82) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (82) = (L.gW ⟨19, by decide⟩).val
    rw [tv5 L pd 82 (by norm_num) (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨19, by decide⟩).val
    have : (symO ⟨19, by decide⟩).val = 140 := rfl
    omega
  have hkp : F.keep ⟨82, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (82) h (by omega), src_keptV F _ (82) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 82 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (kh + kh) true ++ [false] = List.replicate (2 * P.kh) true ++ [false]
  rw [hB.e_kh, two_mul]

include hS hB in
theorem ent_84 (h : 84 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨84, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨84, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨84, h⟩ = L.gW ⟨20, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (84) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (84) = (L.gW ⟨20, by decide⟩).val
    rw [tv7 L pd 84 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨20, by decide⟩).val
    have : (symO ⟨20, by decide⟩).val = 141 := rfl
    omega
  have hkp : F.keep ⟨84, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (84) h (by omega), src_keptV F _ (84) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 84 (by norm_num) (by norm_num) (by omega), hB.hW]
  rfl

include hS hB in
theorem ent_85 (h : 85 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨85, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨85, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨85, h⟩ = L.gW ⟨21, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (85) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (85) = (L.gW ⟨21, by decide⟩).val
    rw [tv7 L pd 85 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨21, by decide⟩).val
    have : (symO ⟨21, by decide⟩).val = 142 := rfl
    omega
  have hkp : F.keep ⟨85, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (85) h (by omega), src_keptV F _ (85) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 85 (by norm_num) (by norm_num) (by omega), hB.hW]
  rfl

include hS hB in
theorem ent_86 (h : 86 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨86, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨86, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨86, h⟩ = L.gW ⟨22, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (86) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (86) = (L.gW ⟨22, by decide⟩).val
    rw [tv7 L pd 86 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨22, by decide⟩).val
    have : (symO ⟨22, by decide⟩).val = 143 := rfl
    omega
  have hkp : F.keep ⟨86, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (86) h (by omega), src_keptV F _ (86) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 86 (by norm_num) (by norm_num) (by omega), hB.hW]
  show [true, true] ++ FiltRec.reps (dd 6) [true, false] ++ [false] = frame (binary P.ell 1)
  rw [hB.e_ell, frame_bin1 ell hB.h_ell1, hB.e_dd]
  show [true, true] ++ FiltRec.reps (max (kh + kh) (Nat.clog 2 Q) - 1) [true, false] ++ [false] = _
  rw [← hB.e_ellQ]

include hS hB in
theorem ent_87 (h : 87 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨87, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨87, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨87, h⟩ = L.gW ⟨23, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (87) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (87) = (L.gW ⟨23, by decide⟩).val
    rw [tv7 L pd 87 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨23, by decide⟩).val
    have : (symO ⟨23, by decide⟩).val = 144 := rfl
    omega
  have hkp : F.keep ⟨87, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (87) h (by omega), src_keptV F _ (87) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 87 (by norm_num) (by norm_num) (by omega), hB.hW]
  rfl

include hS hB in
theorem ent_88 (h : 88 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨88, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨88, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨88, h⟩ = L.gW ⟨24, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (88) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (88) = (L.gW ⟨24, by decide⟩).val
    rw [tv7 L pd 88 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨24, by decide⟩).val
    have : (symO ⟨24, by decide⟩).val = 145 := rfl
    omega
  have hkp : F.keep ⟨88, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (88) h (by omega), src_keptV F _ (88) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 88 (by norm_num) (by norm_num) (by omega), hB.hW]
  show List.replicate (fr 0) true ++ [false] = List.replicate TWd true ++ [false]
  rw [hB.e_TW]

include hS hB in
theorem ent_89 (h : 89 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨89, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨89, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨89, h⟩ = L.gW ⟨25, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (89) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (89) = (L.gW ⟨25, by decide⟩).val
    rw [tv7 L pd 89 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨25, by decide⟩).val
    have : (symO ⟨25, by decide⟩).val = 146 := rfl
    omega
  have hkp : F.keep ⟨89, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (89) h (by omega), src_keptV F _ (89) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 89 (by norm_num) (by norm_num) (by omega), hB.hW]
  show [false] ++ List.replicate cnt true = RepairSource.VerifierDecoding.CompareMachine.word (nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh))
  rw [hB.e_cnt]
  rfl

include hS hB in
theorem ent_76 (h : 76 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨76, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨76, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨76, h⟩ = L.gP1 := by
    rw [slx_some (symExt_isK L pd (show isK pd (76) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (76) = (L.gP1).val
    rw [tv4 L pd 76 rfl]
    rfl
  have hkp : F.keep ⟨76, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (76) h (by omega), src_keptV F _ (76) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 76 (by norm_num) (by norm_num) (by omega), hB.hP1, hB.e_v]
  rfl

include hS hB in
theorem ent_83 (h : 83 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨83, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨83, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨83, h⟩ = L.gMA := by
    rw [slx_some (symExt_isK L pd (show isK pd (83) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (83) = (L.gMA).val
    rw [tv6 L pd 83 rfl]
    rfl
  have hkp : F.keep ⟨83, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (83) h (by omega), src_keptV F _ (83) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.keu 83 (by norm_num) (by norm_num) (by omega), hB.hMA]
  show frame (binary ell (GF.firstPrimitive ell)) = frame (binary P.ell P.modulus)
  rw [hB.e_mod, hB.e_ell]

include hS hB in
theorem ent_17 (h : 17 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨17, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨17, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨17, h⟩ = L.gW ⟨10, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (17) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (17) = (L.gW ⟨10, by decide⟩).val
    rw [tv3 L pd 17 (by norm_num) (by norm_num)]
    show _ = 9925 + 3 * L.U + (symO ⟨10, by decide⟩).val
    have : (symO ⟨10, by decide⟩).val = 130 := rfl
    omega
  have hkp : F.keep ⟨17, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (17) h (by omega), src_keptV F _ (17) (by omega) (by omega) hkp]
  rw [cin_pfx F _ (by omega) (by rw [hS.pfx]), hB.hW]
  rfl

include hS hB in
theorem ent_0 (h : 0 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨0, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨0, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨0, h⟩ = L.gPRE := by
    rw [slx_some (symExt_isK L pd (show isK pd (0) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (0) = (L.gPRE).val
    rw [tv0 L pd 0 rfl]
    rfl
  have hkp : F.keep ⟨0, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (0) h (by omega), src_keptV F _ (0) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.k0 (by omega), hB.hPRE]

include hS hB in
theorem ent_2 (h : 2 < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨2, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨2, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨2, h⟩ = L.gPOST := by
    rw [slx_some (symExt_isK L pd (show isK pd (2) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (2) = (L.gPOST).val
    rw [tv1 L pd 2 rfl]
    rfl
  have hkp : F.keep ⟨2, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (2) h (by omega), src_keptV F _ (2) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.k2 (by omega), hB.hPOST]

include hS hB in
theorem ent_qq (h : 199 + pd < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨199 + pd, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨199 + pd, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨199 + pd, h⟩ = L.gW ⟨26, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (199 + pd) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (199 + pd) = (L.gW ⟨26, by decide⟩).val
    rw [tv8 L pd (199 + pd) rfl]
    show _ = 9925 + 3 * L.U + (symO ⟨26, by decide⟩).val
    have : (symO ⟨26, by decide⟩).val = 147 := rfl
    omega
  have hkp : F.keep ⟨199 + pd, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (199 + pd) h (by omega), src_keptV F _ (199 + pd) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.kqq (by omega), hB.hW]
  show List.replicate (fr 2) true = _
  rw [hB.e_q]

include hS hB in
theorem ent_uu (h : 200 + pd < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨200 + pd, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨200 + pd, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨200 + pd, h⟩ = L.gUU := by
    rw [slx_some (symExt_isK L pd (show isK pd (200 + pd) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (200 + pd) = (L.gUU).val
    rw [tv9 L pd (200 + pd) rfl]
    rfl
  have hkp : F.keep ⟨200 + pd, by omega⟩ = true := by rw [hS.keep]; exact decide_eq_true (by unfold kept; omega)
  rw [e, loopBank_ltV F _ _ (200 + pd) h (by omega), src_keptV F _ (200 + pd) (by omega) (by omega) hkp]
  rw [cin_kept F _ (by omega) (by rw [hS.pfx]; omega) hkp]
  rw [hS.kuu (by omega), hB.hUU, hB.e_uu]

include hS hB in
theorem ent_log (h : 410 + 2 * pd < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨410 + 2 * pd, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨410 + 2 * pd, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨410 + 2 * pd, h⟩ = L.gLG := by
    rw [slx_some (symExt_isK L pd (show isK pd (410 + 2 * pd) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (410 + 2 * pd) = (L.gLG).val
    rw [tv10 L pd (410 + 2 * pd) rfl]
    rfl
  rw [e]
  rw [loopBank_log F _ _ ⟨410 + 2 * pd, h⟩ (by show 410 + 2 * pd = F.T; omega), hB.hLG]

include hS hB in
theorem ent_drv (h : 411 + 2 * pd < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨411 + 2 * pd, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨411 + 2 * pd, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨411 + 2 * pd, h⟩ = L.gRR := by
    rw [slx_some (symExt_isK L pd (show isK pd (411 + 2 * pd) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (411 + 2 * pd) = (L.gRR).val
    rw [tv11 L pd (411 + 2 * pd) rfl]
    rfl
  rw [e]
  rw [loopBank_drv F _ _ ⟨411 + 2 * pd, h⟩ (by show 411 + 2 * pd = F.T + 1; omega), hB.hRR]

include hS hB in
theorem ent_cnt (h : 412 + 2 * pd < F.T + 1 + 1 + 1) :
    B (slx L.oLP hoff (symExt L pd) ⟨412 + 2 * pd, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨412 + 2 * pd, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have e : slx L.oLP hoff (symExt L pd) ⟨412 + 2 * pd, h⟩ = L.gW ⟨27, by decide⟩ := by
    rw [slx_some (symExt_isK L pd (show isK pd (412 + 2 * pd) by unfold isK; omega))]
    apply Fin.ext
    show tgtV L pd (412 + 2 * pd) = (L.gW ⟨27, by decide⟩).val
    rw [tv12 L pd (412 + 2 * pd) rfl]
    show _ = 9925 + 3 * L.U + (symO ⟨27, by decide⟩).val
    have : (symO ⟨27, by decide⟩).val = 148 := rfl
    omega
  rw [e]
  rw [loopBank_cnt F _ _ ⟨412 + 2 * pd, h⟩ (by show 412 + 2 * pd = F.T + 2; omega), hB.hW, hS.bound]
  show [false] ++ List.replicate (dd 4) true = false :: List.replicate (8 * P.ell) true
  rw [hB.e_dd]
  show [false] ++ List.replicate (max (kh + kh) (Nat.clog 2 Q) * 8) true = _
  rw [← hB.e_ellQ, hB.e_ell, Nat.mul_comm]
  rfl

include hS hB in
theorem ent_scr (j : ℕ) (h : j < F.T + 1 + 1 + 1) (hk : ¬ isK pd j) (hTT : F.T + 1 + 1 + 1 ≤ L.T) :
    B (slx L.oLP hoff (symExt L pd) ⟨j, h⟩) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 ⟨j, h⟩ := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  have hn : symExt L pd (⟨j, h⟩ : Fin (F.T + 1 + 1 + 1)) = none := by
    unfold symExt
    rw [dif_neg hk]
  have hjT : j < F.T := by unfold isK at hk; omega
  have hm : L.maskLP (slx L.oLP hoff (symExt L pd) ⟨j, h⟩) = true := by
    unfold Lay.maskLP
    rw [slx_none hn]
    simp only [Fin.val_mk, decide_eq_true_eq]
    omega
  rw [hB.hmask _ hm, loopBank_lt F _ _ _ (by simp only [Fin.val_mk]; omega)]
  symm
  apply src_scr
  unfold C4Loop.ChildFam.cellS
  split_ifs with hl
  · simp only [Fin.val_mk] at hl
    rw [hS.keep]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    unfold kept
    unfold isK at hk
    omega
  · rfl

include hS hB in
/-- **The loop's entry** on the SYM setup's bank: every docked tape carries `loopBank F (2^ρ) (2^ρ + 1) 0`. -/
theorem entry_all (hTT : F.T + 1 + 1 + 1 ≤ L.T) (j : Fin (F.T + 1 + 1 + 1)) :
    B (slx L.oLP hoff (symExt L pd) j) = C4Wrap.loopBank F (2 ^ ρ) (2 ^ ρ + 1) 0 j := by
  have ht := hS.ht
  have hT2 : F.T = 2 * F.t + 6 := rfl
  obtain ⟨w, h⟩ := j
  by_cases hk : isK pd w
  · unfold isK at hk
    rcases hk with e | e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩ | e | e | e | e | e
    · subst e; exact ent_0 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · subst e; exact ent_2 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · subst e; exact ent_6 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · interval_cases w
      · exact ent_8 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_9 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_10 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_11 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_12 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_13 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_14 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_15 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_16 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_17 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · interval_cases w
      · exact ent_73 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_74 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_75 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_76 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_77 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_78 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_79 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_80 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_81 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_82 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_83 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_84 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_85 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_86 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_87 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_88 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
      · exact ent_89 L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · subst e; exact ent_qq L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · subst e; exact ent_uu L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · subst e; exact ent_log L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · subst e; exact ent_drv L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
    · subst e; exact ent_cnt L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff h
  · exact ent_scr L F pd P ents TWd Cap nT pre post q uu B ρ v Q kh ell cnt d2 fr dd hS hB hoff w h hk hTT

end Entry

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
