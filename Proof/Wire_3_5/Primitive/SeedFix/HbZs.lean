import Proof.Wire_3_5.Primitive.SeedFix.HbTerm

/-! # C4.Hb, machine part 7: the factors `Z_{ι_r}` of a cell's term (P3:2255-2262)

"`δ_{a,j}^{2t} = Σ_{i_1,…,i_{2t}} Z_{a,i_1}⋯Z_{a,i_{2t}} A_{i_1,j}⋯A_{i_{2t},j}`" (P3:2255-2258): a cell's term has
the `2t` factors `Z_{ι_r}`, `Z^{sgn}` of gate `gis[ι_r]` at row `q`. For each `r`, the program reads `ι_r` from the
odometer's word (`readRawW`), finds the gate (`skipPopsC`, `skipElemsNC`, `readElemC`), returns the populations'
stream to cell `0` (C5's `WM.rewind`) and writes the factor record `T polyWord Z` (`zW`): one uniform body
(**`zBodyW_spec`**) for C6's counted loop.

Registers: `0` the output length; `1` `4q`, `2` `G`, `3` the gate, `4` the sign; `5 … 8` `zW`'s scratch; `11` `p`;
`16` `ℓ₀`; `17` the populations' move count; `18 … 22` scratch.

Paper quantity of the main type: the factor records `Z_{ι_r}` (`zBodyW_spec`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.HbM
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.ListMachine.Rec (polyWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## The factor writer's cost is monotone in the gate -/

theorem atomCost_mono (q4 G k : ℕ) {gi gi' : ℕ} (h : gi ≤ gi') : atomCost q4 G gi k ≤ atomCost q4 G gi' k := by
  unfold atomCost; omega

theorem atomsCost_mono (q4 G : ℕ) {gi gi' : ℕ} (h : gi ≤ gi') :
    ∀ m : List ℕ, atomsCost q4 G gi m ≤ atomsCost q4 G gi' m
  | [] => le_refl _
  | k :: m => by
    simp only [atomsCost]
    have := atomCost_mono q4 G k h
    have := atomsCost_mono q4 G h m
    omega

theorem monosCost_mono (q4 G : ℕ) {gi gi' : ℕ} (h : gi ≤ gi') :
    ∀ ms : List (List ℕ), monosCost q4 G gi ms ≤ monosCost q4 G gi' ms
  | [] => le_refl _
  | m :: ms => by
    simp only [monosCost, monoCost]
    have := atomsCost_mono q4 G h m
    have := monosCost_mono q4 G h ms
    omega

theorem zCost_mono (q4 G : ℕ) {gi gi' : ℕ} (h : gi ≤ gi') : zCost q4 G gi ≤ zCost q4 G gi' := by
  unfold zCost
  have := monosCost_mono q4 G h zPlusL
  have := monosCost_mono q4 G h zMinusL
  omega

theorem monoRoom_mono (q4 G : ℕ) {gi gi' : ℕ} (h : gi ≤ gi') : monoRoom q4 G gi ≤ monoRoom q4 G gi' := by
  unfold monoRoom atomRoom; omega

/-! ## One factor, in three stages -/

section Body
variable (cap : ℕ)

/-- Stage A: read `ι_r` into register `20`, then walk to population `p`'s record (moves counted in `17`). -/
def zLookA : HW :=
  .seq (FinalPass.Hash4.wcopyR 16 19 22) (.seq (readRawW sCTR 19 20 21 22) (.seq (FinalPass.Hash4.wcopyR 11 18 22)
    (skipPopsC sPOPS 17 18)))

/-- The raw reader's cost for `ℓ` bits. -/
def rawCost (ℓ : ℕ) : ℕ := 1 + 3 + 1 + (ℓ * (36 * 2 ^ ℓ + 12 + 4) + 1 + 1 + (3 * 2 ^ ℓ + 1))

def lookACost (ℓ p pw : ℕ) : ℕ := (18 * ℓ + 3) + 1 + (rawCost ℓ + 1 + ((18 * p + 3) + 1 + (p * (9 * pw + 20 + 4) + 1)))

theorem zLookA_spec (ℓ p i : ℕ) (pops : List (Bool × List ℕ)) (hp : p < pops.length) (hil : i < 2 ^ ℓ) (σ : HS)
    (x0 : ℕ) (hC : ∀ m < ℓ, readTapeBit (σ.st sCTR) (x0 + m) = (binary ℓ i).getD m false) (hCh : σ.sh sCTR = x0)
    (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = 0) (h11 : σ.val 11 = p) (h16 : σ.val 16 = ℓ)
    (h17 : σ.val 17 = 0) (h18 : σ.val 18 = 0) (h19 : σ.val 19 = 0) (h20 : σ.val 20 = 0) (h21 : σ.val 21 = 0)
    (h22 : σ.val 22 = 0) (hcap : (popsWord pops).length + 2 ^ (ℓ + 1) + p + ℓ ≤ cap) :
    WExec cap zLookA σ ((((σ.seth sCTR (x0 + ℓ)).seth sPOPS (popsPre pops p).length).setv 20 i).setv 17
      (popsPre pops p).length) (lookACost ℓ p (popsWord pops).length) := by
  have hpow : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  have hpow2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have hpl : (popsPre pops p).length ≤ (popsWord pops).length := by
    rw [popsWord_split pops p hp]; simp only [List.length_append]; omega
  have s1 := FinalPass.Hash4.wcopyR_spec cap 16 19 22 (by decide) (by decide) (by decide) σ h19 h22
    (by rw [h16]; omega)
  rw [h16] at s1
  have s2 := readRawW_spec cap sCTR 19 20 21 22 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (σ.setv 19 ℓ) (binary ℓ i) (by simp) (by simp [h21]) (by simp [h22])
    (fun m hm => by simp only [binary_length] at hm; simp [hCh]; exact hC m hm)
    (by simp [h20, binary_length]; omega)
  rw [bitsValue_binary, Nat.mod_eq_of_lt hil, binary_length] at s2
  have e2 : ((((σ.setv 19 ℓ).seth sCTR ((σ.setv 19 ℓ).sh sCTR + ℓ)).setv 20 ((σ.setv 19 ℓ).val 20 + i)).setv 19 0) =
      (σ.seth sCTR (x0 + ℓ)).setv 20 i := by
    wst
    all_goals (try simp_all) <;> omega
  rw [e2] at s2
  have s3 := FinalPass.Hash4.wcopyR_spec cap 11 18 22 (by decide) (by decide) (by decide)
    ((σ.seth sCTR (x0 + ℓ)).setv 20 i) (by simp [h18]) (by simp [h22]) (by simp [h11]; omega)
  have v3 : ((σ.seth sCTR (x0 + ℓ)).setv 20 i).val 11 = p := by simp [h11]
  rw [v3] at s3
  have s4 := skipPopsC_spec cap sPOPS 17 18 (by decide) pops p hp.le (((σ.seth sCTR (x0 + ℓ)).setv 20 i).setv 18 p)
    (by simp [hP]) (by simp [hPh]) (by simp) (by simp [h17]; omega) (by omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · wst
    all_goals (try simp_all) <;> omega
  · unfold lookACost rawCost; omega

end Body

section BodyB
variable (cap : ℕ)

/-- Stage B: enter the record's gate list, skip `ι_r` gates, read the gate into register `3`, return the stream. -/
def zLookB : HW :=
  .seq (WM.fwdC sPOPS 17) (.seq (WM.fwdC sPOPS 17) (.seq (skipElemsNC sPOPS 17 20) (.seq (readElemC sPOPS 17 3)
    (WM.rewind sPOPS 17))))

def lookBCost (i pw G : ℕ) : ℕ :=
  5 + 1 + (5 + 1 + ((i * (7 * pw + 13 + 4) + 1) + 1 + ((11 * G + 13) + 1 + (5 * pw + 1))))

theorem zLookB_spec (p i G : ℕ) (pops : List (Bool × List ℕ)) (hp : p < pops.length) (hi : i < pops[p].2.length)
    (hG : pops[p].2[i] ≤ G) (σ : HS) (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = (popsPre pops p).length)
    (h17 : σ.val 17 = (popsPre pops p).length) (h20 : σ.val 20 = i) (h3 : σ.val 3 = 0)
    (hcap : (popsWord pops).length + G ≤ cap) :
    WExec cap zLookB σ (((σ.seth sPOPS 0).setv 17 0).setv 20 0 |>.setv 3 pops[p].2[i])
      (lookBCost i (popsWord pops).length G) := by
  have hpw := popsWord_split pops p hp
  have hrec : popRec pops[p] = [true, pops[p].1] ++ (pops[p].2.flatMap elemW ++ [false]) := rfl
  have hgs := gis_split pops[p].2 i hi
  have hlen1 : (popsPre pops p).length + 2 + (pops[p].2.flatMap elemW).length + 1 ≤ (popsWord pops).length := by
    rw [hpw, hrec]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hlen2 : (gisPre pops[p].2 i).length + (pops[p].2[i] + 2) ≤ (pops[p].2.flatMap elemW).length := by
    rw [hgs]; simp only [List.length_append, elemW_length]; omega
  have hflat : i ≤ (pops[p].2.flatMap elemW).length := by
    have : i ≤ (gisPre pops[p].2 i).length := by
      unfold gisPre
      have hl := List.length_take_of_le hi.le (l := pops[p].2)
      calc i = (pops[p].2.take i).length := hl.symm
        _ ≤ ((pops[p].2.take i).flatMap elemW).length := by
          rw [List.length_flatMap]
          calc (pops[p].2.take i).length = ((pops[p].2.take i).map fun _ => 1).sum := by simp [sum_map_const']
            _ ≤ ((pops[p].2.take i).map fun a => (elemW a).length).sum :=
              List.sum_le_sum (fun a _ => by rw [elemW_length]; omega)
    omega
  have s1 := wfwdC_spec cap sPOPS 17 σ (by omega)
  have s2 := wfwdC_spec cap sPOPS 17 ((σ.seth sPOPS (σ.sh sPOPS + 1)).setv 17 (σ.val 17 + 1)) (by simp; omega)
  set σ2 := (((σ.seth sPOPS (σ.sh sPOPS + 1)).setv 17 (σ.val 17 + 1)).seth sPOPS
    (((σ.seth sPOPS (σ.sh sPOPS + 1)).setv 17 (σ.val 17 + 1)).sh sPOPS + 1)).setv 17
    (((σ.seth sPOPS (σ.sh sPOPS + 1)).setv 17 (σ.val 17 + 1)).val 17 + 1) with hσ2
  have v2s : σ2.st sPOPS = (popsPre pops p ++ [true, pops[p].1]) ++ (pops[p].2.flatMap elemW ++
      ([false] ++ ((pops.drop (p + 1)).flatMap popRec ++ [false]))) := by
    simp [σ2, hP, hpw, hrec]
  have v2h : σ2.sh sPOPS = (popsPre pops p ++ [true, pops[p].1]).length := by simp [σ2, hPh]
  have v2c : σ2.val 17 = (popsPre pops p).length + 2 := by simp [σ2, h17]
  have s3 := skipElemsNC_spec cap sPOPS 17 20 (by decide) pops[p].2 i hi.le (popsPre pops p ++ [true, pops[p].1])
    ([false] ++ ((pops.drop (p + 1)).flatMap popRec ++ [false])) σ2 v2s v2h (by simp [σ2, h20])
    (by rw [v2c]; omega) (by omega)
  set σ3 := ((σ2.seth sPOPS ((popsPre pops p ++ [true, pops[p].1]).length + (gisPre pops[p].2 i).length)).setv 17
    (σ2.val 17 + (gisPre pops[p].2 i).length)).setv 20 0 with hσ3
  have s4 := readElemC_spec cap sPOPS 17 3 (by decide) pops[p].2[i]
    (popsPre pops p ++ [true, pops[p].1] ++ gisPre pops[p].2 i)
    ((pops[p].2.drop (i + 1)).flatMap elemW ++ ([false] ++ ((pops.drop (p + 1)).flatMap popRec ++ [false]))) σ3
    (by simp [σ3, v2s, hgs]) (by simp [σ3]; omega)
    (by simp only [hσ3, WState.setv_val, Function.update_apply]; simp [v2c]; omega)
    (by simp [σ3, σ2, h3]; omega)
  set σ4 := ((σ3.seth sPOPS ((popsPre pops p ++ [true, pops[p].1] ++ gisPre pops[p].2 i).length +
    (elemW pops[p].2[i]).length)).setv 17 (σ3.val 17 + (elemW pops[p].2[i]).length)).setv 3
    (σ3.val 3 + pops[p].2[i]) with hσ4
  have v4c : σ4.val 17 = (popsPre pops p).length + 2 + (gisPre pops[p].2 i).length + (pops[p].2[i] + 2) := by
    simp [σ4, σ3, v2c, elemW_length]
  have v4h : σ4.sh sPOPS = σ4.val 17 := by rw [v4c]; simp [σ4, σ3, elemW_length]; omega
  have s5 := wrewind_spec cap sPOPS 17 (σ4.val 17) σ4 rfl (by rw [v4c]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) ?_ ?_
  · rw [v4h, Nat.sub_self, hσ4, hσ3, hσ2]
    wst
    all_goals (try simp_all) <;> omega
  · unfold lookBCost; rw [v4c]
    have : i * (7 * (pops[p].2.flatMap elemW).length + 13 + 4) ≤ i * (7 * (popsWord pops).length + 13 + 4) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end BodyB

section BodyC
variable (cap : ℕ)

/-- The factor record of gate `gi` at row `q`. -/
def zRec (G q : ℕ) (sgn : Bool) (gi : ℕ) : List Bool := true :: polyWord (HashB.zPoly G q sgn gi)

/-- Stage C: the record `T polyWord Z`, then the gate register cleared. -/
def zEmitW : HW := .seq (emitC sOUT 0 true) (.seq zW (WM.clear 3))

theorem zEmitW_spec (q G gi : ℕ) (sgn : Bool) (σ : HS) (h1 : σ.val 1 = 4 * q) (h2 : σ.val 2 = G) (h3 : σ.val 3 = gi)
    (h4 : σ.val 4 = if sgn then 1 else 0) (h5 : σ.val 5 = 0) (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0)
    (h8 : σ.val 8 = 0) (hO : σ.sh sOUT = (σ.st sOUT).length)
    (hcap : σ.val 0 + 1 + 11 * monoRoom (4 * q) G gi + gi ≤ cap) :
    WExec cap zEmitW σ ((appendO σ sOUT 0 (zRec G q sgn gi)).setv 3 0) (7 + 1 + (zCost (4 * q) G gi + 1 + (3 * gi + 1))) := by
  have s1 := emitC_app cap sOUT 0 true σ hO (by omega)
  have s2 := zW_spec cap q G gi sgn (appendO σ sOUT 0 [true]) (by simp [h1]) (by simp [h2]) (by simp [h3])
    (by simp [h4]) (by simp [h5]) (by simp [h6]) (by simp [h7]) (by simp [h8]) (by simp [hO]) (by simp; omega)
  have s3 := wclear_spec cap 3 gi (appendO (appendO σ sOUT 0 [true]) sOUT 0 (polyWord (HashB.zPoly G q sgn gi)))
    (by simp [h3]) (by simp [h3]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (le_refl _)
  rw [appendO_append]
  rfl

/-- **One factor `Z_{ι_r}`**: stages A, B, C. -/
def zBodyW : HW := .seq zLookA (.seq zLookB zEmitW)

/-- A uniform bound on one factor's cost (every gate `≤ G`). -/
def zBodyBound (q G ℓ p pw : ℕ) : ℕ :=
  lookACost ℓ p pw + 1 + (lookBCost pw pw G + 1 + (7 + 1 + (zCost (4 * q) G G + 1 + (3 * G + 1))))

theorem zBodyW_spec (G q ℓ p i : ℕ) (pops : List (Bool × List ℕ)) (hp : p < pops.length)
    (hi : i < pops[p].2.length) (hil : i < 2 ^ ℓ) (hG : ∀ gi ∈ pops[p].2, gi ≤ G) (σ : HS) (x0 : ℕ)
    (hC : ∀ m < ℓ, readTapeBit (σ.st sCTR) (x0 + m) = (binary ℓ i).getD m false) (hCh : σ.sh sCTR = x0)
    (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = 0)
    (h1 : σ.val 1 = 4 * q) (h2 : σ.val 2 = G) (h3 : σ.val 3 = 0) (h4 : σ.val 4 = if pops[p].1 then 1 else 0)
    (h5 : σ.val 5 = 0) (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0) (h8 : σ.val 8 = 0) (h11 : σ.val 11 = p)
    (h16 : σ.val 16 = ℓ) (h17 : σ.val 17 = 0) (h18 : σ.val 18 = 0) (h19 : σ.val 19 = 0) (h20 : σ.val 20 = 0)
    (h21 : σ.val 21 = 0) (h22 : σ.val 22 = 0) (hO : σ.sh sOUT = (σ.st sOUT).length)
    (hcap : σ.val 0 + 1 + 11 * monoRoom (4 * q) G G + (popsWord pops).length + 2 ^ (ℓ + 1) + p + ℓ + G ≤ cap) :
    WExec cap zBodyW σ (appendO (σ.seth sCTR (x0 + ℓ)) sOUT 0 (zRec G q pops[p].1 (pops[p].2.getD i 0)))
      (zBodyBound q G ℓ p (popsWord pops).length) := by
  have hgi : pops[p].2[i] ≤ G := hG _ (List.getElem_mem hi)
  have hgiD : pops[p].2.getD i 0 = pops[p].2[i] := by rw [List.getD_eq_getElem _ _ hi]
  have hmr := monoRoom_mono (4 * q) G hgi
  have hil2 : i ≤ (popsWord pops).length := by
    have hpw := popsWord_split pops p hp
    have hrec : popRec pops[p] = [true, pops[p].1] ++ (pops[p].2.flatMap elemW ++ [false]) := rfl
    have hgs := gis_split pops[p].2 i hi
    rw [hpw, hrec, hgs]; simp only [List.length_append, List.length_cons, List.length_nil, elemW_length]
    have : i ≤ (gisPre pops[p].2 i).length := by
      unfold gisPre
      rw [List.length_flatMap]
      calc i = ((pops[p].2.take i).map fun _ => 1).sum := by
            simp [sum_map_const', List.length_take_of_le hi.le]; omega
        _ ≤ ((pops[p].2.take i).map fun a => (elemW a).length).sum :=
          List.sum_le_sum (fun a _ => by rw [elemW_length]; omega)
    omega
  have sA := zLookA_spec cap ℓ p i pops hp hil σ x0 hC hCh hP hPh h11 h16 h17 h18 h19 h20 h21 h22 (by omega)
  set σA := (((σ.seth sCTR (x0 + ℓ)).seth sPOPS (popsPre pops p).length).setv 20 i).setv 17
    (popsPre pops p).length with hσA
  have sB := zLookB_spec cap p i G pops hp hi hgi σA (by simp [σA, hP]) (by simp [σA]) (by simp [σA])
    (by simp [σA]) (by simp [σA, h3]) (by omega)
  set σB := (((σA.seth sPOPS 0).setv 17 0).setv 20 0).setv 3 pops[p].2[i] with hσB
  have sC := zEmitW_spec cap q G pops[p].2[i] pops[p].1 σB (by simp [σB, σA, h1]) (by simp [σB, σA, h2])
    (by simp [σB]) (by simp [σB, σA, h4]) (by simp [σB, σA, h5]) (by simp [σB, σA, h6]) (by simp [σB, σA, h7])
    (by simp [σB, σA, h8]) (by simp [σB, σA, hO]) (by simp [σB, σA]; omega)
  refine WExec.cast cap (WExec.seq sA (WExec.seq sB sC)) ?_ ?_
  · rw [hgiD, hσB, hσA]
    wst
    all_goals (try simp_all) <;> omega
  · unfold zBodyBound
    have b1 : lookBCost i (popsWord pops).length G ≤ lookBCost (popsWord pops).length (popsWord pops).length G := by
      unfold lookBCost
      have := Nat.mul_le_mul_right (7 * (popsWord pops).length + 13 + 4) hil2
      omega
    have b2 := zCost_mono (4 * q) G hgi
    omega

end BodyC

section Loop
variable (cap : ℕ)

theorem monoE_le_room (q4 G gi : ℕ) (m : List ℕ) (hk : ∀ k ∈ m, k ≤ 3) (hm : m.length ≤ 3) (hgi : gi ≤ G) :
    (monoE q4 G gi m).length ≤ monoRoom q4 G G :=
  (monoE_length_le q4 G gi m hk hm).trans (monoRoom_mono q4 G hgi)

theorem zRec_length_le (G q gi : ℕ) (sgn : Bool) (hgi : gi ≤ G) :
    (zRec G q sgn gi).length ≤ 10 * monoRoom (4 * q) G G + 2 := by
  unfold zRec
  rw [List.length_cons, zPoly_word, List.length_append, List.length_flatMap]
  have : (((if sgn then zPlusL else zMinusL).map fun m => (monoE (4 * q) G gi m).length)).sum ≤
      10 * monoRoom (4 * q) G G := by
    calc (((if sgn then zPlusL else zMinusL).map fun m => (monoE (4 * q) G gi m).length)).sum
        ≤ (((if sgn then zPlusL else zMinusL).map fun _ => monoRoom (4 * q) G G)).sum :=
          List.sum_le_sum (fun m hm => monoE_le_room _ _ _ m (zL_ok sgn m hm).1 (zL_ok sgn m hm).2 hgi)
      _ = 10 * monoRoom (4 * q) G G := by rw [sum_map_const', zL_length]
  simp only [List.length_singleton]; omega

/-- **The `2t` factors** `Z_{ι_0}, …, Z_{ι_{2t−1}}`: register `15` holds `2t`, the loop counts in `25`. -/
def zsW : HW := .seq (FinalPass.Hash4.wcopyR 15 25 22) (.whr 25 (.seq (.dec 25) zBodyW))

theorem zsW_spec (G q ℓ p : ℕ) (ιs : List ℕ) (pops : List (Bool × List ℕ)) (hp : p < pops.length)
    (hι : ∀ i ∈ ιs, i < pops[p].2.length ∧ i < 2 ^ ℓ) (hG : ∀ gi ∈ pops[p].2, gi ≤ G) (σ : HS) (x0 : ℕ)
    (hC : ∀ k < ιs.length, ∀ m < ℓ, readTapeBit (σ.st sCTR) (x0 + k * ℓ + m) = (binary ℓ (ιs.getD k 0)).getD m false)
    (hCh : σ.sh sCTR = x0) (hP : σ.st sPOPS = popsWord pops) (hPh : σ.sh sPOPS = 0)
    (h1 : σ.val 1 = 4 * q) (h2 : σ.val 2 = G) (h3 : σ.val 3 = 0) (h4 : σ.val 4 = if pops[p].1 then 1 else 0)
    (h5 : σ.val 5 = 0) (h6 : σ.val 6 = 0) (h7 : σ.val 7 = 0) (h8 : σ.val 8 = 0) (h11 : σ.val 11 = p)
    (h15 : σ.val 15 = ιs.length) (h16 : σ.val 16 = ℓ) (h17 : σ.val 17 = 0) (h18 : σ.val 18 = 0)
    (h19 : σ.val 19 = 0) (h20 : σ.val 20 = 0) (h21 : σ.val 21 = 0) (h22 : σ.val 22 = 0) (h25 : σ.val 25 = 0)
    (hO : σ.sh sOUT = (σ.st sOUT).length)
    (hcap : σ.val 0 + ιs.length * (10 * monoRoom (4 * q) G G + 2) + 1 + 11 * monoRoom (4 * q) G G +
      (popsWord pops).length + 2 ^ (ℓ + 1) + p + ℓ + G + ιs.length ≤ cap) :
    WExec cap zsW σ (appendO (σ.seth sCTR (x0 + ιs.length * ℓ)) sOUT 0
        (ιs.flatMap fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)))
      ((18 * ιs.length + 3) + 1 + (ιs.length * (zBodyBound q G ℓ p (popsWord pops).length + 4) + 1)) := by
  have hpow : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hpow2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have s1 := FinalPass.Hash4.wcopyR_spec cap 15 25 22 (by decide) (by decide) (by decide) σ h25 h22
    (by rw [h15]; omega)
  rw [h15] at s1
  have hzrl : ∀ i ∈ ιs, (zRec G q pops[p].1 (pops[p].2.getD i 0)).length ≤ 10 * monoRoom (4 * q) G G + 2 := by
    intro i hi
    have hgi : pops[p].2.getD i 0 ≤ G := by
      rw [List.getD_eq_getElem _ _ (hι i hi).1]; exact hG _ (List.getElem_mem _)
    exact zRec_length_le G q _ _ hgi
  have htl : ∀ k ≤ ιs.length, ((ιs.take k).flatMap fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)).length ≤
      ιs.length * (10 * monoRoom (4 * q) G G + 2) := by
    intro k hk
    rw [List.length_flatMap]
    calc ((ιs.take k).map fun i => (zRec G q pops[p].1 (pops[p].2.getD i 0)).length).sum
        ≤ ((ιs.take k).map fun _ => 10 * monoRoom (4 * q) G G + 2).sum :=
          List.sum_le_sum (fun i hi => hzrl i (List.mem_of_mem_take hi))
      _ = (ιs.take k).length * (10 * monoRoom (4 * q) G G + 2) := sum_map_const' _ _
      _ ≤ ιs.length * (10 * monoRoom (4 * q) G G + 2) := Nat.mul_le_mul_right _ (by simp)
  let S : ℕ → HS := fun k => (appendO (σ.seth sCTR (x0 + k * ℓ)) sOUT 0
    ((ιs.take k).flatMap fun i => zRec G q pops[p].1 (pops[p].2.getD i 0))).setv 25 (ιs.length - k)
  have hS0 : S 0 = σ.setv 25 ιs.length := by
    simp only [S, List.take_zero, List.flatMap_nil, appendO_nil, Nat.zero_mul, Nat.add_zero, Nat.sub_zero, ← hCh,
      wseth_same]
  have hloop := UnionMachine.Round.wloop cap 25 zBodyW (zBodyBound q G ℓ p (popsWord pops).length) ιs.length S
    (fun k _ => by simp [S]) (by omega)
    (fun k hk => by
      have hmem : ιs[k] ∈ ιs := List.getElem_mem hk
      have hb := zBodyW_spec cap G q ℓ p ιs[k] pops hp (hι _ hmem).1 (hι _ hmem).2 hG
        ((S k).setv 25 (ιs.length - k - 1)) (x0 + k * ℓ)
        (fun m hm => by
          have := hC k hk m hm
          rw [List.getD_eq_getElem _ _ hk] at this
          simpa [S] using this)
        (by simp [S]) (by simp [S, hP]) (by simp [S, hPh]) (by simp [S, h1]) (by simp [S, h2]) (by simp [S, h3])
        (by simp [S, h4]) (by simp [S, h5]) (by simp [S, h6]) (by simp [S, h7]) (by simp [S, h8])
        (by simp [S, h11]) (by simp [S, h16]) (by simp [S, h17]) (by simp [S, h18]) (by simp [S, h19])
        (by simp [S, h20]) (by simp [S, h21]) (by simp [S, h22]) (by simp [S, hO])
        (by
          have := htl k hk.le
          have h0 : ((S k).setv 25 (ιs.length - k - 1)).val 0 = σ.val 0 +
              ((ιs.take k).flatMap fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)).length := by
            simp [S]
          rw [h0]; omega)
      refine WExec.cast cap hb ?_ (le_refl _)
      have htk : (ιs.take (k + 1)).flatMap (fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)) =
          (ιs.take k).flatMap (fun i => zRec G q pops[p].1 (pops[p].2.getD i 0)) ++
            zRec G q pops[p].1 (pops[p].2.getD ιs[k] 0) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append]; simp
      simp only [S, htk]
      wst
      all_goals (try simp_all) <;> (try ring_nf) <;> omega)
  rw [hS0] at hloop
  refine WExec.cast cap (WExec.seq s1 hloop) ?_ (le_refl _)
  simp only [S, List.take_length, Nat.sub_self]
  wst
  all_goals (try simp_all) <;> omega

end Loop

end NearCubicWires.WireExponent3_5.PrimT.HbM
