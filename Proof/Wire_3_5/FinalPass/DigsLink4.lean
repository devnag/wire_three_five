import Proof.Wire_3_5.FinalPass.DigsLink3

/-! # `DigsW`'s body, part 18: the program's output is `digsWord` of the digit populations (P3:2596-2599; W17)

Per digit `d`: `(thrDigGis … d).flatMap enc = Ls oOff d (base mod p) p Sd wsd [] a'` (`dig_eq`): the digit
population lists occurrence `oOff + o` iff digit `d` of `a_o = (w_o mod p).toNat` is `1`; by `EqRef.weights_blocks`
the occurrences are circuit `i`'s block of `base^i · w_{i,k}`, and `resid_mul` gives `a = (base^i mod p) · (w mod p)
mod p`, the program's product. Then **`Wd_digs`**: `Wd … [] τ₀ = digsWord (List.ofFn fun d => thrDigGis … d)`.
Main declarations: `rep_enc`, `finRange_flatMap`, `ws_child`, `dig_eq`, **`Wd_digs`**. Paper quantity: the digit
populations `v_{i,d}` of row `(g, p)` (P3:2598-2599), as `DigsW`'s pinned word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.ThrArith

theorem rep_enc (r x : ℕ) (hr : r < 2) (off o d a : ℕ) (hra : r = a / 2 ^ d % 2) (hx : x = off + o) :
    (List.replicate r x).flatMap enc = emitW off o d a := by
  unfold emitW
  rcases (show r = 0 ∨ r = 1 by omega) with h | h
  · rw [h, if_neg (by omega)]; simp
  · rw [h, if_pos (by omega), hx]; simp

theorem finRange_flatMap {α : Type} (n : ℕ) (B : ℕ → List α) :
    (List.finRange n).flatMap (fun i => B i.val) = (List.range n).flatMap B := by
  have h1 : (List.finRange n).flatMap (fun i => B i.val) = (List.ofFn fun i : Fin n => B i.val).flatten := by
    rw [List.ofFn_eq_map]; rfl
  rw [h1, ofFn_range B n]; rfl

section Sel
variable (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
  (alg : DecompositionAlgorithm)

theorem ws_child (g : Primitive.ThrEq P Cs alg) (i : Fin (List.ofFn Cs).length) :
    List.ofFn (PacketsMeta.CutoffMath.child alg (Primitive.thrRequest P Cs) g i).weight =
      wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i.val := by
  have h := ys_child P Cs alg g i
  unfold ysOf at h
  exact (List.append_inj' h rfl).1

theorem wsd_len_all (g : Primitive.ThrEq P Cs alg) (i : ℕ) :
    (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) i).length =
      Sd Cs i := by
  by_cases h : i < a'
  · exact wsd_len Cs alg _ i h (Nat.mod_lt _ (by have := md_pos P Cs alg g i h; omega))
  · simp [wsd, Sd, dif_neg h]

variable (carriers : List (Stars.Carrier P.n)) (den : ℕ)

/-- **One digit's population word** is the program's output for that digit. -/
theorem dig_eq (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den))
    (hp : 2 ≤ pr.val) (d : Fin (Primitive.thrDigits P Cs alg den)) :
    (PrimAsm.Records.thrDigGis P Cs carriers alg den g pr d).flatMap enc =
      Ls (PrimAsm.Records.thrOff P Cs carriers) d.val (PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g % pr.val)
        pr.val (Sd Cs) (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
        [] a' := by
  have hpos : 0 < pr.val := by omega
  obtain ⟨base, hbase⟩ : ∃ b, b = PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g := ⟨_, rfl⟩
  rw [← hbase]
  -- the population word, occurrence by occurrence
  unfold PrimAsm.Records.thrDigGis
  rw [List.flatMap_assoc]
  have h1 : (List.finRange (Primitive.thrOccs P Cs).length).flatMap (fun o =>
      (List.replicate (Primitive.digitOf (Primitive.thrOccs P Cs) (Primitive.thrRealize P Cs alg g) pr.val 2
        (Primitive.thrDigits P Cs alg den) o d) (PrimAsm.Records.thrOff P Cs carriers + o)).flatMap enc) =
      (List.ofFn fun o : Fin (Primitive.thrOccs P Cs).length => emitW (PrimAsm.Records.thrOff P Cs carriers) (0 + o.val)
        d.val (Primitive.redCoeff (Primitive.thrOccs P Cs) (Primitive.thrRealize P Cs alg g) pr.val o)).flatten := by
    refine (List.flatMap_congr (fun o _ => rep_enc _ _ (Nat.mod_lt _ (by norm_num)) (PrimAsm.Records.thrOff P Cs carriers)
      (0 + o.val) d.val (Primitive.redCoeff (Primitive.thrOccs P Cs) (Primitive.thrRealize P Cs alg g) pr.val o) rfl
      (by rw [Nat.zero_add]))).trans ?_
    rw [List.ofFn_eq_map]; rfl
  rw [h1, emitAs_ofFn]
  -- the occurrences, circuit by circuit
  have h2 : List.ofFn (Primitive.redCoeff (Primitive.thrOccs P Cs) (Primitive.thrRealize P Cs alg g) pr.val) =
      (List.range a').flatMap (fun i => (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ)
        (md Cs alg) j % md Cs alg j) i).map fun w => Bs (base % pr.val) pr.val i * (w % (pr.val : ℤ)).toNat % pr.val) := by
    have e1 : List.ofFn (Primitive.redCoeff (Primitive.thrOccs P Cs) (Primitive.thrRealize P Cs alg g) pr.val) =
        (List.ofFn (Primitive.thrRealize P Cs alg g).weights).map (fun w => (w % (pr.val : ℤ)).toNat) := by
      rw [List.map_ofFn]; rfl
    rw [e1]
    unfold Primitive.thrRealize
    rw [PrimThrW.EqRef.weights_blocks, List.map_flatMap, ← hbase]
    obtain ⟨B, hB⟩ : ∃ B : ℕ → List ℕ, B = fun j => (wsd Cs alg (fun j =>
        Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j) j).map fun w =>
        Bs (base % pr.val) pr.val j * (w % (pr.val : ℤ)).toNat % pr.val := ⟨_, rfl⟩
    rw [show (List.finRange (Primitive.thrRequest P Cs).circuits.length).flatMap (fun i =>
        (List.ofFn fun k => ((base : ℕ) : ℤ) ^ i.val *
          (PacketsMeta.CutoffMath.child alg (Primitive.thrRequest P Cs) g i).weight k).map
          (fun w => (w % (pr.val : ℤ)).toNat)) =
        (List.finRange (List.ofFn Cs).length).flatMap (fun i => B i.val) from
      List.flatMap_congr (fun i _ => by
        rw [hB]
        beta_reduce
        rw [← ws_child P Cs alg g i, List.map_ofFn, List.map_ofFn]
        congr 1
        funext k
        simp only [Function.comp_apply]
        rw [resid_mul base i.val _ pr.val hpos, Bs_eq _ _ hp, ← Nat.pow_mod])]
    rw [finRange_flatMap (List.ofFn Cs).length B, hB]
    simp only [List.length_ofFn]
  rw [h2, ← Ls_as _ _ _ _ _ _ (wsd_len_all P Cs alg g)]

/-- **The program's output is `digsWord` of the digit populations.** -/
theorem Wd_digs (g : Primitive.ThrEq P Cs alg) (pr : SupplierPrime.PrimeIndex (Primitive.thrCutoff P Cs alg den))
    (hp : 2 ≤ pr.val) :
    Wd a' (PrimAsm.Records.thrOff P Cs carriers) (PrimThrW.EqRef.baseOf alg (Primitive.thrRequest P Cs) g % pr.val)
      pr.val (Sd Cs) (wsd Cs alg (fun j => Gs (PrimAsm.Enum.thrEqEquiv P Cs alg g : ℕ) (md Cs alg) j % md Cs alg j))
      [] (Primitive.thrDigits P Cs alg den) =
      Digs.digsWord (List.ofFn fun d => PrimAsm.Records.thrDigGis P Cs carriers alg den g pr d) := by
  unfold Wd Digs.digsWord
  rw [List.nil_append]
  have e : (List.ofFn fun d => PrimAsm.Records.thrDigGis P Cs carriers alg den g pr d) =
      List.ofFn fun d : Fin (Primitive.thrDigits P Cs alg den) => (fun k => if h : k < Primitive.thrDigits P Cs alg den
        then PrimAsm.Records.thrDigGis P Cs carriers alg den g pr ⟨k, h⟩ else []) d.val := by
    congr 1; funext d; simp [d.isLt]
  rw [e, ofFn_range (fun k => if h : k < Primitive.thrDigits P Cs alg den
    then PrimAsm.Records.thrDigGis P Cs carriers alg den g pr ⟨k, h⟩ else []) (Primitive.thrDigits P Cs alg den),
    List.flatMap_map]
  refine List.flatMap_congr (fun k hk => ?_)
  have hk' : k < Primitive.thrDigits P Cs alg den := List.mem_range.mp hk
  simp only [dif_pos hk']
  unfold dWord
  rw [← dig_eq P Cs alg carriers den g pr hp ⟨k, hk'⟩]
  rfl

end Sel

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
