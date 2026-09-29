import Proof.Wire_3_5.FinalPass.SdF1

/-! # S4 (the seeds phase), part 49: the front's words at a star call, read (P3:3170-3178)

The front's words `frontWordsOfW2` at a SYM star call (`fwS_lt8`: S4's words, `fwS_mid`: the THR slots blank,
`fwS_word`, `fwS_nums`: the SYM evaluator's words and numbers) and at a THR star call (`fwT_lt8`, `fwT_word`: THR's
words, `fwT_nums`: THR's numbers, `fwT_hi`: the SYM slots blank).

Paper quantity of the main type: the seeds phase's entry words at a star call (P3:3170-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymWords frontWordsOfW2 s4Core2 symCallOf thrCallOf thrWords
  thrNums)

section Req
variable {kc : ℕ} {En : Envelope} {B : TimeBudget kc En} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (Sw : SymWords) {n a' : ℕ} (ha' : a' ≤ 4)
  (carriers : List (Carrier n)) (translation : List ℕ)

theorem fwS_lt8 (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n) (i : ℕ) (hi : i < 8) :
    frontWordsOfW2 I alg Sw ⟨n, .sym, a', ha', Cs, carriers, translation⟩ ⟨i, by omega⟩ =
      s4Core2 (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        ((SeedFix.greedySampler I alg).symS Cs carriers translation hs) carriers (I.filterParams .sym n) ⟨i, hi⟩ := by
  simp only [frontWordsOfW2, dif_pos hs, dif_pos hi]

theorem fwS_mid (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n) (i : ℕ) (h8 : 8 ≤ i)
    (h16 : i < 16) : frontWordsOfW2 I alg Sw ⟨n, .sym, a', ha', Cs, carriers, translation⟩ ⟨i, by omega⟩ = [] := by
  simp only [frontWordsOfW2, dif_pos hs, dif_neg (show ¬ i < 8 by omega), if_pos h16]

theorem fwS_word (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n) (i : Fin Sw.nw) :
    frontWordsOfW2 I alg Sw ⟨n, .sym, a', ha', Cs, carriers, translation⟩ ⟨16 + i.val, by omega⟩ =
      Sw.words (symCallOf I hs ha' Cs carriers) i := by
  simp only [frontWordsOfW2, dif_pos hs, dif_neg (show ¬ 16 + i.val < 8 by omega),
    if_neg (show ¬ 16 + i.val < 16 by omega), dif_pos (show 16 + i.val - 16 < Sw.nw by omega)]
  congr 1
  exact Fin.ext (by simp)

theorem fwS_nums (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (hs : I.StarAt n) :
    frontWordsOfW2 I alg Sw ⟨n, .sym, a', ha', Cs, carriers, translation⟩ ⟨16 + Sw.nw, by omega⟩ =
      PrimAsm.Data.unaryList (List.ofFn (Sw.nums (symCallOf I hs ha' Cs carriers))) := by
  simp only [frontWordsOfW2, dif_pos hs, dif_neg (show ¬ 16 + Sw.nw < 8 by omega),
    if_neg (show ¬ 16 + Sw.nw < 16 by omega), dif_neg (show ¬ 16 + Sw.nw - 16 < Sw.nw by omega)]

theorem fwT_lt8 (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : I.StarAt n) (i : ℕ) (hi : i < 8) :
    frontWordsOfW2 I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨i, by omega⟩ =
      s4Core2 (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs) carriers (I.filterParams .thr n) ⟨i, hi⟩ := by
  simp only [frontWordsOfW2, dif_pos hs, dif_pos hi]

theorem fwT_word (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : I.StarAt n) (i : Fin 7) :
    frontWordsOfW2 I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨8 + i.val, by omega⟩ =
      thrWords (thrCallOf I alg hs ha' Cs carriers translation) i := by
  simp only [frontWordsOfW2, dif_pos hs, dif_neg (show ¬ 8 + i.val < 8 by omega),
    dif_pos (show 8 + i.val < 15 by omega)]
  congr 1
  exact Fin.ext (by simp)

theorem fwT_nums (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (hs : I.StarAt n) :
    frontWordsOfW2 I alg Sw ⟨n, .thr, a', ha', Cs, carriers, translation⟩ ⟨15, by omega⟩ =
      PrimAsm.Data.unaryList (List.ofFn (thrNums (thrCallOf I alg hs ha' Cs carriers translation))) := by
  simp only [frontWordsOfW2, dif_pos hs, dif_neg (show ¬ (15 : ℕ) < 8 by omega),
    dif_neg (show ¬ (15 : ℕ) < 15 by omega), ite_true]

end Req

end NearCubicWires.WireExponent3_5.FinalPass.Sd
