import Proof.Wire_3_5.Primitive.Writers.WriteNat
import Proof.Wire_3_5.UnionMachine.RadSpecBase

/-! # RADIX, Route B: the block writer on streams that are read in place (`RadBlockW3`)

`RadSpec2.RadBlockW2` reads the table word and one digit's indices from streams that hold EXACTLY those words,
heads at `0`. The RADIX setup calls the block writer for each of the row's `τ₀` digits (`τ₀` unbounded in `n`), each
digit with its own table word (at `L_d = |gis_d|`) and indices, on a fixed stream layout whose tapes never shrink: after
the first digit no stream holds exactly the next digit's words. **`RadBlockW3`** is `RadBlockW2` with the table word
and the indices read in place: `(σ.st T).drop (σ.sh T) = levelWord … ++ restT` and
`(σ.st GS).drop (σ.sh GS) = gisWord gis ++ restG` for any `restT`, `restG` and heads; the exit is again
`WriteNat.appendO σ O OP B` (the table and index streams, their heads, every register but `OP`: unchanged).

Paper quantity of the main type: the RADIX row's factor blocks (row:radix, P3:2585-2623). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSpec3
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

/-- **The RADIX block writer, reading in place**: as `RadSpec2.RadBlockW2`, with the table word on `T` and the digit's
indices on `GS` read from their heads (any suffix after them). -/
structure RadBlockW3 where
  prog : ∀ {ns nr : ℕ}, Fin (ns + 1) → Fin (ns + 1) → Fin (ns + 1) → (Fin 2 → Fin (ns + 1)) →
    (Fin radBlkK ↪ Fin nr) → Fin nr → WM ns nr
  need : ℕ → ℕ
  bound : ℕ → ℕ
  C : ℕ
  D : ℕ
  need_le : ∀ N, need N ≤ C * (N + 1) ^ D
  bound_le : ∀ c, bound c ≤ C * (c + 1) ^ D
  run : ∀ {ns nr : ℕ} (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr) (OP : Fin nr),
    O ≠ T → O ≠ GS → T ≠ GS → Function.Injective Sc → (∀ i, Sc i ≠ O ∧ Sc i ≠ T ∧ Sc i ≠ GS) →
    (∀ j, Rg j ≠ OP) →
    ∀ (Dl : ListData) (gis : List ℕ) (G row t : ℕ) (sgn : Bool) (cap : ℕ) (restT restG : List Bool)
      (σ : WState ns nr),
    (σ.st T).drop (σ.sh T) =
      FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W (FinalPass.ListEval.rowsOf Dl gis.length) ++ restT →
    (σ.st GS).drop (σ.sh GS) = gisWord gis ++ restG → σ.sh O = (σ.st O).length →
    (∀ i, σ.st (Sc i) = [] ∧ σ.sh (Sc i) = 0) →
    σ.val (Rg 0) = gis.length → σ.val (Rg 1) = G → σ.val (Rg 2) = row → σ.val (Rg 3) = t →
    σ.val (Rg 4) = (if sgn then 1 else 0) → σ.val (Rg 5) = 3 * ListMachine.listBound Dl →
    σ.val (Rg 6) = capC Dl gis.length →
    (∀ j : Fin radBlkK, 7 ≤ j.val → σ.val (Rg j) = 0) →
    need (blkSize Dl gis G row t sgn (σ.st O).length) ≤ cap →
    σ.val OP + (Streaming.marks (true :: blockC Dl gis.length t sgn false
      (CompilerMachine.Pool.labsOf G row gis))).length ≤ cap →
    WExec cap (prog O T GS Sc Rg OP) σ
      (appendO σ O OP (Streaming.marks (true :: blockC Dl gis.length t sgn false
        (CompilerMachine.Pool.labsOf G row gis))))
      (bound cap)

end NearCubicWires.WireExponent3_5.UnionMachine.RadSpec3
