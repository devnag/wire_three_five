import Proof.Wire_3_5.UnionMachine.RadAsm5

/-! # RADIX, stage 6's value link: the record the cell holds IS the Route-B record (P3:2585-2623)

The Route-B record `RadReqB.record q` is the setup fields, then every factor block marked `true ::` in store order
(`radBlocksC`: per digit, the `+` blocks for `t = 0 … M`, then the `−` blocks), then `false`; framed, it is the cell's
record stream after stage 6 (`RadAsm.radixB_run`): `fieldsWordB R Lg M τ₀ p s cap ++ ls.flatMap (digBlocks D · G row)
++ [true, false, false]`, when the request's digits are `ls.map (fun gis => (|gis|, labsOf G row gis))`.

* `marks_flatMap`, **`radBlocks_marks`**, **`record_frame`**.

Paper quantity of the main type: the RADIX row's record `radRowRecC`-shape at Route B's capacities (`RadReqB.record`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadLink
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB

theorem marks_flatMap {α : Type} (l : List α) (g : α → List Bool) :
    Streaming.marks (l.flatMap g) = l.flatMap (fun a => Streaming.marks (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, PrimAsm.FiltRec.marks_append', ih, List.flatMap_cons]

/-- **The factor blocks, marked, are the digits' blocks.** -/
theorem radBlocks_marks (D : ListData) (G row : ℕ) (ls : List (List ℕ)) :
    Streaming.marks ((radBlocksC D (ls.map fun gis => (gis.length, CompilerMachine.Pool.labsOf G row gis))).flatMap
      (fun b => true :: b)) = ls.flatMap (fun gis => RadBlk.digBlocks D gis G row) := by
  induction ls with
  | nil => rfl
  | cons gis ls ih =>
    unfold radBlocksC at ih ⊢
    rw [List.map_cons, List.flatMap_cons, List.flatMap_append, PrimAsm.FiltRec.marks_append', ih, List.flatMap_cons]
    congr 1
    unfold RadBlk.digBlocks RadBlk.bws
    rw [List.flatMap_append, PrimAsm.FiltRec.marks_append', List.flatMap_map, List.flatMap_map, marks_flatMap,
      marks_flatMap]
    rfl

/-- **The framed Route-B record** is the fields, the digits' blocks and `[true, false, false]`. -/
theorem record_frame (r : RadReq) (Lmax Mlab lb lw G row : ℕ) (ls : List (List ℕ))
    (hd : r.digs = ls.map fun gis => (gis.length, CompilerMachine.Pool.labsOf G row gis)) (hb0 : r.b0 = 2) :
    frame (reqB r Lmax Mlab lb lw).record =
      RadFieldsP.fieldsWordB (reqB r Lmax Mlab lb lw).R (reqB r Lmax Mlab lb lw).Lg r.D.M r.digs.length r.p r.s
        (reqB r Lmax Mlab lb lw).cap ++ ls.flatMap (fun gis => RadBlk.digBlocks r.D gis G row) ++
        [true, false, false] := by
  unfold RadReqB.record
  rw [RadFields.frame_flat, List.flatMap_append]
  have h1 : (fieldsWord (setupFieldsG (19 + 1) (reqB r Lmax Mlab lb lw).R (reqB r Lmax Mlab lb lw).Lg
      (radEv (reqB r Lmax Mlab lb lw).r.D.M (2 * (reqB r Lmax Mlab lb lw).r.digs.length)
        (radCs (reqB r Lmax Mlab lb lw).r.D (reqB r Lmax Mlab lb lw).r.digs (reqB r Lmax Mlab lb lw).r.p
          (reqB r Lmax Mlab lb lw).r.b0)
        (radT (reqB r Lmax Mlab lb lw).r.digs (reqB r Lmax Mlab lb lw).r.p (reqB r Lmax Mlab lb lw).r.s)
        (reqB r Lmax Mlab lb lw).cap))).flatMap (fun b => [true, b]) =
      RadFieldsP.fieldsWordB (reqB r Lmax Mlab lb lw).R (reqB r Lmax Mlab lb lw).Lg r.D.M r.digs.length r.p r.s
        (reqB r Lmax Mlab lb lw).cap := by
    have e := PrimAsm.FiltRec.frame_fieldsWord (setupFieldsG (19 + 1) (reqB r Lmax Mlab lb lw).R
      (reqB r Lmax Mlab lb lw).Lg (radEv (reqB r Lmax Mlab lb lw).r.D.M (2 * (reqB r Lmax Mlab lb lw).r.digs.length)
        (radCs (reqB r Lmax Mlab lb lw).r.D (reqB r Lmax Mlab lb lw).r.digs (reqB r Lmax Mlab lb lw).r.p
          (reqB r Lmax Mlab lb lw).r.b0)
        (radT (reqB r Lmax Mlab lb lw).r.digs (reqB r Lmax Mlab lb lw).r.p (reqB r Lmax Mlab lb lw).r.s)
        (reqB r Lmax Mlab lb lw).cap))
    rw [RadFields.frame_flat] at e
    have e2 := List.append_cancel_right e
    rw [e2]
    unfold RadFieldsP.fieldsWordB radCs radT
    show _ = (setupFieldsG (19 + 1) _ _ (radEv r.D.M (2 * r.digs.length) (consFrom r.D.M r.p 2 0 r.digs.length)
      (patT r.p r.s (2 * r.digs.length * r.p + 1)) _)).flatMap PrimAsm.FiltRec.fieldE
    rw [← hb0]
    rfl
  have h2 : ((radBlocksC r.D r.digs).flatMap (fun b => true :: b) ++ [false]).flatMap (fun b => [true, b]) ++ [false] =
      ls.flatMap (fun gis => RadBlk.digBlocks r.D gis G row) ++ [true, false, false] := by
    rw [List.flatMap_append, hd]
    have e := radBlocks_marks r.D G row ls
    unfold Streaming.marks at e
    rw [e]
    simp
  have hr : (reqB r Lmax Mlab lb lw).r = r := rfl
  rw [h1, List.append_assoc, hr, h2, List.append_assoc]

end NearCubicWires.WireExponent3_5.UnionMachine.RadLink
