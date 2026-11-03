import Lean
import Proof.Wire_3_5.Primitive.Writers.Enum
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixJLink
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA (d): the batch writers' interface (FUSE; the consumers build against this file)

C4's enumeration (`SeedFix.JLink.sampEnum_run`, verified) reads the call's entries from its `BAT` tape as
`blockWord ents ++ tail`, with `EntsOk` (`ents = chunk N nT R batch`), and its printed value is `sampElim` when the
entry rows satisfy `sampTerms_eval`'s `hD` (P3:3011-3016). The writers produce exactly that tape. Each printed row is
the concatenation of its requests' C2 reference expressions (what C2's certified row machines print,
#43). No record tape is kept (FUSE).

This file fixes:
* the printed expressions: `refOf` (per request, C2's `filtRefC`/`popRefC`/`radRefC`), `groupExpr`, `batchExprs`;
* the tapes: **`symTape`**, **`thrTape`** (C4's `BAT` word) and **`hashTape`** (the HASH rows, one row per entry
  record, the same `blockWord` format);
* their values, proved here: `sym_entsOk`/**`sym_hD`**, `thr_entsOk`/**`thr_hD`** (= `sampTerms_eval`'s `hD` at
  `bitZ (symStateBits/thrStateBits (enum t) x)`), **`hash_val`** (the aux filter on `thrZres`);
* the machines' types: `SymWriterAt`, `ThrWriterAt`, `HashWriterAt` (a `ReadyRun` from `frame req.word` to the tape,
  every other tape blank, heads at `0`, within `c_W·classBound E_W .preprocessing n k Ψ`), and **`WriterLeaf`** in
  `SeedFixLeaf`'s order of choice (`fe`, then the floors `E_W`, then `F`, then `c_W`).

Paper quantities of the main types: `SeedFix.symStateBits`, `SeedFix.thrStateBits` (row:matrix), the auxiliary
filter on `thrZres` (filt:soft), inside C4's `BAT` word. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Pop
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

/-! ## The printed expressions -/

/-! ## Each request's expression meets its errSpec -/

/-! ## The SYM tape -/

section Sym
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

end Sym

/-! ## The THR tape -/

section Thr
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

end Thr

/-! ## The HASH tape -/

section Hash
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

end Hash

/-! ## The writers' machine types -/

section Writers
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

end Writers

end NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

end
