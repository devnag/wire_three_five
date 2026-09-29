import Proof.Assembly.Production

/-! A source-global row package owns its private initialization as well as
completion/cleanup. Callers provide only explicit public words, never an
arbitrary private bank claimed to be computable. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJd4d1d9d7d1fa4313_Production
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

abbrev geometryOf (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (r : Request) :=
  Packets.geometry selector (r.family a)

/-- Caller-supplied numerical caps. Their actual binary words are inputs;
unary reserves are produced and paid by the initializer. -/
structure RowCaps where
  headerFuel : Nat
  copyCap : Nat
  descriptorReserve : Nat
  rawReserve : Nat

def RowCaps.word (c : RowCaps) : List Bool :=
  natListWord [c.headerFuel,c.copyCap,c.descriptorReserve,c.rawReserve]

def RowCaps.Good (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (c : RowCaps) : Prop :=
  (∀ row ∈ (r.family a).rows,
    PCJcc051fd4c1bd4540_Header.budget a (r.family a) (geometryOf selector a r) layout row ≤ c.headerFuel) ∧
  (∀ row (hr : row ∈ (r.family a).rows), ∀ i,
    2*(PCJ38fbfed565f64139_Row.Frame.fields printer
      (Packets.datum a (r.family a) (geometryOf selector a r) layout row hr (facts row hr)) i).length+1 ≤ c.copyCap) ∧
  (r.raw selector a).length ≤ c.rawReserve ∧
  (PCJ38fbfed565f64139_Cached.descriptorWord printer
    (dataList a (r.family a) (geometryOf selector a r) layout facts)).length ≤ c.descriptorReserve

/-- Exact serialized metadata; its full length is charged at initialization. -/
def rowMetadataWord (w degree C : Nat) (caps : RowCaps) : List Bool :=
  RepairOrdinary.frame (natListWord [w,degree,C] ++ caps.word)

/-- The two public metadata ports precede independently chosen private work. -/
abbrev rowWork (privateWork : Nat) := 2+privateWork
abbrev rowTapes (printer : WilliamsAlgorithm) (privateWork : Nat) :=
  PCJ38fbfed565f64139_Ready.tapes printer (rowWork privateWork)

def rowRequestPort (printer : WilliamsAlgorithm) (privateWork : Nat) :
    Fin (rowTapes printer privateWork+1) :=
  ⟨440+(P1TopDownPaidPayload.tapes printer+2),by unfold rowTapes rowWork PCJ38fbfed565f64139_Ready.tapes; omega⟩
def rowCapsPort (printer : WilliamsAlgorithm) (privateWork : Nat) :
    Fin (rowTapes printer privateWork+1) :=
  ⟨440+(P1TopDownPaidPayload.tapes printer+2)+1,by unfold rowTapes rowWork PCJ38fbfed565f64139_Ready.tapes; omega⟩

def rowPublicInput (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) (privateWork : Nat) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) :
    Fin (rowTapes printer privateWork+1) → List Bool := fun i =>
  if i.val=0 then exactListWord (Packets.pool a (r.family a) (geometryOf selector a r))
  else if i.val=262 then r.raw selector a
  else if i=rowRequestPort printer privateWork then RepairOrdinary.frame (r.input a)
  else if i=rowCapsPort printer privateWork then
    rowMetadataWord layout.w layout.degree layout.C caps
  else []

/-- Header cost appears linearly, as do large output/copy fields. Neither the
family raw reserve nor descriptor reserve is charged inside this row factor. -/
def rowBudget (a : DecompositionAlgorithm) (coefficient degree : Nat) (r : Request)
    (C : Nat) (caps : RowCaps) : Nat :=
  coefficient * ((r.smallSize a)^degree + caps.headerFuel + C + caps.copyCap +
    2^(Packets.residual (r.family a))*(r.q+(r.input a).length+1)^degree + 1)

def rowInitBudget (a : DecompositionAlgorithm) (coefficient degree : Nat) (r : Request)
    (w layoutDegree C : Nat) (caps : RowCaps) : Nat :=
  rowBudget a coefficient degree r C caps +
    coefficient * (caps.rawReserve+caps.descriptorReserve+(r.family a).rows.length+
      (rowMetadataWord w layoutDegree C caps).length+1)

structure RowProducer (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) where
  privateWork : Nat
  coefficient : Nat
  degree : Nat
  positive : 0 < coefficient
  program : PCJ38fbfed565f64139_Ready.Program printer (rowWork privateWork)
  initializeStates : Nat
  initializer : Machine (rowTapes printer privateWork+1) initializeStates
  state : (r : Request) →
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) →
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) →
    RowCaps → PCJ38fbfed565f64139_Family.State (t:=rowTapes printer privateWork) printer
  initial : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    let s := state r layout facts caps
    let entry := PCJ38fbfed565f64139_Family.entry printer
      (PCJ38fbfed565f64139_Ready.code program) (r.family a) s
    Step initializer (rowInitBudget a coefficient degree r layout.w layout.degree layout.C caps)
      (fun _ => 0) (rowPublicInput selector a printer privateWork r layout caps)
      entry.heads entry.tapes
  ready : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    PCJ38fbfed565f64139_Ready.Ready printer program a (r.family a)
      (geometryOf selector a r) layout facts (state r layout facts caps)
  descriptor : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    ∀ j, j ≤ (r.family a).rows.length → ∀ out,
    let port := PCJ38fbfed565f64139_Ready.descriptor printer (rowWork privateWork)
    (state r layout facts caps).heads j out port = out.length ∧
    (state r layout facts caps).tapes j out port = ZeroPadding.pad caps.descriptorReserve out
  cost : ∀ r layout facts caps, RowCaps.Good selector a printer r layout facts caps →
    (state r layout facts caps).rowFuel ≤ rowBudget a coefficient degree r layout.C caps

end
end PCJd4d1d9d7d1fa4313_Production
