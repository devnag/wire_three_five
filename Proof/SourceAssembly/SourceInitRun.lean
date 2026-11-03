import Proof.SourceAssembly.SourceInitLayout

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.SupplierEstimator
open PCJ1fef9807c6954e94_Native
namespace NearCubicWires.SourceConstruction.InitRun
noncomputable section

/-! ## 1. The values -/

/-- The live count `K`. -/
abbrev Kc (L q : ℕ) : ℕ := normalizedLiveCount q L
/-- `U0 = 3(K+3) + 2⌈(q-K)/2⌉` (`RowConst.U0_eq`). -/
abbrev U0 (L q : ℕ) : ℕ := 3*(Kc L q+2+1) + ((q - Kc L q+1)/2 + (q - Kc L q+1)/2)
/-- The big slope `Mb = uniformDeg q L · Ms`. -/
abbrev Mb (L q : ℕ) : ℕ := q / InitSlopes.dv L q * InitPost.Ms L q
/-- The encoder's uniform `D` and `cap` (`D + 1 = cap`, `D ≥ 20b+22`). -/
abbrev D0 (b : ℕ) : ℕ := InitEnc.rr b + 1
abbrev cap0 (b : ℕ) : ℕ := InitEnc.rr b + 2
/-- `V`'s exact log from the pipeline. -/
abbrev VLog (eV L cVc q : ℕ) : ℕ := cVc*(q+1)^eV*(2*2^(q - normalizedLiveCount q L)+3)+2

/-! ## 2. The machine -/

namespace Place
variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T)

def initCost (_pl : Place d eX pX gW eR eV X T) (L C cVc cS cR q b : ℕ) : ℕ :=
  Once.onceCost eR eV L C cVc q + 1 +
    InitPost.cost L cS cR q b (cVc * RuntimeShape.tableClass L eV q) (Once.Rc eR L C q)

end Place

/-! ## 3. The exit, in the consumers' terms -/

/-! ## 4. Where the residents sit in the dock -/

namespace Place


/-! ## 5. `Once`'s side conditions on this placement -/




end Place

/-! ## 6. The post-`Once` machine's input, on `Once`'s exit -/

namespace Place

end Place

/-! ## 7. The exit facts -/

namespace Place

end Place

/-! ## 8. The exit of the post-`Once` machine, as one proposition -/

namespace Place

end Place

/-! ## 9. The frame -/

namespace Place

end Place

/-! ## 10. The run -/

namespace Place

end Place

/-! ## 11. The consumer's side conditions at the uniform choices -/


end
end NearCubicWires.SourceConstruction.InitRun
end
