import Proof.Assembly.ClosureBinaryCacheMetadata

/-! This bounds the complete executed metadata generator, including all
literal generation, resets, copies and 39 composition transitions. It is
additive source preparation and contains no residual-table multiplier. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryCacheColdMetadata
open RepairOrdinary

theorem budget_bound (L q N K W : Nat) :
    budget L q N K W ≤ 2^24*(L+q+N+K+W+1)^3 := by
  dsimp only [budget,budget40,budget39,budget38,budget37,budget36,budget35,budget34,
    budget33,budget32,budget31,budget30,budget29,budget28,budget27,budget26,budget25,
    budget24,budget23,budget22,budget21,budget20,budget19,budget18,budget17,budget16,
    budget15,budget14,budget13,budget12,budget11,budget10,budget9,budget8,budget7,
    budget6,budget5,budget4,budget3,budget2,budget1,v1,v2,v3,v4,v5,v6,v7,v8,v9,
    v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,WilliamsUnaryProduct.budget]
  simp only [UnaryTemplate.tape,List.length_append,List.length_cons,List.length_replicate,
    List.length_nil]
  ring_nf
  omega

end NearCubicWires.P1Closure.BinaryCacheColdMetadata
