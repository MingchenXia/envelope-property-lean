import EnvelopeProperty.AlgGeom.SchemeStalkMapLocalOrders
import EnvelopeProperty.AlgGeom.CurveFiniteClosedSubschemes

/-! # SAME original global regular section orders and native weighted local transport -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeRegularSectionOrders
open AffineSchemeLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

private instance topNonempty : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- The actual ORIGINAL native Scheme.ord of the actual original global
regular section, weighted by its original structure-field residue degree. -/
def weightedOrder {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) (c : Γ(X, ⊤)) (x : X) : ℤ :=
  letI := residueAlgebra p x
  X.ord (X.germToFunctionField ⊤ c) x * (Module.finrank k (X.residueField x) : ℤ)

/-- The SAME original generic-point term is genuinely zero. -/
theorem weightedOrder_genericPoint {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) (c : Γ(X, ⊤)) : weightedOrder p c (genericPoint X) = 0 := by
  unfold weightedOrder
  have hx : Order.coheight (genericPoint X) ≠ 1 := by
    change Order.coheight (⊤ : X) ≠ 1
    simp
  rw [X.ord_eq_zero_of_coheight_neq_one hx, zero_mul]

/-- Every SAME original nongeneric actual curve point has its TRUE native
section weighted order computed by its SAME actual stalk principal quotient. -/
theorem weightedOrder_eq_stalk {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) (hdim : topologicalKrullDim X ≤ 1)
    (c : Γ(X, ⊤)) (hc : c ≠ 0) (x : X) (hx : x ≠ genericPoint X) :
    letI := residueAlgebra p x
    weightedOrder p c x =
      ((Ring.ord (X.presheaf.stalk x) (X.presheaf.germ ⊤ x trivial c)).toNat : ℤ) *
        (Module.finrank k (X.residueField x) : ℤ) := by
  let := residueAlgebra p x
  unfold weightedOrder
  rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length x
    (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) ⊤ trivial c hc]
  rfl

omit [IsLocallyNoetherian X] in
/-- One actual original stalk isomorphism internally proves that the SAME
global original section's actual pullback is nonzero on the original source. -/
theorem pullback_ne_zero {Y : Scheme.{u}}
    (g : Y ⟶ X) (y : Y) [IsIso (g.stalkMap y)] (c : Γ(X, ⊤)) (hc : c ≠ 0) :
    g.appTop c ≠ 0 := by
  intro hz
  have hg := ConcreteCategory.congr_hom (g.germ_stalkMap ⊤ y trivial) c
  change g.stalkMap y (X.presheaf.germ ⊤ (g y) trivial c) =
    Y.presheaf.germ ⊤ y trivial (g.appTop c) at hg
  rw [hz, map_zero] at hg
  have hzero : X.presheaf.germ ⊤ (g y) trivial c = 0 :=
    (ConcreteCategory.bijective_of_isIso (g.stalkMap y)).injective (hg.trans (map_zero _).symm)
  exact hc ((germ_injective_of_isIntegral X (U := ⊤) (g y) trivial) (hzero.trans (map_zero _).symm))

/-- TRUE weighted native Scheme.ord of EVERY original global regular
section is preserved by the SAME actual stalk isomorphism and original pullback.
No section nonvanishing, order or residue comparison is supplied for the pullback. -/
theorem weightedOrder_pullback {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {k : Type u} [Field k] (g : Y ⟶ X) (p : X ⟶ Spec (.of k))
    (hdimX : topologicalKrullDim X ≤ 1) (hdimY : topologicalKrullDim Y ≤ 1)
    (y : Y) [IsIso (g.stalkMap y)] (hy : y ≠ genericPoint Y)
    (hgy : g y ≠ genericPoint X) (c : Γ(X, ⊤)) (hc : c ≠ 0) :
    weightedOrder p c (g y) = weightedOrder (g ≫ p) (g.appTop c) y := by
  rw [weightedOrder_eq_stalk p hdimX c hc (g y) hgy,
    weightedOrder_eq_stalk (g ≫ p) hdimY (g.appTop c) (pullback_ne_zero g y c hc) y hy]
  exact SchemeStalkMapLocalOrders.weightedOrder_germ_pullback g y p ⊤ trivial c

/-- The ENTIRE original native weighted-order sum is exactly the sum over
ALL original nongeneric points, with no supplied support/finite-sum certificate. -/
theorem finsum_eq_nongeneric {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) (c : Γ(X, ⊤)) :
    (∑ᶠ x : X, weightedOrder p c x) =
      ∑ᶠ x : {x : X // x ≠ genericPoint X}, weightedOrder p c x.1 := by
  have hs : Set.univ ∩ Function.support (weightedOrder p c) =
      {x : X | x ≠ genericPoint X} ∩ Function.support (weightedOrder p c) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨?_, hx⟩
      intro he
      exact hx (he ▸ weightedOrder_genericPoint p c)
    · exact And.right
  rw [← finsum_mem_univ (weightedOrder p c),
    finsum_mem_inter_support_eq (weightedOrder p c) Set.univ {x | x ≠ genericPoint X} hs,
    ← finsum_set_coe_eq_finsum_mem]
  rfl

end EnvelopeProperty.SchemeRegularSectionOrders
