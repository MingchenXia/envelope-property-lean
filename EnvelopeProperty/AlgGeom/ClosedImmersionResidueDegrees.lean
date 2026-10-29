import EnvelopeProperty.AlgGeom.AffineSchemeLocalDegrees
import EnvelopeProperty.AlgGeom.ClosedImmersionStalkQuotients

/-! # Original closed-immersion residue degrees and SAME ambient local degrees -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.ClosedImmersionResidueDegrees
open AffineSchemeLocalDegrees SchemeCoherentEulerIndex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X D : Scheme.{u}}

/-- The literal original residue-field map of the closed immersion is a
whole algebra isomorphism over the SAME original structure field. -/
def residueFieldAlgEquiv (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (y : D) :
    letI := residueAlgebra f (g y)
    letI := residueAlgebra (g ≫ f) y
    X.residueField (g y) ≃ₐ[k] D.residueField y := by
  letI := residueAlgebra f (g y)
  letI := residueAlgebra (g ≫ f) y
  letI : IsIso (g.residueFieldMap y) := ClosedImmersionStalkQuotients.residueFieldMap_isIso g y
  refine AlgEquiv.ofBijective
    { toRingHom := (g.residueFieldMap y).hom
      commutes' := ?_ } (ConcreteCategory.bijective_of_isIso (g.residueFieldMap y))
  intro r
  change g.residueFieldMap y (X.Γevaluation (g y) (f.appTop (baseScalar r))) =
    D.Γevaluation y ((g ≫ f).appTop (baseScalar r))
  rw [Scheme.Γevaluation_naturality_apply]
  rfl

/-- The whole algebra isomorphism is the literal original residue-field map. -/
@[simp] theorem residueFieldAlgEquiv_apply (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (y : D) (a : X.residueField (g y)) :
    residueFieldAlgEquiv g f y a = g.residueFieldMap y a := rfl

/-- The original closed and ambient residue fields have the SAME actual degree. -/
theorem residue_finrank_eq (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (y : D) :
    letI := residueAlgebra f (g y)
    letI := residueAlgebra (g ≫ f) y
    Module.finrank k (X.residueField (g y)) = Module.finrank k (D.residueField y) := by
  let := residueAlgebra f (g y)
  let := residueAlgebra (g ≫ f) y
  exact (residueFieldAlgEquiv g f y).toLinearEquiv.finrank_eq

/-- The native ORIGINAL local order weighted by the ORIGINAL ambient
residue degree is exactly the actual closed-scheme local degree. -/
theorem ord_mul_residue_finrank_eq_local_degree (g : D ⟶ X) [IsClosedImmersion g]
    [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Spec (.of k))
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    (c : Γ(X, U)) (hc : c ≠ 0)
    (hker : g.ker.ideal ⟨U, hU⟩ = Ideal.span {c})
    (y : D) (hy : g y ∈ U) (hcodim : Order.coheight (g y) = 1) :
    letI := residueAlgebra f (g y)
    letI := residueAlgebra (g ≫ f) y
    X.ord (X.germToFunctionField U c) (g y) *
        (Module.finrank k (X.residueField (g y)) : ℤ) =
      (((Module.length (D.presheaf.stalk y) (D.presheaf.stalk y)).toNat *
        Module.finrank k (D.residueField y) : ℕ) : ℤ) := by
  let := residueAlgebra f (g y)
  let := residueAlgebra (g ≫ f) y
  rw [ClosedImmersionStalkQuotients.ord_eq_closedStalk_length g U hU c hc hker y hy hcodim,
    residue_finrank_eq g f y]
  simp only [Nat.cast_mul]

/-- The SAME finite closed ideal's full Euler degree uses the actual
ambient residue degrees through its literal original closed immersion. -/
theorem normalizedEulerCharacteristic_idealModule_eq_neg_sum_ambient_residue
    (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)] :
    SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic f (ModularCurves.idealModule g) =
      -((∑ᶠ y : D, letI := residueAlgebra f (g y)
        (Module.length (D.presheaf.stalk y) (D.presheaf.stalk y)).toNat *
          Module.finrank k (X.residueField (g y))) : ℕ) := by
  rw [normalizedEulerCharacteristic_idealModule_eq_neg_sum_points g f hf]
  congr 2
  apply finsum_congr
  intro y
  let := residueAlgebra f (g y)
  let := residueAlgebra (g ≫ f) y
  rw [residue_finrank_eq g f y]

end EnvelopeProperty.ClosedImmersionResidueDegrees
