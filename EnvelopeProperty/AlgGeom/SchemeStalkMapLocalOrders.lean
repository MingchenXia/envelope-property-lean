import EnvelopeProperty.Algebra.SemilinearPrincipalLengths
import EnvelopeProperty.AlgGeom.AffineSchemeLocalDegrees

/-! # True native local orders and ORIGINAL residue weights under original stalk isomorphisms -/
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.SchemeStalkMapLocalOrders
open AffineSchemeLocalDegrees SchemeCoherentEulerIndex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (y : Y) [IsIso (g.stalkMap y)]

/-- The SAME actual original native stalk map preserves TRUE original
principal ring order, with no order comparison input. -/
theorem ord_stalkMap (a : X.presheaf.stalk (g y)) :
    Ring.ord (X.presheaf.stalk (g y)) a = Ring.ord (Y.presheaf.stalk y) (g.stalkMap y a) :=
  SemilinearPrincipalLengths.ord_ringEquiv (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv a

/-- The SAME actual native original residue map is a whole algebra isomorphism
over the SAME original structure field, with its actual coefficient action. -/
def residueFieldAlgEquiv {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) :
    letI := residueAlgebra p (g y)
    letI := residueAlgebra (g ≫ p) y
    X.residueField (g y) ≃ₐ[k] Y.residueField y := by
  let := residueAlgebra p (g y)
  let := residueAlgebra (g ≫ p) y
  let : IsIso (g.residueFieldMap y) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  refine AlgEquiv.ofBijective
    { toRingHom := (g.residueFieldMap y).hom
      commutes' := ?_ } (ConcreteCategory.bijective_of_isIso (g.residueFieldMap y))
  intro c
  change g.residueFieldMap y (X.Γevaluation (g y) (p.appTop (baseScalar c))) =
    Y.Γevaluation y ((g ≫ p).appTop (baseScalar c))
  rw [Scheme.Γevaluation_naturality_apply]
  rfl

/-- The SAME original residue-field degrees agree through that actual native coefficient map. -/
theorem residue_finrank_eq {k : Type u} [Field k] (p : X ⟶ Spec (.of k)) :
    letI := residueAlgebra p (g y)
    letI := residueAlgebra (g ≫ p) y
    Module.finrank k (X.residueField (g y)) = Module.finrank k (Y.residueField y) := by
  let := residueAlgebra p (g y)
  let := residueAlgebra (g ≫ p) y
  exact (residueFieldAlgEquiv g y p).toLinearEquiv.finrank_eq

/-- TRUE actual original principal local order times ORIGINAL residue degree
is preserved by the SAME original stalk map, with no weighted-degree certificate. -/
theorem weightedOrder_stalkMap {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    (a : X.presheaf.stalk (g y)) :
    letI := residueAlgebra p (g y)
    letI := residueAlgebra (g ≫ p) y
    ((Ring.ord (X.presheaf.stalk (g y)) a).toNat : ℤ) *
        (Module.finrank k (X.residueField (g y)) : ℤ) =
      ((Ring.ord (Y.presheaf.stalk y) (g.stalkMap y a)).toNat : ℤ) *
        (Module.finrank k (Y.residueField y) : ℤ) := by
  let := residueAlgebra p (g y)
  let := residueAlgebra (g ≫ p) y
  rw [ord_stalkMap, residue_finrank_eq]

/-- Every SAME ORIGINAL regular section and its ACTUAL original pullback
have exactly the same TRUE native weighted local order through an actual stalk isomorphism. -/
theorem weightedOrder_germ_pullback {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    (U : X.Opens) (hy : g y ∈ U) (c : Γ(X, U)) :
    letI := residueAlgebra p (g y)
    letI := residueAlgebra (g ≫ p) y
    ((Ring.ord (X.presheaf.stalk (g y)) (X.presheaf.germ U (g y) hy c)).toNat : ℤ) *
        (Module.finrank k (X.residueField (g y)) : ℤ) =
      ((Ring.ord (Y.presheaf.stalk y) (Y.presheaf.germ (g ⁻¹ᵁ U) y hy (g.app U c))).toNat : ℤ) *
        (Module.finrank k (Y.residueField y) : ℤ) := by
  let := residueAlgebra p (g y)
  let := residueAlgebra (g ≫ p) y
  have h := weightedOrder_stalkMap g y p (X.presheaf.germ U (g y) hy c)
  have hg := ConcreteCategory.congr_hom (g.germ_stalkMap U y hy) c
  change g.stalkMap y (X.presheaf.germ U (g y) hy c) =
    Y.presheaf.germ (g ⁻¹ᵁ U) y hy (g.app U c) at hg
  rw [hg] at h
  exact h

end EnvelopeProperty.SchemeStalkMapLocalOrders
