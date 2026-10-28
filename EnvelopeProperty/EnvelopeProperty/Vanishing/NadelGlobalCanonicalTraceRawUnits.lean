import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTracePureSections

/-! # Original ordinary differentials in the same native affine unit

The categorical-to-ordinary cotangent comparison is a genuine transport of
the original algebra structure.  These readbacks retain the original D(a),
which is needed in the canonical trace normalization on coordinate frames.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem algebraDifferentialTransport
    (K : Type u) [Field K] (A : CommRingCat.{u})
    (a₁ a₂ : Algebra K A) (h : a₁ = a₂) (z : A) :
    (eqToHom (congrArg (fun a : Algebra K A =>
      letI : Algebra K A := a
      ModuleCat.of A (KaehlerDifferential K A)) h))
        (letI : Algebra K A := a₁
         KaehlerDifferential.D K A z) =
      (letI : Algebra K A := a₂
       KaehlerDifferential.D K A z) := by
  cases h
  rfl

variable (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]

/-- The actual categorical/ordinary coordinate comparison retains EVERY
original universal differential under its literal algebra-structure transport. -/
theorem affineCotangentModuleIso_inv_D (z : A) :
    (affineCotangentModuleIso K A).inv (KaehlerDifferential.D K A z) =
      CommRingCat.KaehlerDifferential.d (f := affineBaseRingMap K A) z := by
  exact algebraDifferentialTransport K A inferInstance (algebraMap K A).toAlgebra
    (toAlgebra_algebraMap (R := K) (S := A)).symm z

/-- The same ordinary coordinate differential enters the actual native
presheaf as the universal differential of the SAME original coefficient. -/
theorem affineOrdinaryCotangentToOpen_D (U : (Spec A).Opensᵒᵖ) (z : A) :
    affineOrdinaryCotangentSemilinear K A U (KaehlerDifferential.D K A z) =
      (cotangentPresheafDerivation (affineStructuralMap K A)).d (affineCoordinateMap A U z) := by
  change affineCotangentToOpen K A U
    ((affineCotangentModuleIso K A).inv (KaehlerDifferential.D K A z)) = _
  rw [affineCotangentModuleIso_inv_D, affineCotangentToOpen_d]

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
