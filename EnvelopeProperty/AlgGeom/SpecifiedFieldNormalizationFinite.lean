import EnvelopeProperty.AlgGeom.SpecifiedFieldNormalizationCharts
import EnvelopeProperty.Alterations.Algebra.IntegralClosureFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Hironaka.Algebra.RegularSmooth.SmoothAt

/-! # Finiteness and genuine normal stalks of the SAME specified-field normalization -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.SpecifiedFieldSchemeNormalization

private theorem finite_of_coefficientSquare {A B C : CommRingCat.{u}}
    (q : A ⟶ B) (e : B ≅ C) (r : A ⟶ C) (h : q ≫ e.hom = r)
    (hr : r.hom.Finite) : q.hom.Finite := by
  have hq : q = r ≫ e.inv := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hq]
  exact (RingHom.Finite.of_surjective e.inv.hom
    e.symm.commRingCatIsoToRingEquiv.surjective).comp hr

private theorem stalk_isIntegrallyClosed_of_affine {Y : Scheme.{u}}
    (V : Y.Opens) (hV : IsAffineOpen V) [IsDomain Γ(Y, V)] [IsIntegrallyClosed Γ(Y, V)]
    (z : Y) (hz : z ∈ V) : IsIntegrallyClosed (Y.presheaf.stalk z) := by
  let q := hV.primeIdealOf ⟨z, hz⟩
  have hq : hV.fromSpec q = z := hV.fromSpec_primeIdealOf ⟨z, hz⟩
  let : IsOpenImmersion hV.fromSpec := inferInstance
  let : IsIso (hV.fromSpec.stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion hV.fromSpec›).2 q
  let : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  rw [← hq]
  exact IsIntegrallyClosed.of_equiv
    ((Spec.stalkIso Γ(Y, V) q).commRingCatIsoToRingEquiv.symm.trans
      (asIso (hV.fromSpec.stalkMap q)).commRingCatIsoToRingEquiv.symm)

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

/-- The actual original affine coefficients give the SAME true extension-field scalar tower. -/
theorem sectionExtensionAlgebra_isScalarTower (U : X.Opens) [Nonempty U] :
    letI := sectionExtensionAlgebra X L U
    IsScalarTower Γ(X, U) X.functionField L := by
  let := sectionExtensionAlgebra X L U
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Finite original function-field extensions give actual finite closure modules
over EVERY original finite-type nonempty affine section ring, over ANY coefficient field. -/
theorem affineClosure_finite {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [FiniteDimensional X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := sectionExtensionAlgebra X L U
    Module.Finite Γ(X, U) (integralClosure Γ(X, U) L) := by
  let := f.sectionsAlgebra U
  let := f.finiteType_sectionsAlgebra hU
  let := sectionExtensionAlgebra X L U
  let := sectionExtensionAlgebra_isScalarTower X L U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  exact Alterations.Algebra.IntegralClosureFiniteType.finite_of_isIntegralClosure_of_finiteType
    k Γ(X, U) X.functionField L (integralClosure Γ(X, U) L)

/-- The SAME actual whole projection section map is finite on EVERY nonempty affine open. -/
theorem projection_finite_app {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [FiniteDimensional X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    ((projection X L).app U).hom.Finite := by
  let := sectionExtensionAlgebra X L U
  let := affineClosure_finite X L f U hU
  exact finite_of_coefficientSquare ((projection X L).app U) (affineSectionIso X L U hU)
    (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)))
    (affineSectionIso_coefficients X L U hU) (RingHom.finite_algebraMap.mpr inferInstance)

/-- The SAME actual normalization projection is finite over ANY original coefficient field.
No supplied finite-normalization premise or perfectness assumption is used. -/
theorem projection_isFinite {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [FiniteDimensional X.functionField L] :
    IsFinite (projection X L) := by
  let := projection_isIntegralHom X L
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  classical
  by_cases hne : Nonempty U
  · let := hne
    exact projection_finite_app X L f U hU
  · have hbot : U = ⊥ := by
      ext x
      exact ⟨fun hx => (hne ⟨⟨x, hx⟩⟩).elim, False.elim⟩
    subst U
    have hs : Subsingleton Γ(normalization X L, (projection X L) ⁻¹ᵁ ⊥) := by
      rw [Scheme.Hom.preimage_bot]
      infer_instance
    exact RingHom.Finite.of_surjective _ (fun s => ⟨0, hs.elim _ _⟩)

/-- Every original actual normalization stalk is integrally closed in the SAME specified finite field.
No original scheme normality, perfectness, finite type or dimension premise is used. -/
theorem stalk_isIntegrallyClosed [FiniteDimensional X.functionField L]
    (z : normalization X L) : IsIntegrallyClosed ((normalization X L).presheaf.stalk z) := by
  let := normalization_isIntegral X L
  obtain ⟨U, hU, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (show projection X L z ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨projection X L z, hz⟩⟩
  let : Nonempty ((projection X L) ⁻¹ᵁ U) := ⟨⟨z, hz⟩⟩
  let := sectionExtensionAlgebra X L U
  let := sectionExtensionAlgebra_isScalarTower X L U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsIntegrallyClosed (integralClosure Γ(X, U) L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension X.functionField
  let : IsIntegrallyClosed Γ(normalization X L, (projection X L) ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (affineSectionIso X L U hU).commRingCatIsoToRingEquiv.symm
  exact stalk_isIntegrallyClosed_of_affine ((projection X L) ⁻¹ᵁ U)
    (affinePreimage_isAffineOpen X L U hU) z hz

end EnvelopeProperty.SpecifiedFieldSchemeNormalization
