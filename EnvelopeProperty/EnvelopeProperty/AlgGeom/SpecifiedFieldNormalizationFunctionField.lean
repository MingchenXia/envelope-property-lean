import EnvelopeProperty.AlgGeom.SpecifiedFieldNormalizationFinite
import EnvelopeProperty.AlgGeom.SchemeFunctionFieldSubalgebras

/-! # The genuine original function field of the SAME specified-field normalization -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SpecifiedFieldSchemeNormalization

private theorem pullback_section_coefficient {Y Z : Scheme.{u}} {k : Type u} [CommRing k]
    (p : Y ⟶ Z) (f : Z ⟶ Spec (.of k)) (U : Z.Opens) (c : k) :
    letI := f.sectionsAlgebra U
    letI := (p ≫ f).sectionsAlgebra (p ⁻¹ᵁ U)
    p.app U (algebraMap k Γ(Z, U) c) = algebraMap k Γ(Y, p ⁻¹ᵁ U) c := by
  let := f.sectionsAlgebra U
  let := (p ≫ f).sectionsAlgebra (p ⁻¹ᵁ U)
  have hc := Scheme.Hom.appLE_comp_appLE p f ⊤ U (p ⁻¹ᵁ U) le_top le_rfl
  have hc' := congrArg (fun q : Γ(Spec (.of k), ⊤) ⟶ Γ(Y, p ⁻¹ᵁ U) =>
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q) c) hc
  change (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top) ≫ p.app U) c =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (p ≫ f).appLE ⊤ (p ⁻¹ᵁ U) le_top) c
  simpa only [Scheme.Hom.app_eq_appLE, Category.assoc] using hc'

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

private local instance : IsIntegral (normalization X L) := normalization_isIntegral X L

/-- The actual extension-field generic lift meets EVERY original nonempty-open inverse image. -/
theorem affinePreimage_nonempty (U : X.Opens) [Nonempty U] :
    Nonempty ((projection X L) ⁻¹ᵁ U) := by
  let z : Spec (.of L) := IsLocalRing.closedPoint L
  have hx : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  refine ⟨⟨genericLift X L z, ?_⟩⟩
  change projection X L (genericLift X L z) ∈ U
  have hh := congrArg (fun f : Spec (.of L) ⟶ X => f z) (genericLift_comp_projection X L)
  rw [← Scheme.Hom.comp_apply, hh, genericMap_apply]
  exact hx

/-- The whole actual normalization function field is the SAME specified extension field,
constructed from the genuine original affine section ring and its literal closure. -/
def functionFieldEquiv [FiniteDimensional X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (normalization X L).functionField ≃+* L := by
  let := sectionExtensionAlgebra X L U
  let := sectionExtensionAlgebra_isScalarTower X L U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsFractionRing (integralClosure Γ(X, U) L) L :=
    integralClosure.isFractionRing_of_finite_extension X.functionField L
  let := affinePreimage_nonempty X L U
  let := functionField_isFractionRing_of_isAffineOpen (normalization X L)
    ((projection X L) ⁻¹ᵁ U) (affinePreimage_isAffineOpen X L U hU)
  exact IsFractionRing.ringEquivOfRingEquiv
    (K := (normalization X L).functionField) (L := L)
      (affineSectionIso X L U hU).commRingCatIsoToRingEquiv

/-- EVERY original whole normalization-chart section has its SAME actual value in the specified field. -/
theorem functionFieldEquiv_section [FiniteDimensional X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (s : Γ(normalization X L, (projection X L) ⁻¹ᵁ U)) :
    letI := sectionExtensionAlgebra X L U
    letI := affinePreimage_nonempty X L U
    functionFieldEquiv X L U hU
      ((normalization X L).germToFunctionField ((projection X L) ⁻¹ᵁ U) s) =
      ((affineSectionIso X L U hU).hom s : integralClosure Γ(X, U) L).val := by
  let := sectionExtensionAlgebra X L U
  let := sectionExtensionAlgebra_isScalarTower X L U
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsFractionRing (integralClosure Γ(X, U) L) L :=
    integralClosure.isFractionRing_of_finite_extension X.functionField L
  let := affinePreimage_nonempty X L U
  let := functionField_isFractionRing_of_isAffineOpen (normalization X L)
    ((projection X L) ⁻¹ᵁ U) (affinePreimage_isAffineOpen X L U hU)
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (K := (normalization X L).functionField) (L := L)
      (affineSectionIso X L U hU).commRingCatIsoToRingEquiv s

/-- EVERY actual original base-chart coefficient is sent to the literal specified generic-field embedding. -/
theorem functionFieldEquiv_projection_section [FiniteDimensional X.functionField L]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (s : Γ(X, U)) :
    letI := affinePreimage_nonempty X L U
    functionFieldEquiv X L U hU
      ((normalization X L).germToFunctionField ((projection X L) ⁻¹ᵁ U)
        ((projection X L).app U s)) =
      algebraMap X.functionField L (X.germToFunctionField U s) := by
  let := affinePreimage_nonempty X L U
  let := sectionExtensionAlgebra X L U
  rw [functionFieldEquiv_section]
  have hh := congrArg (fun q : Γ(X, U) ⟶ CommRingCat.of (integralClosure Γ(X, U) L) => q s)
    (affineSectionIso_coefficients X L U hU)
  exact congrArg Subtype.val hh

/-- The ACTUAL original coefficient-field action extends through the original generic embedding. -/
abbrev coefficientExtensionAlgebra {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) :
    Algebra k L :=
  letI := f.stalkAlgebra (genericPoint X)
  ((algebraMap X.functionField L).comp (algebraMap k X.functionField)).toAlgebra

/-- The SAME genuine normalization-function-field equivalence preserves the ACTUAL
original native structure-map stalk action, on all original coefficients. -/
def functionFieldAlgEquiv {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    [FiniteDimensional X.functionField L] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (projection X L ≫ f).stalkAlgebra (genericPoint (normalization X L))
    letI := coefficientExtensionAlgebra X L f
    (normalization X L).functionField ≃ₐ[k] L := by
  let := f.sectionsAlgebra U
  let := f.stalkAlgebra (genericPoint X)
  let := affinePreimage_nonempty X L U
  let := (projection X L ≫ f).sectionsAlgebra ((projection X L) ⁻¹ᵁ U)
  let := (projection X L ≫ f).stalkAlgebra (genericPoint (normalization X L))
  let := coefficientExtensionAlgebra X L f
  refine { functionFieldEquiv X L U hU with commutes' := ?_ }
  intro c
  rw [← ((projection X L ≫ f).sectionsFunctionFieldAlgHom
    ((projection X L) ⁻¹ᵁ U)).commutes c]
  change functionFieldEquiv X L U hU
    ((normalization X L).germToFunctionField ((projection X L) ⁻¹ᵁ U)
      (algebraMap k Γ(normalization X L, (projection X L) ⁻¹ᵁ U) c)) = _
  rw [← pullback_section_coefficient (projection X L) f U c,
    functionFieldEquiv_projection_section]
  change algebraMap X.functionField L
    ((f.sectionsFunctionFieldAlgHom U) (algebraMap k Γ(X, U) c)) = _
  rw [(f.sectionsFunctionFieldAlgHom U).commutes c]
  rfl

end EnvelopeProperty.SpecifiedFieldSchemeNormalization
