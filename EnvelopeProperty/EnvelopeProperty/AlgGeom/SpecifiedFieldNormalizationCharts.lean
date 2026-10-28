import EnvelopeProperty.AlgGeom.SpecifiedFieldGenericMap

/-! # Actual relative-normalization charts inside the SAME specified field -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.SpecifiedFieldSchemeNormalization
variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L] [Algebra X.functionField L]

private local instance : QuasiCompact (genericMap X L) := genericMap_quasiCompact X L
private local instance : QuasiSeparated (genericMap X L) := genericMap_quasiSeparated X L

/-- The ACTUAL original section-ring action through the SAME original generic embedding. -/
abbrev sectionExtensionAlgebra (U : X.Opens) [Nonempty U] : Algebra Γ(X, U) L :=
  ((algebraMap X.functionField L).comp (X.germToFunctionField U).hom).toAlgebra

/-- The native ACTUAL relative normalization in the SAME specified field. -/
abbrev normalization : Scheme.{u} := (genericMap X L).normalization

/-- The actual original projection of the SAME relative normalization. -/
def projection : normalization X L ⟶ X := (genericMap X L).fromNormalization

/-- The SAME actual extension-field generic morphism factors through its actual normalization. -/
def genericLift : Spec (.of L) ⟶ normalization X L := (genericMap X L).toNormalization

/-- The literal original generic morphism is retained by the native factorization. -/
@[simp] theorem genericLift_comp_projection : genericLift X L ≫ projection X L = genericMap X L :=
  (genericMap X L).toNormalization_fromNormalization

/-- The original projection is genuinely integral without any finite-normalization premise. -/
theorem projection_isIntegralHom : IsIntegralHom (projection X L) := by
  unfold projection
  infer_instance

/-- The actual source field forces integralness of the SAME whole native normalization. -/
theorem normalization_isIntegral : IsIntegral (normalization X L) := by
  exact inferInstanceAs (IsIntegral (genericMap X L).normalization)

/-- The ENTIRE actual relative-normalization affine closure is the literal closure in the SAME L. -/
def affineClosureEquiv (U : X.Opens) [Nonempty U] :
    letI := sectionExtensionAlgebra X L U
    letI := ((genericMap X L).app U).hom.toAlgebra
    integralClosure Γ(X, U) Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U) L := by
  let := sectionExtensionAlgebra X L U
  let := ((genericMap X L).app U).hom.toAlgebra
  let e : Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] L := {
    __ := (genericSectionIso X L U).commRingCatIsoToRingEquiv
    commutes' a := by
      exact congrArg (fun f : Γ(X, U) ⟶ CommRingCat.of L => f a)
        (genericSectionIso_coefficients X L U) }
  exact e.mapIntegralClosure

/-- EVERY original section coefficient survives the actual whole affine-closure equivalence. -/
@[simp] theorem affineClosureEquiv_algebraMap (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    letI := sectionExtensionAlgebra X L U
    letI := ((genericMap X L).app U).hom.toAlgebra
    affineClosureEquiv X L U (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U)) a) =
      algebraMap Γ(X, U) (integralClosure Γ(X, U) L) a :=
  (affineClosureEquiv X L U).commutes a

/-- Every original affine open has an ACTUAL affine normalization inverse image. -/
theorem affinePreimage_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen ((projection X L) ⁻¹ᵁ U) := by
  let := projection_isIntegralHom X L
  exact hU.preimage (projection X L)

/-- The WHOLE actual original normalization inverse-image section ring is the literal closure in L. -/
def affineSectionIso (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := sectionExtensionAlgebra X L U
    Γ(normalization X L, (projection X L) ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(X, U) L) := by
  let := sectionExtensionAlgebra X L U
  let := ((genericMap X L).app U).hom.toAlgebra
  exact (genericMap X L).normalizationObjIso hU ≪≫
    (affineClosureEquiv X L U).toRingEquiv.toCommRingCatIso

/-- The original projection coefficient square is preserved on EVERY whole original affine chart. -/
theorem affineSectionIso_coefficients (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := sectionExtensionAlgebra X L U
    (projection X L).app U ≫ (affineSectionIso X L U hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U) L)) := by
  let := sectionExtensionAlgebra X L U
  let := ((genericMap X L).app U).hom.toAlgebra
  have hn := (genericMap X L).fromNormalization_app hU
  have hn' := congrArg (fun q : Γ(X, U) ⟶
      Γ(normalization X L, (projection X L) ⁻¹ᵁ U) =>
      q ≫ (affineSectionIso X L U hU).hom) hn
  refine hn'.trans ?_
  change (CommRingCat.ofHom (algebraMap Γ(X, U) (integralClosure Γ(X, U)
      Γ(Spec (.of L), (genericMap X L) ⁻¹ᵁ U))) ≫
      ((genericMap X L).normalizationObjIso hU).inv) ≫
      ((genericMap X L).normalizationObjIso hU).hom ≫
        (affineClosureEquiv X L U).toRingEquiv.toCommRingCatIso.hom = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact CommRingCat.hom_ext (by
    ext a
    exact congrArg Subtype.val ((affineClosureEquiv X L U).commutes a))

end EnvelopeProperty.SpecifiedFieldSchemeNormalization
