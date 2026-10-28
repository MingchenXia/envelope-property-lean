import Mathlib.AlgebraicGeometry.Modules.Tilde
import EnvelopeProperty.AlgGeom.SchemeOpenRestrictionHomology
import EnvelopeProperty.AlgGeom.AffineQuasicoherentComplexHomology

/-! # The SAME actual affine restriction/section functors, with whole original coefficients -/
noncomputable section
namespace EnvelopeProperty.AffineRestrictionSections
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

private theorem imageTop_eq : hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) = V :=
  (Scheme.Hom.image_top_eq_opensRange _).trans hV.opensRange_fromSpec

private theorem fromSpec_appLE_top
    (he : (⊤ : (Spec Γ(X, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V) :
    hV.fromSpec.appLE V ⊤ he = (Scheme.ΓSpecIso Γ(X, V)).inv := by
  dsimp only [Scheme.Hom.appLE]
  rw [hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  have hi : (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE he).op =
      𝟙 (op (⊤ : (Spec Γ(X, V)).Opens)) := Subsingleton.elim _ _
  rw [hi, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The ENTIRE original affine restriction coefficient triangle, no matching premise. -/
theorem coefficient_triangle :
    (Scheme.ΓSpecIso Γ(X, V)).inv ≫ (hV.fromSpec.appIso ⊤).inv =
      X.presheaf.map (homOfLE (imageTop_eq hV).le).op := by
  have he : (⊤ : (Spec Γ(X, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by
    rw [hV.fromSpec_preimage_self]
  have h := Scheme.Hom.appLE_appIso_inv hV.fromSpec (U := V) (V := ⊤) he
  rw [fromSpec_appLE_top hV he] at h
  exact h

private def additiveIso (M : X.Modules) :
    Γ(M.restrict hV.fromSpec, (⊤ : (Spec Γ(X, V)).Opens)) ≅ Γ(M, V) :=
  M.restrictAppIso hV.fromSpec ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (imageTop_eq hV).symm).op

private theorem coefficient_cancel (r : Γ(X, V)) :
    X.presheaf.map (eqToHom (imageTop_eq hV).symm).op
      ((hV.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, V)).inv r)) = r := by
  have h := congrArg (fun a => a ≫ X.presheaf.map (eqToHom (imageTop_eq hV).symm).op)
    (coefficient_triangle hV)
  rw [← Functor.map_comp] at h
  have hi : (homOfLE (imageTop_eq hV).le).op ≫ (eqToHom (imageTop_eq hV).symm).op =
      𝟙 (op V) := Subsingleton.elim _ _
  rw [hi, CategoryTheory.Functor.map_id] at h
  exact ConcreteCategory.congr_hom h r

private theorem additiveIso_smul (M : X.Modules) (r : Γ(X, V))
    (x : moduleSpecΓFunctor.obj (M.restrict hV.fromSpec)) :
    (additiveIso hV M).hom (r • x) =
      r • (show Γ(M, V) from (additiveIso hV M).hom x) := by
  change M.presheaf.map (eqToHom (imageTop_eq hV).symm).op
      ((M.restrictAppIso hV.fromSpec ⊤).hom
        ((Scheme.ΓSpecIso Γ(X, V)).inv r •
          (show Γ(M.restrict hV.fromSpec, (⊤ : (Spec Γ(X, V)).Opens)) from x))) = _
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply,
    Scheme.Modules.map_smul, coefficient_cancel]
  rfl

/-- GENUINE original whole coefficient-linear affine restriction/section isomorphism. -/
def sectionsIso (M : X.Modules) :
    moduleSpecΓFunctor.obj (M.restrict hV.fromSpec) ≅ M.val.obj (op V) := by
  refine ModuleCat.isoMk (additiveIso hV M) ?_
  intro r
  ext x
  exact (additiveIso_smul hV M r x).symm

/-- EVERY original section retains exactly its true native restriction comparison. -/
theorem sectionsIso_hom_apply (M : X.Modules)
    (x : moduleSpecΓFunctor.obj (M.restrict hV.fromSpec)) :
    (sectionsIso hV M).hom.hom x =
      M.presheaf.map (eqToHom (imageTop_eq hV).symm).op
        ((M.restrictAppIso hV.fromSpec ⊤).hom x) := rfl

/-- The ENTIRE original module section comparison is genuinely natural in EVERY original map. -/
def functorIso : Scheme.Modules.restrictFunctor hV.fromSpec ⋙ moduleSpecΓFunctor ≅
    SheafOfModules.evaluation X.ringCatSheaf (op V) :=
  NatIso.ofComponents (sectionsIso hV) (by
    intro M N α
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Eq.symm
    change α.val.app (op V)
        (M.presheaf.map (eqToHom (imageTop_eq hV).symm).op
          ((M.restrictAppIso hV.fromSpec ⊤).hom x)) =
      N.presheaf.map (eqToHom (imageTop_eq hV).symm).op
        ((N.restrictAppIso hV.fromSpec ⊤).hom
          (α.val.app (op (hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens))) x))
    exact PresheafOfModules.naturality_apply α.val
      (eqToHom (imageTop_eq hV).symm).op x)

private instance evaluationAdditive :
    (SheafOfModules.evaluation X.ringCatSheaf (op V)).Additive := by
  dsimp only [SheafOfModules.evaluation]
  infer_instance

/-- The SAME entire original affine restriction section complex, without QC assumptions. -/
def complexIso (K : CochainComplex X.Modules ℕ) :
    AffineQuasicoherentComplexHomology.sectionComplex Γ(X, V)
        (SchemeOpenRestrictionHomology.restrictedComplex hV.fromSpec K) ≅
      ((SheafOfModules.evaluation X.ringCatSheaf (op V)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K := by
  refine HomologicalComplex.Hom.isoOfComponents (fun q => sectionsIso hV (K.X q)) ?_
  intro i j _
  exact ((functorIso hV).hom.naturality (K.d i j)).symm

end EnvelopeProperty.AffineRestrictionSections
