import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.ForMathlib.SchemeModuleBaseCechBasic

/-! # Actual affine-open module restriction localizes at the SAME global base parameter

The native affine quasicoherent localization theorem is restricted along the
actual base coefficient map. All scalar towers are proved from original
presheaf composition, with no localization or coefficient certificate.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EnvelopeProperty.AffineOpenGlobalParameterLocalization
universe u
set_option backward.isDefEq.respectTransparency false
variable {X B : Scheme.{u}} (π : X ⟶ B) (M : X.Modules) [M.IsQuasicoherent]

private theorem originalRestrictionLocalizationCongr
    {T : TopCat.{u}} {A : Type u} [CommRing A]
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{u} A) (r : A)
    {U V W : Opens T} (h : V = W) (hV : V ≤ U) (hW : W ≤ U)
    (hl : IsLocalizedModule.Away r (P.map (homOfLE hV).op).hom) :
    IsLocalizedModule.Away r (P.map (homOfLE hW).op).hom := by
  subst W
  exact hl

/-- The SAME original affine restriction localizes at the SAME original global
base parameter; actual quasi-coherence supplies the local localization. -/
theorem restriction_isLocalizedModule (U : X.affineOpens) (r : Γ(B, ⊤)) :
    IsLocalizedModule.Away r
      ((Scheme.Modules.baseModulePresheaf π M).map
        (homOfLE (inf_le_left : U.1 ⊓ π ⁻¹ᵁ B.basicOpen r ≤ U.1)).op).hom := by
  let A := Γ(X, U.1)
  let φ : Γ(B, ⊤) →+* A :=
    (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom.comp π.appTop.hom
  let : Algebra Γ(B, ⊤) A := φ.toAlgebra
  let f : A := φ r
  let V := X.basicOpen f
  let : Module A Γ(M, V) := Module.compHom _ (algebraMap A Γ(X, V))
  let : Module Γ(B, ⊤) Γ(M, U.1) :=
    ((Scheme.Modules.baseModulePresheaf π M).obj (op U.1)).isModule
  let : Module Γ(B, ⊤) Γ(M, V) :=
    ((Scheme.Modules.baseModulePresheaf π M).obj (op V)).isModule
  let : IsScalarTower Γ(B, ⊤) A Γ(M, U.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Γ(B, ⊤) A Γ(M, V) := by
    apply IsScalarTower.of_algebraMap_smul
    intro a m
    change (X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op (π.appTop a))) • m = _
    rw [← X.presheaf.map_comp_apply]
    rfl
  let ψ : Γ(M, U.1) →ₗ[A] Γ(M, V) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le f)).op
      map_add' := (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.map_add
      map_smul' := fun a m => M.map_smul (homOfLE (X.basicOpen_le f)) a m }
  let : IsLocalizedModule.Away f ψ :=
    Scheme.Modules.isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen M U f
  have hlocal := IsLocalizedModule.restrictScalars_powers r ψ
  have hopen : V = U.1 ⊓ π ⁻¹ᵁ B.basicOpen r := by
    change X.basicOpen (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op
      (π.appTop r)) = _
    rw [X.basicOpen_res, Scheme.preimage_basicOpen_top]
  have hh : IsLocalizedModule.Away r
      ((Scheme.Modules.baseModulePresheaf π M).map
        (homOfLE (X.basicOpen_le f)).op).hom := hlocal
  exact originalRestrictionLocalizationCongr (Scheme.Modules.baseModulePresheaf π M) r
    hopen (X.basicOpen_le f) inf_le_left hh

end EnvelopeProperty.AffineOpenGlobalParameterLocalization
