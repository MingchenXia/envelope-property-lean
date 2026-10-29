import EnvelopeProperty.AlgGeom.Canonical.ExteriorSheaf

/-!
# All actual exterior sections on genuine free affine charts

The original sheafification unit is an isomorphism on every principal
open. Its bijectivity is derived from the actual localized affine comparison.
-/

open CategoryTheory AlgebraicGeometry Opposite PrimeSpectrum

namespace EnvelopeProperty.CanonicalGeometry

universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K] (A : CommRingCat.{u}) [Algebra K A]

/-- On every actual principal open of a free affine differential chart,
the actual exterior sheafification unit retains ALL sections bijectively. -/
theorem affineExteriorSheafificationMap_bijective {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential K A)) (n : ℕ) (r : A) :
    Function.Bijective ((exteriorSheafificationMap
      (cotangentPresheaf (affineStructuralMap K A)) n).app (.op (basicOpen r))) := by
  let P := exteriorCotangentPresheaf (affineStructuralMap K A) n
  let M := affineExteriorCotangentModule K A n
  let φ := affineExteriorCotangentToOpen K A n
  let hφ : ∀ {U V : (Spec A).Opensᵒᵖ} (i : U ⟶ V),
      φ U ≫ (specPresheafToAModules A P).map i = φ V :=
    fun i ↦ affineExteriorCotangentToOpen_naturality K A n i
  let hloc := affineExteriorCotangentToOpen_isLocalized K A b n
  let E := affineExteriorCotangentSheafIso K A b n
  let F := (affineLocalizedBasisIso A P M φ hφ hloc).app (.op r)
  have hE : Function.Bijective (E.hom.val.app (.op (basicOpen r))) := by
    constructor
    · intro x y hxy
      exact (congr($(E.hom_inv_id).val.app (.op (basicOpen r)) |>.hom x)).symm.trans
        ((congrArg (E.inv.val.app (.op (basicOpen r))) hxy).trans
          (congr($(E.hom_inv_id).val.app (.op (basicOpen r)) |>.hom y)))
    · intro y
      exact ⟨E.inv.val.app (.op (basicOpen r)) y,
        congr($(E.inv_hom_id).val.app (.op (basicOpen r)) |>.hom y)⟩
  have hF : Function.Bijective F.hom := ConcreteCategory.bijective_of_isIso _
  have hunit (x : P.obj (.op (basicOpen r))) :
      E.hom.val.app (.op (basicOpen r))
          ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K A)) n).app
            (.op (basicOpen r)) x) = F.hom x :=
    affineLocalizedSheafificationHom_unit_apply A P M φ hφ hloc r x
  constructor
  · intro x y hxy
    apply hF.injective
    exact (hunit x).symm.trans ((congrArg (E.hom.val.app (.op (basicOpen r))) hxy).trans
      (hunit y))
  · intro y
    obtain ⟨x, hx⟩ := hF.surjective (E.hom.val.app (.op (basicOpen r)) y)
    refine ⟨x, hE.injective ?_⟩
    exact (hunit x).trans hx

/-- The actual unit is bijective on the WHOLE original affine scheme. -/
theorem affineExteriorSheafificationMap_top_bijective {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential K A)) (n : ℕ) :
    Function.Bijective ((exteriorSheafificationMap
      (cotangentPresheaf (affineStructuralMap K A)) n).app (.op ⊤)) := by
  have h := affineExteriorSheafificationMap_bijective K A b n (1 : A)
  have hone : (basicOpen (1 : A) : (Spec A).Opens) = ⊤ := PrimeSpectrum.basicOpen_one
  exact hone ▸ h

/-- The actual principal-open section isomorphism is the original
sheafification unit itself, with its derived genuine inverse. -/
def affineExteriorSheafificationSectionsIso {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential K A)) (n : ℕ) (r : A) :
    (exteriorCotangentPresheaf (affineStructuralMap K A) n).obj (.op (basicOpen r)) ≅
      (exteriorCotangentSheaf (affineStructuralMap K A) n).val.obj
        (.op (basicOpen r)) := by
  let η := (exteriorSheafificationMap
    (cotangentPresheaf (affineStructuralMap K A)) n).app (.op (basicOpen r))
  exact (LinearEquiv.ofBijective η.hom
    (affineExteriorSheafificationMap_bijective K A b n r)).toModuleIso

/-- The whole original affine section isomorphism is the same actual unit,
with its whole original raw and sheaf section modules. -/
def affineExteriorSheafificationTopSectionsIso {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential K A)) (n : ℕ) :
    (exteriorCotangentPresheaf (affineStructuralMap K A) n).obj (.op ⊤) ≅
      (exteriorCotangentSheaf (affineStructuralMap K A) n).val.obj (.op ⊤) := by
  let η := (exteriorSheafificationMap
    (cotangentPresheaf (affineStructuralMap K A)) n).app (.op ⊤)
  exact (LinearEquiv.ofBijective η.hom
    (affineExteriorSheafificationMap_top_bijective K A b n)).toModuleIso

/-- Standard-smoothness itself supplies the differential basis for ALL
original principal-open exterior section comparisons. -/
theorem standardSmoothExteriorSheafificationMap_bijective (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d K A] (n : ℕ) (r : A) :
    Function.Bijective ((exteriorSheafificationMap
      (cotangentPresheaf (affineStructuralMap K A)) n).app (.op (basicOpen r))) :=
  affineExteriorSheafificationMap_bijective K A (standardSmoothDifferentialBasis K A d) n r

end
end EnvelopeProperty.CanonicalGeometry
