import EnvelopeProperty.AlgGeom.Canonical.AffineExteriorSections
import EnvelopeProperty.AlgGeom.Canonical.ExteriorPullbackSections
import EnvelopeProperty.AlgGeom.Canonical.CanonicalMorphismSections

/-!
# Full actual sheaf differential image on genuine free affine charts

Both coordinate identifications use the SAME actual sheafification units.
The affine pullback comparison and the actual sheaf differential map are retained.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace EnvelopeProperty.CanonicalGeometry

universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem affineExteriorPullback_unit {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [(exteriorCotangentSheaf f n).IsQuasicoherent]
    (z : (exteriorCotangentPresheaf f n).obj (.op ⊤)) :
    (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)
      ((Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom
        ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)]
          (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z)) =
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤)
        (exteriorCotangentMorphismComponent f g n (.op ⊤) z) := by
  rw [Scheme.Modules.affinePullbackΓIso_hom_one_tmul]
  have hu : Scheme.Modules.affinePullbackUnitTop g (exteriorCotangentSheaf f n)
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (exteriorCotangentSheaf f n)).val.app (.op ⊤)
          ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z) := by
    change ((Scheme.Modules.pullback g).obj (exteriorCotangentSheaf f n)).presheaf.map
      (𝟙 (.op ⊤)) _ = _
    exact congr($(((Scheme.Modules.pullback g).obj
      (exteriorCotangentSheaf f n)).presheaf.map_id (.op ⊤)).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (exteriorCotangentSheaf f n)).val.app (.op ⊤)
            ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z)))
  rw [hu]
  have h := congr($(exteriorCotangentSheafPullbackMap_unit f g n).val.app (.op ⊤) |>.hom
    ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z))
  exact h.trans (congr($(exteriorCotangentSheafMorphism_unit f g n).app (.op ⊤) |>.hom z))

/-- The actual scalar-extended raw differential morphism, in the native
module categories of the original WHOLE affine section rings. -/
def exteriorCotangentRawBaseChangeMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ) :
    (ModuleCat.extendScalars g.appTop.hom).obj
        ((exteriorCotangentPresheaf f n).obj (.op ⊤)) ⟶
      (exteriorCotangentPresheaf (g ≫ f) n).obj (.op ⊤) :=
  ModuleCat.ofHom (exteriorCotangentMorphismBaseChange f g ⊤ n)

/-- The intrinsic full source-function image, in the native original raw
section module. The underlying image is the existing ordinary Kaehler image
for the SAME actual structural section algebras and ring map. -/
def exteriorCotangentRawImage {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ) :
    Submodule Γ(Y, ⊤) ((exteriorCotangentPresheaf (g ≫ f) n).obj (.op ⊤)) := by
  letI := cotangentOpenAlgebra f ⊤
  letI := cotangentOpenAlgebra (g ≫ f) (g ⁻¹ᵁ ⊤)
  letI := (schemeMorphismSectionAlgebraHom f g ⊤).toAlgebra
  letI : IsScalarTower k Γ(X, ⊤) Γ(Y, g ⁻¹ᵁ ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      ((schemeMorphismSectionAlgebraHom f g ⊤).commutes a).symm
  exact EnvelopeProperty.Char0.affineCanonicalDifferentialImage
    (k := k) (R := Γ(X, ⊤)) (A := Γ(Y, g ⁻¹ᵁ ⊤)) n

/-- The actual native scalar-extended raw map has the entire intrinsic
all-original-source-functions image, with no supplied image premise. -/
theorem range_exteriorCotangentRawBaseChangeMorphism {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ) :
    LinearMap.range (exteriorCotangentRawBaseChangeMorphism f g n).hom =
      exteriorCotangentRawImage f g n := by
  exact range_exteriorCotangentMorphismBaseChange f g ⊤ n

private theorem affineExteriorPullback_rawBaseChange {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [(exteriorCotangentSheaf f n).IsQuasicoherent] :
    (ModuleCat.extendScalars g.appTop.hom).map
        ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)) ≫
      (Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom ≫
      (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤) =
    exteriorCotangentRawBaseChangeMorphism f g n ≫
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤) := by
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, g ⁻¹ᵁ ⊤) := (g.app ⊤).hom.toAlgebra
  apply ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).injective
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro z
  change (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)
      ((Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom
        ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)]
          (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z)) =
    (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤)
      (exteriorCotangentMorphismBaseChange f g ⊤ n
        ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)] z))
  refine (affineExteriorPullback_unit f g n z).trans ?_
  apply congrArg ((exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤))
  change exteriorCotangentMorphismComponent f g n (.op ⊤) z =
    exteriorCotangentMorphismBaseChange f g ⊤ n ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)] z)
  rw [exteriorCotangentMorphismBaseChange, LinearMap.liftBaseChange_one_tmul]
  rfl

private def affineExteriorUnitIso {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    (h : Function.Bijective
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤))) :
    (exteriorCotangentPresheaf f n).obj (.op ⊤) ≅
      (exteriorCotangentSheaf f n).val.obj (.op ⊤) :=
  (LinearEquiv.ofBijective
    ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)).hom h).toModuleIso

private def affineExteriorSheafDifferential {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [(exteriorCotangentSheaf f n).IsQuasicoherent]
    (hX : Function.Bijective
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)))
    (hY : Function.Bijective
      ((exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤))) :
    (ModuleCat.extendScalars g.appTop.hom).obj
        ((exteriorCotangentPresheaf f n).obj (.op ⊤)) ⟶
      (exteriorCotangentPresheaf (g ≫ f) n).obj (.op ⊤) :=
  ((ModuleCat.extendScalars g.appTop.hom).map (affineExteriorUnitIso f n hX).hom ≫
    (Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom ≫
    (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)) ≫
    (affineExteriorUnitIso (g ≫ f) n hY).inv

set_option backward.isDefEq.respectTransparency true in
private theorem affineExteriorSheafDifferential_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [(exteriorCotangentSheaf f n).IsQuasicoherent]
    (hX : Function.Bijective
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤)))
    (hY : Function.Bijective
      ((exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op ⊤))) :
    affineExteriorSheafDifferential f g n hX hY =
      exteriorCotangentRawBaseChangeMorphism f g n := by
  unfold affineExteriorSheafDifferential
  apply (affineExteriorUnitIso (g ≫ f) n hY).comp_inv_eq.mpr
  exact affineExteriorPullback_rawBaseChange f g n

variable (K : Type u) [Field K] (A B : CommRingCat.{u}) [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B)

/-- The SAME original algebra homomorphism gives the SAME actual structural
commutative square of affine schemes over the field. -/
theorem affineAlgebraMap_structuralSquare :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A =
      affineStructuralMap K B := by
  unfold affineStructuralMap
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  exact φ.commutes a

private theorem affineExteriorQuasicoherent {I : Type v} [LinearOrder I]
    (bA : Module.Basis I A (KaehlerDifferential K A)) (n : ℕ) :
    (exteriorCotangentSheaf (affineStructuralMap K A) n).IsQuasicoherent := by
  exact (Scheme.Modules.isQuasicoherent (Spec A)).prop_of_iso
    (affineExteriorCotangentSheafIso K A bA n).symm inferInstance

private theorem affineTargetExteriorUnitBijective {J : Type w} [LinearOrder J]
    (bB : Module.Basis J B (KaehlerDifferential K B)) (n : ℕ) :
    Function.Bijective ((exteriorSheafificationMap
      (cotangentPresheaf
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ affineStructuralMap K A)) n).app (.op ⊤)) := by
  have h := affineExteriorSheafificationMap_top_bijective K B bB n
  let Q : (Spec B ⟶ Spec (.of K)) → Prop := fun q ↦
    Function.Bijective ((exteriorSheafificationMap (cotangentPresheaf q) n).app (.op ⊤))
  exact Eq.mp (congrArg Q (affineAlgebraMap_structuralSquare K A B φ).symm) h

set_option backward.isDefEq.respectTransparency true in
/-- The ENTIRE actual sheaf-pullback differential morphism on global
sections, through the actual source/target unit and native affine pullback
isomorphisms. Every map in this composite is the actual original map. -/
def affineCanonicalSheafDifferential {I : Type v} {J : Type w}
    [LinearOrder I] [LinearOrder J]
    (bA : Module.Basis I A (KaehlerDifferential K A))
    (bB : Module.Basis J B (KaehlerDifferential K B)) (n : ℕ) :=
  letI : (exteriorCotangentSheaf (affineStructuralMap K A) n).IsQuasicoherent :=
    affineExteriorQuasicoherent K A bA n
  affineExteriorSheafDifferential (affineStructuralMap K A)
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) n
    (affineExteriorSheafificationMap_top_bijective K A bA n)
    (affineTargetExteriorUnitBijective K A B φ bB n)

set_option backward.isDefEq.respectTransparency true in
/-- The ENTIRE actual sheaf-derived map agrees with scalar extension of
the actual raw differential component, using the SAME original ring map. -/
theorem affineCanonicalSheafDifferential_eq_rawBaseChange
    {I : Type v} {J : Type w} [LinearOrder I] [LinearOrder J]
    (bA : Module.Basis I A (KaehlerDifferential K A))
    (bB : Module.Basis J B (KaehlerDifferential K B)) (n : ℕ) :
    affineCanonicalSheafDifferential K A B φ bA bB n =
      exteriorCotangentRawBaseChangeMorphism (affineStructuralMap K A)
        (Spec.map (CommRingCat.ofHom φ.toRingHom)) n := by
  let : (exteriorCotangentSheaf (affineStructuralMap K A) n).IsQuasicoherent :=
    affineExteriorQuasicoherent K A bA n
  exact affineExteriorSheafDifferential_eq (affineStructuralMap K A)
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) n
    (affineExteriorSheafificationMap_top_bijective K A bA n)
    (affineTargetExteriorUnitBijective K A B φ bB n)

/-- The full actual SHEAF-derived differential image is exactly the
intrinsic image generated by ALL original source-function differentials. -/
theorem range_affineCanonicalSheafDifferential
    {I : Type v} {J : Type w} [LinearOrder I] [LinearOrder J]
    (bA : Module.Basis I A (KaehlerDifferential K A))
    (bB : Module.Basis J B (KaehlerDifferential K B)) (n : ℕ) :
    LinearMap.range (affineCanonicalSheafDifferential K A B φ bA bB n).hom =
      exteriorCotangentRawImage (affineStructuralMap K A)
        (Spec.map (CommRingCat.ofHom φ.toRingHom)) n := by
  rw [affineCanonicalSheafDifferential_eq_rawBaseChange]
  exact range_exteriorCotangentRawBaseChangeMorphism _ _ n

set_option backward.isDefEq.respectTransparency true in
/-- The actual original standard-smooth algebras themselves supply both
coordinate cotangent bases for the full original SHEAF differential map. -/
def standardSmoothAffineCanonicalSheafDifferential (dA dB : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension dA K A]
    [Algebra.IsStandardSmoothOfRelativeDimension dB K B] (n : ℕ) :=
  affineCanonicalSheafDifferential K A B φ
    (standardSmoothDifferentialBasis K A dA) (standardSmoothDifferentialBasis K B dB) n

/-- On arbitrary original standard-smooth affine algebras, the full actual
sheaf differential has the original intrinsic image, with no supplied basis,
sheaf-unit compatibility, differential-map or image certificate. -/
theorem range_standardSmoothAffineCanonicalSheafDifferential (dA dB : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension dA K A]
    [Algebra.IsStandardSmoothOfRelativeDimension dB K B] (n : ℕ) :
    LinearMap.range (standardSmoothAffineCanonicalSheafDifferential K A B φ dA dB n).hom =
      exteriorCotangentRawImage (affineStructuralMap K A)
        (Spec.map (CommRingCat.ofHom φ.toRingHom)) n :=
  range_affineCanonicalSheafDifferential K A B φ
    (standardSmoothDifferentialBasis K A dA) (standardSmoothDifferentialBasis K B dB) n

end
end EnvelopeProperty.CanonicalGeometry
