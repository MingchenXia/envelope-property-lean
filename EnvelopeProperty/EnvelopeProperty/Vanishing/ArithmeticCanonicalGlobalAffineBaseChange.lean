import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalBaseChange
import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalUnits
import EnvelopeProperty.AffineGlobalSections
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-! # Actual affine section comparison for the global arithmetic differential

The original categorical fibre internally produces the actual coefficient
pushout. The global differential is compared using its original adjunction
unit, rather than assuming a desired affine or global comparison isomorphism.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalAffineBaseChange

open CanonicalGeometry ArithmeticCanonicalGlobal ArithmeticCanonicalGlobalBaseChange

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

local instance [IsAffine X] : IsAffine (fiberScheme S f) := by
  dsimp [fiberScheme, baseMap]
  infer_instance

/-- The actual whole-open constants are the existing original coefficient map. -/
theorem constantsTop : (relativeConstants f).app (.op ⊤) =
    CommRingCat.ofHom (ProperBirationalSections.coefficientMap f) := by
  change (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
      X.presheaf.map (Opens.leTop ⊤).op = (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop
  rw [show (Opens.leTop (⊤ : X.Opens)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _,
    X.presheaf.map_id, Category.comp_id]

/-- The native original fibre derives its actual section-ring pushout;
no flatness or coefficient comparison certificate is supplied. -/
theorem affineCoefficientPushout [IsAffine X] :
    IsPushout ((relativeConstants f).app (.op ⊤))
      (CommRingCat.ofHom (algebraMap R S)) (fiberProjection S f).appTop
      ((relativeConstants (fiberStructure S f)).app (.op ⊤)) := by
  rw [constantsTop, constantsTop]
  exact AffineGlobalSections.originalSectionSquare (S := S) f

/-- Scalar extension of the actual raw exterior differential, using the
original projection's actual whole-open ring map. -/
def rawExteriorBaseChange (q : ℕ) :
    (ModuleCat.extendScalars (fiberProjection S f).appTop.hom).obj
        ((relativeExteriorPresheaf f q).obj (.op ⊤)) ⟶
      (relativeExteriorPresheaf (fiberStructure S f) q).obj (.op ⊤) :=
  ((ModuleCat.extendRestrictScalarsAdj (fiberProjection S f).appTop.hom).homEquiv
    _ _).symm (exteriorComponent S f q (.op ⊤))

theorem rawExteriorBaseChange_one_tmul (q : ℕ)
    (z : (relativeExteriorPresheaf f q).obj (.op ⊤)) :
    rawExteriorBaseChange S f q ((1 : Γ(fiberScheme S f, ⊤)) ⊗ₜ[Γ(X, ⊤)] z) =
      exteriorComponent S f q (.op ⊤) z := by
  have h := congr($(((ModuleCat.extendRestrictScalarsAdj
    (fiberProjection S f).appTop.hom).homEquiv _ _).apply_symm_apply
      (exteriorComponent S f q (.op ⊤))) z)
  exact h

/-- The actual global morphism preserves every raw original form through
the genuine affine pullback comparison and the same sheafification units. -/
theorem affineExteriorPullback_one_tmul [IsAffine X] (q : ℕ)
    [(relativeExteriorSheaf f q).IsQuasicoherent]
    (z : (relativeExteriorPresheaf f q).obj (.op ⊤)) :
    (exteriorPullbackMap S f q).val.app (.op ⊤)
      ((Scheme.Modules.affinePullbackΓIso (fiberProjection S f)
        (relativeExteriorSheaf f q)).hom
        ((1 : Γ(fiberScheme S f, ⊤)) ⊗ₜ[Γ(X, ⊤)]
          (exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op ⊤) z)) =
      (exteriorSheafificationMap (relativeCotangentPresheaf (fiberStructure S f)) q).app
        (.op ⊤) (exteriorComponent S f q (.op ⊤) z) := by
  rw [Scheme.Modules.affinePullbackΓIso_hom_one_tmul]
  have hu : Scheme.Modules.affinePullbackUnitTop (fiberProjection S f)
      (relativeExteriorSheaf f q)
      ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op ⊤) z) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).unit.app
        (relativeExteriorSheaf f q)).val.app (.op ⊤)
          ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op ⊤) z) := by
    change ((Scheme.Modules.pullback (fiberProjection S f)).obj
      (relativeExteriorSheaf f q)).presheaf.map (𝟙 (.op ⊤)) _ = _
    exact congr($(((Scheme.Modules.pullback (fiberProjection S f)).obj
      (relativeExteriorSheaf f q)).presheaf.map_id (.op ⊤)).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction (fiberProjection S f)).unit.app
          (relativeExteriorSheaf f q)).val.app (.op ⊤)
            ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op ⊤) z)))
  rw [hu]
  have h := congr($(exteriorPullbackMap_unit S f q).val.app (.op ⊤) |>.hom
    ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op ⊤) z))
  exact h.trans (congr($(exteriorSheafPushMap_unit S f q).app (.op ⊤) |>.hom z))

/-- Equality of whole actual section morphisms, retaining the original
coefficient extension and both actual units. -/
theorem affineExteriorPullback_unit [IsAffine X] (q : ℕ)
    [(relativeExteriorSheaf f q).IsQuasicoherent] :
    (ModuleCat.extendScalars (fiberProjection S f).appTop.hom).map
        ((exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op ⊤)) ≫
      (Scheme.Modules.affinePullbackΓIso (fiberProjection S f)
        (relativeExteriorSheaf f q)).hom ≫
      (exteriorPullbackMap S f q).val.app (.op ⊤) =
    rawExteriorBaseChange S f q ≫
      (exteriorSheafificationMap (relativeCotangentPresheaf (fiberStructure S f)) q).app
        (.op ⊤) := by
  let : Algebra Γ(X, ⊤) Γ(fiberScheme S f, ⊤) := (fiberProjection S f).appTop.hom.toAlgebra
  apply ((ModuleCat.extendRestrictScalarsAdj (fiberProjection S f).appTop.hom).homEquiv
    _ _).injective
  apply ModuleCat.Hom.ext
  apply LinearMap.ext
  intro z
  change (exteriorPullbackMap S f q).val.app (.op ⊤)
      ((Scheme.Modules.affinePullbackΓIso (fiberProjection S f)
        (relativeExteriorSheaf f q)).hom
        ((1 : Γ(fiberScheme S f, ⊤)) ⊗ₜ[Γ(X, ⊤)]
          (exteriorSheafificationMap (relativeCotangentPresheaf f) q).app (.op ⊤) z)) =
    (exteriorSheafificationMap (relativeCotangentPresheaf (fiberStructure S f)) q).app
      (.op ⊤) (rawExteriorBaseChange S f q ((1 : Γ(fiberScheme S f, ⊤)) ⊗ₜ[Γ(X, ⊤)] z))
  rw [rawExteriorBaseChange_one_tmul]
  exact affineExteriorPullback_one_tmul S f q z

private def exteriorPushoutEquiv (R S A B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A)) (q : ℕ) :
    B ⊗[A] (⋀[A]^q (KaehlerDifferential R A)) ≃ₗ[B]
      (⋀[B]^q (KaehlerDifferential S B)) :=
  (exteriorBasisBaseChangeEquiv b q).trans
    (exteriorLinearEquiv (KaehlerDifferential.tensorKaehlerEquiv R S A B) q)

private theorem exteriorPushoutEquiv_wedge (R S A B : Type u)
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A))
    (q : ℕ) (w : Fin q → KaehlerDifferential R A) :
    exteriorPushoutEquiv R S A B b q (1 ⊗ₜ[A] exteriorPower.ιMulti A q w) =
      exteriorPower.ιMulti B q (fun j => KaehlerDifferential.map R S A B (w j)) := by
  rw [exteriorPushoutEquiv, LinearEquiv.trans_apply,
    exteriorBasisBaseChangeEquiv_wedge, exteriorLinearEquiv_ιMulti]
  congr 1
  funext j
  let F : KaehlerDifferential R A →ₗ[A] KaehlerDifferential S B :=
    ((KaehlerDifferential.tensorKaehlerEquiv R S A B).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A B (KaehlerDifferential R A) 1)
  have hF : F = KaehlerDifferential.map R S A B := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A)
    rintro _ ⟨a, rfl⟩
    change KaehlerDifferential.tensorKaehlerEquiv R S A B
      (1 ⊗ₜ[A] KaehlerDifferential.D R A a) = _
    rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul, KaehlerDifferential.map_D]
  exact LinearMap.congr_fun hF (w j)

/-- The actual raw differential is an isomorphism on every original
standard-smooth affine chart. Its section-ring pushout and differential bases
are derived internally from that chart, without comparison certificates. -/
theorem rawExteriorBaseChange_isIso [IsAffine X] (d : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension d
      ((relativeConstants f).app (.op ⊤)).hom) (q : ℕ) :
    IsIso (rawExteriorBaseChange S f q) := by
  let A := Γ(X, ⊤)
  let B := Γ(fiberScheme S f, ⊤)
  let : Algebra R A := ((relativeConstants f).app (.op ⊤)).hom.toAlgebra
  let : Algebra S B := ((relativeConstants (fiberStructure S f)).app (.op ⊤)).hom.toAlgebra
  let : Algebra A B := (fiberProjection S f).appTop.hom.toAlgebra
  let : Algebra R B := ((fiberProjection S f).appTop.hom.comp
    ((relativeConstants f).app (.op ⊤)).hom).toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (fiberConstantsSquare S f ⊤))
  let : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp (affineCoefficientPushout S f).flip
  let : Algebra.IsStandardSmoothOfRelativeDimension d R A := hs
  let b := standardSmoothDifferentialBasis R A d
  let e : (ModuleCat.extendScalars (fiberProjection S f).appTop.hom).obj
        ((relativeExteriorPresheaf f q).obj (.op ⊤)) ≃ₗ[B]
      (relativeExteriorPresheaf (fiberStructure S f) q).obj (.op ⊤) :=
    exteriorPushoutEquiv R S A B b q
  have hc (w : KaehlerDifferential R A) :
      cotangentSemilinear S f (.op ⊤) w = KaehlerDifferential.map R S A B w := by
    let F : KaehlerDifferential R A →ₗ[A] KaehlerDifferential S B :=
      { toFun := cotangentSemilinear S f (.op ⊤),
        map_add' := (cotangentSemilinear S f (.op ⊤)).map_add,
        map_smul' := (cotangentSemilinear S f (.op ⊤)).map_smulₛₗ }
    have hF : F = KaehlerDifferential.map R S A B := by
      apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A)
      rintro _ ⟨a, rfl⟩
      change (cotangentPresheafMap S f).app (.op ⊤)
          (KaehlerDifferential.D R A a) = _
      rw [KaehlerDifferential.map_D]
      exact cotangentPresheafMap_d S f ⊤ a
    exact LinearMap.congr_fun hF w
  have he : rawExteriorBaseChange S f q = e.toModuleIso.hom := by
    apply ((ModuleCat.extendRestrictScalarsAdj (fiberProjection S f).appTop.hom).homEquiv
      _ _).injective
    apply ModuleCat.Hom.ext
    apply LinearMap.ext_on (exteriorPower.ιMulti_span A q (KaehlerDifferential R A))
    rintro _ ⟨w, rfl⟩
    change rawExteriorBaseChange S f q ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A q w) =
      e ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A q w)
    rw [rawExteriorBaseChange_one_tmul, exteriorComponent_wedge]
    symm
    refine (exteriorPushoutEquiv_wedge R S A B b q w).trans ?_
    exact congrArg (exteriorPower.ιMulti B q) (funext fun j => (hc (w j)).symm)
  rw [he]
  infer_instance

/-- Actual affine base change preserves the original standard-smooth chart
dimension on its own whole section ring. -/
theorem affineFiberStandardSmooth [IsAffine X] (d : ℕ)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension d
      ((relativeConstants f).app (.op ⊤)).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension d
      ((relativeConstants (fiberStructure S f)).app (.op ⊤)).hom := by
  exact (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
    (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange d)).1
      (affineCoefficientPushout S f).flip hs

local instance (n : ℕ) [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (fiberStructure S f) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  dsimp [fiberStructure, baseMap]
  exact MorphismProperty.pullback_snd f _ inferInstance

/-- The actual whole global canonical differential, on an original affine
standard-smooth chart, is an isomorphism on the native categorical fibre.
All coefficient pushouts, raw comparisons and unit bijections are produced
internally from the chart and the original smooth structural morphism. -/
theorem affineCanonicalPullback_isIso [IsAffine X] (n : ℕ)
    [SmoothOfRelativeDimension n f]
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants f).app (.op ⊤)).hom) :
    IsIso (exteriorPullbackMap S f n) := by
  let hX := ArithmeticCanonicalGlobalFrames.canonicalObject_isInvertible f n
  let hY := ArithmeticCanonicalGlobalFrames.canonicalObject_isInvertible (fiberStructure S f) n
  let : (relativeExteriorSheaf f n).IsQuasicoherent := hX.isQuasicoherent
  let : (relativeExteriorSheaf (fiberStructure S f) n).IsQuasicoherent := hY.isQuasicoherent
  let : ((Scheme.Modules.pullback (fiberProjection S f)).obj
    (relativeExteriorSheaf f n)).IsQuasicoherent := (hX.pullback (fiberProjection S f)).isQuasicoherent
  let uX := (exteriorSheafificationMap (relativeCotangentPresheaf f) n).app (.op ⊤)
  let uY := (exteriorSheafificationMap (relativeCotangentPresheaf (fiberStructure S f)) n).app (.op ⊤)
  have huX : Function.Bijective uX :=
    ArithmeticCanonicalGlobalUnits.standardSmoothChartUnit_bijective f (isAffineOpen_top X) n hs n
  have huY : Function.Bijective uY :=
    ArithmeticCanonicalGlobalUnits.standardSmoothChartUnit_bijective (fiberStructure S f)
      (isAffineOpen_top (fiberScheme S f)) n (affineFiberStandardSmooth S f n hs) n
  let : IsIso uX := (ConcreteCategory.isIso_iff_bijective uX).mpr huX
  let : IsIso uY := (ConcreteCategory.isIso_iff_bijective uY).mpr huY
  let : IsIso (rawExteriorBaseChange S f n) := rawExteriorBaseChange_isIso S f n hs n
  let pref := (ModuleCat.extendScalars (fiberProjection S f).appTop.hom).map uX ≫
    (Scheme.Modules.affinePullbackΓIso (fiberProjection S f) (relativeExteriorSheaf f n)).hom
  let : IsIso pref := inferInstance
  have hcomm : pref ≫ (exteriorPullbackMap S f n).val.app (.op ⊤) =
      rawExteriorBaseChange S f n ≫ uY := by
    simpa only [pref, uX, uY, Category.assoc] using affineExteriorPullback_unit S f n
  have hcomp : IsIso (pref ≫ (exteriorPullbackMap S f n).val.app (.op ⊤)) := by
    rw [hcomm]
    infer_instance
  have htop : IsIso ((exteriorPullbackMap S f n).val.app (.op ⊤)) := by
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ pref _ inferInstance hcomp
  exact Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
    (exteriorPullbackMap S f n) htop

/-- The proved original affine comparison to the existing native field
canonical line on the same actual fibre. -/
def affineFieldCanonicalIso (k : Type u) [Field k] [Algebra R k]
    [IsAffine X] (n : ℕ) [SmoothOfRelativeDimension n f]
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants f).app (.op ⊤)).hom) :
    (Scheme.Modules.pullback (fiberProjection k f)).obj
        (ArithmeticCanonicalGlobalFrames.canonicalObject f n) ≅
      canonicalLineSheaf (fiberStructure k f) n :=
  letI := affineCanonicalPullback_isIso k f n hs
  asIso (exteriorPullbackMap k f n) ≪≫
    ArithmeticCanonicalGlobalFrames.canonicalObject_fieldIso (fiberStructure k f) n

section SpecCharts

variable (R) (A : CommRingCat.{u}) [Algebra R A]

/-- A standard-smooth original coordinate algebra yields the same relative
dimension for the actual whole-open structural coefficient map on its spectrum. -/
theorem affineSpecStandardSmooth (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants (affineStructure R A)).app (.op ⊤)).hom := by
  rw [← affineConstantsSquare]
  have hc : affineCoordinateMap A (.op ⊤) = (Scheme.ΓSpecIso A).inv := by
    change (Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.map (Opens.leTop ⊤).op = _
    rw [show (Opens.leTop (⊤ : (Spec A).Opens)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _,
      (Spec A).presheaf.map_id, Category.comp_id]
  rw [hc]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_right_isIso
    (affineBaseRingMap R A) (Scheme.ΓSpecIso A).inv).mpr
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance)

/-- The original standard-smooth coordinate algebra produces actual scheme
smoothness of the same relative dimension, without a geometric certificate. -/
theorem affineSpecSmooth (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    SmoothOfRelativeDimension n (affineStructure R A) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
    (φ := affineBaseRingMap R A)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr inferInstance)

/-- The actual global fibre differential on an original arithmetic spectrum
is an isomorphism, with every hypothesis produced by its standard-smooth algebra. -/
theorem affineSpecCanonicalPullback_isIso (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    IsIso (exteriorPullbackMap S (affineStructure R A) n) := by
  let : SmoothOfRelativeDimension n (affineStructure R A) := affineSpecSmooth R A n
  exact affineCanonicalPullback_isIso S (affineStructure R A) n (affineSpecStandardSmooth R A n)

end SpecCharts

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalAffineBaseChange
