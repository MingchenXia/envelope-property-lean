import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf
import ModularCurves.ForMathlib.AffineModuleBaseChange
import ModularCurves.ForMathlib.PullbackTensorGeneral
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual affine relative-canonical models over arithmetic bases

The relative model uses genuine Kähler modules over arbitrary commutative
rings. Its fibre comparisons use actual tensor-product fibres, never a supplied
differential or canonical-sheaf comparison certificate.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalAffine

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

open CanonicalGeometry

/-- Reconstruct the actual affine tilde-pullback comparison from the native
global-section comparison and the actual quasicoherent adjunction counit. -/
def tildePullbackIso {A C : CommRingCat.{u}} (φ : A ⟶ C) (M : ModuleCat.{u} A) :
    (pullback (Spec.map φ)).obj ((tilde.functor A).obj M) ≅
      (tilde.functor C).obj ((ModuleCat.extendScalars φ.hom).obj M) := by
  let : ((tilde.functor A).obj M).IsQuasicoherent :=
    inferInstanceAs (AlgebraicGeometry.tilde M).IsQuasicoherent
  let N := (pullback (Spec.map φ)).obj ((tilde.functor A).obj M)
  let : N.IsQuasicoherent :=
    isQuasicoherent_pullback_of_isAffine (Spec.map φ) ((tilde.functor A).obj M)
  let : IsIso N.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent N
  exact (asIso N.fromTildeΓ).symm ≪≫
    (tilde.functor C).mapIso
      ((specPullbackΓIso φ ((tilde.functor A).obj M)).symm ≪≫
        (ModuleCat.extendScalars φ.hom).mapIso (tilde.isoTop M).symm)

/-- The categorical extension-of-scalars object is the ordinary tensor module
for the actual algebra map, with its existing algebra structure retained. -/
def extendScalarsAlgebraMapIso (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap A C)).obj M ≅
      ModuleCat.of C (C ⊗[A] M) := by
  let F : Algebra A C → ModuleCat C := fun a =>
    letI := a
    ModuleCat.of C (C ⊗[A] M)
  exact eqToIso (congrArg F (toAlgebra_algebraMap (R := A) (S := C)))

/-- The actual affine relative-cotangent model, over any commutative base. -/
def relativeCotangentModel (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    (Spec (.of A)).Modules :=
  (tilde.functor (.of A)).obj (ModuleCat.of A (KaehlerDifferential R A))

/-- Actual affine base change of the relative cotangent model to the literal
tensor-product fibre. The Kähler comparison is produced by the native pushout. -/
def tensorFiberCotangentIso (R K A : Type u) [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] :
    (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap A (K ⊗[R] A))))).obj (relativeCotangentModel R A) ≅
        relativeCotangentModel K (K ⊗[R] A) := by
  let C := K ⊗[R] A
  exact tildePullbackIso (CommRingCat.ofHom (algebraMap A C))
      (ModuleCat.of A (KaehlerDifferential R A)) ≪≫
    (tilde.functor (.of C)).mapIso
      (extendScalarsAlgebraMapIso A C (ModuleCat.of A (KaehlerDifferential R A)) ≪≫
        (KaehlerDifferential.tensorKaehlerEquiv R K A C).toModuleIso)

/-- Over a field, the arithmetic affine model is the already existing actual
cotangent sheaf, by the native affine coordinate-module comparison. -/
def fieldCotangentIso (k : Type u) [Field k] (A : CommRingCat.{u}) [Algebra k A] :
    relativeCotangentModel k A ≅ cotangentSheaf (affineStructuralMap k A) :=
  ((tilde.functor A).mapIso (affineCotangentModuleIso k A)).symm ≪≫
    (affineCotangentSheafIso k A).symm

/-- The genuine tensor-product fibre recovers the existing native field
cotangent sheaf, without a supplied comparison isomorphism. -/
def tensorFiberFieldCotangentIso (R k A : Type u) [CommRing R] [Field k] [CommRing A]
    [Algebra R k] [Algebra R A] :
    (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap A (k ⊗[R] A))))).obj (relativeCotangentModel R A) ≅
        cotangentSheaf (affineStructuralMap k (.of (k ⊗[R] A))) :=
  tensorFiberCotangentIso R k A ≪≫ fieldCotangentIso k (.of (k ⊗[R] A))

/-- The actual relative exterior model over an arbitrary commutative base. -/
def relativeExteriorModel (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (q : ℕ) : (Spec (.of A)).Modules :=
  (tilde.functor (.of A)).obj (ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A)))

/-- Whole exterior powers of relative forms commute with the actual tensor
fibre when the original differential basis is produced on a smooth chart. -/
def tensorFiberExteriorEquiv (R K A : Type u) [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] {I : Type v} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A)) (q : ℕ) :
    (K ⊗[R] A) ⊗[A] (⋀[A]^q (KaehlerDifferential R A)) ≃ₗ[K ⊗[R] A]
      (⋀[K ⊗[R] A]^q (KaehlerDifferential K (K ⊗[R] A))) :=
  (exteriorBasisBaseChangeEquiv b q).trans
    (exteriorLinearEquiv (KaehlerDifferential.tensorKaehlerEquiv R K A (K ⊗[R] A)) q)

/-- The exterior comparison retains wedges of arbitrary whole original
forms and sends each differential to its actual coefficient-pushout image. -/
theorem tensorFiberExteriorEquiv_wedge (R K A : Type u)
    [CommRing R] [CommRing K] [CommRing A] [Algebra R K] [Algebra R A]
    {I : Type v} [LinearOrder I] (b : Module.Basis I A (KaehlerDifferential R A))
    (q : ℕ) (ω : Fin q → KaehlerDifferential R A) :
    tensorFiberExteriorEquiv R K A b q (1 ⊗ₜ[A] exteriorPower.ιMulti A q ω) =
      exteriorPower.ιMulti (K ⊗[R] A) q
        (fun i => KaehlerDifferential.map R K A (K ⊗[R] A) (ω i)) := by
  rw [tensorFiberExteriorEquiv, LinearEquiv.trans_apply,
    exteriorBasisBaseChangeEquiv_wedge, exteriorLinearEquiv_ιMulti]
  congr 1
  funext i
  let F : KaehlerDifferential R A →ₗ[A] KaehlerDifferential K (K ⊗[R] A) :=
    ((KaehlerDifferential.tensorKaehlerEquiv R K A (K ⊗[R] A)).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A (K ⊗[R] A) (KaehlerDifferential R A) 1)
  have hF : F = KaehlerDifferential.map R K A (K ⊗[R] A) := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A)
    rintro _ ⟨a, rfl⟩
    change KaehlerDifferential.tensorKaehlerEquiv R K A (K ⊗[R] A)
      (1 ⊗ₜ[A] KaehlerDifferential.D R A a) = _
    rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul, KaehlerDifferential.map_D]
  exact LinearMap.congr_fun hF (ω i)

/-- A standard-smooth presentation supplies the actual basis internally;
all exterior model sheaves pull back to the existing field-relative forms. -/
def tensorFiberExteriorIso (R k A : Type u) [CommRing R] [Field k] [CommRing A]
    [Algebra R k] [Algebra R A] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] (q : ℕ) :
    (pullback (Spec.map (CommRingCat.ofHom
      (algebraMap A (k ⊗[R] A))))).obj (relativeExteriorModel R A q) ≅
        exteriorCotangentSheaf (affineStructuralMap k (.of (k ⊗[R] A))) q := by
  let C := k ⊗[R] A
  let b := standardSmoothDifferentialBasis R A n
  let bC := (b.baseChange C).map (KaehlerDifferential.tensorKaehlerEquiv R k A C)
  exact tildePullbackIso (CommRingCat.ofHom (algebraMap A C))
      (ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A))) ≪≫
    (tilde.functor (.of C)).mapIso
      (extendScalarsAlgebraMapIso A C (ModuleCat.of A (⋀[A]^q (KaehlerDifferential R A))) ≪≫
        (tensorFiberExteriorEquiv R k A b q).toModuleIso) ≪≫
    (affineExteriorCotangentSheafIso k (.of C) bC q).symm

section ActualFiber

variable (R k A : Type u) [CommRing R] [Field k] [CommRing A]
    [Algebra R k] [Algebra R A]

/-- The actual categorical fibre of the affine arithmetic family; its first
projection is its field structure and its second projection goes to the model. -/
def fiberScheme : Scheme.{u} :=
  Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R k)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))

def fiberStructure : fiberScheme R k A ⟶ Spec (.of k) :=
  Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R k)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))

def fiberProjection : fiberScheme R k A ⟶ Spec (.of A) :=
  Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R k)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The tensor presentation is derived for the actual categorical fibre. -/
def fiberTensorIso : fiberScheme R k A ≅ Spec (.of (k ⊗[R] A)) :=
  pullbackSpecIso R k A

/-- Pulling the actual relative cotangent model to the actual categorical
fibre gives its native field-relative cotangent sheaf. No comparison is input. -/
def fiberCotangentIso :
    (pullback (fiberProjection R k A)).obj (relativeCotangentModel R A) ≅
      cotangentSheaf (fiberStructure R k A) := by
  let e := fiberTensorIso R k A
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (k ⊗[R] A)))
  let h := affineStructuralMap k (.of (k ⊗[R] A))
  have hj : e.hom ≫ j = fiberProjection R k A := pullbackSpecIso_hom_snd R k A
  have hh : e.hom ≫ h = fiberStructure R k A := pullbackSpecIso_hom_fst' R k A
  exact (pullbackCongr hj.symm).app (relativeCotangentModel R A) ≪≫
    ((pullbackComp e.hom j).app (relativeCotangentModel R A)).symm ≪≫
    (pullback e.hom).mapIso (tensorFiberFieldCotangentIso R k A) ≪≫
    ((restrictFunctorIsoPullback e.hom).app (cotangentSheaf h)).symm ≪≫
    cotangentSheafOpenImmersionIso h e.hom ≪≫
    eqToIso (congrArg cotangentSheaf hh)

/-- The all-degree exterior comparison on the actual categorical fibre.
In degree n this is the relative canonical model comparison on this chart. -/
def fiberExteriorIso (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
    (q : ℕ) :
    (pullback (fiberProjection R k A)).obj (relativeExteriorModel R A q) ≅
      exteriorCotangentSheaf (fiberStructure R k A) q := by
  let e := fiberTensorIso R k A
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (k ⊗[R] A)))
  let h := affineStructuralMap k (.of (k ⊗[R] A))
  have hj : e.hom ≫ j = fiberProjection R k A := pullbackSpecIso_hom_snd R k A
  have hh : e.hom ≫ h = fiberStructure R k A := pullbackSpecIso_hom_fst' R k A
  exact (pullbackCongr hj.symm).app (relativeExteriorModel R A q) ≪≫
    ((pullbackComp e.hom j).app (relativeExteriorModel R A q)).symm ≪≫
    (pullback e.hom).mapIso (tensorFiberExteriorIso R k A n q) ≪≫
    ((restrictFunctorIsoPullback e.hom).app (exteriorCotangentSheaf h q)).symm ≪≫
    exteriorCotangentSheafOpenImmersionIso h e.hom q ≪≫
    eqToIso (congrArg (fun g => exteriorCotangentSheaf g q) hh)

/-- The canonical-twisted actual model module has the correct whole pullback
on the actual fibre. This retains any actual model line as its coefficient. -/
def fiberCanonicalTwistIso (L : (Spec (.of A)).Modules) (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    (pullback (fiberProjection R k A)).obj (L ⊗ relativeExteriorModel R A n) ≅
      (pullback (fiberProjection R k A)).obj L ⊗
        canonicalLineSheaf (fiberStructure R k A) n := by
  let π := fiberProjection R k A
  letI : (pullback π).Monoidal := Scheme.Modules.pullbackMonoidal π
  exact (Functor.Monoidal.μIso (pullback π) L (relativeExteriorModel R A n)).symm ≪≫
    (Iso.refl _ ⊗ᵢ fiberExteriorIso R k A n n)

end ActualFiber

end EnvelopeProperty.Vanishing.ArithmeticCanonicalAffine
