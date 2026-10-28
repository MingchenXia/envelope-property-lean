import EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistNaturality
import EnvelopeProperty.DeligneIllusie.WittTwoEtaleRestrictionCoherence
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistDividedOneForm
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistDivisorLocalization
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationDividedFrobeniusNaturality
import EnvelopeProperty.Cartier.RelativeCartierContinuationNativeAllAlgebraNaturality
import EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistReduction
import EnvelopeProperty.DeligneIllusie.WittTwoGeometricDifferential
import Mathlib.RingTheory.RingHom.Smooth

/-! # Actual copied Witt coefficients for the native restriction construction

Blueprint: `blueprint/src/deligne-illusie-witt-global-descent.tex`,
nodes `thm:di-witt-native-arbitrary-restriction-xi` and
`thm:di-witt-native-arbitrary-restriction-H`. The coefficient reduction and
copied-base formal smoothness feed the same canonical xi/H constructions.
Their arbitrary-etale restriction compares the original lifts with the
internally produced restrictions. Actual section-model and sheaf-chart
exchanges are subsequent source slices of the global construction.

No native-map comparison or chosen-lift naturality is an input.
-/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistRestriction
open Cartier.FrobeniusLiftDifference WittTwoNativeTwist
universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.copyAlgebra copyReductionAlgebra copyReductionModule

@[instance_reducible] private def copyReductionSMul :
    SMul (CoefficientCopy p k) k := (copyReductionModule p k).toSMul
attribute [local instance] copyReductionSMul

/-- The genuine copied Witt coefficient ring has its ordinary prime reduction. -/
def coefficientReduction : Reduction p (CoefficientCopy p k) k where
  map := copyReduction p k
  surjective d := by
    obtain ⟨w, hw⟩ := WittTwo.reduction_surjective p k d
    exact ⟨ULift.up w, hw⟩
  kernel_iff w := by
    change WittTwo.reduction p k w.down = 0 ↔
      ∃ z : CoefficientCopy p k, (p : CoefficientCopy p k) * z = w
    constructor
    · intro hw
      obtain ⟨z, hz⟩ := (WittTwo.exists_mul_prime_iff p k w.down).mpr hw
      refine ⟨ULift.up z, ?_⟩
      apply ULift.ext
      exact (mul_comm _ _).trans hz.symm
    · rintro ⟨z, rfl⟩
      change WittTwo.reduction p k ((p : WittTwo.Ring p k) * z.down) = 0
      rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

omit [CharP k p] [PerfectRing k p] in
/-- Actual smoothness over the original Witt ring gives formal smoothness over its
ordinary coefficient copy, retaining the original action on the target algebra. -/
theorem copyFormallySmooth
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D]
    [Algebra.Smooth (WittTwo.Ring p k) D] :
    Algebra.FormallySmooth (CoefficientCopy p k) D := by
  apply RingHom.formallySmooth_algebraMap.mp
  change ((algebraMap (WittTwo.Ring p k) D).comp
    (ULift.ringEquiv : CoefficientCopy p k ≃+* WittTwo.Ring p k).toRingHom).FormallySmooth
  exact (RingHom.FormallySmooth.of_bijective ULift.ringEquiv.bijective).comp
    (RingHom.formallySmooth_algebraMap.mpr inferInstance)


open AlgebraicGeometry CategoryTheory Cartier
open scoped TensorProduct
attribute [local instance] WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra sourceLeftAlgebra sourceLeftModule nativeCoefficientAlgebra
  Algebra.TensorProduct.rightAlgebra

@[instance_reducible] private def copiedTargetModule
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Module (CoefficientCopy p k) D := (WittTwoRelativeLift.copyAlgebra p k D).toModule
attribute [local instance] copiedTargetModule

@[instance_reducible] private def copiedTargetSMul
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    SMul (CoefficientCopy p k) D := (copiedTargetModule p k D).toSMul
attribute [local instance] copiedTargetSMul

-- Fresh names pin these roles after the generic copied-target instances.
@[instance_reducible] private def ordinaryCoefficientAlgebra :
    Algebra (CoefficientCopy p k) k := copyReductionAlgebra p k
attribute [local instance] ordinaryCoefficientAlgebra

@[instance_reducible] private def ordinaryCoefficientModule :
    Module (CoefficientCopy p k) k := (ordinaryCoefficientAlgebra p k).toModule
attribute [local instance] ordinaryCoefficientModule

@[instance_reducible] private def ordinaryCoefficientSMul :
    SMul (CoefficientCopy p k) k := (ordinaryCoefficientModule p k).toSMul
attribute [local instance] ordinaryCoefficientSMul

@[instance_reducible] private def coefficientSelfAlgebra :
    Algebra (CoefficientCopy p k) (CoefficientCopy p k) :=
  (RingHom.id (CoefficientCopy p k)).toAlgebra
attribute [local instance] coefficientSelfAlgebra

@[instance_reducible] private def coefficientSelfModule :
    Module (CoefficientCopy p k) (CoefficientCopy p k) :=
  (coefficientSelfAlgebra p k).toModule
attribute [local instance] coefficientSelfModule

@[instance_reducible] private def coefficientSelfSMul :
    SMul (CoefficientCopy p k) (CoefficientCopy p k) := (coefficientSelfModule p k).toSMul
attribute [local instance] coefficientSelfSMul

@[instance_reducible] private def genuineSourceModule
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Module (CoefficientCopy p k) (LiftSource p k D) := sourceLeftModule p k D
attribute [local instance] genuineSourceModule

@[instance_reducible] private def sourceLeftSMul
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    SMul (CoefficientCopy p k) (LiftSource p k D) := (sourceLeftModule p k D).toSMul
attribute [local instance] sourceLeftSMul

private instance coefficientSelfTower
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    IsScalarTower (CoefficientCopy p k) (CoefficientCopy p k) D :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
  [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']

@[instance_reducible] private def nativeKAlgebra
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Algebra k (NativeTwist p k D) :=
  (RelativeFrobenius.coefficientMap (algebraMap k (ResidueAlgebra p k D)) p).hom.toAlgebra
attribute [local instance] nativeKAlgebra

@[instance_reducible] private def nativeKModule
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Module k (NativeTwist p k D) := (nativeKAlgebra p k D).toModule
attribute [local instance] nativeKModule

@[instance_reducible] private def nativeKSMul
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    SMul k (NativeTwist p k D) := (nativeKModule p k D).toSMul
attribute [local instance] nativeKSMul

@[instance_reducible] private def coefficientCAlgebra
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Algebra (CoefficientCopy p k) (NativeTwist p k D) :=
  ((RelativeFrobenius.coefficientMap (algebraMap k (ResidueAlgebra p k D)) p).hom.comp
    (algebraMap (CoefficientCopy p k) k)).toAlgebra
attribute [local instance] coefficientCAlgebra

@[instance_reducible] private def coefficientCModule
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Module (CoefficientCopy p k) (NativeTwist p k D) := (coefficientCAlgebra p k D).toModule
attribute [local instance] coefficientCModule

@[instance_reducible] private def coefficientCSMul
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    SMul (CoefficientCopy p k) (NativeTwist p k D) := (coefficientCModule p k D).toSMul
attribute [local instance] coefficientCSMul

private instance coefficientTower
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    IsScalarTower (CoefficientCopy p k) k (NativeTwist p k D) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

@[instance_reducible] private def reductionAlgebra
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Algebra (LiftSource p k D) (NativeTwist p k D) :=
  (sourceReduction p k D).toAlgebra
attribute [local instance] reductionAlgebra

@[instance_reducible] private def reductionModule
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Module (LiftSource p k D) (NativeTwist p k D) := (reductionAlgebra p k D).toModule
attribute [local instance] reductionModule

@[instance_reducible] private def reductionSMul
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    SMul (LiftSource p k D) (NativeTwist p k D) := (reductionModule p k D).toSMul
attribute [local instance] reductionSMul

private instance sourceTower
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    IsScalarTower (CoefficientCopy p k) (LiftSource p k D) (NativeTwist p k D) :=
  IsScalarTower.of_algebraMap_eq fun w => (sourceReduction_coefficient p k D w).symm

@[instance_reducible] private def targetReductionAlgebra
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Algebra D (ResidueAlgebra p k D) := (originalReduction p k D).toAlgebra
attribute [local instance] targetReductionAlgebra

@[instance_reducible] private def targetReductionModule
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Module D (ResidueAlgebra p k D) := (targetReductionAlgebra p k D).toModule
attribute [local instance] targetReductionModule

@[instance_reducible] private def targetReductionSMul
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    SMul D (ResidueAlgebra p k D) := (targetReductionModule p k D).toSMul
attribute [local instance] targetReductionSMul

@[instance_reducible] private def residueCAlgebra
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Algebra (CoefficientCopy p k) (ResidueAlgebra p k D) :=
  ((algebraMap k (ResidueAlgebra p k D)).comp (copyReduction p k)).toAlgebra
attribute [local instance] residueCAlgebra

@[instance_reducible] private def residueCModule
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    Module (CoefficientCopy p k) (ResidueAlgebra p k D) := (residueCAlgebra p k D).toModule
attribute [local instance] residueCModule

@[instance_reducible] private def residueCSMul
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    SMul (CoefficientCopy p k) (ResidueAlgebra p k D) := (residueCModule p k D).toSMul
attribute [local instance] residueCSMul

private instance residueCoefficientTower
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    IsScalarTower (CoefficientCopy p k) k (ResidueAlgebra p k D) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private instance targetTower
    (D : Type u) [CommRing D] [Algebra (WittTwo.Ring p k) D] :
    IsScalarTower (CoefficientCopy p k) D (ResidueAlgebra p k D) := by
  apply IsScalarTower.of_algebraMap_eq
  intro w
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul w.down

private theorem liftSquare (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    (actualFlatReduction p k A).map.comp F.toRingHom =
      (nativeBeta p k A).comp (actualReduction p k A).map := by
  apply RingHom.ext
  intro r
  exact (hF r).trans (RingHom.congr_fun (nativeBeta_sourceReduction p k A) r).symm

private def oneForm (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    KaehlerDifferential k (NativeTwist p k A) →ₗ[NativeTwist p k A]
      SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := ResidueAlgebra p k A) p 1 := by
  let copiedFormalSmooth := copyFormallySmooth p k A
  exact DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap
    p (coefficientReduction p k) (actualReduction p k A) (actualFlatReduction p k A)
    F (liftSquare p k F hF) rfl rfl

private def oneFormValue (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (ω : KaehlerDifferential k (NativeTwist p k A)) :
    ⋀[ResidueAlgebra p k A]^1 (KaehlerDifferential k (ResidueAlgebra p k A)) :=
  oneForm p k F hF ω

private theorem oneForm_D_of_lift (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (r : LiftSource p k A) (η : KaehlerDifferential (CoefficientCopy p k) A)
    (hη : (p : A) • η = KaehlerDifferential.D (CoefficientCopy p k) A (F r)) :
    (exteriorPower.oneEquiv (ResidueAlgebra p k A)
      (KaehlerDifferential k (ResidueAlgebra p k A)))
      (oneFormValue p k F hF
        (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r))) =
    KaehlerDifferential.map (CoefficientCopy p k) k A (ResidueAlgebra p k A) η := by
  let copiedFormalSmooth := copyFormallySmooth p k A
  exact DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap_D_of_lift
    p (coefficientReduction p k) (actualReduction p k A) (actualFlatReduction p k A)
    F (liftSquare p k F hF) rfl rfl r η hη

private theorem canonical_one_apply {K D D' : Type u}
    [CommRing K] [CommRing D] [CommRing D']
    [Algebra K D] [Algebra K D'] [Algebra D D'] [IsScalarTower K D D']
    (η : KaehlerDifferential K D) :
    Char0.canonicalDifferentialLinearMap (k := K) (R := D) (A := D') 1
      ((exteriorPower.oneEquiv D (KaehlerDifferential K D)).symm η) =
    (exteriorPower.oneEquiv D' (KaehlerDifferential K D')).symm
      (KaehlerDifferential.map K K D D' η) := by
  rw [exteriorPower.oneEquiv_symm_apply,
    Char0.canonicalDifferentialLinearMap_wedge, exteriorPower.oneEquiv_symm_apply]

private def zeroForm (F G : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    KaehlerDifferential k (NativeTwist p k A) →ₗ[NativeTwist p k A]
      SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := ResidueAlgebra p k A) p 0 :=
  DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm
    p (coefficientReduction p k) (actualReduction p k A) (actualFlatReduction p k A)
    F G (liftSquare p k F hF) (liftSquare p k G hG) rfl rfl

private def zeroFormValue (F G : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (ω : KaehlerDifferential k (NativeTwist p k A)) :
    ⋀[ResidueAlgebra p k A]^0 (KaehlerDifferential k (ResidueAlgebra p k A)) :=
  zeroForm p k F G hF hG ω

private theorem zeroForm_D_of_lift (F G : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (r : LiftSource p k A) (z : A) (hz : (p : A) * z = F r - G r) :
    zeroFormValue p k F G hF hG
        (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r)) =
      (exteriorPower.zeroEquiv (ResidueAlgebra p k A)
        (KaehlerDifferential k (ResidueAlgebra p k A))).symm (originalReduction p k A z) := by
  change (exteriorPower.zeroEquiv (ResidueAlgebra p k A)
    (KaehlerDifferential k (ResidueAlgebra p k A))).symm
    (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm
      (coefficientReduction p k) (actualReduction p k A) (actualFlatReduction p k A)
      F G (nativeBeta p k A) (liftSquare p k F hF) (liftSquare p k G hG) rfl rfl
      (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r))) = _
  apply congrArg (exteriorPower.zeroEquiv (ResidueAlgebra p k A)
    (KaehlerDifferential k (ResidueAlgebra p k A))).symm
  dsimp only [DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm]
  rw [FrobeniusLiftDifference.cotangentMap_D]
  exact FrobeniusLiftDifference.difference_eq_of_lift
    (actualReduction p k A) (actualFlatReduction p k A) (nativeBeta p k A)
    F.toRingHom G.toRingHom
    (fun r => RingHom.congr_fun (liftSquare p k F hF) r)
    (fun r => RingHom.congr_fun (liftSquare p k G hG) r) r z hz

private theorem canonical_zero_apply {K D D' : Type u}
    [CommRing K] [CommRing D] [CommRing D']
    [Algebra K D] [Algebra K D'] [Algebra D D'] [IsScalarTower K D D'] (z : D) :
    Char0.canonicalDifferentialLinearMap (k := K) (R := D) (A := D') 0
      ((exteriorPower.zeroEquiv D (KaehlerDifferential K D)).symm z) =
    (exteriorPower.zeroEquiv D' (KaehlerDifferential K D')).symm (algebraMap D D' z) := by
  rw [exteriorPower.zeroEquiv_symm_apply, map_smul,
    Char0.canonicalDifferentialLinearMap_wedge, exteriorPower.zeroEquiv_symm_apply,
    ← IsScalarTower.algebraMap_smul D' z]
  apply congrArg (fun ω : ⋀[D']^0 (KaehlerDifferential K D') => algebraMap D D' z • ω)
  exact congrArg (exteriorPower.ιMulti D' 0) (Subsingleton.elim _ _)

variable (β : A →ₐ[WittTwo.Ring p k] A')

private def copyHom : A →ₐ[CoefficientCopy p k] A' :=
  { β.toRingHom with commutes' := fun w => β.commutes w.down }

private theorem cotangentReduction_naturality
    (η : KaehlerDifferential (CoefficientCopy p k) A) :
    letI : Algebra A A' := β.toRingHom.toAlgebra
    letI : IsScalarTower (CoefficientCopy p k) A A' :=
      IsScalarTower.of_algebraMap_eq fun w => ((copyHom p k β).commutes w).symm
    letI : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
      (residueMap p k β).toAlgebra
    letI : IsScalarTower k (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
      IsScalarTower.of_algebraMap_eq fun d => ((residueMap p k β).commutes d).symm
    KaehlerDifferential.map k k (ResidueAlgebra p k A) (ResidueAlgebra p k A')
      (KaehlerDifferential.map (CoefficientCopy p k) k A (ResidueAlgebra p k A) η) =
    KaehlerDifferential.map (CoefficientCopy p k) k A' (ResidueAlgebra p k A')
      (KaehlerDifferential.map (CoefficientCopy p k) (CoefficientCopy p k) A A' η) := by
  let liftingAlgebraβ : Algebra A A' := β.toRingHom.toAlgebra
  let liftingTowerβ : IsScalarTower (CoefficientCopy p k) A A' :=
    IsScalarTower.of_algebraMap_eq fun w => ((copyHom p k β).commutes w).symm
  let residueAlgebraβ : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
    (residueMap p k β).toAlgebra
  let residueTowerβ : IsScalarTower k (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
    IsScalarTower.of_algebraMap_eq fun d => ((residueMap p k β).commutes d).symm
  exact congrFun
    (DeligneIllusieLocalContinuationDividedFrobeniusNaturality.reduction_naturality
      (copyHom p k β) (residueMap p k β)
      (fun x => residueMap_originalReduction p k β x)) η

omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A'] in
private theorem residueTower :
    letI : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
      (residueMap p k β).toAlgebra
    IsScalarTower k (ResidueAlgebra p k A) (ResidueAlgebra p k A') := by
  let residueAlgebraβ : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
    (residueMap p k β).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun d => ((residueMap p k β).commutes d).symm

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A'] in
private theorem nativeMap_eq_twistMap :
    letI : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
      (residueMap p k β).toAlgebra
    letI := residueTower p k β
    nativeMap p k β =
      (RelativeEtaleCartierNaturality.twistMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p).hom := by
  let residueAlgebraβ : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
    (residueMap p k β).toAlgebra
  let residueTowerβ := residueTower p k β
  have h : CommRingCat.ofHom (R := NativeTwist p k A) (S := NativeTwist p k A')
      (nativeMap p k β) =
      RelativeEtaleCartierNaturality.twistMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p := by
    apply CategoryTheory.Limits.pushout.hom_ext
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      exact (nativeMap_coefficient p k β d).trans
        (congrArg (fun q => q.hom d)
          (RelativeEtaleCartierNaturality.twistMap_coefficient
            (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p)).symm
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      exact (nativeMap_source p k β b).trans
        (congrArg (fun q => q.hom b)
          (RelativeEtaleCartierNaturality.twistMap_source
            (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p)).symm
  exact congrArg CommRingCat.Hom.hom h

variable (hβ : β.toRingHom.Etale)
  (F G : WittTwoLiftDifference.Lift p k A)
  (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
    WittTwoRelativeLift.residueFrobenius p k A r)
  (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
    WittTwoRelativeLift.residueFrobenius p k A r)

local notation "F'" => WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
local notation "G'" => WittTwoEtaleRestrictionCoherence.restrictedLift p k β G hG hβ
local notation "hF'" => WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
local notation "hG'" => WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β G hG hβ

/-- Actual arbitrary etale restriction of the SAME canonical H; both target lifts are produced. -/
theorem zeroFormTerm_restrictedLift :
    letI : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
      (residueMap p k β).toAlgebra
    letI := residueTower p k β
    ModuleCat.ofHom
      (X := ModuleCat.of (NativeTwist p k A) (KaehlerDifferential k (NativeTwist p k A)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := ResidueAlgebra p k A) p 0)
      (zeroForm p k F G hF hG) ≫
      RelativeNativeAllAlgebraNaturality.formMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p 0 =
    RelativeEtaleCartierNaturality.cotangentMap
      (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap
          (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (NativeTwist p k A') (KaehlerDifferential k (NativeTwist p k A')))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
            (k := k) (B := ResidueAlgebra p k A') p 0)
          (zeroForm p k F' G' hF' hG')) := by
  let residueAlgebraβ : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
    (residueMap p k β).toAlgebra
  let residueTowerβ := residueTower p k β
  let Fr : WittTwoLiftDifference.Lift p k A' := F'
  let Gr : WittTwoLiftDifference.Lift p k A' := G'
  have hFr : ∀ r, algebraMap A' (ResidueAlgebra p k A') (Fr r) =
      WittTwoRelativeLift.residueFrobenius p k A' r := hF'
  have hGr : ∀ r, algebraMap A' (ResidueAlgebra p k A') (Gr r) =
      WittTwoRelativeLift.residueFrobenius p k A' r := hG'
  let f := ModuleCat.ofHom
      (X := ModuleCat.of (NativeTwist p k A) (KaehlerDifferential k (NativeTwist p k A)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := ResidueAlgebra p k A) p 0)
      (zeroForm p k F G hF hG) ≫
      RelativeNativeAllAlgebraNaturality.formMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p 0
  let g := RelativeEtaleCartierNaturality.cotangentMap
      (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap
          (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (NativeTwist p k A') (KaehlerDifferential k (NativeTwist p k A')))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
            (k := k) (B := ResidueAlgebra p k A') p 0)
          (zeroForm p k Fr Gr hFr hGr))
  change f = g
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation k (NativeTwist p k A))
  rintro _ ⟨t, rfl⟩
  obtain ⟨r, rfl⟩ := sourceReduction_surjective p k A t
  have hz0 : originalReduction p k A (F r-G r) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr ((hF r).trans (hG r).symm)
  obtain ⟨z, hz⟩ := ((actualFlatReduction p k A).kernel_iff (F r-G r)).mp hz0
  have hz' : (p : A') * β z = Fr (liftSourceMap p k β r) - Gr (liftSourceMap p k β r) := by
    have h := congrArg β hz
    rw [map_mul, map_natCast, map_sub] at h
    exact h.trans (congrArg₂ (fun a b : A' => a-b)
      (WittTwoEtaleRestrictionCoherence.restrictedLift_commutes p k β F hF hβ r)
      (WittTwoEtaleRestrictionCoherence.restrictedLift_commutes p k β G hG hβ r))
  have hρ := RelativeEtaleCartierNaturality.cotangentMap_D
    (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p
    (sourceReduction p k A r)
  have ha : sourceReduction p k A' (liftSourceMap p k β r) =
      nativeMap p k β (sourceReduction p k A r) :=
    RingHom.congr_fun (sourceReduction_naturality p k β) r
  rw [nativeMap_eq_twistMap p k β] at ha
  have harg := hρ.trans
    (congrArg (KaehlerDifferential.D k (NativeTwist p k A')) ha.symm)
  change Char0.canonicalDifferentialLinearMap
      (k := k) (R := ResidueAlgebra p k A) (A := ResidueAlgebra p k A') 0
      (zeroFormValue p k F G hF hG
        (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r))) =
    zeroFormValue p k Fr Gr hFr hGr
      (RelativeEtaleCartierNaturality.cotangentMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p
        (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r)))
  rw [zeroForm_D_of_lift p k F G hF hG r z hz, canonical_zero_apply,
    harg, zeroForm_D_of_lift p k Fr Gr hFr hGr (liftSourceMap p k β r) (β z) hz']
  exact congrArg (exteriorPower.zeroEquiv (ResidueAlgebra p k A')
    (KaehlerDifferential k (ResidueAlgebra p k A'))).symm
    (residueMap_originalReduction p k β z)

/-- Actual arbitrary etale restriction of the SAME canonical xi; the target lift is produced. -/
theorem oneFormMap_restrictedLift :
    letI : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
      (residueMap p k β).toAlgebra
    letI := residueTower p k β
    ModuleCat.ofHom
      (X := ModuleCat.of (NativeTwist p k A) (KaehlerDifferential k (NativeTwist p k A)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := ResidueAlgebra p k A) p 1)
      (oneForm p k F hF) ≫
      RelativeNativeAllAlgebraNaturality.formMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p 1 =
    RelativeEtaleCartierNaturality.cotangentMap
      (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap
          (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (NativeTwist p k A') (KaehlerDifferential k (NativeTwist p k A')))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
            (k := k) (B := ResidueAlgebra p k A') p 1)
          (oneForm p k F' hF')) := by
  let residueAlgebraβ : Algebra (ResidueAlgebra p k A) (ResidueAlgebra p k A') :=
    (residueMap p k β).toAlgebra
  let residueTowerβ := residueTower p k β
  let liftingAlgebraβ : Algebra A A' := β.toRingHom.toAlgebra
  let liftingTowerβ : IsScalarTower (CoefficientCopy p k) A A' :=
    IsScalarTower.of_algebraMap_eq fun w => ((copyHom p k β).commutes w).symm
  let copiedFormalSmooth := copyFormallySmooth p k A
  let Fr : WittTwoLiftDifference.Lift p k A' := F'
  have hFr : ∀ r, algebraMap A' (ResidueAlgebra p k A') (Fr r) =
      WittTwoRelativeLift.residueFrobenius p k A' r := hF'
  let f := ModuleCat.ofHom
      (X := ModuleCat.of (NativeTwist p k A) (KaehlerDifferential k (NativeTwist p k A)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
        (k := k) (B := ResidueAlgebra p k A) p 1)
      (oneForm p k F hF) ≫
      RelativeNativeAllAlgebraNaturality.formMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p 1
  let g := RelativeEtaleCartierNaturality.cotangentMap
      (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap
          (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (NativeTwist p k A') (KaehlerDifferential k (NativeTwist p k A')))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule
            (k := k) (B := ResidueAlgebra p k A') p 1)
          (oneForm p k Fr hFr))
  change f = g
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation k (NativeTwist p k A))
  rintro _ ⟨t, rfl⟩
  obtain ⟨r, rfl⟩ := sourceReduction_surjective p k A t
  obtain ⟨η, hη⟩ :=
    DeligneIllusieLocalContinuationTrueTwistDivisorLocalization.exists_native_divisor
      p (coefficientReduction p k) (actualReduction p k A) (actualFlatReduction p k A)
      F (liftSquare p k F hF) rfl rfl r
  let ρA := KaehlerDifferential.map (CoefficientCopy p k) (CoefficientCopy p k) A A'
  have hη' : (p : A') • ρA η =
      KaehlerDifferential.D (CoefficientCopy p k) A' (Fr (liftSourceMap p k β r)) := by
    have h := congrArg ρA hη
    rw [map_smul, KaehlerDifferential.map_D] at h
    calc
      _ = (algebraMap A A' (p : A)) • ρA η := by rw [map_natCast]
      _ = (p : A) • ρA η := IsScalarTower.algebraMap_smul A' (p : A) _
      _ = KaehlerDifferential.D (CoefficientCopy p k) A' (β (F r)) := h
      _ = _ := congrArg (KaehlerDifferential.D (CoefficientCopy p k) A')
        (WittTwoEtaleRestrictionCoherence.restrictedLift_commutes p k β F hF hβ r)
  let e := exteriorPower.oneEquiv (ResidueAlgebra p k A)
    (KaehlerDifferential k (ResidueAlgebra p k A))
  let e' := exteriorPower.oneEquiv (ResidueAlgebra p k A')
    (KaehlerDifferential k (ResidueAlgebra p k A'))
  have hv : oneFormValue p k F hF
        (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r)) =
      e.symm (KaehlerDifferential.map (CoefficientCopy p k) k A (ResidueAlgebra p k A) η) :=
    (e.symm_apply_apply _).symm.trans
      (congrArg e.symm (oneForm_D_of_lift p k F hF r η hη))
  have hρ := RelativeEtaleCartierNaturality.cotangentMap_D
    (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p
    (sourceReduction p k A r)
  have ha : sourceReduction p k A' (liftSourceMap p k β r) =
      nativeMap p k β (sourceReduction p k A r) :=
    RingHom.congr_fun (sourceReduction_naturality p k β) r
  rw [nativeMap_eq_twistMap p k β] at ha
  have harg := hρ.trans
    (congrArg (KaehlerDifferential.D k (NativeTwist p k A')) ha.symm)
  change Char0.canonicalDifferentialLinearMap
      (k := k) (R := ResidueAlgebra p k A) (A := ResidueAlgebra p k A') 1
      (oneFormValue p k F hF
        (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r))) =
    oneFormValue p k Fr hFr
      (RelativeEtaleCartierNaturality.cotangentMap
        (k := k) (A := ResidueAlgebra p k A) (B := ResidueAlgebra p k A') p
        (KaehlerDifferential.D k (NativeTwist p k A) (sourceReduction p k A r)))
  rw [hv, canonical_one_apply, harg]
  apply e'.injective
  rw [LinearEquiv.apply_symm_apply,
    oneForm_D_of_lift p k Fr hFr (liftSourceMap p k β r) (ρA η) hη']
  exact cotangentReduction_naturality p k β η

section NativeSectionTransport

omit [PerfectRing k p] in
private def twistMapOfAlgHom {B D : Type u} [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (e : B →ₐ[k] D) :
    RelativeFrobenius.twist (algebraMap k B) p →+*
      RelativeFrobenius.twist (algebraMap k D) p :=
  (CategoryTheory.Limits.pushout.desc
    (f := CommRingCat.ofHom (frobenius k p))
    (g := CommRingCat.ofHom (algebraMap k B))
    (RelativeFrobenius.coefficientMap (algebraMap k D) p)
    (CommRingCat.ofHom (R := B) (S := D) e.toRingHom ≫
      RelativeFrobenius.sourceMap (algebraMap k D) p)
    (by
      ext d
      change (RelativeFrobenius.coefficientMap (algebraMap k D) p).hom (d ^ p) =
        (RelativeFrobenius.sourceMap (algebraMap k D) p).hom (e (algebraMap k B d))
      rw [e.commutes]
      exact congrArg
        (fun q : CommRingCat.of k ⟶ RelativeFrobenius.twist (algebraMap k D) p => q.hom d)
        (CategoryTheory.Limits.pushout.condition
          (f := CommRingCat.ofHom (frobenius k p))
          (g := CommRingCat.ofHom (algebraMap k D))))).hom

omit [PerfectRing k p] in
private theorem twistMapOfAlgHom_coefficient {B D : Type u} [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (e : B →ₐ[k] D) (d : k) :
    twistMapOfAlgHom p k e ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom d) =
      (RelativeFrobenius.coefficientMap (algebraMap k D) p).hom d := by
  exact congrArg
    (fun q : CommRingCat.of k ⟶ RelativeFrobenius.twist (algebraMap k D) p => q.hom d)
    (CategoryTheory.Limits.pushout.inl_desc
      (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k B))
      (RelativeFrobenius.coefficientMap (algebraMap k D) p)
      (CommRingCat.ofHom (R := B) (S := D) e.toRingHom ≫
        RelativeFrobenius.sourceMap (algebraMap k D) p) _)

omit [PerfectRing k p] in
private theorem twistMapOfAlgHom_source {B D : Type u} [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (e : B →ₐ[k] D) (b : B) :
    twistMapOfAlgHom p k e ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b) =
      (RelativeFrobenius.sourceMap (algebraMap k D) p).hom (e b) := by
  exact congrArg
    (fun q : CommRingCat.of B ⟶ RelativeFrobenius.twist (algebraMap k D) p => q.hom b)
    (CategoryTheory.Limits.pushout.inr_desc
      (f := CommRingCat.ofHom (frobenius k p))
      (g := CommRingCat.ofHom (algebraMap k B))
      (RelativeFrobenius.coefficientMap (algebraMap k D) p)
      (CommRingCat.ofHom (R := B) (S := D) e.toRingHom ≫
        RelativeFrobenius.sourceMap (algebraMap k D) p) _)

omit [PerfectRing k p] in
private theorem twistMapOfAlgEquiv_leftInverse {B D : Type u} [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (e : B ≃ₐ[k] D) :
    Function.LeftInverse (twistMapOfAlgHom p k e.symm.toAlgHom)
      (twistMapOfAlgHom p k e.toAlgHom) := by
  have h : CommRingCat.ofHom
      (R := RelativeFrobenius.twist (algebraMap k B) p)
      (S := RelativeFrobenius.twist (algebraMap k B) p)
      ((twistMapOfAlgHom p k e.symm.toAlgHom).comp (twistMapOfAlgHom p k e.toAlgHom)) =
      𝟙 (RelativeFrobenius.twist (algebraMap k B) p) := by
    apply CategoryTheory.Limits.pushout.hom_ext
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      change twistMapOfAlgHom p k e.symm.toAlgHom
        (twistMapOfAlgHom p k e.toAlgHom
          ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom d)) =
        (RelativeFrobenius.coefficientMap (algebraMap k B) p).hom d
      rw [twistMapOfAlgHom_coefficient, twistMapOfAlgHom_coefficient]
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change twistMapOfAlgHom p k e.symm.toAlgHom
        (twistMapOfAlgHom p k e.toAlgHom
          ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b)) =
        (RelativeFrobenius.sourceMap (algebraMap k B) p).hom b
      rw [twistMapOfAlgHom_source, twistMapOfAlgHom_source]
      exact congrArg (RelativeFrobenius.sourceMap (algebraMap k B) p).hom
        (e.toRingEquiv.symm_apply_apply b)
  intro t
  exact congrArg
    (fun q : RelativeFrobenius.twist (algebraMap k B) p ⟶
      RelativeFrobenius.twist (algebraMap k B) p => q.hom t) h

attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra

omit [PerfectRing k p] in
/-- The actual native relative twists of a coefficient-preserving residue equivalence.
No ordinary-residue untwist or chosen cotangent map enters the construction. -/
def nativeTwistEquiv {B D : Type u} [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (e : B ≃ₐ[k] D) :
    RelativeFrobenius.twist (algebraMap k B) p ≃ₐ[k]
      RelativeFrobenius.twist (algebraMap k D) p where
  toFun := twistMapOfAlgHom p k e.toAlgHom
  invFun := twistMapOfAlgHom p k e.symm.toAlgHom
  left_inv := twistMapOfAlgEquiv_leftInverse p k e
  right_inv := twistMapOfAlgEquiv_leftInverse p k e.symm
  map_mul' := (twistMapOfAlgHom p k e.toAlgHom).map_mul
  map_add' := (twistMapOfAlgHom p k e.toAlgHom).map_add
  commutes' := twistMapOfAlgHom_coefficient p k e.toAlgHom

omit [PerfectRing k p] in
/-- The whole native twist equivalence retains the SAME original source inclusion. -/
theorem nativeTwistEquiv_source {B D : Type u} [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (e : B ≃ₐ[k] D) (b : B) :
    nativeTwistEquiv p k e ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b) =
      (RelativeFrobenius.sourceMap (algebraMap k D) p).hom (e b) :=
  twistMapOfAlgHom_source p k e.toAlgHom b

omit [PerfectRing k p] in
/-- The whole geometric-beta square for the SAME actual native equivalence, including zero rings. -/
theorem nativeTwistEquiv_beta {B D : Type u} [CommRing B] [CommRing D]
    [Algebra k B] [Algebra k D] (e : B ≃ₐ[k] D) :
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom.comp
        (nativeTwistEquiv p k e).toRingHom =
      e.toRingHom.comp (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p).hom := by
  have h : CommRingCat.ofHom
      (R := RelativeFrobenius.twist (algebraMap k B) p) (S := D)
      ((SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom.comp
        (nativeTwistEquiv p k e).toRingHom) =
      CommRingCat.ofHom (R := RelativeFrobenius.twist (algebraMap k B) p) (S := D)
        (e.toRingHom.comp
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p).hom) := by
    apply CategoryTheory.Limits.pushout.hom_ext
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      change (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom
          (nativeTwistEquiv p k e
            ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom d)) =
        e ((SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p).hom
          ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom d))
      have ht : nativeTwistEquiv p k e
          ((RelativeFrobenius.coefficientMap (algebraMap k B) p).hom d) =
          (RelativeFrobenius.coefficientMap (algebraMap k D) p).hom d :=
        twistMapOfAlgHom_coefficient p k e.toAlgHom d
      have hD := congrArg
        (fun q : CommRingCat.of k ⟶ CommRingCat.of D => q.hom d)
        (SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (algebraMap k D) p)
      have hB := congrArg
        (fun q : CommRingCat.of k ⟶ CommRingCat.of B => q.hom d)
        (SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (algebraMap k B) p)
      exact (congrArg (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom ht).trans
        (hD.trans ((e.commutes d).symm.trans (congrArg e hB).symm))
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom
          (nativeTwistEquiv p k e ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b)) =
        e ((SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k B) p).hom
          ((RelativeFrobenius.sourceMap (algebraMap k B) p).hom b))
      have ht := nativeTwistEquiv_source p k e b
      have hD := SchemeRelativeFrobeniusAffineMap.source_ringMap_apply (algebraMap k D) p (e b)
      have hB := SchemeRelativeFrobeniusAffineMap.source_ringMap_apply (algebraMap k B) p b
      exact (congrArg (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom ht).trans
        (hD.trans ((map_pow e b p).symm.trans (congrArg e hB).symm))
  exact congrArg CommRingCat.Hom.hom h

private def transportReduction {R B D : Type u} [CommRing R] [CommRing B] [CommRing D]
    (a : Reduction p R B) (e : B ≃+* D) : Reduction p R D where
  map := e.toRingHom.comp a.map
  surjective := e.surjective.comp a.surjective
  kernel_iff r := by
    change e (a.map r) = 0 ↔ _
    rw [e.map_eq_zero_iff]
    exact a.kernel_iff r

private def transportFlatReduction {S B D : Type u} [CommRing S] [CommRing B] [CommRing D]
    (b : FlatReduction p S B) (e : B ≃+* D) : FlatReduction p S D where
  toReduction := transportReduction p b.toReduction e
  p_sq_zero := b.p_sq_zero
  flat s hs := by
    change e (b.map s) = 0
    rw [b.flat s hs, map_zero]

variable {D : Type u} [CommRing D] [Algebra k D]
  (e : ResidueAlgebra p k A ≃ₐ[k] D)

/-- The actual original source reduction transported to the TRUE native section-ring twist. -/
def sourceReductionAlongEquiv : Reduction p (LiftSource p k A)
    (RelativeFrobenius.twist (algebraMap k D) p) :=
  transportReduction p (actualReduction p k A) (nativeTwistEquiv p k e).toRingEquiv

/-- The actual original flat target reduction transported to the SAME genuine section ring. -/
def flatReductionAlongEquiv : FlatReduction p A D :=
  transportFlatReduction p (actualFlatReduction p k A) e.toRingEquiv

/-- The whole original lift square after the coefficient-preserving true-native model comparison. -/
theorem liftSquareAlongEquiv (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    (flatReductionAlongEquiv p k e).map.comp F.toRingHom =
      (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom.comp
        (sourceReductionAlongEquiv p k e).map := by
  apply RingHom.ext
  intro r
  change e (originalReduction p k A (F r)) =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom
      (nativeTwistEquiv p k e (sourceReduction p k A r))
  exact (congrArg e (RingHom.congr_fun (liftSquare p k F hF) r)).trans
    (RingHom.congr_fun (nativeTwistEquiv_beta p k e) (sourceReduction p k A r)).symm

/-- The genuine copied-base tower on the original model transported to the actual native twist. -/
theorem sourceTowerAlongEquiv :
    letI : Algebra (CoefficientCopy p k) (RelativeFrobenius.twist (algebraMap k D) p) :=
      ((RelativeFrobenius.coefficientMap (algebraMap k D) p).hom.comp
        (copyReduction p k)).toAlgebra
    letI : Algebra (LiftSource p k A) (RelativeFrobenius.twist (algebraMap k D) p) :=
      (sourceReductionAlongEquiv p k e).map.toAlgebra
    IsScalarTower (CoefficientCopy p k) (LiftSource p k A)
      (RelativeFrobenius.twist (algebraMap k D) p) := by
  letI : Algebra (CoefficientCopy p k) (RelativeFrobenius.twist (algebraMap k D) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k D) p).hom.comp
      (copyReduction p k)).toAlgebra
  letI : Algebra (LiftSource p k A) (RelativeFrobenius.twist (algebraMap k D) p) :=
    (sourceReductionAlongEquiv p k e).map.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro w
  change (RelativeFrobenius.coefficientMap (algebraMap k D) p).hom (copyReduction p k w) =
    nativeTwistEquiv p k e (sourceReduction p k A
      (algebraMap (CoefficientCopy p k) (LiftSource p k A) w))
  rw [sourceReduction_coefficient]
  exact (twistMapOfAlgHom_coefficient p k e.toAlgHom (copyReduction p k w)).symm

/-- The SAME zero-safe canonical xi, instantiated on the genuine native section-ring twist model. -/
def oneFormAlongEquiv (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D) p) →ₗ[
      RelativeFrobenius.twist (algebraMap k D) p]
      SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := D) p 1 := by
  letI : Algebra (CoefficientCopy p k) (RelativeFrobenius.twist (algebraMap k D) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k D) p).hom.comp
      (copyReduction p k)).toAlgebra
  letI : Algebra (LiftSource p k A) (RelativeFrobenius.twist (algebraMap k D) p) :=
    (sourceReductionAlongEquiv p k e).map.toAlgebra
  letI := sourceTowerAlongEquiv p k e
  letI := copyFormallySmooth p k A
  exact DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap
    p (coefficientReduction p k) (sourceReductionAlongEquiv p k e)
    (flatReductionAlongEquiv p k e) F (liftSquareAlongEquiv p k e F hF) rfl rfl

private def oneFormAlongEquivValue (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (ω : KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D) p)) :
    ⋀[D]^1 (KaehlerDifferential k D) := oneFormAlongEquiv p k e F hF ω

/-- The SAME canonical zero-form term in the actual coefficient-preserving section-ring model. -/
def zeroFormAlongEquiv (F G : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D) p) →ₗ[
      RelativeFrobenius.twist (algebraMap k D) p]
      SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := D) p 0 := by
  letI : Algebra (CoefficientCopy p k) (RelativeFrobenius.twist (algebraMap k D) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k D) p).hom.comp
      (copyReduction p k)).toAlgebra
  letI : Algebra (LiftSource p k A) (RelativeFrobenius.twist (algebraMap k D) p) :=
    (sourceReductionAlongEquiv p k e).map.toAlgebra
  letI := sourceTowerAlongEquiv p k e
  exact DeligneIllusieLocalContinuationTrueTwistZeroFormTerm.nativeZeroFormTerm
    p (coefficientReduction p k) (sourceReductionAlongEquiv p k e)
    (flatReductionAlongEquiv p k e) F G
    (liftSquareAlongEquiv p k e F hF) (liftSquareAlongEquiv p k e G hG) rfl rfl

private def zeroFormAlongEquivValue (F G : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (ω : KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D) p)) :
    ⋀[D]^0 (KaehlerDifferential k D) := zeroFormAlongEquiv p k e F G hF hG ω

private theorem targetTowerAlongEquiv :
    letI : Algebra (CoefficientCopy p k) D :=
      ((algebraMap k D).comp (copyReduction p k)).toAlgebra
    letI : Algebra A D := (flatReductionAlongEquiv p k e).map.toAlgebra
    IsScalarTower (CoefficientCopy p k) A D := by
  letI : Algebra (CoefficientCopy p k) D :=
    ((algebraMap k D).comp (copyReduction p k)).toAlgebra
  letI : Algebra A D := (flatReductionAlongEquiv p k e).map.toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro w
  change algebraMap k D (copyReduction p k w) =
    e (originalReduction p k A (algebraMap (CoefficientCopy p k) A w))
  have h : originalReduction p k A (algebraMap (CoefficientCopy p k) A w) =
      algebraMap k (ResidueAlgebra p k A) (copyReduction p k w) :=
    (Algebra.TensorProduct.tmul_one_eq_one_tmul w.down).symm
  rw [h]
  exact (e.commutes (copyReduction p k w)).symm

private theorem oneFormAlongEquiv_D_of_lift (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (r : LiftSource p k A) (η : KaehlerDifferential (CoefficientCopy p k) A)
    (hη : (p : A) • η = KaehlerDifferential.D (CoefficientCopy p k) A (F r)) :
    letI : Algebra (CoefficientCopy p k) D :=
      ((algebraMap k D).comp (copyReduction p k)).toAlgebra
    letI : IsScalarTower (CoefficientCopy p k) k D :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : Algebra A D := (flatReductionAlongEquiv p k e).map.toAlgebra
    letI := targetTowerAlongEquiv p k e
    (exteriorPower.oneEquiv D (KaehlerDifferential k D))
      (oneFormAlongEquivValue p k e F hF
        (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
          ((sourceReductionAlongEquiv p k e).map r))) =
      KaehlerDifferential.map (CoefficientCopy p k) k A D η := by
  letI : Algebra (CoefficientCopy p k) D :=
    ((algebraMap k D).comp (copyReduction p k)).toAlgebra
  letI : IsScalarTower (CoefficientCopy p k) k D :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra A D := (flatReductionAlongEquiv p k e).map.toAlgebra
  letI := targetTowerAlongEquiv p k e
  letI : Algebra (CoefficientCopy p k) (RelativeFrobenius.twist (algebraMap k D) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k D) p).hom.comp
      (copyReduction p k)).toAlgebra
  letI : Algebra (LiftSource p k A) (RelativeFrobenius.twist (algebraMap k D) p) :=
    (sourceReductionAlongEquiv p k e).map.toAlgebra
  letI := sourceTowerAlongEquiv p k e
  letI := copyFormallySmooth p k A
  exact DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap_D_of_lift
    p (coefficientReduction p k) (sourceReductionAlongEquiv p k e)
    (flatReductionAlongEquiv p k e) F (liftSquareAlongEquiv p k e F hF) rfl rfl r η hη

private theorem zeroFormAlongEquiv_D_of_lift (F G : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (r : LiftSource p k A) (z : A) (hz : (p : A) * z = F r-G r) :
    zeroFormAlongEquivValue p k e F G hF hG
        (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
          ((sourceReductionAlongEquiv p k e).map r)) =
    (exteriorPower.zeroEquiv D (KaehlerDifferential k D)).symm (e (originalReduction p k A z)) := by
  letI : Algebra (CoefficientCopy p k) (RelativeFrobenius.twist (algebraMap k D) p) :=
    ((RelativeFrobenius.coefficientMap (algebraMap k D) p).hom.comp
      (copyReduction p k)).toAlgebra
  letI : Algebra (LiftSource p k A) (RelativeFrobenius.twist (algebraMap k D) p) :=
    (sourceReductionAlongEquiv p k e).map.toAlgebra
  letI := sourceTowerAlongEquiv p k e
  change (exteriorPower.zeroEquiv D (KaehlerDifferential k D)).symm
    (DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm
      (coefficientReduction p k) (sourceReductionAlongEquiv p k e) (flatReductionAlongEquiv p k e)
      F G (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom
      (liftSquareAlongEquiv p k e F hF) (liftSquareAlongEquiv p k e G hG) rfl rfl
      (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
        ((sourceReductionAlongEquiv p k e).map r))) = _
  apply congrArg (exteriorPower.zeroEquiv D (KaehlerDifferential k D)).symm
  dsimp only [DeligneIllusieLocalContinuationCotangentLocalization.cotangentTerm]
  rw [FrobeniusLiftDifference.cotangentMap_D]
  exact FrobeniusLiftDifference.difference_eq_of_lift
    (sourceReductionAlongEquiv p k e) (flatReductionAlongEquiv p k e)
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap k D) p).hom
    F.toRingHom G.toRingHom
    (fun r => RingHom.congr_fun (liftSquareAlongEquiv p k e F hF) r)
    (fun r => RingHom.congr_fun (liftSquareAlongEquiv p k e G hG) r) r z hz

end NativeSectionTransport

/- This final specialization additionally imports
   EnvelopeProperty.DeligneIllusie.WittTwoGeometricDifferential. -/
section ActualSpecialFibreSections
-- The true chart uses the coefficient inclusion, rather than its source inclusion.
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
variable {Xtilde : Scheme.{u}}
  (f : Xtilde ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
private abbrev specialFibre := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev specialFibreMap : specialFibre p k f ⟶ Spec (CommRingCat.of k) :=
  CategoryTheory.Limits.pullback.fst
    (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f
private abbrev specialOpen (U : Xtilde.Opens) :=
  WittTwoSpecialFibreOpens.residueOpen p k f U

omit [PerfectRing k p] in
/-- The genuine LEFT-Witt native source is transported to the ORIGINAL true chart section twist.
The field action is exactly the existing cotangentOpenAlgebra action. -/
def sectionTwistEquiv {U : Xtilde.Opens} (hU : IsAffineOpen U) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    NativeTwist p k Γ(Xtilde,U) ≃ₐ[k]
      RelativeFrobenius.twist (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p := by
  letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  exact nativeTwistEquiv p k (WittTwoGeometricDifferential.sectionEquiv p k f hU)

omit [PerfectRing k p] in
/-- Every original residue source function has exactly its actual original scheme-section image. -/
theorem sectionTwistEquiv_source {U : Xtilde.Opens} (hU : IsAffineOpen U)
    (b : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
      ResidueAlgebra p k Γ(Xtilde,U)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    sectionTwistEquiv p k f hU (nativeSource p k Γ(Xtilde,U) b) =
      (RelativeFrobenius.sourceMap
        (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p).hom
        (WittTwoSpecialFibreOpens.residueOpenSections p k f hU b) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  exact nativeTwistEquiv_source p k (WittTwoGeometricDifferential.sectionEquiv p k f hU) b

omit [PerfectRing k p] in
/-- Every original copied residue coefficient keeps the TRUE coefficient inclusion on the chart. -/
theorem sectionTwistEquiv_coefficient {U : Xtilde.Opens} (hU : IsAffineOpen U) (d : k) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    sectionTwistEquiv p k f hU (nativeCoefficient p k Γ(Xtilde,U) d) =
      (RelativeFrobenius.coefficientMap
        (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p).hom d := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  exact (sectionTwistEquiv p k f hU).commutes d

end ActualSpecialFibreSections

/- Continuation inside the same namespace, AFTER ActualSpecialFibreSections.
The bridge and the model-transport fragment are not yet kernel evidence.
This fragment proves the actual section-model restriction squares internally. -/
section ActualSectionRestriction
variable {Xtilde : Scheme.{u}}
  (f : Xtilde ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
  {U V : Xtilde.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V)

omit [PerfectRing k p] in
private theorem originalResidueMap_eq (b :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    ResidueAlgebra p k Γ(Xtilde,V)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    residueMap p k (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i) b =
      WittTwoAlgebraDivisionNaturality.residueMap p k
        (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i) b := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  induction b using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add b c hb hc => rw [map_add, map_add, hb, hc]
  | tmul d a =>
    rw [residueMap_tmul, WittTwoAlgebraDivisionNaturality.residueMap_tmul]

omit [PerfectRing k p] in
/-- The ORIGINAL coefficient-preserving native section model commutes with EVERY actual
affine Witt restriction, as a whole ring-map square; no principal-open description is used. -/
theorem sectionTwistEquiv_restrict :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
    letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).toAlgebra
    letI : IsScalarTower k
        Γ(specialFibre p k f,specialOpen p k f V)
        Γ(specialFibre p k f,specialOpen p k f U) :=
      IsScalarTower.of_algebraMap_eq fun d =>
        ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).commutes d).symm
    (sectionTwistEquiv p k f hU).toRingHom.comp
        (nativeMap p k (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i)) =
      (RelativeEtaleCartierNaturality.twistMap
        (k := k) (A := Γ(specialFibre p k f,specialOpen p k f V))
        (B := Γ(specialFibre p k f,specialOpen p k f U)) p).hom.comp
        (sectionTwistEquiv p k f hV).toRingHom := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).toAlgebra
  let : IsScalarTower k
      Γ(specialFibre p k f,specialOpen p k f V)
      Γ(specialFibre p k f,specialOpen p k f U) :=
    IsScalarTower.of_algebraMap_eq fun d =>
      ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).commutes d).symm
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  let τ := RelativeEtaleCartierNaturality.twistMap
    (k := k) (A := Γ(specialFibre p k f,specialOpen p k f V))
    (B := Γ(specialFibre p k f,specialOpen p k f U)) p
  have h : CommRingCat.ofHom (R := NativeTwist p k Γ(Xtilde,V))
      (S := RelativeFrobenius.twist
        (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p)
      ((sectionTwistEquiv p k f hU).toRingHom.comp (nativeMap p k β)) =
      CommRingCat.ofHom (R := NativeTwist p k Γ(Xtilde,V))
        (S := RelativeFrobenius.twist
          (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p)
        (τ.hom.comp (sectionTwistEquiv p k f hV).toRingHom) := by
    apply CategoryTheory.Limits.pushout.hom_ext
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro d
      change sectionTwistEquiv p k f hU (nativeMap p k β (nativeCoefficient p k Γ(Xtilde,V) d)) =
        τ.hom (sectionTwistEquiv p k f hV (nativeCoefficient p k Γ(Xtilde,V) d))
      have hτ := congrArg
        (fun q : CommRingCat.of k ⟶ RelativeFrobenius.twist
          (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p => q.hom d)
        (RelativeEtaleCartierNaturality.twistMap_coefficient
          (k := k) (A := Γ(specialFibre p k f,specialOpen p k f V))
          (B := Γ(specialFibre p k f,specialOpen p k f U)) p)
      exact (congrArg (sectionTwistEquiv p k f hU) (nativeMap_coefficient p k β d)).trans
        ((sectionTwistEquiv_coefficient p k f hU d).trans
          (hτ.symm.trans (congrArg τ.hom (sectionTwistEquiv_coefficient p k f hV d).symm)))
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change sectionTwistEquiv p k f hU (nativeMap p k β (nativeSource p k Γ(Xtilde,V) b)) =
        τ.hom (sectionTwistEquiv p k f hV (nativeSource p k Γ(Xtilde,V) b))
      have hr := (congrArg (WittTwoSpecialFibreOpens.residueOpenSections p k f hU)
          (originalResidueMap_eq p k f i b)).trans
        (WittTwoSpecialFibreReduction.residueOpenSections_restrict p k f hU hV i b)
      have hτ := congrArg
        (fun q : CommRingCat.of Γ(specialFibre p k f,specialOpen p k f V) ⟶
          RelativeFrobenius.twist
            (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p =>
          q.hom (WittTwoSpecialFibreOpens.residueOpenSections p k f hV b))
        (RelativeEtaleCartierNaturality.twistMap_source
          (k := k) (A := Γ(specialFibre p k f,specialOpen p k f V))
          (B := Γ(specialFibre p k f,specialOpen p k f U)) p)
      exact (congrArg (sectionTwistEquiv p k f hU) (nativeMap_source p k β b)).trans
        ((sectionTwistEquiv_source p k f hU (residueMap p k β b)).trans
          ((congrArg
            (RelativeFrobenius.sourceMap
              (algebraMap k Γ(specialFibre p k f,specialOpen p k f U)) p).hom hr).trans
            (hτ.symm.trans (congrArg τ.hom (sectionTwistEquiv_source p k f hV b).symm))))
  exact congrArg CommRingCat.Hom.hom h

/-- The actual source-reduction model, transported to genuine geometric section rings,
preserves the ENTIRE restriction square with no model-comparison hypothesis. -/
theorem sectionSourceReduction_restrict [Smooth f] :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
    letI := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).toAlgebra
    letI : IsScalarTower k
        Γ(specialFibre p k f,specialOpen p k f V)
        Γ(specialFibre p k f,specialOpen p k f U) :=
      IsScalarTower.of_algebraMap_eq fun d =>
        ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).commutes d).symm
    (sourceReductionAlongEquiv p k (WittTwoGeometricDifferential.sectionEquiv p k f hU)).map.comp
        (liftSourceMap p k (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i)).toRingHom =
      (RelativeEtaleCartierNaturality.twistMap
        (k := k) (A := Γ(specialFibre p k f,specialOpen p k f V))
        (B := Γ(specialFibre p k f,specialOpen p k f U)) p).hom.comp
        (sourceReductionAlongEquiv p k (WittTwoGeometricDifferential.sectionEquiv p k f hV)).map := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hV
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
  let := (EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).toAlgebra
  let : IsScalarTower k
      Γ(specialFibre p k f,specialOpen p k f V)
      Γ(specialFibre p k f,specialOpen p k f U) :=
    IsScalarTower.of_algebraMap_eq fun d =>
      ((EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r).commutes d).symm
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  apply RingHom.ext
  intro t
  change sectionTwistEquiv p k f hU (sourceReduction p k Γ(Xtilde,U) (liftSourceMap p k β t)) =
    (RelativeEtaleCartierNaturality.twistMap
      (k := k) (A := Γ(specialFibre p k f,specialOpen p k f V))
      (B := Γ(specialFibre p k f,specialOpen p k f U)) p).hom
      (sectionTwistEquiv p k f hV (sourceReduction p k Γ(Xtilde,V) t))
  have hsource : sourceReduction p k Γ(Xtilde,U) (liftSourceMap p k β t) =
      nativeMap p k β (sourceReduction p k Γ(Xtilde,V) t) :=
    RingHom.congr_fun (sourceReduction_naturality p k β) t
  exact (congrArg (sectionTwistEquiv p k f hU) hsource).trans
    (RingHom.congr_fun (sectionTwistEquiv_restrict p k f hU hV i)
      (sourceReduction p k Γ(Xtilde,V) t))

end ActualSectionRestriction

/- Continuation inside the same namespace, after the section-model restriction fragment.
The auxiliary accepts honest R/S reduction diagrams only. Public actual-scheme
specializations below derive those diagrams from the original geometric restrictions.
No statement here is accepted kernel evidence until parent serial replay. -/
section RestrictedGeometricModels
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
variable {D D' : Type u} [CommRing D] [CommRing D'] [Algebra k D] [Algebra k D']
  (e : ResidueAlgebra p k A ≃ₐ[k] D) (e' : ResidueAlgebra p k A' ≃ₐ[k] D')
  (ψ : D →ₐ[k] D')

private theorem modelZeroForm_restrictedLift
    (β : A →ₐ[WittTwo.Ring p k] A') (hβ : β.toRingHom.Etale)
    (F G : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r)
    (hG : ∀ r, algebraMap A (ResidueAlgebra p k A) (G r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    letI : Algebra D D' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower k D D' :=
      IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
    (∀ r, (sourceReductionAlongEquiv p k e').map (liftSourceMap p k β r) =
      (RelativeEtaleCartierNaturality.twistMap (k := k) (A := D) (B := D') p).hom
        ((sourceReductionAlongEquiv p k e).map r)) →
    (∀ s, e' (originalReduction p k A' (β s)) = ψ (e (originalReduction p k A s))) →
    ModuleCat.ofHom
      (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k D) p)
        (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D) p)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := D) p 0)
      (zeroFormAlongEquiv p k e F G hF hG) ≫
        RelativeNativeAllAlgebraNaturality.formMap (k := k) (A := D) (B := D') p 0 =
    RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := D) (B := D') p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap (k := k) (A := D) (B := D') p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k D') p)
            (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D') p)))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := D') p 0)
          (zeroFormAlongEquiv p k e'
            (WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ)
            (WittTwoEtaleRestrictionCoherence.restrictedLift p k β G hG hβ)
            (WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ)
            (WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β G hG hβ))) := by
  let : Algebra D D' := ψ.toRingHom.toAlgebra
  let : IsScalarTower k D D' :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  intro ha hb
  let Fr : WittTwoLiftDifference.Lift p k A' :=
    WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
  let Gr : WittTwoLiftDifference.Lift p k A' :=
    WittTwoEtaleRestrictionCoherence.restrictedLift p k β G hG hβ
  have hFr : ∀ r, algebraMap A' (ResidueAlgebra p k A') (Fr r) =
      WittTwoRelativeLift.residueFrobenius p k A' r :=
    WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
  have hGr : ∀ r, algebraMap A' (ResidueAlgebra p k A') (Gr r) =
      WittTwoRelativeLift.residueFrobenius p k A' r :=
    WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β G hG hβ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on
    (KaehlerDifferential.span_range_derivation k (RelativeFrobenius.twist (algebraMap k D) p))
  rintro _ ⟨t,rfl⟩
  obtain ⟨r,rfl⟩ := (sourceReductionAlongEquiv p k e).surjective t
  have hz0 : originalReduction p k A (F r-G r) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr ((hF r).trans (hG r).symm)
  obtain ⟨z,hz⟩ := ((actualFlatReduction p k A).kernel_iff (F r-G r)).mp hz0
  have hz' : (p : A') * β z = Fr (liftSourceMap p k β r)-Gr (liftSourceMap p k β r) := by
    have h := congrArg β hz
    rw [map_mul, map_natCast, map_sub] at h
    exact h.trans (congrArg₂ (fun x y : A' => x-y)
      (WittTwoEtaleRestrictionCoherence.restrictedLift_commutes p k β F hF hβ r)
      (WittTwoEtaleRestrictionCoherence.restrictedLift_commutes p k β G hG hβ r))
  have harg := (RelativeEtaleCartierNaturality.cotangentMap_D
      (k := k) (A := D) (B := D') p ((sourceReductionAlongEquiv p k e).map r)).trans
    (congrArg (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D') p))
      (ha r).symm)
  change Char0.canonicalDifferentialLinearMap (k := k) (R := D) (A := D') 0
      (zeroFormAlongEquivValue p k e F G hF hG
        (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
          ((sourceReductionAlongEquiv p k e).map r))) =
    zeroFormAlongEquivValue p k e' Fr Gr hFr hGr
      (RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := D) (B := D') p
        (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
          ((sourceReductionAlongEquiv p k e).map r)))
  rw [zeroFormAlongEquiv_D_of_lift p k e F G hF hG r z hz,
    canonical_zero_apply, harg,
    zeroFormAlongEquiv_D_of_lift p k e' Fr Gr hFr hGr (liftSourceMap p k β r) (β z) hz']
  exact congrArg (exteriorPower.zeroEquiv D' (KaehlerDifferential k D')).symm (hb z).symm

private theorem modelCotangentReduction_naturality
    (β : A →ₐ[WittTwo.Ring p k] A')
    (hb : ∀ s, e' (originalReduction p k A' (β s)) = ψ (e (originalReduction p k A s)))
    (η : KaehlerDifferential (CoefficientCopy p k) A) :
    letI : Algebra D D' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower k D D' :=
      IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
    letI : Algebra (CoefficientCopy p k) D := ((algebraMap k D).comp (copyReduction p k)).toAlgebra
    letI : Algebra (CoefficientCopy p k) D' := ((algebraMap k D').comp (copyReduction p k)).toAlgebra
    letI : IsScalarTower (CoefficientCopy p k) k D := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower (CoefficientCopy p k) k D' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : Algebra A D := (flatReductionAlongEquiv p k e).map.toAlgebra
    letI : Algebra A' D' := (flatReductionAlongEquiv p k e').map.toAlgebra
    letI := targetTowerAlongEquiv p k e
    letI := targetTowerAlongEquiv p k e'
    letI : Algebra A A' := β.toRingHom.toAlgebra
    letI : IsScalarTower (CoefficientCopy p k) A A' :=
      IsScalarTower.of_algebraMap_eq fun w => ((copyHom p k β).commutes w).symm
    KaehlerDifferential.map k k D D'
        (KaehlerDifferential.map (CoefficientCopy p k) k A D η) =
      KaehlerDifferential.map (CoefficientCopy p k) k A' D'
        (KaehlerDifferential.map (CoefficientCopy p k) (CoefficientCopy p k) A A' η) := by
  let : Algebra D D' := ψ.toRingHom.toAlgebra
  let : IsScalarTower k D D' :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  let : Algebra (CoefficientCopy p k) D := ((algebraMap k D).comp (copyReduction p k)).toAlgebra
  let : Algebra (CoefficientCopy p k) D' := ((algebraMap k D').comp (copyReduction p k)).toAlgebra
  let : IsScalarTower (CoefficientCopy p k) k D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (CoefficientCopy p k) k D' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra A D := (flatReductionAlongEquiv p k e).map.toAlgebra
  let : Algebra A' D' := (flatReductionAlongEquiv p k e').map.toAlgebra
  let := targetTowerAlongEquiv p k e
  let := targetTowerAlongEquiv p k e'
  let : Algebra A A' := β.toRingHom.toAlgebra
  let : IsScalarTower (CoefficientCopy p k) A A' :=
    IsScalarTower.of_algebraMap_eq fun w => ((copyHom p k β).commutes w).symm
  exact congrFun
    (DeligneIllusieLocalContinuationDividedFrobeniusNaturality.reduction_naturality
      (copyHom p k β) ψ (fun s => (hb s).symm)) η

private theorem modelOneForm_restrictedLift
    (β : A →ₐ[WittTwo.Ring p k] A') (hβ : β.toRingHom.Etale)
    (F : WittTwoLiftDifference.Lift p k A)
    (hF : ∀ r, algebraMap A (ResidueAlgebra p k A) (F r) =
      WittTwoRelativeLift.residueFrobenius p k A r) :
    letI : Algebra D D' := ψ.toRingHom.toAlgebra
    letI : IsScalarTower k D D' :=
      IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
    (∀ r, (sourceReductionAlongEquiv p k e').map (liftSourceMap p k β r) =
      (RelativeEtaleCartierNaturality.twistMap (k := k) (A := D) (B := D') p).hom
        ((sourceReductionAlongEquiv p k e).map r)) →
    (∀ s, e' (originalReduction p k A' (β s)) = ψ (e (originalReduction p k A s))) →
    ModuleCat.ofHom
      (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k D) p)
        (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D) p)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := D) p 1)
      (oneFormAlongEquiv p k e F hF) ≫
        RelativeNativeAllAlgebraNaturality.formMap (k := k) (A := D) (B := D') p 1 =
    RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := D) (B := D') p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap (k := k) (A := D) (B := D') p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k D') p)
            (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k D') p)))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := D') p 1)
          (oneFormAlongEquiv p k e'
            (WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ)
            (WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ))) := by
  let : Algebra D D' := ψ.toRingHom.toAlgebra
  let : IsScalarTower k D D' :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  intro ha hb
  let : Algebra A A' := β.toRingHom.toAlgebra
  let : IsScalarTower (CoefficientCopy p k) A A' :=
    IsScalarTower.of_algebraMap_eq fun w => ((copyHom p k β).commutes w).symm
  let : Algebra (CoefficientCopy p k) D := ((algebraMap k D).comp (copyReduction p k)).toAlgebra
  let : Algebra (CoefficientCopy p k) D' := ((algebraMap k D').comp (copyReduction p k)).toAlgebra
  let : IsScalarTower (CoefficientCopy p k) k D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (CoefficientCopy p k) k D' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra A D := (flatReductionAlongEquiv p k e).map.toAlgebra
  let : Algebra A' D' := (flatReductionAlongEquiv p k e').map.toAlgebra
  let := targetTowerAlongEquiv p k e
  let := targetTowerAlongEquiv p k e'
  let := copyFormallySmooth p k A
  let Fr : WittTwoLiftDifference.Lift p k A' :=
    WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
  have hFr : ∀ r, algebraMap A' (ResidueAlgebra p k A') (Fr r) =
      WittTwoRelativeLift.residueFrobenius p k A' r :=
    WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_on
    (KaehlerDifferential.span_range_derivation k (RelativeFrobenius.twist (algebraMap k D) p))
  rintro _ ⟨t,rfl⟩
  obtain ⟨r,rfl⟩ := (sourceReductionAlongEquiv p k e).surjective t
  obtain ⟨η,hη⟩ :=
    DeligneIllusieLocalContinuationTrueTwistDivisorLocalization.exists_native_divisor
      p (coefficientReduction p k) (actualReduction p k A) (actualFlatReduction p k A)
      F (liftSquare p k F hF) rfl rfl r
  let ρA := KaehlerDifferential.map (CoefficientCopy p k) (CoefficientCopy p k) A A'
  have hη' : (p : A') • ρA η =
      KaehlerDifferential.D (CoefficientCopy p k) A' (Fr (liftSourceMap p k β r)) := by
    have h := congrArg ρA hη
    rw [map_smul, KaehlerDifferential.map_D] at h
    calc
      _ = (algebraMap A A' (p : A)) • ρA η := by rw [map_natCast]
      _ = (p : A) • ρA η := IsScalarTower.algebraMap_smul A' (p : A) _
      _ = KaehlerDifferential.D (CoefficientCopy p k) A' (β (F r)) := h
      _ = _ := congrArg (KaehlerDifferential.D (CoefficientCopy p k) A')
        (WittTwoEtaleRestrictionCoherence.restrictedLift_commutes p k β F hF hβ r)
  let E := exteriorPower.oneEquiv D (KaehlerDifferential k D)
  let E' := exteriorPower.oneEquiv D' (KaehlerDifferential k D')
  have hv : oneFormAlongEquivValue p k e F hF
        (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
          ((sourceReductionAlongEquiv p k e).map r)) =
      E.symm (KaehlerDifferential.map (CoefficientCopy p k) k A D η) :=
    (E.symm_apply_apply _).symm.trans
      (congrArg E.symm (oneFormAlongEquiv_D_of_lift p k e F hF r η hη))
  have harg := (RelativeEtaleCartierNaturality.cotangentMap_D
      (k := k) (A := D) (B := D') p ((sourceReductionAlongEquiv p k e).map r)).trans
    (congrArg (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D') p))
      (ha r).symm)
  change Char0.canonicalDifferentialLinearMap (k := k) (R := D) (A := D') 1
      (oneFormAlongEquivValue p k e F hF
        (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
          ((sourceReductionAlongEquiv p k e).map r))) =
    oneFormAlongEquivValue p k e' Fr hFr
      (RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := D) (B := D') p
        (KaehlerDifferential.D k (RelativeFrobenius.twist (algebraMap k D) p)
          ((sourceReductionAlongEquiv p k e).map r)))
  rw [hv, canonical_one_apply, harg]
  apply E'.injective
  rw [LinearEquiv.apply_symm_apply,
    oneFormAlongEquiv_D_of_lift p k e' Fr hFr (liftSourceMap p k β r) (ρA η) hη']
  exact modelCotangentReduction_naturality p k e e' ψ β hb η

end RestrictedGeometricModels

section ActualGeometricZeroRestriction
attribute [local instance] RelativeEtaleCartierDomain.coefficientAlgebra
variable {Xtilde : Scheme.{u}}
  (f : Xtilde ⟶ Spec (CommRingCat.of (WittTwo.Ring p k))) [Smooth f]
  {U V : Xtilde.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V)

omit [PerfectRing k p] in
private theorem sectionFlatReduction_restrict (s : Γ(Xtilde,V)) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    WittTwoGeometricDifferential.sectionEquiv p k f hU
        (originalReduction p k Γ(Xtilde,U)
          (WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i s)) =
      (EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f)
          (WittTwoSpecialFibreReduction.residueInclusion p k f i))
        (WittTwoGeometricDifferential.sectionEquiv p k f hV
          (originalReduction p k Γ(Xtilde,V) s)) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hV
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  have hr := WittTwoSpecialFibreReduction.residueOpenSections_restrict p k f hU hV i
    (originalReduction p k Γ(Xtilde,V) s)
  rw [← originalResidueMap_eq p k f i, residueMap_originalReduction] at hr
  exact hr

/-- Actual arbitrary-affine restriction of the SAME zero-safe canonical H in the TRUE
geometric section model. Both restricted lifts and every model diagram are produced internally. -/
theorem sectionZeroFormTerm_restrictedLift
    (F G : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
      WittTwoLiftDifference.Lift p k Γ(Xtilde,V))
    (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
      ∀ r, algebraMap Γ(Xtilde,V) (ResidueAlgebra p k Γ(Xtilde,V)) (F r) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,V) r)
    (hG : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
      ∀ r, algebraMap Γ(Xtilde,V) (ResidueAlgebra p k Γ(Xtilde,V)) (G r) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,V) r) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
    let ψ := EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r
    letI := ψ.toAlgebra
    letI : IsScalarTower k
        Γ(specialFibre p k f,specialOpen p k f V)
        Γ(specialFibre p k f,specialOpen p k f U) :=
      IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
    let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
    let hβ : β.toRingHom.Etale := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
    let Fr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
    let Gr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β G hG hβ
    let hFr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
    let hGr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β G hG hβ
    let eV := WittTwoGeometricDifferential.sectionEquiv p k f hV
    let eU := WittTwoGeometricDifferential.sectionEquiv p k f hU
    let DV := Γ(specialFibre p k f,specialOpen p k f V)
    let DU := Γ(specialFibre p k f,specialOpen p k f U)
    ModuleCat.ofHom
      (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k DV) p)
        (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k DV) p)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := DV) p 0)
      (zeroFormAlongEquiv p k eV F G hF hG) ≫
        RelativeNativeAllAlgebraNaturality.formMap (k := k) (A := DV) (B := DU) p 0 =
    RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := DV) (B := DU) p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap (k := k) (A := DV) (B := DU) p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k DU) p)
            (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k DU) p)))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := DU) p 0)
          (zeroFormAlongEquiv p k eU Fr Gr hFr hGr)) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hV
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
  let ψ := EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r
  let := ψ.toAlgebra
  let : IsScalarTower k
      Γ(specialFibre p k f,specialOpen p k f V)
      Γ(specialFibre p k f,specialOpen p k f U) :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  have hβ : β.toRingHom.Etale := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
  apply modelZeroForm_restrictedLift p k
    (WittTwoGeometricDifferential.sectionEquiv p k f hV)
    (WittTwoGeometricDifferential.sectionEquiv p k f hU) ψ β hβ F G hF hG
  · intro t
    exact RingHom.congr_fun (sectionSourceReduction_restrict p k f hU hV i) t
  · intro s
    exact sectionFlatReduction_restrict p k f hU hV i s

/-- Actual arbitrary-affine restriction of the SAME zero-safe canonical xi in the TRUE
geometric section model. The target lift and both entire model diagrams are derived internally. -/
theorem sectionOneFormMap_restrictedLift
    (F : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
      WittTwoLiftDifference.Lift p k Γ(Xtilde,V))
    (hF : letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
      ∀ r, algebraMap Γ(Xtilde,V) (ResidueAlgebra p k Γ(Xtilde,V)) (F r) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Xtilde,V) r) :
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
    letI := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hV
    letI := WittTwoSchemeAffineRestrictions.affine_smooth f hU
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
    letI := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
    let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
    let ψ := EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r
    letI := ψ.toAlgebra
    letI : IsScalarTower k
        Γ(specialFibre p k f,specialOpen p k f V)
        Γ(specialFibre p k f,specialOpen p k f U) :=
      IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
    let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
    let hβ : β.toRingHom.Etale := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
    let Fr := WittTwoEtaleRestrictionCoherence.restrictedLift p k β F hF hβ
    let hFr := WittTwoEtaleRestrictionCoherence.restrictedLift_reduction p k β F hF hβ
    let eV := WittTwoGeometricDifferential.sectionEquiv p k f hV
    let eU := WittTwoGeometricDifferential.sectionEquiv p k f hU
    let DV := Γ(specialFibre p k f,specialOpen p k f V)
    let DU := Γ(specialFibre p k f,specialOpen p k f U)
    ModuleCat.ofHom
      (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k DV) p)
        (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k DV) p)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := DV) p 1)
      (oneFormAlongEquiv p k eV F hF) ≫
        RelativeNativeAllAlgebraNaturality.formMap (k := k) (A := DV) (B := DU) p 1 =
    RelativeEtaleCartierNaturality.cotangentMap (k := k) (A := DV) (B := DU) p ≫
      (ModuleCat.restrictScalars
        (RelativeEtaleCartierNaturality.twistMap (k := k) (A := DV) (B := DU) p).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap k DU) p)
            (KaehlerDifferential k (RelativeFrobenius.twist (algebraMap k DU) p)))
          (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := k) (B := DU) p 1)
          (oneFormAlongEquiv p k eU Fr hFr)) := by
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f V
  let := WittTwoSchemeAffineRestrictions.sectionAlgebra f U
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hV
  let := WittTwoSchemeAffineRestrictions.affine_smooth f hU
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f V)
  let := CanonicalGeometry.cotangentOpenAlgebra (specialFibreMap p k f) (specialOpen p k f U)
  let r := WittTwoSpecialFibreReduction.residueInclusion p k f i
  let ψ := EtaleSchemeSectionDifferential.restrictionAlgebraHom (specialFibreMap p k f) r
  let := ψ.toAlgebra
  let : IsScalarTower k
      Γ(specialFibre p k f,specialOpen p k f V)
      Γ(specialFibre p k f,specialOpen p k f U) :=
    IsScalarTower.of_algebraMap_eq fun d => (ψ.commutes d).symm
  let β := WittTwoSchemeAffineRestrictions.restrictionAlgebraHom f i
  have hβ : β.toRingHom.Etale := WittTwoSchemeAffineRestrictions.restriction_etale hU hV i
  apply modelOneForm_restrictedLift p k
    (WittTwoGeometricDifferential.sectionEquiv p k f hV)
    (WittTwoGeometricDifferential.sectionEquiv p k f hU) ψ β hβ F hF
  · intro t
    exact RingHom.congr_fun (sectionSourceReduction_restrict p k f hU hV i) t
  · intro s
    exact sectionFlatReduction_restrict p k f hU hV i s

end ActualGeometricZeroRestriction

end EnvelopeProperty.DeligneIllusie.WittTwoNativeTwistRestriction
