import EnvelopeProperty.DeligneIllusie.WittTwoLiftDifferenceNaturality

/-! # Whole native source cotangent naturality of SAME original actual lift differences -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoLiftCotangentNaturality
open scoped TensorProduct
universe u

private def nativeCotangentMap {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] (β : C →ₐ[R] D) :
    KaehlerDifferential R C →ₛₗ[β.toRingHom] KaehlerDifferential R D := by
  letI : Algebra C D := β.toRingHom.toAlgebra
  letI : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq (fun a => (β.commutes a).symm)
  let f := KaehlerDifferential.map R R C D
  exact { f.toAddMonoidHom with
    map_smul' := fun a w => by
      change f (a • w) = β a • f w
      rw [f.map_smul]
      exact (IsScalarTower.algebraMap_smul D a (f w)).symm }

private theorem nativeCotangentMap_D {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] (β : C →ₐ[R] D) (a : C) :
    nativeCotangentMap β (KaehlerDifferential.D R C a) = KaehlerDifferential.D R D (β a) := by
  let : Algebra C D := β.toRingHom.toAlgebra
  let : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq (fun a => (β.commutes a).symm)
  change KaehlerDifferential.map R R C D (KaehlerDifferential.D R C a) = _
  rw [KaehlerDifferential.map_D]
  rfl

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra WittTwoLiftDifference.frobeniusAlgebra
  WittTwoLiftDifferenceNaturality.copiedSMul WittTwoLiftDifferenceNaturality.copiedTower
  WittTwoLiftDifference.sourceBaseSMul WittTwoLiftDifference.sourceBaseModule
  WittTwoLiftDifference.residueBaseSMul WittTwoLiftDifference.residueBaseModule
  WittTwoLiftDifference.residueBaseTower
variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
private abbrev T (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoSmoothDifferentials.ResidueAlgebra p k A

/-- The genuine native whole source cotangent map of the SAME original actual twist map. -/
def twistCotangentMap (β : A →ₐ[WittTwo.Ring p k] A') :
    KaehlerDifferential (W' p k) (T p k A) →ₛₗ[(WittTwoLiftDifferenceNaturality.twistMap p k β).toRingHom]
      KaehlerDifferential (W' p k) (T p k A') :=
  nativeCotangentMap (WittTwoLiftDifferenceNaturality.twistMap p k β)

omit [PerfectRing k p] in
/-- EVERY original universal differential has its actual SAME original twist-map derivative. -/
theorem twistCotangentMap_D (β : A →ₐ[WittTwo.Ring p k] A') (t : T p k A) :
    twistCotangentMap p k β (KaehlerDifferential.D (W' p k) (T p k A) t) =
      KaehlerDifferential.D (W' p k) (T p k A') (WittTwoLiftDifferenceNaturality.twistMap p k β t) :=
  nativeCotangentMap_D _ t

variable [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']
variable (β : A →ₐ[WittTwo.Ring p k] A')
variable (f g : WittTwoLiftDifference.Lift p k A) (f' g' : WittTwoLiftDifference.Lift p k A')
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hf' : ∀ t, algebraMap A' (B p k A') (f' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hg' : ∀ t, algebraMap A' (B p k A') (g' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hff' : ∀ t, β (f t) = f' (WittTwoLiftDifferenceNaturality.twistMap p k β t))
variable (hgg' : ∀ t, β (g t) = g' (WittTwoLiftDifferenceNaturality.twistMap p k β t))
include hff' hgg'

/-- EVERY whole native original cotangent form has the genuinely derived divided-difference restriction. -/
theorem differenceLinear_naturality (w : KaehlerDifferential (W' p k) (T p k A)) :
    WittTwoAlgebraDivisionNaturality.residueMap p k β
      (WittTwoLiftDifference.differenceLinear p k A f g hf hg w) =
    WittTwoLiftDifference.differenceLinear p k A' f' g' hf' hg' (twistCotangentMap p k β w) := by
  have hw : w ∈ Submodule.span (T p k A) (Set.range (KaehlerDifferential.D (W' p k) (T p k A))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, rfl⟩ := hw
    rw [twistCotangentMap_D, WittTwoLiftDifference.differenceLinear_D,
      WittTwoLiftDifference.differenceLinear_D]
    exact WittTwoLiftDifferenceNaturality.differenceDerivation_naturality
      p k β f g f' g' hf hg hf' hg' hff' hgg' t
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  | smul a z _ hz =>
    rw [(WittTwoLiftDifference.differenceLinear p k A f g hf hg).map_smul a z,
      (twistCotangentMap p k β).map_smulₛₗ a z,
      (WittTwoLiftDifference.differenceLinear p k A' f' g' hf' hg').map_smul]
    change WittTwoAlgebraDivisionNaturality.residueMap p k β
        (WittTwoRelativeLift.residueFrobenius p k A a *
          WittTwoLiftDifference.differenceLinear p k A f g hf hg z) =
      WittTwoRelativeLift.residueFrobenius p k A' (WittTwoLiftDifferenceNaturality.twistMap p k β a) *
        WittTwoLiftDifference.differenceLinear p k A' f' g' hf' hg' (twistCotangentMap p k β z)
    rw [map_mul, WittTwoLiftDifferenceNaturality.residueFrobenius_naturality, hz]

end EnvelopeProperty.DeligneIllusie.WittTwoLiftCotangentNaturality
