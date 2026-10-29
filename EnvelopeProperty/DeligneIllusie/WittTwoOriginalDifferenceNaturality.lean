import EnvelopeProperty.DeligneIllusie.WittTwoLiftCotangentNaturality
import EnvelopeProperty.DeligneIllusie.WittTwoOriginalCotangentMaps

/-! # Whole actual restriction naturality on the SAME original residue cotangent modules -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoOriginalDifferenceNaturality
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
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
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

/-- The actual native whole cotangent map on the SAME original residue algebras. -/
def residueCotangentMap (β : A →ₐ[WittTwo.Ring p k] A') :
    KaehlerDifferential k (B p k A) →ₛₗ[(WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom]
      KaehlerDifferential k (B p k A') :=
  nativeCotangentMap (WittTwoAlgebraDivisionNaturality.residueMap p k β)

omit [CharP k p] [PerfectRing k p] in
/-- EVERY original residue derivative retains its SAME actual mapped derivative. -/
theorem residueCotangentMap_D (β : A →ₐ[WittTwo.Ring p k] A') (b : B p k A) :
    residueCotangentMap p k β (KaehlerDifferential.D k (B p k A) b) =
      KaehlerDifferential.D k (B p k A') (WittTwoAlgebraDivisionNaturality.residueMap p k β b) :=
  nativeCotangentMap_D _ b

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

private theorem generator_naturality (b : B p k A) :
    WittTwoAlgebraDivisionNaturality.residueMap p k β
      (WittTwoOriginalCotangentMaps.difference p k A f g hf hg (KaehlerDifferential.D k (B p k A) b)) =
    WittTwoOriginalCotangentMaps.difference p k A' f' g' hf' hg'
      (KaehlerDifferential.D k (B p k A') (WittTwoAlgebraDivisionNaturality.residueMap p k β b)) := by
  obtain ⟨a, ha⟩ := WittTwoResidue.tensorReduction_surjective p k A b
  have hρ : algebraMap A (B p k A) a = b := ha
  rw [← hρ, WittTwoAlgebraDivisionNaturality.residueMap_reduction]
  change WittTwoAlgebraDivisionNaturality.residueMap p k β
      (WittTwoOriginalCotangentMaps.difference p k A f g hf hg
        (KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a))) =
    WittTwoOriginalCotangentMaps.difference p k A' f' g' hf' hg'
      (KaehlerDifferential.D k (B p k A') ((1 : k) ⊗ₜ[WittTwo.Ring p k] β a))
  rw [WittTwoOriginalCotangentMaps.difference_coordinate,
    WittTwoOriginalCotangentMaps.difference_coordinate]
  have he := WittTwoLiftCotangentNaturality.differenceLinear_naturality
    p k β f g f' g' hf hg hf' hg' hff' hgg'
    (KaehlerDifferential.D (W' p k) (T p k A) ((1 : W' p k) ⊗ₜ[WittTwo.Ring p k] a))
  rw [WittTwoLiftCotangentNaturality.twistCotangentMap_D,
    WittTwoLiftDifferenceNaturality.twistMap_tmul] at he
  exact he

/-- EVERY SAME original residue cotangent form satisfies actual canonical homotopy naturality. -/
theorem difference_naturality (w : KaehlerDifferential k (B p k A)) :
    WittTwoAlgebraDivisionNaturality.residueMap p k β
      (WittTwoOriginalCotangentMaps.difference p k A f g hf hg w) =
    WittTwoOriginalCotangentMaps.difference p k A' f' g' hf' hg' (residueCotangentMap p k β w) := by
  have hw : w ∈ Submodule.span (B p k A) (Set.range (KaehlerDifferential.D k (B p k A))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨b, rfl⟩ := hw
    rw [residueCotangentMap_D]
    exact generator_naturality p k β f g f' g' hf hg hf' hg' hff' hgg' b
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  | smul a z _ hz =>
    rw [(WittTwoOriginalCotangentMaps.difference p k A f g hf hg).map_smulₛₗ a z,
      (residueCotangentMap p k β).map_smulₛₗ a z,
      (WittTwoOriginalCotangentMaps.difference p k A' f' g' hf' hg').map_smulₛₗ,
      Cartier.AlgebraFrobenius.map_apply, Cartier.AlgebraFrobenius.map_apply]
    change WittTwoAlgebraDivisionNaturality.residueMap p k β
        (a^p * WittTwoOriginalCotangentMaps.difference p k A f g hf hg z) =
      (WittTwoAlgebraDivisionNaturality.residueMap p k β a)^p *
        WittTwoOriginalCotangentMaps.difference p k A' f' g' hf' hg' (residueCotangentMap p k β z)
    rw [map_mul, map_pow, hz]

end EnvelopeProperty.DeligneIllusie.WittTwoOriginalDifferenceNaturality
