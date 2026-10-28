import EnvelopeProperty.DeligneIllusie.WittTwoOriginalDifferenceNaturality
import EnvelopeProperty.DeligneIllusie.WittTwoCoordinateValues

/-! # Genuine whole restriction naturality of the SAME original divided cotangent map -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoOriginalDividedNaturality
open scoped TensorProduct
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.sourceRing WittTwoOriginalCotangentMaps.sourceCommSemiring
  WittTwoOriginalCotangentMaps.sourceSemiring WittTwoOriginalCotangentMaps.sourceResidueRing
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
  [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
private abbrev T (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoSmoothDifferentials.ResidueAlgebra p k A
variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- EVERY actual original coordinate correction has its SAME original native divided value. -/
theorem divided_coordinate_of_correction (a b : A)
    (hb : f ((1 : W' p k) ⊗ₜ[WittTwo.Ring p k] a) = a^p + (p : A)*b) :
    WittTwoOriginalCotangentMaps.divided p k A f hf
      (KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)) =
    ((1 : k) ⊗ₜ[WittTwo.Ring p k] a)^(p-1) •
        KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) +
      KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] b) := by
  have hd : KaehlerDifferential.D (WittTwo.Ring p k) A
      (f ((1 : W' p k) ⊗ₜ[WittTwo.Ring p k] a)) =
      (p : WittTwo.Ring p k) •
        (a^(p-1) • KaehlerDifferential.D (WittTwo.Ring p k) A a +
          KaehlerDifferential.D (WittTwo.Ring p k) A b) := by
    rw [hb]
    exact DividedCoordinateDifferential.differential_prime p k A a b
  rw [WittTwoOriginalCotangentMaps.divided_coordinate,
    WittTwoArbitraryLiftDifferential.dividedDifferential_prime _ _ _ _ _ _ _ hd,
    map_add, map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D]
  congr 1
  change algebraMap A (B p k A) (a^(p-1)) •
      KaehlerDifferential.D k (B p k A) (algebraMap A (B p k A) a) = _
  rw [map_pow]
  rfl

variable (β : A →ₐ[WittTwo.Ring p k] A') (f' : WittTwoLiftDifference.Lift p k A')
variable (hf' : ∀ t, algebraMap A' (B p k A') (f' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hff' : ∀ t, β (f t) = f' (WittTwoLiftDifferenceNaturality.twistMap p k β t))
include hff'

private theorem generator_naturality (c : B p k A) :
    WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β
      (WittTwoOriginalCotangentMaps.divided p k A f hf (KaehlerDifferential.D k (B p k A) c)) =
    WittTwoOriginalCotangentMaps.divided p k A' f' hf'
      (KaehlerDifferential.D k (B p k A') (WittTwoAlgebraDivisionNaturality.residueMap p k β c)) := by
  obtain ⟨a, ha⟩ := WittTwoResidue.tensorReduction_surjective p k A c
  obtain ⟨b, hb⟩ := WittTwoCoordinateValues.coordinate_correction p k A f hf a
  have hb' : f' ((1 : W' p k) ⊗ₜ[WittTwo.Ring p k] β a) = (β a)^p + (p : A')*β b := by
    have he := congrArg β hb
    rw [map_add, map_pow, map_mul, map_natCast] at he
    have hc := hff' ((1 : W' p k) ⊗ₜ[WittTwo.Ring p k] a)
    rw [WittTwoLiftDifferenceNaturality.twistMap_tmul] at hc
    exact hc.symm.trans he
  have hρ : algebraMap A (B p k A) a = c := ha
  rw [← hρ, WittTwoAlgebraDivisionNaturality.residueMap_reduction]
  change WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β
      (WittTwoOriginalCotangentMaps.divided p k A f hf
        (KaehlerDifferential.D k (B p k A) ((1 : k) ⊗ₜ[WittTwo.Ring p k] a))) =
    WittTwoOriginalCotangentMaps.divided p k A' f' hf'
      (KaehlerDifferential.D k (B p k A') ((1 : k) ⊗ₜ[WittTwo.Ring p k] β a))
  rw [divided_coordinate_of_correction p k f hf a b hb,
    divided_coordinate_of_correction p k f' hf' (β a) (β b) hb',
    map_add, LinearMap.map_smulₛₗ,
    WittTwoOriginalDifferenceNaturality.residueCotangentMap_D,
    WittTwoOriginalDifferenceNaturality.residueCotangentMap_D,
    map_pow, WittTwoAlgebraDivisionNaturality.residueMap_tmul,
    WittTwoAlgebraDivisionNaturality.residueMap_tmul]
  have hc : (WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom
      ((1 : k) ⊗ₜ[WittTwo.Ring p k] a) = (1 : k) ⊗ₜ[WittTwo.Ring p k] β a :=
    WittTwoAlgebraDivisionNaturality.residueMap_tmul p k β 1 a
  rw [hc]

/-- EVERY SAME original whole residue cotangent form satisfies actual divided-map naturality. -/
theorem divided_naturality (w : KaehlerDifferential k (B p k A)) :
    WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β
      (WittTwoOriginalCotangentMaps.divided p k A f hf w) =
    WittTwoOriginalCotangentMaps.divided p k A' f' hf'
      (WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β w) := by
  have hw : w ∈ Submodule.span (B p k A) (Set.range (KaehlerDifferential.D k (B p k A))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨c, rfl⟩ := hw
    rw [WittTwoOriginalDifferenceNaturality.residueCotangentMap_D]
    exact generator_naturality p k f hf β f' hf' hff' c
  | zero => simp only [map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  | smul a z _ hz =>
    rw [(WittTwoOriginalCotangentMaps.divided p k A f hf).map_smulₛₗ a z,
      (WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β).map_smulₛₗ,
      (WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β).map_smulₛₗ a z,
      (WittTwoOriginalCotangentMaps.divided p k A' f' hf').map_smulₛₗ,
      Cartier.AlgebraFrobenius.map_apply, Cartier.AlgebraFrobenius.map_apply, map_pow, hz]

end EnvelopeProperty.DeligneIllusie.WittTwoOriginalDividedNaturality
