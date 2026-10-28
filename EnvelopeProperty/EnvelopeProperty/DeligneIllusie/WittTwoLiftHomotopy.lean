import EnvelopeProperty.DeligneIllusie.WittTwoArbitraryLiftDifferential
import EnvelopeProperty.DeligneIllusie.WittTwoSourceResidue

/-! Actual whole divided-map differential homotopy of two genuine relative Frobenius lifts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace EnvelopeProperty.DeligneIllusie.WittTwoLiftHomotopy
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra Algebra.TensorProduct.rightAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoRelativeLift.residueCopyAlgebra WittTwoLiftDifference.frobeniusAlgebra
  WittTwoLiftDifference.sourceBaseSMul WittTwoLiftDifference.sourceBaseModule
  WittTwoLiftDifference.residueBaseSMul WittTwoLiftDifference.residueBaseModule
  WittTwoLiftDifference.residueBaseTower
  WittTwoArbitraryLiftDifferential.residueFormBaseSMul
  WittTwoArbitraryLiftDifferential.residueFormBaseModule
  WittTwoArbitraryLiftDifferential.residueFormBaseTower
  WittTwoArbitraryLiftDifferential.residueFormSourceTower
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev W' := ULift.{0} (WittTwo.Ring p k)
private abbrev T := WittTwoRelativeLift.TwistAlgebra p k A
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev N := KaehlerDifferential k (B p k A)
variable (f g : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- The actual native differential of the genuine whole divided-difference Kähler map is T-linear. -/
def differenceDifferential : KaehlerDifferential (W' p k) (T p k A) →ₗ[T p k A] N p k A where
  toFun w := KaehlerDifferential.D k (B p k A) (WittTwoLiftDifference.differenceLinear p k A f g hf hg w)
  map_add' w z := by rw [map_add, map_add]
  map_smul' t w := by
    simp only [RingHom.id_apply]
    rw [map_smul, Algebra.smul_def t (WittTwoLiftDifference.differenceLinear p k A f g hf hg w),
      Derivation.leibniz]
    have hz : KaehlerDifferential.D k (B p k A) (algebraMap (T p k A) (B p k A) t) = 0 :=
      WittTwoRelativeDifferential.residueFrobenius_differential_zero p k A t
    rw [hz, smul_zero, add_zero]
    exact IsScalarTower.algebraMap_smul (B p k A) t _

private theorem universal_difference (t : T p k A) :
    WittTwoArbitraryLiftDifferential.dividedDifferential p k A f hf
        (KaehlerDifferential.D (W' p k) (T p k A) t) -
      WittTwoArbitraryLiftDifferential.dividedDifferential p k A g hg
        (KaehlerDifferential.D (W' p k) (T p k A) t) =
    differenceDifferential p k A f g hf hg (KaehlerDifferential.D (W' p k) (T p k A) t) := by
  obtain ⟨a, ha⟩ := WittTwoAlgebraDivision.kernel_prime p k A
    (WittTwoLiftDifference.differenceElement p k A f g hf hg t)
  have ha' : f t-g t = (p : A)*a := congrArg Subtype.val ha
  have he : WittTwoArbitraryLiftDifferential.primeDifferential p k A f hf t -
      WittTwoArbitraryLiftDifferential.primeDifferential p k A g hg t =
        WittTwoDividedLift.primeForm p k A (KaehlerDifferential.D (WittTwo.Ring p k) A a) := by
    apply Subtype.ext
    change KaehlerDifferential.D (WittTwo.Ring p k) A (f t) -
      KaehlerDifferential.D (WittTwo.Ring p k) A (g t) =
        (p : A) • KaehlerDifferential.D (WittTwo.Ring p k) A a
    rw [← map_sub, ha', Derivation.leibniz]
    have hp : KaehlerDifferential.D (WittTwo.Ring p k) A (p : A) = 0 := by
      rw [← map_natCast (algebraMap (WittTwo.Ring p k) A) p, Derivation.map_algebraMap]
    rw [hp, smul_zero, add_zero]
  have hdiv := congrArg (WittTwoDividedLift.divisionLinear p k A) he
  rw [map_sub, WittTwoDividedLift.divisionLinear_primeForm, KaehlerDifferential.map_D] at hdiv
  rw [WittTwoArbitraryLiftDifferential.dividedDifferential_D,
    WittTwoArbitraryLiftDifferential.dividedDifferential_D]
  change WittTwoDividedLift.divisionLinear p k A
      (WittTwoArbitraryLiftDifferential.primeDifferential p k A f hf t) -
    WittTwoDividedLift.divisionLinear p k A
      (WittTwoArbitraryLiftDifferential.primeDifferential p k A g hg t) =
    KaehlerDifferential.D k (B p k A)
      (WittTwoLiftDifference.differenceLinear p k A f g hf hg
        (KaehlerDifferential.D (W' p k) (T p k A) t))
  rw [WittTwoLiftDifference.differenceLinear_D,
    WittTwoLiftDifference.differenceDerivation_prime _ _ _ _ _ _ _ t a ha']
  exact hdiv

/-- The ACTUAL WHOLE native difference of the two original divided maps equals d of the genuine whole h. -/
theorem dividedDifferential_sub :
    WittTwoArbitraryLiftDifferential.dividedDifferential p k A f hf -
      WittTwoArbitraryLiftDifferential.dividedDifferential p k A g hg =
    differenceDifferential p k A f g hf hg := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro t
  exact universal_difference p k A f g hf hg t

omit [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
private theorem sourcePrime_le_ker {V : Type u} [AddCommGroup V]
    [Module (B p k A) V] [Module (T p k A) V] [IsScalarTower (T p k A) (B p k A) V]
    (F : KaehlerDifferential (W' p k) (T p k A) →ₗ[T p k A] V) :
    WittTwoDividedLift.sourcePrimeForms p k A ≤ LinearMap.ker F := by
  rintro w ⟨z, rfl⟩
  change F ((p : T p k A) • z) = 0
  rw [map_smul, ← IsScalarTower.algebraMap_smul (B p k A) (p : T p k A), map_natCast]
  have hp : (p : B p k A) = 0 := by
    rw [← map_natCast (algebraMap k (B p k A)) p, CharP.cast_eq_zero, map_zero]
  rw [hp, zero_smul]

private def residueFactor {V : Type u} [AddCommGroup V]
    [Module (B p k A) V] [Module (T p k A) V] [IsScalarTower (T p k A) (B p k A) V]
    (F : KaehlerDifferential (W' p k) (T p k A) →ₗ[T p k A] V) :
    KaehlerDifferential k (WittTwoSourceResidue.SourceResidue p k A) →ₗ[T p k A] V :=
  ((WittTwoDividedLift.sourcePrimeForms p k A).liftQ F (sourcePrime_le_ker p k A F)).comp
    (WittTwoSourceResidue.sourceResidueEquiv p k A).symm.toLinearMap

private theorem residueFactor_reduction {V : Type u} [AddCommGroup V]
    [Module (B p k A) V] [Module (T p k A) V] [IsScalarTower (T p k A) (B p k A) V]
    (F : KaehlerDifferential (W' p k) (T p k A) →ₗ[T p k A] V)
    (w : KaehlerDifferential (W' p k) (T p k A)) :
    residueFactor p k A F (WittTwoSourceResidue.sourceReduction p k A w) = F w := by
  rw [← WittTwoSourceResidue.sourceResidueEquiv_mk]
  change (WittTwoDividedLift.sourcePrimeForms p k A).liftQ F (sourcePrime_le_ker p k A F)
    ((WittTwoSourceResidue.sourceResidueEquiv p k A).symm
      (WittTwoSourceResidue.sourceResidueEquiv p k A
        ((WittTwoDividedLift.sourcePrimeForms p k A).mkQ w))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The SAME actual whole divided lift acts on the genuine native residue Kähler source. -/
def residueDividedDifferential :
    KaehlerDifferential k (WittTwoSourceResidue.SourceResidue p k A) →ₗ[T p k A] N p k A :=
  residueFactor p k A (WittTwoArbitraryLiftDifferential.dividedDifferential p k A f hf)

/-- The SAME actual whole h acts on the SAME genuine native residue Kähler source. -/
def residueDifferenceLinear :
    KaehlerDifferential k (WittTwoSourceResidue.SourceResidue p k A) →ₗ[T p k A] B p k A :=
  residueFactor p k A (WittTwoLiftDifference.differenceLinear p k A f g hf hg)

/-- EVERY actual native reduction retains its SAME original whole divided value. -/
theorem residueDividedDifferential_reduction (w : KaehlerDifferential (W' p k) (T p k A)) :
    residueDividedDifferential p k A f hf (WittTwoSourceResidue.sourceReduction p k A w) =
      WittTwoArbitraryLiftDifferential.dividedDifferential p k A f hf w :=
  residueFactor_reduction p k A _ w

/-- EVERY actual native reduction retains its SAME original whole h value. -/
theorem residueDifferenceLinear_reduction (w : KaehlerDifferential (W' p k) (T p k A)) :
    residueDifferenceLinear p k A f g hf hg (WittTwoSourceResidue.sourceReduction p k A w) =
      WittTwoLiftDifference.differenceLinear p k A f g hf hg w :=
  residueFactor_reduction p k A _ w

/-- The genuine SAME actual exact-differential identity holds on EVERY native residue source form. -/
theorem residueDividedDifferential_sub
    (w : KaehlerDifferential k (WittTwoSourceResidue.SourceResidue p k A)) :
    residueDividedDifferential p k A f hf w - residueDividedDifferential p k A g hg w =
      KaehlerDifferential.D k (B p k A) (residueDifferenceLinear p k A f g hf hg w) := by
  obtain ⟨z, rfl⟩ := WittTwoSourceResidue.sourceReduction_surjective p k A w
  rw [residueDividedDifferential_reduction, residueDividedDifferential_reduction,
    residueDifferenceLinear_reduction]
  exact LinearMap.congr_fun (dividedDifferential_sub p k A f g hf hg) z

end EnvelopeProperty.DeligneIllusie.WittTwoLiftHomotopy
