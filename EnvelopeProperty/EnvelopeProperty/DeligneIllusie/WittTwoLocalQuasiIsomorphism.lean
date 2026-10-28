import EnvelopeProperty.DeligneIllusie.WittTwoCartierClassComparison
import EnvelopeProperty.Algebra.ZeroComplexNativeHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # The SAME actual original Witt divided cochain map is a genuine local quasi-isomorphism -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.DeligneIllusie.WittTwoLocalQuasiIsomorphism
open CategoryTheory
open scoped TensorProduct
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
  WittTwoExteriorLiftMaps.originalCommSemiring WittTwoExteriorLiftMaps.originalSemiring
variable (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A]
private abbrev B := WittTwoSmoothDifferentials.ResidueAlgebra p k A
private abbrev N := KaehlerDifferential k (B p k A)

/-- The ENTIRE original source has its genuine SAME whole native source-class equivalence. -/
def sourceClassEquiv (q : ℕ) : (⋀[B p k A]^q (N p k A)) ≃ₗ[B p k A]
    (WittTwoExteriorLiftMaps.zeroComplex p k A).homology q :=
  ZeroComplexNativeHomology.cycleClassEquiv
    (fun q => ModuleCat.of (B p k A) (⋀[B p k A]^q (N p k A))) q

omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A] in
/-- EVERY original form has EXACTLY its SAME original whole native source-cycle class. -/
theorem sourceClassEquiv_apply (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    sourceClassEquiv p k A q w = ModuleComplexNativeCycleClasses.cycleClass
      (WittTwoExteriorLiftMaps.zeroComplex p k A) q (WittTwoNativeCycleClasses.sourceCycle p k A q w) := by
  have h := ZeroComplexNativeHomology.cycleClassEquiv_value
    (fun q => ModuleCat.of (B p k A) (⋀[B p k A]^q (N p k A))) q w
  exact h.trans (congrArg
    (ModuleComplexNativeCycleClasses.cycleClass (WittTwoExteriorLiftMaps.zeroComplex p k A) q)
      (show ZeroComplexNativeHomology.cycleEquiv
          (fun q => ModuleCat.of (B p k A) (⋀[B p k A]^q (N p k A))) q w =
        WittTwoNativeCycleClasses.sourceCycle p k A q w from Subtype.ext rfl))

variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- The ACTUAL induced whole homology map sends EVERY true source-equivalence value to SAME Cartier. -/
theorem homologyMap_sourceClassEquiv (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    (HomologicalComplex.homologyMap (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q).hom
      (sourceClassEquiv p k A q w) = Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier v hv p q w := by
  rw [sourceClassEquiv_apply]
  exact WittTwoCartierClassComparison.homologyMap_sourceClass p k A f hf v hv q w

/-- The ENTIRE actual native induced homology map is canonical Cartier after genuine source inverse. -/
theorem homologyMap_eq (q : ℕ) :
    (HomologicalComplex.homologyMap (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q).hom =
      (Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier v hv p q).hom.comp
        (sourceClassEquiv p k A q).symm.toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (sourceClassEquiv p k A q).surjective z
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact homologyMap_sourceClassEquiv p k A f hf v hv q w

/-- The SAME actual native homology map is bijective on the ENTIRE actual source H, EVERY degree. -/
theorem homologyMap_bijective (q : ℕ) : Function.Bijective
    (HomologicalComplex.homologyMap (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q) := by
  change Function.Bijective
    (HomologicalComplex.homologyMap (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q).hom
  rw [homologyMap_eq]
  exact (Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier_bijective v hv p q).comp
    (sourceClassEquiv p k A q).symm.bijective

/-- Genuine categorical isomorphism of SAME actual native homology map, EVERYq and zero algebras. -/
theorem homologyMap_isIso (q : ℕ) : IsIso
    (HomologicalComplex.homologyMap (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (homologyMap_bijective p k A f hf v hv q)

/-- The SAME original actual whole divided cochain map is genuinely a native quasi-isomorphism. -/
theorem quasiIso : QuasiIso (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) := by
  rw [quasiIso_iff]
  intro q
  exact (quasiIsoAt_iff_isIso_homologyMap _ q).mpr
    (homologyMap_isIso p k A f hf v hv q)

/-- Actual smooth Witt lifting PRODUCES the original whole local cochain map internally. -/
def producedComplexMap : WittTwoExteriorLiftMaps.zeroComplex p k A ⟶
    Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p :=
  WittTwoExteriorLiftMaps.complexMap p k A (WittTwoArbitraryLiftDifferential.producedLift p k A)
    (WittTwoArbitraryLiftDifferential.producedLift_reduction p k A) v hv

/-- The internally produced actual relative lift gives a genuine original native local quasi-isomorphism. -/
theorem producedComplexMap_quasiIso : QuasiIso (producedComplexMap p k A v hv) :=
  quasiIso p k A (WittTwoArbitraryLiftDifferential.producedLift p k A)
    (WittTwoArbitraryLiftDifferential.producedLift_reduction p k A) v hv

/-- Actual smooth W2 A and actual residue etale chart PRODUCE genuine quasiiso + SAME actual Cartier values. -/
theorem exists_quasiIso : ∃ φ : WittTwoExteriorLiftMaps.zeroComplex p k A ⟶
    Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p,
    QuasiIso φ ∧ ∀ q (w : ⋀[B p k A]^q (N p k A)),
      (HomologicalComplex.homologyMap φ q).hom
        (ModuleComplexNativeCycleClasses.cycleClass (WittTwoExteriorLiftMaps.zeroComplex p k A) q
          (WittTwoNativeCycleClasses.sourceCycle p k A q w)) =
        Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier v hv p q w := by
  refine ⟨producedComplexMap p k A v hv, producedComplexMap_quasiIso p k A v hv, ?_⟩
  intro q w
  exact WittTwoCartierClassComparison.homologyMap_sourceClass p k A
    (WittTwoArbitraryLiftDifferential.producedLift p k A)
    (WittTwoArbitraryLiftDifferential.producedLift_reduction p k A) v hv q w
end EnvelopeProperty.DeligneIllusie.WittTwoLocalQuasiIsomorphism
