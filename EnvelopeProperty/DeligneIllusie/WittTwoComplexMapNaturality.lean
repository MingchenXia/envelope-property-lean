import EnvelopeProperty.DeligneIllusie.WittTwoOriginalDividedNaturality
import EnvelopeProperty.DeligneIllusie.WittTwoNativeOneRestriction

/-! # The SAME actual ALLq original divided cochain map has genuine native restriction naturality -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoComplexMapNaturality
open CategoryTheory
open scoped TensorProduct
universe u

private theorem nativeExteriorNaturality (p : ℕ) [Fact p.Prime]
    {k C D : Type u} [Field k] [CharP k p] [CommRing C] [CommRing D]
    [Algebra k C] [Algebra k D] [Algebra C D] [IsScalarTower k C D]
    (φ : KaehlerDifferential k C →ₛₗ[Cartier.AlgebraFrobenius.map k C p] KaehlerDifferential k C)
    (ψ : KaehlerDifferential k D →ₛₗ[Cartier.AlgebraFrobenius.map k D p] KaehlerDifferential k D)
    (he : ∀ m, KaehlerDifferential.map k k C D (φ m) = ψ (KaehlerDifferential.map k k C D m))
    (q : ℕ) (w : ⋀[C]^q (KaehlerDifferential k C)) :
    Char0.canonicalDifferentialLinearMap (k := k) (R := C) (A := D) q
      (CanonicalGeometry.exteriorSemilinearMap _ φ q w) =
    CanonicalGeometry.exteriorSemilinearMap _ ψ q
      (Char0.canonicalDifferentialLinearMap (k := k) (R := C) (A := D) q w) := by
  have hw : w ∈ Submodule.span C (Set.range (exteriorPower.ιMulti C q (M := KaehlerDifferential k C))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, rfl⟩ := hw
    rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti,
      Char0.canonicalDifferentialLinearMap_wedge,
      Char0.canonicalDifferentialLinearMap_wedge,
      CanonicalGeometry.exteriorSemilinearMap_ιMulti]
    congr 1
    funext i
    exact he (t i)
  | zero => simp only [map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]
  | smul a z _ hz =>
    rw [LinearMap.map_smulₛₗ, map_smul, map_smul,
      ← IsScalarTower.algebraMap_smul D (Cartier.AlgebraFrobenius.map k C p a),
      ← IsScalarTower.algebraMap_smul D a, LinearMap.map_smulₛₗ,
      Cartier.AlgebraFrobenius.map_apply, Cartier.AlgebraFrobenius.map_apply, map_pow, hz]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
  WittTwoExteriorLiftMaps.originalCommSemiring WittTwoExteriorLiftMaps.originalSemiring
variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
  [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoSmoothDifferentials.ResidueAlgebra p k A
variable (β : A →ₐ[WittTwo.Ring p k] A')
variable (f : WittTwoLiftDifference.Lift p k A) (f' : WittTwoLiftDifference.Lift p k A')
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hf' : ∀ t, algebraMap A' (B p k A') (f' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hff' : ∀ t, β (f t) = f' (WittTwoLiftDifferenceNaturality.twistMap p k β t))

@[instance_reducible] private def residueRestrictionAlgebra : Algebra (B p k A) (B p k A') :=
  (WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom.toAlgebra

omit [CharP k p] [PerfectRing k p] [Algebra.Smooth (WittTwo.Ring p k) A]
  [Algebra.Smooth (WittTwo.Ring p k) A'] in
private theorem residueTower :
    letI := residueRestrictionAlgebra p k β
    IsScalarTower k (B p k A) (B p k A') := by
  let := residueRestrictionAlgebra p k β
  exact IsScalarTower.of_algebraMap_eq fun a =>
    ((WittTwoAlgebraDivisionNaturality.residueMap p k β).commutes a).symm

include hff'
/-- EVERY SAME original whole exterior lift map commutes with actual coefficient restriction, ALLq. -/
theorem map_naturality (q : ℕ) (w : ⋀[B p k A]^q (KaehlerDifferential k (B p k A))) :
    letI := residueRestrictionAlgebra p k β
    letI := residueTower p k β
    Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') q
      (WittTwoExteriorLiftMaps.map p k A f hf q w) =
    WittTwoExteriorLiftMaps.map p k A' f' hf' q
      (Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') q w) := by
  let := residueRestrictionAlgebra p k β
  let := residueTower p k β
  apply nativeExteriorNaturality p
    (WittTwoOriginalCotangentMaps.divided p k A f hf)
    (WittTwoOriginalCotangentMaps.divided p k A' f' hf')
  intro z
  exact WittTwoOriginalDividedNaturality.divided_naturality p k f hf β f' hf' hff' z

variable {n m : ℕ} (v : Fin n → B p k A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (v' : Fin m → B p k A') (hv' : (MvPolynomial.aeval (R := k) v').toRingHom.Etale)

/-- The SAME WHOLE original divided cochain maps have their actual native restriction square. -/
theorem complexMap_naturality :
    letI := residueRestrictionAlgebra p k β
    letI := residueTower p k β
    WittTwoExteriorLiftMaps.complexMap p k A f hf v hv ≫
      Cartier.EtaleAlgebraFrobeniusNaturality.complexMap p v hv v' hv' =
    WittTwoNativeOneRestriction.zeroComplexMap p k β ≫
      ((ModuleCat.restrictScalars (WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (WittTwoExteriorLiftMaps.complexMap p k A' f' hf' v' hv') := by
  let := residueRestrictionAlgebra p k β
  let := residueTower p k β
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact map_naturality p k β f f' hf hf' hff' q w

end EnvelopeProperty.DeligneIllusie.WittTwoComplexMapNaturality
