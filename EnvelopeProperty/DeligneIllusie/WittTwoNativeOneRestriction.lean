import EnvelopeProperty.DeligneIllusie.WittTwoOriginalDifferenceNaturality
import EnvelopeProperty.DeligneIllusie.WittTwoCanonicalOneHomotopy
import EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusNaturality

/-! # SAME actual native zero-source restriction and canonical degree-one homotopy square -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoNativeOneRestriction
open CategoryTheory Limits
open scoped TensorProduct
universe u

private theorem canonicalZero {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra C D] [IsScalarTower R C D] (c : C) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := C) (A := D) 0
      ((exteriorPower.zeroEquiv C (KaehlerDifferential R C)).symm c) =
    (exteriorPower.zeroEquiv D (KaehlerDifferential R D)).symm (algebraMap C D c) := by
  apply (exteriorPower.zeroEquiv D (KaehlerDifferential R D)).injective
  rw [LinearEquiv.apply_symm_apply, exteriorPower.zeroEquiv_symm_apply,
    map_smul, Char0.canonicalDifferentialLinearMap_wedge,
    ← IsScalarTower.algebraMap_smul D c, map_smul,
    exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]

private theorem canonicalOne {R C D : Type u} [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra R D] [Algebra C D] [IsScalarTower R C D]
    (m : KaehlerDifferential R C) :
    Char0.canonicalDifferentialLinearMap (k := R) (R := C) (A := D) 1
      ((exteriorPower.oneEquiv C (KaehlerDifferential R C)).symm m) =
    (exteriorPower.oneEquiv D (KaehlerDifferential R D)).symm
      (KaehlerDifferential.map R R C D m) := by
  rw [exteriorPower.oneEquiv_symm_apply, Char0.canonicalDifferentialLinearMap_wedge,
    exteriorPower.oneEquiv_symm_apply]

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
  WittTwoExteriorLiftMaps.originalCommSemiring WittTwoExteriorLiftMaps.originalSemiring
variable {A A' : Type u} [CommRing A] [CommRing A']
  [Algebra (WittTwo.Ring p k) A] [Algebra (WittTwo.Ring p k) A']
private abbrev B (A : Type u) [CommRing A] [Algebra (WittTwo.Ring p k) A] :=
  WittTwoSmoothDifferentials.ResidueAlgebra p k A

@[instance_reducible] private def residueRestrictionAlgebra (β : A →ₐ[WittTwo.Ring p k] A') :
    Algebra (B p k A) (B p k A') :=
  (WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom.toAlgebra

omit [CharP k p] [PerfectRing k p] in
private theorem residueTower (β : A →ₐ[WittTwo.Ring p k] A') :
    letI := residueRestrictionAlgebra p k β
    IsScalarTower k (B p k A) (B p k A') := by
  let := residueRestrictionAlgebra p k β
  exact IsScalarTower.of_algebraMap_eq fun a =>
    ((WittTwoAlgebraDivisionNaturality.residueMap p k β).commutes a).symm

/-- The SAME original whole zero-source complexes have their genuine native coefficient restriction. -/
def zeroComplexMap (β : A →ₐ[WittTwo.Ring p k] A') :
    WittTwoExteriorLiftMaps.zeroComplex p k A ⟶
      ((ModuleCat.restrictScalars (WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (WittTwoExteriorLiftMaps.zeroComplex p k A') := by
  let := residueRestrictionAlgebra p k β
  let := residueTower p k β
  exact {
    f q := ModuleCat.ofHom
      (X := (WittTwoExteriorLiftMaps.zeroComplex p k A).X q)
      (Y := (ModuleCat.restrictScalars
        (WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom).obj
          ((WittTwoExteriorLiftMaps.zeroComplex p k A').X q))
      (Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') q)
    comm' i j _ := by
      have hs : (WittTwoExteriorLiftMaps.zeroComplex p k A).d i j = 0 :=
        ZeroComplexNativeHomology.d_eq_zero
          (fun q => ModuleCat.of (B p k A) (⋀[B p k A]^q (KaehlerDifferential k (B p k A)))) i j
      have ht : (WittTwoExteriorLiftMaps.zeroComplex p k A').d i j = 0 :=
        ZeroComplexNativeHomology.d_eq_zero
          (fun q => ModuleCat.of (B p k A') (⋀[B p k A']^q (KaehlerDifferential k (B p k A')))) i j
      simp only [Functor.mapHomologicalComplex_obj_d, hs, ht, Functor.map_zero]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro w
      exact (map_zero (Char0.canonicalDifferentialLinearMap
        (k := k) (R := B p k A) (A := B p k A') j)).symm }

omit [CharP k p] [PerfectRing k p] in
/-- EVERY source component retains EXACTLY its SAME original native canonical form value. -/
theorem zeroComplexMap_f_apply (β : A →ₐ[WittTwo.Ring p k] A') (q : ℕ)
    (w : (WittTwoExteriorLiftMaps.zeroComplex p k A).X q) :
    letI := residueRestrictionAlgebra p k β
    letI := residueTower p k β
    (zeroComplexMap p k β).f q w =
      Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') q w := rfl

variable [Algebra.Smooth (WittTwo.Ring p k) A] [Algebra.Smooth (WittTwo.Ring p k) A']
variable (β : A →ₐ[WittTwo.Ring p k] A')
variable (f g : WittTwoLiftDifference.Lift p k A) (f' g' : WittTwoLiftDifference.Lift p k A')
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hf' : ∀ t, algebraMap A' (B p k A') (f' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hg' : ∀ t, algebraMap A' (B p k A') (g' t) = WittTwoRelativeLift.residueFrobenius p k A' t)
variable (hff' : ∀ t, β (f t) = f' (WittTwoLiftDifferenceNaturality.twistMap p k β t))
variable (hgg' : ∀ t, β (g t) = g' (WittTwoLiftDifferenceNaturality.twistMap p k β t))
variable {n m : ℕ} (v : Fin n → B p k A) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (v' : Fin m → B p k A') (hv' : (MvPolynomial.aeval (R := k) v').toRingHom.Etale)
include hff' hgg'

/-- EVERY original form has the actual original canonical degree-one restriction square. -/
theorem onePrimitive_naturality (w : (WittTwoExteriorLiftMaps.zeroComplex p k A).X 1) :
    letI := residueRestrictionAlgebra p k β
    letI := residueTower p k β
    Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') 0
      (WittTwoCanonicalOneHomotopy.onePrimitive p k A f g hf hg v hv w) =
    WittTwoCanonicalOneHomotopy.onePrimitive p k A' f' g' hf' hg' v' hv'
      (Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') 1 w) := by
  let := residueRestrictionAlgebra p k β
  let := residueTower p k β
  have hK (z : KaehlerDifferential k (B p k A)) :
      KaehlerDifferential.map k k (B p k A) (B p k A') z =
        WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β z := rfl
  have hc : Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') 1 w =
      (exteriorPower.oneEquiv (B p k A') (KaehlerDifferential k (B p k A'))).symm
        (WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β
          (exteriorPower.oneEquiv (B p k A) (KaehlerDifferential k (B p k A)) w)) := by
    have he := canonicalOne (R := k) (C := B p k A) (D := B p k A')
      (exteriorPower.oneEquiv (B p k A) (KaehlerDifferential k (B p k A)) w)
    exact (congrArg (Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') 1)
      ((exteriorPower.oneEquiv (B p k A) (KaehlerDifferential k (B p k A))).symm_apply_apply w)).symm.trans
        (he.trans (congrArg (exteriorPower.oneEquiv (B p k A') (KaehlerDifferential k (B p k A'))).symm (hK _)))
  have hA := congrArg (Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') 0)
    (WittTwoCanonicalOneHomotopy.onePrimitive_value p k A f g hf hg v hv w)
  have hB := canonicalZero (R := k) (C := B p k A) (D := B p k A')
    (WittTwoOriginalCotangentMaps.difference p k A f g hf hg
      (exteriorPower.oneEquiv (B p k A) (KaehlerDifferential k (B p k A)) w))
  have hC := congrArg (exteriorPower.oneEquiv (B p k A') (KaehlerDifferential k (B p k A'))) hc
  have hC' : exteriorPower.oneEquiv (B p k A') (KaehlerDifferential k (B p k A'))
      (Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') 1 w) =
    WittTwoOriginalDifferenceNaturality.residueCotangentMap p k β
      (exteriorPower.oneEquiv (B p k A) (KaehlerDifferential k (B p k A)) w) :=
    hC.trans ((exteriorPower.oneEquiv (B p k A') (KaehlerDifferential k (B p k A'))).apply_symm_apply _)
  have hN := WittTwoOriginalDifferenceNaturality.difference_naturality
    p k β f g f' g' hf hg hf' hg' hff' hgg'
      (exteriorPower.oneEquiv (B p k A) (KaehlerDifferential k (B p k A)) w)
  have hN' := hN.trans (congrArg (WittTwoOriginalCotangentMaps.difference p k A' f' g' hf' hg') hC'.symm)
  have hD := congrArg (exteriorPower.zeroEquiv (B p k A') (KaehlerDifferential k (B p k A'))).symm hN'
  have hE := WittTwoCanonicalOneHomotopy.onePrimitive_value p k A' f' g' hf' hg' v' hv'
    (Char0.canonicalDifferentialLinearMap (k := k) (R := B p k A) (A := B p k A') 1 w)
  exact hA.trans (hB.trans (hD.trans hE.symm))

/-- The SAME original canonical degree-one restriction square is a genuine native module-map identity. -/
theorem native_onePrimitive_square :
    letI := residueRestrictionAlgebra p k β
    letI := residueTower p k β
    WittTwoCanonicalOneHomotopy.onePrimitive p k A f g hf hg v hv ≫
      Cartier.EtaleAlgebraFrobeniusNaturality.formMap
        (k := k) (A := B p k A) (B := B p k A') p 0 =
    (zeroComplexMap p k β).f 1 ≫
      (ModuleCat.restrictScalars (WittTwoAlgebraDivisionNaturality.residueMap p k β).toRingHom).map
        (WittTwoCanonicalOneHomotopy.onePrimitive p k A' f' g' hf' hg' v' hv') := by
  let := residueRestrictionAlgebra p k β
  let := residueTower p k β
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact onePrimitive_naturality p k β f g f' g' hf hg hf' hg' hff' hgg' v hv v' hv' w

end EnvelopeProperty.DeligneIllusie.WittTwoNativeOneRestriction
