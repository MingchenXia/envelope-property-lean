import EnvelopeProperty.DeligneIllusie.WittTwoLiftCochainHomotopy

/-! # The SAME original canonical native degree-one homotopy has its true additive cocycle -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoCanonicalOneHomotopy
open CategoryTheory
open scoped TensorProduct Classical
universe u

private def nativeOne {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (F : R →+* R) (h : M →ₛₗ[F] R) : (⋀[R]^1 M) →ₛₗ[F] (⋀[R]^0 M) where
  toFun w := (exteriorPower.zeroEquiv R M).symm (h (exteriorPower.oneEquiv R M w))
  map_add' w z := by rw [map_add, map_add, map_add]
  map_smul' a w := by rw [map_smul, LinearMap.map_smulₛₗ, map_smul]

private def nativeRestrictedMap {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : R →+* R) (h : M →ₛₗ[F] N) :
    ModuleCat.of R M ⟶ (ModuleCat.restrictScalars F).obj (ModuleCat.of R N) := by
  let Y := (ModuleCat.restrictScalars F).obj (ModuleCat.of R N)
  letI := Y.isModule
  exact ModuleCat.ofHom (X := ModuleCat.of R M) (Y := Y)
    { toFun := h, map_add' := h.map_add, map_smul' := h.map_smulₛₗ }

private theorem nativeExteriorOne {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (F : R →+* R) (φ : M →ₛₗ[F] M) (w : ⋀[R]^1 M) :
    exteriorPower.oneEquiv R M (CanonicalGeometry.exteriorSemilinearMap F φ 1 w) =
      φ (exteriorPower.oneEquiv R M w) := by
  obtain ⟨m, rfl⟩ := (exteriorPower.oneEquiv R M).symm.surjective w
  rw [exteriorPower.oneEquiv_symm_apply, CanonicalGeometry.exteriorSemilinearMap_ιMulti,
    exteriorPower.oneEquiv_ιMulti, exteriorPower.oneEquiv_ιMulti]
  rfl

private theorem nativeOneEquation (p : ℕ) [Fact p.Prime]
    {k B : Type u} [Field k] [CharP k p] [CommRing B] [Algebra k B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (φ ψ : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] KaehlerDifferential k B)
    (h : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] B)
    (he : ∀ m, φ m - ψ m = KaehlerDifferential.D k B (h m))
    (w : ⋀[B]^1 (KaehlerDifferential k B)) :
    Cartier.EtaleDeRham.differential v hv 0 (nativeOne _ h w) =
      CanonicalGeometry.exteriorSemilinearMap _ φ 1 w -
        CanonicalGeometry.exteriorSemilinearMap _ ψ 1 w := by
  apply (exteriorPower.oneEquiv B (KaehlerDifferential k B)).injective
  change exteriorPower.oneEquiv B (KaehlerDifferential k B)
    (Cartier.EtaleDeRham.differential v hv 0
      ((exteriorPower.zeroEquiv B (KaehlerDifferential k B)).symm
        (h (exteriorPower.oneEquiv B (KaehlerDifferential k B) w)))) = _
  rw [Cartier.EtaleDeRham.differential_zero, map_sub, nativeExteriorOne, nativeExteriorOne]
  exact (he _).symm

private theorem nativeOneMorphismEquation (p : ℕ) [Fact p.Prime]
    {k B : Type u} [Field k] [CharP k p] [CommRing B] [Algebra k B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (φ ψ : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] KaehlerDifferential k B)
    (h : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] B)
    (he : ∀ m, φ m - ψ m = KaehlerDifferential.D k B (h m)) :
    nativeRestrictedMap _ (nativeOne _ h) ≫ Cartier.EtaleAlgebraFrobeniusComplex.differential v hv p 0 =
      nativeRestrictedMap _ (CanonicalGeometry.exteriorSemilinearMap _ φ 1) -
        nativeRestrictedMap _ (CanonicalGeometry.exteriorSemilinearMap _ ψ 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact nativeOneEquation p v hv φ ψ h he

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
variable (f g : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable (hg : ∀ t, algebraMap A (B p k A) (g t) = WittTwoRelativeLift.residueFrobenius p k A t)

/-- The SAME actual original residue cotangent difference is zero for equal actual lifts. -/
theorem originalDifference_self (w : N p k A) :
    WittTwoOriginalCotangentMaps.difference p k A f f hf hf w = 0 := by
  rw [WittTwoOriginalCotangentMaps.difference_apply]
  obtain ⟨z, hz⟩ := WittTwoSourceResidue.sourceReduction_surjective p k A
    (WittTwoOriginalCotangentMaps.sourceTransport p k A w)
  rw [← hz, WittTwoLiftHomotopy.residueDifferenceLinear_reduction,
    WittTwoLiftDifference.differenceLinear_self]
  rfl

/-- EVERY original cotangent form satisfies the genuine canonical three-lift cocycle. -/
theorem originalDifference_cocycle (h : WittTwoLiftDifference.Lift p k A)
    (hh : ∀ t, algebraMap A (B p k A) (h t) = WittTwoRelativeLift.residueFrobenius p k A t)
    (w : N p k A) :
    WittTwoOriginalCotangentMaps.difference p k A f h hf hh w =
      WittTwoOriginalCotangentMaps.difference p k A f g hf hg w +
        WittTwoOriginalCotangentMaps.difference p k A g h hg hh w := by
  rw [WittTwoOriginalCotangentMaps.difference_apply,
    WittTwoOriginalCotangentMaps.difference_apply, WittTwoOriginalCotangentMaps.difference_apply]
  obtain ⟨z, hz⟩ := WittTwoSourceResidue.sourceReduction_surjective p k A
    (WittTwoOriginalCotangentMaps.sourceTransport p k A w)
  rw [← hz, WittTwoLiftHomotopy.residueDifferenceLinear_reduction,
    WittTwoLiftHomotopy.residueDifferenceLinear_reduction,
    WittTwoLiftHomotopy.residueDifferenceLinear_reduction]
  exact LinearMap.congr_fun (WittTwoLiftDifference.differenceLinear_cocycle p k A f g hf hg h hh) z

variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
private abbrev D := Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p

/-- The canonical SAME original degree-one difference in the actual native complex modules. -/
def onePrimitive : (WittTwoExteriorLiftMaps.zeroComplex p k A).X 1 ⟶ (D p k A v hv).X 0 :=
  nativeRestrictedMap _ (nativeOne _ (WittTwoOriginalCotangentMaps.difference p k A f g hf hg))

/-- EVERY original form retains exactly its genuine canonical difference coefficient. -/
theorem onePrimitive_value (w : ⋀[B p k A]^1 (N p k A)) :
    onePrimitive p k A f g hf hg v hv w =
      (exteriorPower.zeroEquiv (B p k A) (N p k A)).symm
        (WittTwoOriginalCotangentMaps.difference p k A f g hf hg
          (exteriorPower.oneEquiv (B p k A) (N p k A) w)) := rfl

/-- Its SAME actual target differential is EXACTLY the whole original degree-one map difference. -/
theorem onePrimitive_d : onePrimitive p k A f g hf hg v hv ≫ (D p k A v hv).d 0 1 =
    (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f 1 -
      (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f 1 := by
  have hφ : (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv).f 1 =
      nativeRestrictedMap _ (CanonicalGeometry.exteriorSemilinearMap _
        (WittTwoOriginalCotangentMaps.divided p k A f hf) 1) := rfl
  have hψ : (WittTwoExteriorLiftMaps.complexMap p k A g hg v hv).f 1 =
      nativeRestrictedMap _ (CanonicalGeometry.exteriorSemilinearMap _
        (WittTwoOriginalCotangentMaps.divided p k A g hg) 1) := rfl
  have hd : (D p k A v hv).d 0 1 =
      Cartier.EtaleAlgebraFrobeniusComplex.differential v hv p 0 := by
    exact CochainComplex.of_d
      (Cartier.EtaleAlgebraFrobeniusComplex.formModule (k := k) (B := B p k A) p)
      (Cartier.EtaleAlgebraFrobeniusComplex.differential v hv p) 0
  rw [hφ, hψ, hd]
  unfold onePrimitive
  exact nativeOneMorphismEquation p (B := B p k A) (k := k) v hv
    (WittTwoOriginalCotangentMaps.divided p k A f hf)
    (WittTwoOriginalCotangentMaps.divided p k A g hg)
    (WittTwoOriginalCotangentMaps.difference p k A f g hf hg)
    (WittTwoOriginalCotangentMaps.divided_sub p k A f g hf hg)

/-- Equal actual lifts have zero SAME canonical native homotopy component. -/
theorem onePrimitive_self : onePrimitive p k A f f hf hf v hv = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change (exteriorPower.zeroEquiv (B p k A) (N p k A)).symm
    (WittTwoOriginalCotangentMaps.difference p k A f f hf hf
      (exteriorPower.oneEquiv (B p k A) (N p k A) w)) = 0
  rw [originalDifference_self, map_zero]

/-- The SAME actual native components have the genuine triple-lift additive cocycle. -/
theorem onePrimitive_cocycle (h : WittTwoLiftDifference.Lift p k A)
    (hh : ∀ t, algebraMap A (B p k A) (h t) = WittTwoRelativeLift.residueFrobenius p k A t) :
    onePrimitive p k A f h hf hh v hv =
      onePrimitive p k A f g hf hg v hv + onePrimitive p k A g h hg hh v hv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change (exteriorPower.zeroEquiv (B p k A) (N p k A)).symm
      (WittTwoOriginalCotangentMaps.difference p k A f h hf hh
        (exteriorPower.oneEquiv (B p k A) (N p k A) w)) =
    (exteriorPower.zeroEquiv (B p k A) (N p k A)).symm
      (WittTwoOriginalCotangentMaps.difference p k A f g hf hg
        (exteriorPower.oneEquiv (B p k A) (N p k A) w)) +
    (exteriorPower.zeroEquiv (B p k A) (N p k A)).symm
      (WittTwoOriginalCotangentMaps.difference p k A g h hg hh
        (exteriorPower.oneEquiv (B p k A) (N p k A) w))
  rw [originalDifference_cocycle p k A f g hf hg h hh, map_add]

end EnvelopeProperty.DeligneIllusie.WittTwoCanonicalOneHomotopy
