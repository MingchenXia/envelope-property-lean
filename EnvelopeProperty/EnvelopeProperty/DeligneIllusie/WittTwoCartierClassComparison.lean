import EnvelopeProperty.DeligneIllusie.WittTwoCoordinateValues
import EnvelopeProperty.Cartier.EtaleNativeCycleClass
import EnvelopeProperty.DeligneIllusie.WittTwoNativeCycleClasses
import EnvelopeProperty.Cartier.EtaleAlgebraCartierIsomorphism

/-! # The SAME original divided cochain map has SAME actual native inverse Cartier classes -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoCartierClassComparison
open CategoryTheory
open scoped TensorProduct
universe u

private theorem nativeHomogeneous_ιMulti {B M : Type u} [CommRing B] [AddCommGroup M] [Module B M]
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (g : M →ₗ[B] Cartier.ExteriorFrobeniusLift.forms B M p 1) (q : ℕ) (t : Fin q → M) :
    (show ⋀[B]^q M from Cartier.ExteriorFrobeniusLift.homogeneous B M p g q
      (exteriorPower.ιMulti B q t)) =
      exteriorPower.ιMulti B q (fun i => exteriorPower.oneEquiv B M (g (t i))) := by
  have hι (m : M) : Cartier.ExteriorFrobeniusLift.inclusion B M p 1 (g m) =
      ExteriorAlgebra.ι B (exteriorPower.oneEquiv B M (g m)) := by
    have h := congrArg (fun w : ⋀[B]^1 M => (w : ExteriorAlgebra B M))
      ((exteriorPower.oneEquiv B M).symm_apply_apply (g m))
    rw [exteriorPower.oneEquiv_symm_apply] at h
    change ExteriorAlgebra.ιMulti B 1 (fun _ => exteriorPower.oneEquiv B M (g m)) = _ at h
    rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one] at h
    exact h.symm
  apply Subtype.ext
  change Cartier.ExteriorFrobeniusLift.lift B M p g (ExteriorAlgebra.ιMulti B q t) =
    ExteriorAlgebra.ιMulti B q (fun i => exteriorPower.oneEquiv B M (g (t i)))
  induction q with
  | zero => rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, ExteriorAlgebra.ιMulti_zero_apply]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, map_mul, Cartier.ExteriorFrobeniusLift.lift_ι,
      hι, ih, ExteriorAlgebra.ιMulti_succ_apply]
    rfl

private def nativeRepresentativeMap {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p] {n : ℕ}
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (g : KaehlerDifferential k B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1)
    (q : ℕ) : (⋀[B]^q (KaehlerDifferential k B)) →ₛₗ[Cartier.AlgebraFrobenius.map k B p]
      (⋀[B]^q (KaehlerDifferential k B)) where
  toFun w := Cartier.EtaleClosedExteriorLift.representative v hv p g q w
  map_add' w z := (Cartier.EtaleClosedExteriorLift.representative v hv p g q).map_add w z
  map_smul' b w := by
    rw [Cartier.AlgebraFrobenius.map_apply]
    exact (Cartier.EtaleClosedExteriorLift.representative v hv p g q).map_smul b w

private theorem nativeRepresentative_eq {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP B p] {n : ℕ}
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (g : KaehlerDifferential k B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1)
    (φ : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] KaehlerDifferential k B)
    (hg : ∀ m, (g m).val =
      (show Cartier.EtaleDeRham.frobeniusModule (R := k) (B := B) p 1 from
        (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ m)))
    (q : ℕ) (w : ⋀[B]^q (KaehlerDifferential k B)) :
    nativeRepresentativeMap p v hv g q w =
      CanonicalGeometry.exteriorSemilinearMap (Cartier.AlgebraFrobenius.map k B p) φ q w := by
  have hw : w ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B q (M := KaehlerDifferential k B))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, rfl⟩ := hw
    rw [CanonicalGeometry.exteriorSemilinearMap_ιMulti]
    change (show ⋀[B]^q (KaehlerDifferential k B) from
      Cartier.ExteriorFrobeniusLift.homogeneous B (KaehlerDifferential k B) p
        (Cartier.EtaleClosedExteriorLift.oneFormMap v hv p g) q (exteriorPower.ιMulti B q t)) = _
    rw [nativeHomogeneous_ιMulti]
    congr 1
    funext j
    exact (congrArg (exteriorPower.oneEquiv B (KaehlerDifferential k B)) (hg (t j))).trans
      ((exteriorPower.oneEquiv B (KaehlerDifferential k B)).apply_symm_apply (φ (t j)))
  | zero => rw [map_zero, map_zero]
  | add w z _ _ hw hz => rw [map_add, map_add, hw, hz]
  | smul b w _ hw =>
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hw]

private theorem nativeClosedClass_value {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (g : KaehlerDifferential R B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1)
    (q : ℕ) (w : ⋀[B]^q (KaehlerDifferential R B)) :
    Cartier.EtaleClosedExteriorLift.nativeClassMap v hv p g q w =
      ModuleComplexNativeCycleClasses.cycleClass (Cartier.EtaleDeRham.frobeniusComplex v hv p) q
        (Cartier.EtaleNativeCycleClass.nativeCycle v hv p q
          (Cartier.EtaleClosedExteriorLift.cycleRepresentative v hv p g q w)) :=
  Cartier.EtaleNativeCycleClass.nativeCycleClass_eq_native v hv p q _

private def nativeOneCycleMap (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {B : Type u} [CommRing B] [Algebra k B] [CharP B p] {n : ℕ}
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (φ : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] KaehlerDifferential k B)
    (hφ : ∀ w, Cartier.EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ w)) = 0) :
    KaehlerDifferential k B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1 where
  toFun w := ⟨(exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ w), hφ w⟩
  map_add' w z := Subtype.ext
    ((congrArg (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ.map_add w z)).trans
      ((exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm.map_add (φ w) (φ z)))
  map_smul' b w := by
    apply Subtype.ext
    change (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ (b • w)) =
      b^p • (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ w)
    rw [LinearMap.map_smulₛₗ, Cartier.AlgebraFrobenius.map_apply, map_smul]

private theorem nativeClass_eq_of_boundary {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (z w : Cartier.EtaleCohomologyProducts.cycles v hv p 1)
    (a : Cartier.EtaleDeRham.frobeniusModule (R := R) (B := B) p 0)
    (h : z - w = Cartier.EtaleCohomologyProducts.toCycles v hv p 0 a) :
    Cartier.EtaleCohomologyProducts.nativeCycleClass v hv p 1 z =
      Cartier.EtaleCohomologyProducts.nativeCycleClass v hv p 1 w := by
  have hm : z - w ∈ Cartier.EtaleCohomologyProducts.boundaries v hv p 1 := by
    change z - w ∈ LinearMap.range (Cartier.EtaleCohomologyProducts.toCycles v hv p 0)
    exact ⟨a, h.symm⟩
  exact congrArg (Cartier.EtaleCohomologyProducts.cohomologyIso v hv p 1).inv.hom
    ((Submodule.Quotient.eq (Cartier.EtaleCohomologyProducts.boundaries v hv p 1)).mpr hm)

private def nativeOneClassMap {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (g : KaehlerDifferential R B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1) :
    KaehlerDifferential R B →ₗ[B] (Cartier.EtaleDeRham.frobeniusComplex v hv p).homology 1 :=
  (Cartier.EtaleCohomologyProducts.nativeCycleClass v hv p 1).comp g

private theorem nativeOneClassMap_D_of_boundary {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (g : KaehlerDifferential R B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1)
    (c z : B)
    (h : g (KaehlerDifferential.D R B c) -
        (show Cartier.EtaleCohomologyProducts.cycles v hv p 1 from
          Cartier.IntrinsicCartierOne.generatorCycle v hv p c) =
      Cartier.EtaleCohomologyProducts.toCycles v hv p 0
        ((exteriorPower.zeroEquiv B (KaehlerDifferential R B)).symm z)) :
    nativeOneClassMap v hv p g (KaehlerDifferential.D R B c) =
      (Cartier.EtaleCartierCycleRepresentatives.oneHomologyIso v hv p).hom.hom
        (Cartier.IntrinsicCartierOne.generatorClass v hv p c) := by
  exact (nativeClass_eq_of_boundary v hv p _ _ _ h).trans
    (Cartier.EtaleCartierCycleRepresentatives.oneHomologyIso_cycleClass v hv p
      (Cartier.IntrinsicCartierOne.generatorCycle v hv p c)).symm

private theorem nativeExteriorClass_eq_of_one {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := R) v).toRingHom.Etale)
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (g : KaehlerDifferential R B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1)
    (hg : nativeOneClassMap v hv p g =
      (Cartier.EtaleCartierCycleRepresentatives.inverseCartier v hv p 1).comp
        (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm.toLinearMap) (q : ℕ) :
    Cartier.EtaleClosedExteriorLift.nativeClassMap v hv p g q =
      Cartier.EtaleCartierCycleRepresentatives.inverseCartier v hv p q := by
  apply Cartier.EtaleClosedExteriorLift.nativeClassMap_eq_of_one
  apply LinearMap.ext
  intro w
  let m := exteriorPower.oneEquiv B (KaehlerDifferential R B) w
  have he : (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm m = w :=
    (exteriorPower.oneEquiv B (KaehlerDifferential R B)).symm_apply_apply w
  rw [← he]
  have hc := Cartier.EtaleClosedExteriorLift.cycleRepresentative_one v hv p g m
  have hclass := congrArg (Cartier.EtaleCohomologyProducts.nativeCycleClass v hv p 1) hc
  exact hclass.trans (LinearMap.congr_fun hg m)

private def nativeOneData (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {B : Type u} [CommRing B] [Algebra k B] [CharP B p] {n : ℕ}
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (φ : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] KaehlerDifferential k B)
    (hφ : ∀ w, Cartier.EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ w)) = 0)
    (hD : ∀ c : B, ∃ z : B, φ (KaehlerDifferential.D k B c) =
      c^(p-1) • KaehlerDifferential.D k B c + KaehlerDifferential.D k B z) :
    {g : KaehlerDifferential k B →ₗ[B] Cartier.EtaleCohomologyProducts.cycles v hv p 1 //
      nativeOneClassMap v hv p g =
        (Cartier.EtaleCartierCycleRepresentatives.inverseCartier v hv p 1).comp
          (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm.toLinearMap} := by
  refine ⟨nativeOneCycleMap p k v hv φ hφ, ?_⟩
  apply (Char0.etaleDifferentialBasis v hv).ext
  intro i
  rw [Char0.etaleDifferentialBasis_apply]
  obtain ⟨z, hz⟩ := hD (v i)
  have hb : nativeOneCycleMap p k v hv φ hφ (KaehlerDifferential.D k B (v i)) -
        (show Cartier.EtaleCohomologyProducts.cycles v hv p 1 from
          Cartier.IntrinsicCartierOne.generatorCycle v hv p (v i)) =
      Cartier.EtaleCohomologyProducts.toCycles v hv p 0
        ((exteriorPower.zeroEquiv B (KaehlerDifferential k B)).symm z) := by
    apply Subtype.ext
    change (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm
        (φ (KaehlerDifferential.D k B (v i))) -
        Cartier.IntrinsicCartierOne.generatorForm (R := k) p (v i) =
      Cartier.EtaleDeRham.differential v hv 0
        ((exteriorPower.zeroEquiv B (KaehlerDifferential k B)).symm z)
    apply (exteriorPower.oneEquiv B (KaehlerDifferential k B)).injective
    rw [map_sub, LinearEquiv.apply_symm_apply, Cartier.IntrinsicCartierOne.generatorForm,
      map_smul, LinearEquiv.apply_symm_apply, Cartier.EtaleDeRham.differential_zero, hz]
    abel
  exact (nativeOneClassMap_D_of_boundary v hv p _ _ z hb).trans
    (Cartier.EtaleCartierCycleRepresentatives.inverseCartier_D v hv p (v i)).symm

private theorem nativeClassCartier {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] {n : ℕ}
    (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (φ : KaehlerDifferential k B →ₛₗ[Cartier.AlgebraFrobenius.map k B p] KaehlerDifferential k B)
    (hφ : ∀ w, Cartier.EtaleDeRham.differential v hv 1
      ((exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ w)) = 0)
    (hD : ∀ c : B, ∃ z : B, φ (KaehlerDifferential.D k B c) =
      c^(p-1) • KaehlerDifferential.D k B c + KaehlerDifferential.D k B z)
    (q : ℕ) (w : ⋀[B]^q (KaehlerDifferential k B))
    (z : LinearMap.ker ((Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p).sc q).g.hom)
    (hz : z.val = CanonicalGeometry.exteriorSemilinearMap (Cartier.AlgebraFrobenius.map k B p) φ q w) :
    ModuleComplexNativeCycleClasses.cycleClass (Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p) q z =
      Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier v hv p q w := by
  by_cases h : Nontrivial B
  · let := h
    let : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
    let g := (nativeOneData p k v hv φ hφ hD).val
    have hg (m : KaehlerDifferential k B) : (g m).val =
        (show Cartier.EtaleDeRham.frobeniusModule (R := k) (B := B) p 1 from
          (exteriorPower.oneEquiv B (KaehlerDifferential k B)).symm (φ m)) := rfl
    have hc := nativeExteriorClass_eq_of_one v hv p g (nativeOneData p k v hv φ hφ hD).property q
    apply (Cartier.EtaleAlgebraCartierIsomorphism.nativeHomologyIso v hv p q).toLinearEquiv.injective
    have hclass : (Cartier.EtaleAlgebraCartierIsomorphism.nativeHomologyIso v hv p q).hom
        (ModuleComplexNativeCycleClasses.cycleClass (Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p) q z) =
        Cartier.EtaleClosedExteriorLift.nativeClassMap v hv p g q w := by
      rw [nativeClosedClass_value]
      apply ModuleComplexNativeCycleClasses.homologyMap_cycleClass
      change (show ⋀[B]^q (KaehlerDifferential k B) from z.val) =
        (show ⋀[B]^q (KaehlerDifferential k B) from
          Cartier.EtaleClosedExteriorLift.representative v hv p g q w)
      exact hz.trans (nativeRepresentative_eq p v hv g φ hg q w).symm
    exact hclass.trans ((LinearMap.congr_fun hc w).trans
      (Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier_native v hv p q w).symm)
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    let : Subsingleton ((Cartier.EtaleAlgebraFrobeniusComplex.complex v hv p).homology q) :=
      Module.subsingleton B _
    exact Subsingleton.elim _ _

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
variable (f : WittTwoLiftDifference.Lift p k A)
variable (hf : ∀ t, algebraMap A (B p k A) (f t) = WittTwoRelativeLift.residueFrobenius p k A t)
variable {n : ℕ} (v : Fin n → B p k A)
  (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)

/-- SAME actual original divided native class map equals SAME canonical inverse Cartier ALLq, ALLalgebras. -/
theorem classMap_eq_inverseCartier (q : ℕ) : WittTwoNativeCycleClasses.classMap p k A f hf v hv q =
    (Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier v hv p q).hom := by
  apply LinearMap.ext
  intro w
  refine (WittTwoNativeCycleClasses.classMap_value p k A f hf v hv q w).trans ?_
  apply nativeClassCartier p v hv (WittTwoOriginalCotangentMaps.divided p k A f hf)
  · intro m
    rw [← WittTwoOriginalCotangentMaps.closedDerivative_apply p k A v hv
      (WittTwoOriginalCotangentMaps.divided p k A f hf m)]
    exact WittTwoOriginalCotangentMaps.divided_closed p k A f hf v hv m
  · exact WittTwoCoordinateValues.divided_universalD p k A f hf
  · rw [WittTwoNativeCycleClasses.cycleMap_value]
    rfl

/-- SAME actual divided native class map is bijective EVERYq on EVERY original algebra, including zero. -/
theorem classMap_bijective (q : ℕ) : Function.Bijective (WittTwoNativeCycleClasses.classMap p k A f hf v hv q) := by
  rw [classMap_eq_inverseCartier]
  exact Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier_bijective v hv p q

/-- The ACTUAL native homology functor of SAME original W2 cochain map has SAME canonical Cartier value. -/
theorem homologyMap_sourceClass (q : ℕ) (w : ⋀[B p k A]^q (N p k A)) :
    (HomologicalComplex.homologyMap (WittTwoExteriorLiftMaps.complexMap p k A f hf v hv) q).hom
      (ModuleComplexNativeCycleClasses.cycleClass (WittTwoExteriorLiftMaps.zeroComplex p k A) q
        (WittTwoNativeCycleClasses.sourceCycle p k A q w)) =
      Cartier.EtaleAlgebraCartierIsomorphism.inverseCartier v hv p q w := by
  rw [WittTwoNativeCycleClasses.homologyMap_sourceClass]
  exact LinearMap.congr_fun (classMap_eq_inverseCartier p k A f hf v hv q) w
end EnvelopeProperty.DeligneIllusie.WittTwoCartierClassComparison
