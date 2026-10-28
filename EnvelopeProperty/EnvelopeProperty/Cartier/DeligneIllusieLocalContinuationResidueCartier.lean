import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationTrueTwistDividedOneForm
import EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCartierComparison
import EnvelopeProperty.Cartier.RelativeCartierContinuationNativeAllAlgebraCartier
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierOneFunctions
import EnvelopeProperty.Cartier.RelativeCartierContinuationEtaleCartierMultiplicativity
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.QuasiIso

/-! # Canonical divided forms from the actual residue etale coordinates

The genuine model reductions produce the coordinate correction internally.
The lifting algebra has no supplied etale tuple, and the residue field need
not be perfect. All maps retain the original geometric relative-Frobenius action.
-/

noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationResidueCartier

open CategoryTheory FrobeniusLiftDifference

universe u v
variable {K B C S : Type u} {R : Type v}
  [Field K] [CommRing B] [CommRing C] [CommRing R] [CommRing S]
  [Algebra K B] [Algebra C K] [Algebra C R] [Algebra C S]
  (p : ℕ) [Fact p.Prime] [CharP K p]

private abbrev coefficientAlgebra : Algebra K (RelativeFrobenius.twist (algebraMap K B) p) :=
  (RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.toAlgebra
attribute [local instance] coefficientAlgebra

private abbrev coefficientCAlgebra : Algebra C (RelativeFrobenius.twist (algebraMap K B) p) :=
  ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom.comp (algebraMap C K)).toAlgebra
attribute [local instance] coefficientCAlgebra

private instance coefficientTower : IsScalarTower C K (RelativeFrobenius.twist (algebraMap K B) p) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

private abbrev residueCAlgebra : Algebra C B :=
  ((algebraMap K B).comp (algebraMap C K)).toAlgebra

private theorem residueCoefficientTower :
    letI : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
    IsScalarTower C K B := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable [Algebra R (RelativeFrobenius.twist (algebraMap K B) p)]
  [IsScalarTower C R (RelativeFrobenius.twist (algebraMap K B) p)]
  (c : Reduction p C K) (a : Reduction p R (RelativeFrobenius.twist (algebraMap K B) p))
  (b : FlatReduction p S B) (F : R →ₐ[C] S)
  (hF : b.map.comp F.toRingHom =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom.comp a.map)
  (ha : algebraMap R (RelativeFrobenius.twist (algebraMap K B) p) = a.map)
  (hc : algebraMap C K = c.map)

include hF ha in
private theorem target_base (x : C) :
    b.map (algebraMap C S x) = algebraMap K B (algebraMap C K x) := by
  rw [← F.commutes x]
  have h := RingHom.congr_fun hF (algebraMap C R x)
  change b.map (F (algebraMap C R x)) =
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
      (a.map (algebraMap C R x)) at h
  rw [h, ← ha,
    ← IsScalarTower.algebraMap_apply C R (RelativeFrobenius.twist (algebraMap K B) p)]
  change (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
      ((RelativeFrobenius.coefficientMap (algebraMap K B) p).hom (algebraMap C K x)) = _
  exact congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of B => h.hom (algebraMap C K x))
    (SchemeRelativeFrobeniusAffineMap.coefficient_ringMap (algebraMap K B) p)

include hF ha in
private theorem targetTower :
    letI : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
    letI : Algebra S B := b.map.toAlgebra
    IsScalarTower C S B := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  let : Algebra S B := b.map.toAlgebra
  exact IsScalarTower.of_algebraMap_eq
    (fun x => (target_base p (a := a) (b := b) (F := F) hF ha x).symm)

variable [Algebra.FormallySmooth C S]

private theorem exists_function_correction (t : B) :
    ∃ (r : R) (x z : S),
      a.map r = (RelativeFrobenius.sourceMap (algebraMap K B) p).hom t ∧
      b.map x = t ∧ F r = x^p + (p : S)*z ∧
      (exteriorPower.oneEquiv B (KaehlerDifferential K B))
        (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc
          (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
            ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t))) =
        t^(p-1) • KaehlerDifferential.D K B t + KaehlerDifferential.D K B (b.map z) := by
  let : Algebra C B := residueCAlgebra (C := C) (K := K) (B := B)
  let : IsScalarTower C K B := residueCoefficientTower (C := C) (K := K) (B := B)
  let : Algebra S B := b.map.toAlgebra
  let : IsScalarTower C S B := targetTower p (a := a) (b := b) (F := F) hF ha
  obtain ⟨r, hr⟩ := a.surjective ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t)
  obtain ⟨x, hx⟩ := b.surjective t
  have hzero : b.map (F r-x^p) = 0 := by
    have h := RingHom.congr_fun hF r
    change b.map (F r) =
      (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom (a.map r) at h
    rw [map_sub, h, hr, SchemeRelativeFrobeniusAffineMap.source_ringMap_apply,
      map_pow, hx, sub_self]
  obtain ⟨z, hz⟩ := (b.toReduction.kernel_iff (F r-x^p)).mp hzero
  have hη := DeligneIllusieLocalContinuationCartierComparison.power_difference_divisor
    (C := C) x z (F r) hz
  have hξ := DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap_D_of_lift
    p c a b F hF ha hc r
    (x^(p-1) • KaehlerDifferential.D C S x + KaehlerDifferential.D C S z) hη
  refine ⟨r, x, z, hr, hx, (sub_eq_iff_eq_add.mp hz.symm).trans (add_comm _ _), ?_⟩
  rw [hr] at hξ
  refine hξ.trans ?_
  change DeligneIllusieLocalContinuationClosedness.reductionSemilinear
    (C := C) (K := K) (S := S) (B := B)
      (x^(p-1) • KaehlerDifferential.D C S x + KaehlerDifferential.D C S z) = _
  rw [map_add, map_smulₛₗ, DeligneIllusieLocalContinuationClosedness.reductionSemilinear_D,
    DeligneIllusieLocalContinuationClosedness.reductionSemilinear_D]
  change b.map (x^(p-1)) • KaehlerDifferential.D K B (b.map x) +
    KaehlerDifferential.D K B (b.map z) = _
  rw [map_pow, hx]

/-- The actual model reductions internally produce coordinate lifts and the correction
for the SAME canonical divided one-form map; no lifted etale tuple is supplied. -/
theorem exists_coordinate_correction {n : ℕ} (w : Fin n → B) (i : Fin n) :
    ∃ (r : R) (x z : S),
      a.map r = (RelativeFrobenius.sourceMap (algebraMap K B) p).hom (w i) ∧
      b.map x = w i ∧ F r = x^p + (p : S)*z ∧
      (exteriorPower.oneEquiv B (KaehlerDifferential K B))
        (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc
          (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
            ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (w i)))) =
        (w i)^(p-1) • KaehlerDifferential.D K B (w i) + KaehlerDifferential.D K B (b.map z) :=
  exists_function_correction p c a b F hF ha hc (w i)

variable {n : ℕ} (w : Fin n → B)
  (hw : (MvPolynomial.aeval (R := K) w).toRingHom.Etale)

private theorem oneFormMap_coordinate_closed (i : Fin n) :
    (SchemeRelativeFrobeniusAffineDeRham.differential w hw p 1).hom
      (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc
        (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
          ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (w i)))) = 0 := by
  obtain ⟨r, x, z, hr, hx, hz, hξ⟩ := exists_coordinate_correction p c a b F hF ha hc w i
  have hform : (show ⋀[B]^1 (KaehlerDifferential K B) from
      DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc
        (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
          ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (w i)))) =
      (w i)^(p-1) • (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B (w i)) +
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B (b.map z)) := by
    apply (exteriorPower.oneEquiv B (KaehlerDifferential K B)).injective
    simpa only [map_add, map_smul, LinearEquiv.apply_symm_apply] using hξ
  refine (congrArg (EtaleDeRham.differential w hw 1) hform).trans ?_
  rw [map_add, EtaleDifferentialLeibniz.differential_power_universalD,
    EtaleDifferentialLeibniz.differential_universalD, add_zero]
  rfl

/-- The residue etale tuple alone gives whole closedness for the original canonical xi.
This includes zero residue algebras and has no perfection or lifted-coordinate input. -/
theorem oneFormMap_closed
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (SchemeRelativeFrobeniusAffineDeRham.differential w hw p 1).hom
      (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω) = 0 := by
  let Ξ := DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc
  let d := (SchemeRelativeFrobeniusAffineDeRham.differential w hw p 1).hom
  have h : d.comp Ξ = 0 := by
    apply (RelativeEtaleCartierDomain.cotangentBasis w hw p).ext
    intro i
    rw [LinearMap.comp_apply, LinearMap.zero_apply, RelativeEtaleCartierDomain.cotangentBasis_D]
    exact oneFormMap_coordinate_closed p c a b F hF ha hc w hw i
  exact DFunLike.congr_fun h ω

private theorem target_d (q : ℕ) :
    (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).d q (q+1) =
      SchemeRelativeFrobeniusAffineDeRham.differential w hw p q :=
  CochainComplex.of_d _ _ q

private theorem target_square (q : ℕ) :
    SchemeRelativeFrobeniusAffineDeRham.differential w hw p q ≫
      SchemeRelativeFrobeniusAffineDeRham.differential w hw p (q+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact EtaleDeRham.differential_square w hw q ω

private def oneSource : CochainComplex (ModuleCat (RelativeFrobenius.twist (algebraMap K B) p)) ℕ :=
  (HomologicalComplex.single (ModuleCat (RelativeFrobenius.twist (algebraMap K B) p))
    (ComplexShape.up ℕ) 1).obj
      (ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
        (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))

private def oneCochainMap : oneSource (K := K) (B := B) p ⟶
    SchemeRelativeFrobeniusAffineDeRham.complex w hw p :=
  HomologicalComplex.mkHomFromSingle
    (K := SchemeRelativeFrobeniusAffineDeRham.complex w hw p) (j := 1)
    (A := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
    (ModuleCat.ofHom
      (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
        (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1)
      (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc))
    (fun j hj => by
      have hj' : 1+1 = j := hj
      subst j
      rw [target_d p w hw 1]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro ω
      exact oneFormMap_closed p c a b F hF ha hc w hw ω)

/-- The native degree-one class map is actual homology of the same canonical xi
as a genuine map out of its degree-one single source. -/
def oneFormClassMap :
    ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) ⟶
        (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).homology 1 :=
  (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 1
    (ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))).inv ≫
    HomologicalComplex.homologyMap (oneCochainMap p c a b F hF ha hc w hw) 1

private theorem singleClassMap_eq_liftCycles
    {A : Type u} [CommRing A] (q : ℕ) (M : ModuleCat A) (E : CochainComplex (ModuleCat A) ℕ)
    (φ : M ⟶ E.X q) (hφ : ∀ j, (ComplexShape.up ℕ).Rel q j → φ ≫ E.d q j = 0) :
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) q M).inv ≫
      HomologicalComplex.homologyMap (HomologicalComplex.mkHomFromSingle φ hφ) q =
        E.liftCycles φ (q+1) (by simp) (hφ (q+1) (by simp)) ≫ E.homologyπ q := by
  let H := HomologicalComplex.mkHomFromSingle φ hφ
  let e := HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℕ) q M
  have hcycles : HomologicalComplex.cyclesMap H q =
      e.hom ≫ E.liftCycles φ (q+1) (by simp) (hφ (q+1) (by simp)) := by
    apply (cancel_mono (E.iCycles q)).1
    rw [HomologicalComplex.cyclesMap_i, Category.assoc, HomologicalComplex.liftCycles_i]
    change ((HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) q).obj M).iCycles q ≫
        (HomologicalComplex.mkHomFromSingle φ hφ).f q = e.hom ≫ φ
    rw [HomologicalComplex.mkHomFromSingle_f]
    exact (Category.assoc _ _ _).symm
  apply (cancel_epi e.hom).1
  rw [← Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv,
    HomologicalComplex.homologyπ_naturality, hcycles, Category.assoc]

private def oneCycle
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    LinearMap.ker ((SchemeRelativeFrobeniusAffineDeRham.complex w hw p).sc 1).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle _ _ (target_square p w hw) 1
    ⟨DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω,
      oneFormMap_closed p c a b F hF ha hc w hw ω⟩

private theorem oneClass_eq_cycleClass
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (oneFormClassMap p c a b F hF ha hc w hw).hom ω =
      ModuleComplexNativeCycleClasses.cycleClass
        (SchemeRelativeFrobeniusAffineDeRham.complex w hw p) 1
        (oneCycle p c a b F hF ha hc w hw ω) := by
  let E := SchemeRelativeFrobeniusAffineDeRham.complex w hw p
  let φ : ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) ⟶ E.X 1 :=
    ModuleCat.ofHom
      (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
        (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
      (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1)
      (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc)
  have hφ : ∀ j, (ComplexShape.up ℕ).Rel 1 j → φ ≫ E.d 1 j = 0 := by
    intro j hj
    have hj' : 1+1 = j := hj
    subst j
    rw [target_d p w hw 1]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact oneFormMap_closed p c a b F hF ha hc w hw
  have hclass : oneFormClassMap p c a b F hF ha hc w hw =
      E.liftCycles φ 2 (by simp) (hφ 2 rfl) ≫ E.homologyπ 1 := by
    unfold oneFormClassMap oneCochainMap
    exact singleClassMap_eq_liftCycles 1 _ E φ hφ
  have hinc := congrArg
    (fun L : ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) ⟶ E.X 1 => L ω)
    (E.liftCycles_i φ 2 (by simp) (hφ 2 rfl))
  change E.iCycles 1 (E.liftCycles φ 2 (by simp) (hφ 2 rfl) ω) = φ ω at hinc
  have hc' := (E.sc 1).moduleCatCyclesIso_inv_iCycles_apply
    (oneCycle p c a b F hF ha hc w hw ω)
  change E.iCycles 1 ((E.sc 1).moduleCatCyclesIso.inv
    (oneCycle p c a b F hF ha hc w hw ω)) = φ ω at hc'
  have heq : E.liftCycles φ 2 (by simp) (hφ 2 rfl) ω =
      (E.sc 1).moduleCatCyclesIso.inv (oneCycle p c a b F hF ha hc w hw ω) := by
    apply (ModuleCat.mono_iff_injective (E.iCycles 1)).mp inferInstance
    exact hinc.trans hc'.symm
  have hh := congrArg
    (fun L : ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) ⟶ E.homology 1 => L ω)
    hclass
  exact hh.trans (congrArg (E.homologyπ 1) heq)

private theorem native_square [CharP B p] (q : ℕ) :
    RelativeEtaleDeRham.differential w hw p q ≫
      RelativeEtaleDeRham.differential w hw p (q+1) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact EtaleDeRham.differential_square w hw q ω

private def nativeOneCycle [CharP B p]
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    LinearMap.ker ((RelativeEtaleDeRham.complex w hw p).sc 1).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle _ _ (native_square p w hw) 1
    ⟨(show RelativeEtaleDeRham.formModule (R := K) (B := B) p 1 from
        DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω),
      oneFormMap_closed p c a b F hF ha hc w hw ω⟩

private theorem oneClass_comparison [CharP B p]
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p 1).hom
      ((oneFormClassMap p c a b F hF ha hc w hw).hom ω) =
      ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex w hw p) 1
        (nativeOneCycle p c a b F hF ha hc w hw ω) := by
  rw [oneClass_eq_cycleClass]
  exact ModuleComplexNativeCycleClasses.homologyMap_cycleClass
    (RelativeNativeAllAlgebraCartier.complexIso_native w hw p).hom 1
    (oneCycle p c a b F hF ha hc w hw ω)
    (nativeOneCycle p c a b F hF ha hc w hw ω)
    (RelativeNativeAllAlgebraCartier.complexIso_native_hom_f_apply w hw p 1 _)

private theorem nativeClass_of_boundary {A : Type u} [CommRing A]
    (E : CochainComplex (ModuleCat A) ℕ) (i j : ℕ)
    (z : LinearMap.ker (E.sc j).g.hom) (u : E.X i) (hzu : z.val = E.d i j u) :
    ModuleComplexNativeCycleClasses.cycleClass E j z = 0 := by
  have hc' : (E.sc j).moduleCatCyclesIso.inv z = E.toCycles i j u := by
    apply (ModuleCat.mono_iff_injective (E.iCycles j)).mp inferInstance
    have ht := congrArg (fun L : E.X i ⟶ E.X j => L u) (E.toCycles_i i j)
    change E.iCycles j (E.toCycles i j u) = E.d i j u at ht
    exact ((E.sc j).moduleCatCyclesIso_inv_iCycles_apply z).trans (hzu.trans ht.symm)
  have hz := congrArg (fun L : E.X i ⟶ E.homology j => L u) (E.toCycles_comp_homologyπ i j)
  change E.homologyπ j (E.toCycles i j u) = 0 at hz
  exact (congrArg (E.homologyπ j) hc').trans hz

private theorem nativeOneClass_D_source [CharP B p] (t : B) :
    ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex w hw p) 1
      (nativeOneCycle p c a b F hF ha hc w hw
        (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
          ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t))) =
      RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv w hw p
        (KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
          ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t)) := by
  let E := RelativeEtaleDeRham.complex w hw p
  let ω := KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
    ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom t)
  let zf := nativeOneCycle p c a b F hF ha hc w hw ω
  let zc := RelativeEtaleCartierOneFunctions.generatorCycle w hw p t
  obtain ⟨r, x, z, hr, hx, hz, hξ⟩ := exists_function_correction p c a b F hF ha hc t
  let u : E.X 0 := (exteriorPower.zeroEquiv B (KaehlerDifferential K B)).symm (b.map z)
  have hform : (show ⋀[B]^1 (KaehlerDifferential K B) from
      DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω) =
      t^(p-1) • (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B t) +
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B (b.map z)) := by
    apply (exteriorPower.oneEquiv B (KaehlerDifferential K B)).injective
    simpa only [map_add, map_smul, LinearEquiv.apply_symm_apply] using hξ
  have hsubform : (show ⋀[B]^1 (KaehlerDifferential K B) from
      DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω) -
      IntrinsicCartierOne.generatorForm (R := K) p t =
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B (b.map z)) := by
    refine (congrArg (fun η : ⋀[B]^1 (KaehlerDifferential K B) =>
      η-IntrinsicCartierOne.generatorForm (R := K) p t) hform).trans ?_
    unfold IntrinsicCartierOne.generatorForm
    abel
  have hd : (show ⋀[B]^1 (KaehlerDifferential K B) from E.d 0 1 u) =
      (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
        (KaehlerDifferential.D K B (b.map z)) :=
    DeligneIllusieLocalContinuationCartierComparison.native_differential_zero
      (p := p) w hw (b.map z)
  have hzu : (zf-zc).val = E.d 0 1 u := by
    exact (congrArg (fun η : ⋀[B]^1 (KaehlerDifferential K B) =>
      (show ⋀[B]^1 (KaehlerDifferential K B) from
        DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω)-η)
      (RelativeEtaleCartierOneFunctions.generatorCycle_val w hw p t)).trans
        (hsubform.trans hd.symm)
  have hzero := nativeClass_of_boundary E 0 1 (zf-zc) u hzu
  have hsub := (RelativeEtaleNativeClasses.nativeCycleClassLinear w hw p 1).map_sub zf zc
  change ModuleComplexNativeCycleClasses.cycleClass E 1 (zf-zc) =
    ModuleComplexNativeCycleClasses.cycleClass E 1 zf -
      ModuleComplexNativeCycleClasses.cycleClass E 1 zc at hsub
  exact (sub_eq_zero.mp (hsub.symm.trans hzero)).trans
    (RelativeEtaleCartierOneFunctions.inverseCartierOneEquiv_D_source w hw p t).symm

/-- Actual homology of the SAME canonical xi is the original native inverse Cartier map. -/
theorem oneFormClassMap_eq_inverseCartier :
    oneFormClassMap p c a b F hF ha hc w hw =
      ModuleCat.ofHom
        (X := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
          (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))
        (Y := ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
          (⋀[RelativeFrobenius.twist (algebraMap K B) p]^1
            (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p))))
        (exteriorPower.oneEquiv (RelativeFrobenius.twist (algebraMap K B) p)
          (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p))).symm.toLinearMap ≫
        (RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p 1).hom := by
  classical
  by_cases h : Nontrivial B
  · let := h
    let : CharP B p := charP_of_injective_algebraMap (algebraMap K B).injective p
    apply (cancel_mono (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p 1).hom).1
    rw [RelativeNativeAllAlgebraCartier.inverseCartierIso_eq_native]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply ModuleCat.hom_ext
    apply (RelativeEtaleCartierDomain.cotangentBasis w hw p).ext
    intro i
    rw [RelativeEtaleCartierDomain.cotangentBasis_D]
    exact (oneClass_comparison p c a b F hF ha hc w hw _).trans
      (nativeOneClass_D_source p c a b F hF ha hc w hw (w i))
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    exact (RelativeNativeAllAlgebraCartier.actualHomology_isZero w hw p 1).eq_of_tgt _ _

private abbrev sourceModule (q : ℕ) : ModuleCat (RelativeFrobenius.twist (algebraMap K B) p) :=
  ModuleCat.of (RelativeFrobenius.twist (algebraMap K B) p)
    (⋀[RelativeFrobenius.twist (algebraMap K B) p]^q
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))

private def sourceComplex : CochainComplex (ModuleCat (RelativeFrobenius.twist (algebraMap K B) p)) ℕ :=
  CochainComplex.of (sourceModule (K := K) (B := B) p) (fun _ => 0)
    (fun _ => by simp only [CategoryTheory.Limits.zero_comp])

private theorem source_d (i j : ℕ) : (sourceComplex (K := K) (B := B) p).d i j = 0 := by
  change CochainComplex.of.d (sourceModule (K := K) (B := B) p) (fun _ => 0) i j = 0
  unfold CochainComplex.of.d
  split_ifs <;> simp only [CategoryTheory.Limits.zero_comp]

private def sourceHomologyIso (q : ℕ) :
    (sourceComplex (K := K) (B := B) p).homology q ≅ sourceModule (K := K) (B := B) p q :=
  ((sourceComplex (K := K) (B := B) p).isoHomologyπ _ q rfl (source_d p _ _)).symm ≪≫
    (sourceComplex (K := K) (B := B) p).iCyclesIso q _ rfl (source_d p _ _)

private def oneToCotangent :
    SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1 →ₛₗ[
      (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom]
        KaehlerDifferential K B where
  toFun := exteriorPower.oneEquiv B (KaehlerDifferential K B)
  map_add' := (exteriorPower.oneEquiv B (KaehlerDifferential K B)).map_add
  map_smul' t ω := (exteriorPower.oneEquiv B (KaehlerDifferential K B)).map_smul
    ((SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom t) ω

private def cotangentSemilinear :
    KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p) →ₛₗ[
      (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom]
        KaehlerDifferential K B :=
  (oneToCotangent (K := K) (B := B) p).comp
    (DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc)

private theorem cotangent_one_inverse
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
      (cotangentSemilinear p c a b F hF ha hc ω) =
      (show ⋀[B]^1 (KaehlerDifferential K B) from
        DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω) :=
  (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm_apply_apply _

private def formMap (q : ℕ) : sourceModule (K := K) (B := B) p q →ₗ[
    RelativeFrobenius.twist (algebraMap K B) p]
      SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p q where
  toFun := CanonicalGeometry.exteriorSemilinearMap
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
    (cotangentSemilinear p c a b F hF ha hc) q
  map_add' := (CanonicalGeometry.exteriorSemilinearMap _ _ q).map_add
  map_smul' := (CanonicalGeometry.exteriorSemilinearMap _ _ q).map_smulₛₗ

theorem formMap_ιMulti (q : ℕ)
    (ω : Fin q → KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    formMap p c a b F hF ha hc q
      (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) q ω) =
      (show SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p q from
        exteriorPower.ιMulti B q (cotangentSemilinear p c a b F hF ha hc ∘ ω)) := by
  change CanonicalGeometry.exteriorSemilinearMap
      (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
      (cotangentSemilinear p c a b F hF ha hc) q
        (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) q ω) =
    exteriorPower.ιMulti B q (cotangentSemilinear p c a b F hF ha hc ∘ ω)
  exact CanonicalGeometry.exteriorSemilinearMap_ιMulti
    (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
    (cotangentSemilinear p c a b F hF ha hc) q ω

theorem formMap_one
    (ω : KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    formMap p c a b F hF ha hc 1
      ((exteriorPower.oneEquiv (RelativeFrobenius.twist (algebraMap K B) p)
        (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p))).symm ω) =
      DeligneIllusieLocalContinuationTrueTwistDividedOneForm.oneFormMap p c a b F hF ha hc ω := by
  have hsrc : (exteriorPower.oneEquiv (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p))).symm ω =
      exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) 1 (fun _ => ω) := by
    rw [exteriorPower.oneEquiv_symm_apply]
  have h₁ := congrArg (formMap p c a b F hF ha hc 1) hsrc
  have h₂ := formMap_ιMulti p c a b F hF ha hc 1 (fun _ => ω)
  have h₃ : (show SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1 from
      exteriorPower.ιMulti B 1 (cotangentSemilinear p c a b F hF ha hc ∘ fun _ => ω)) =
      (show SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p 1 from
        (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
          (cotangentSemilinear p c a b F hF ha hc ω)) := by
    change exteriorPower.ιMulti B 1
      (cotangentSemilinear p c a b F hF ha hc ∘ fun _ => ω) =
        (exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
          (cotangentSemilinear p c a b F hF ha hc ω)
    rw [exteriorPower.oneEquiv_symm_apply]
    rfl
  exact Eq.trans h₁ (Eq.trans h₂ (Eq.trans h₃
    (cotangent_one_inverse p c a b F hF ha hc ω)))

private theorem wedgeProduct_one_left {A M : Type u} [CommRing A] [AddCommGroup M]
    [Module A M] (q : ℕ) (η : M) (ω : ⋀[A]^q M) :
    EtaleGradedLeibniz.wedgeProduct 1 q ((exteriorPower.oneEquiv A M).symm η) ω =
      PolynomialDeRham.leftWedge η q ω := by
  rw [exteriorPower.oneEquiv_symm_apply]
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti A 1 (fun _ => η) * (ω : ExteriorAlgebra A M) =
    ExteriorAlgebra.ι A η * ω
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]

private theorem image_wedge_closed (q : ℕ)
    (ω : Fin q → KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)) :
    EtaleDeRham.differential w hw q
      (exteriorPower.ιMulti B q (cotangentSemilinear p c a b F hF ha hc ∘ ω)) = 0 := by
  induction q with
  | zero =>
    have heq : exteriorPower.ιMulti B 0 (cotangentSemilinear p c a b F hF ha hc ∘ ω) =
        exteriorPower.ιMulti B 0 (fun i => KaehlerDifferential.D K B (Fin.elim0 i)) := by
      congr 1
      exact Subsingleton.elim _ _
    rw [heq]
    exact EtaleDifferentialIntrinsic.differential_universalWedge w hw 0 _
  | succ q ih =>
    have heq : exteriorPower.ιMulti B (q+1) (cotangentSemilinear p c a b F hF ha hc ∘ ω) =
        EtaleGradedLeibniz.wedgeProduct 1 q
          ((exteriorPower.oneEquiv B (KaehlerDifferential K B)).symm
            (cotangentSemilinear p c a b F hF ha hc (ω 0)))
          (exteriorPower.ιMulti B q
            (cotangentSemilinear p c a b F hF ha hc ∘ fun i => ω i.succ)) := by
      rw [wedgeProduct_one_left, ExteriorBasisScalarExtension.leftWedge_ιMulti]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [heq]
    apply RelativeEtaleCohomologyProducts.product_closed w hw 1 q
    · exact (congrArg (EtaleDeRham.differential w hw 1)
        (cotangent_one_inverse p c a b F hF ha hc (ω 0))).trans
          (oneFormMap_closed p c a b F hF ha hc w hw (ω 0))
    · exact ih (fun i => ω i.succ)

private theorem formMap_closed (q : ℕ) (ω : sourceModule (K := K) (B := B) p q) :
    (SchemeRelativeFrobeniusAffineDeRham.differential w hw p q).hom
      (formMap p c a b F hF ha hc q ω) = 0 := by
  have hω : ω ∈ Submodule.span (RelativeFrobenius.twist (algebraMap K B) p)
      (Set.range (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) q
        (M := KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p)))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨η, rfl⟩ := hz
    rw [formMap_ιMulti]
    exact image_wedge_closed p c a b F hF ha hc w hw q η
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul t x _ hx => rw [map_smul, map_smul, hx, smul_zero]

private def component (q : ℕ) : sourceModule (K := K) (B := B) p q ⟶
    SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p q :=
  ModuleCat.ofHom (X := sourceModule (K := K) (B := B) p q)
    (Y := SchemeRelativeFrobeniusAffineDeRham.formModule (k := K) (B := B) p q)
    (formMap p c a b F hF ha hc q)

private theorem component_closed (q : ℕ) :
    component p c a b F hF ha hc q ≫
      (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).d q (q+1) = 0 := by
  rw [target_d p w hw q]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact formMap_closed p c a b F hF ha hc w hw q

/-- The whole exterior extension of the SAME canonical xi is an actual native cochain
map; the exterior-zero map is the original geometric relative Frobenius. -/
def cochainMap : sourceComplex (K := K) (B := B) p ⟶
    SchemeRelativeFrobeniusAffineDeRham.complex w hw p :=
  CochainComplex.ofHom (fun q => component p c a b F hF ha hc q)
    (fun q => by
      change component p c a b F hF ha hc q ≫
          (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).d q (q+1) =
        (sourceComplex (K := K) (B := B) p).d q (q+1) ≫ component p c a b F hF ha hc (q+1)
      rw [component_closed p c a b F hF ha hc w hw q, source_d]
      exact (CategoryTheory.Limits.zero_comp
        (X := sourceModule (K := K) (B := B) p q)
        (f := component p c a b F hF ha hc (q+1))).symm)

/-- The class map is actual homology of this whole exterior cochain map, using the
canonical homology isomorphism of its actual zero-differential source. -/
def classMap (q : ℕ) : sourceModule (K := K) (B := B) p q ⟶
    (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).homology q :=
  (sourceHomologyIso (K := K) (B := B) p q).inv ≫
    HomologicalComplex.homologyMap (cochainMap p c a b F hF ha hc w hw) q

private theorem classMap_eq_liftCycles (q : ℕ) :
    classMap p c a b F hF ha hc w hw q =
      (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).liftCycles
        (component p c a b F hF ha hc q) (q+1) (by simp)
        (component_closed p c a b F hF ha hc w hw q) ≫
          (SchemeRelativeFrobeniusAffineDeRham.complex w hw p).homologyπ q := by
  let G := sourceComplex (K := K) (B := B) p
  let E := SchemeRelativeFrobeniusAffineDeRham.complex w hw p
  let Φ := cochainMap p c a b F hF ha hc w hw
  let φ : G.X q ⟶ E.X q := component p c a b F hF ha hc q
  let e := G.iCyclesIso q _ rfl (source_d p _ _)
  have hφ : φ ≫ E.d q (q+1) = 0 := component_closed p c a b F hF ha hc w hw q
  have hcycles : e.inv ≫ HomologicalComplex.cyclesMap Φ q =
      E.liftCycles φ (q+1) (by simp) hφ := by
    apply (cancel_mono (E.iCycles q)).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, HomologicalComplex.liftCycles_i]
    change e.inv ≫ G.iCycles q ≫ Φ.f q = φ
    rw [← Category.assoc]
    change e.inv ≫ e.hom ≫ φ = φ
    rw [Iso.inv_hom_id_assoc]
  change (e.inv ≫ G.homologyπ q) ≫ HomologicalComplex.homologyMap Φ q =
    E.liftCycles φ (q+1) (by simp) hφ ≫ E.homologyπ q
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hcycles]

private def formCycle (q : ℕ) (ω : sourceModule (K := K) (B := B) p q) :
    LinearMap.ker ((SchemeRelativeFrobeniusAffineDeRham.complex w hw p).sc q).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle _ _ (target_square p w hw) q
    ⟨formMap p c a b F hF ha hc q ω, formMap_closed p c a b F hF ha hc w hw q ω⟩

private theorem classMap_eq_cycleClass (q : ℕ) (ω : sourceModule (K := K) (B := B) p q) :
    (classMap p c a b F hF ha hc w hw q).hom ω =
      ModuleComplexNativeCycleClasses.cycleClass
        (SchemeRelativeFrobeniusAffineDeRham.complex w hw p) q
        (formCycle p c a b F hF ha hc w hw q ω) := by
  let E := SchemeRelativeFrobeniusAffineDeRham.complex w hw p
  let φ := component p c a b F hF ha hc q
  have hφ : φ ≫ E.d q (q+1) = 0 := component_closed p c a b F hF ha hc w hw q
  have hinc := congrArg (fun L : sourceModule (K := K) (B := B) p q ⟶ E.X q => L ω)
    (E.liftCycles_i φ (q+1) (by simp) hφ)
  change E.iCycles q (E.liftCycles φ (q+1) (by simp) hφ ω) = φ ω at hinc
  have hc' := (E.sc q).moduleCatCyclesIso_inv_iCycles_apply
    (formCycle p c a b F hF ha hc w hw q ω)
  change E.iCycles q ((E.sc q).moduleCatCyclesIso.inv
    (formCycle p c a b F hF ha hc w hw q ω)) = φ ω at hc'
  have heq : E.liftCycles φ (q+1) (by simp) hφ ω =
      (E.sc q).moduleCatCyclesIso.inv (formCycle p c a b F hF ha hc w hw q ω) := by
    apply (ModuleCat.mono_iff_injective (E.iCycles q)).mp inferInstance
    exact hinc.trans hc'.symm
  have hh := congrArg (fun L : sourceModule (K := K) (B := B) p q ⟶ E.homology q => L ω)
    (classMap_eq_liftCycles p c a b F hF ha hc w hw q)
  exact hh.trans (congrArg (E.homologyπ q) heq)

private def nativeFormCycle [CharP B p] (q : ℕ) (ω : sourceModule (K := K) (B := B) p q) :
    LinearMap.ker ((RelativeEtaleDeRham.complex w hw p).sc q).g.hom :=
  ModuleComplexNativeCycleClasses.ofCycle _ _ (native_square p w hw) q
    ⟨(show RelativeEtaleDeRham.formModule (R := K) (B := B) p q from
        formMap p c a b F hF ha hc q ω),
      formMap_closed p c a b F hF ha hc w hw q ω⟩

private theorem classMap_comparison [CharP B p] (q : ℕ)
    (ω : sourceModule (K := K) (B := B) p q) :
    (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q).hom
      ((classMap p c a b F hF ha hc w hw q).hom ω) =
      ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex w hw p) q
        (nativeFormCycle p c a b F hF ha hc w hw q ω) := by
  rw [classMap_eq_cycleClass]
  exact ModuleComplexNativeCycleClasses.homologyMap_cycleClass
    (RelativeNativeAllAlgebraCartier.complexIso_native w hw p).hom q
    (formCycle p c a b F hF ha hc w hw q ω)
    (nativeFormCycle p c a b F hF ha hc w hw q ω)
    (RelativeNativeAllAlgebraCartier.complexIso_native_hom_f_apply w hw p q _)

theorem nativeFormCycle_wedgeProduct [CharP B p] (q r : ℕ)
    (α : sourceModule (K := K) (B := B) p q) (β : sourceModule (K := K) (B := B) p r) :
    nativeFormCycle p c a b F hF ha hc w hw (r+q)
      (EtaleGradedLeibniz.wedgeProduct q r α β) =
      RelativeEtaleCohomologyProducts.nativeCycleProduct w hw p q r
        (nativeFormCycle p c a b F hF ha hc w hw q α)
        (nativeFormCycle p c a b F hF ha hc w hw r β) := by
  apply Subtype.ext
  rw [RelativeEtaleCohomologyProducts.nativeCycleProduct_val]
  change CanonicalGeometry.exteriorSemilinearMap
      (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
      (cotangentSemilinear p c a b F hF ha hc) (r+q)
        (EtaleGradedLeibniz.wedgeProduct q r α β) =
    EtaleGradedLeibniz.wedgeProduct q r
      (CanonicalGeometry.exteriorSemilinearMap
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
        (cotangentSemilinear p c a b F hF ha hc) q α)
      (CanonicalGeometry.exteriorSemilinearMap
        (SchemeRelativeFrobeniusAffineMap.ringMap (algebraMap K B) p).hom
        (cotangentSemilinear p c a b F hF ha hc) r β)
  exact RelativeEtaleCartierMultiplicativity.exteriorSemilinearMap_wedgeProduct _ _ q r α β

private theorem nativeClass_sourceWedge [CharP B p] (q : ℕ) (t : Fin q → B) :
    ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex w hw p) q
      (nativeFormCycle p c a b F hF ha hc w hw q
        (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) q
          (fun i => KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
            ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (t i))))) =
      (RelativeEtaleCartierDomain.inverseCartierIso w hw p q).hom
        (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) q
          (fun i => KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
            ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (t i)))) := by
  induction q with
  | zero =>
    have heq : nativeFormCycle p c a b F hF ha hc w hw 0
        (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) 0
          (fun i => KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
            ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (t i)))) =
        RelativeEtaleCartierMultiplicativity.functionCycle w hw p 0 t := by
      apply Subtype.ext
      have hf : (show ⋀[B]^0 (KaehlerDifferential K B) from
          formMap p c a b F hF ha hc 0
            (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) 0
              (fun i => KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
                ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (t i))))) =
          exteriorPower.ιMulti B 0
            (cotangentSemilinear p c a b F hF ha hc ∘
              fun i => KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
                ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom (t i))) :=
        formMap_ιMulti p c a b F hF ha hc 0 _
      have hg : (show ⋀[B]^0 (KaehlerDifferential K B) from
          (RelativeEtaleCartierMultiplicativity.functionCycle w hw p 0 t).val) =
          exteriorPower.ιMulti B 0
            (fun i => (t i)^(p-1) • KaehlerDifferential.D K B (t i)) :=
        RelativeEtaleCartierMultiplicativity.functionCycle_val w hw p 0 t
      exact hf.trans ((congrArg (exteriorPower.ιMulti B 0)
        (Subsingleton.elim _ _)).trans hg.symm)
    rw [heq]
    exact (RelativeEtaleCartierMultiplicativity.inverseCartierIso_sourceWedge w hw p 0 t).symm
  | succ q ih =>
    let δ := fun b : B => KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
      ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom b)
    let α := (exteriorPower.oneEquiv (RelativeFrobenius.twist (algebraMap K B) p)
      (KaehlerDifferential K (RelativeFrobenius.twist (algebraMap K B) p))).symm (δ (t 0))
    let β := exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) q
      (fun i => δ (t i.succ))
    have hs : exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) (q+1)
        (fun i => δ (t i)) = EtaleGradedLeibniz.wedgeProduct 1 q α β := by
      rw [wedgeProduct_one_left, ExteriorBasisScalarExtension.leftWedge_ιMulti]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have hcycle : nativeFormCycle p c a b F hF ha hc w hw 1 α =
        nativeOneCycle p c a b F hF ha hc w hw (δ (t 0)) := by
      apply Subtype.ext
      exact formMap_one p c a b F hF ha hc (δ (t 0))
    have hhead : ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex w hw p) 1
        (nativeFormCycle p c a b F hF ha hc w hw 1 α) =
        (RelativeEtaleCartierDomain.inverseCartierIso w hw p 1).hom α := by
      rw [hcycle]
      exact nativeOneClass_D_source p c a b F hF ha hc w hw (t 0)
    change ModuleComplexNativeCycleClasses.cycleClass (RelativeEtaleDeRham.complex w hw p) (q+1)
        (nativeFormCycle p c a b F hF ha hc w hw (q+1)
          (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) (q+1)
            (fun i => δ (t i)))) =
      (RelativeEtaleCartierDomain.inverseCartierIso w hw p (q+1)).hom
        (exteriorPower.ιMulti (RelativeFrobenius.twist (algebraMap K B) p) (q+1)
          (fun i => δ (t i)))
    rw [hs, nativeFormCycle_wedgeProduct,
      ← RelativeEtaleCohomologyProducts.nativeCohomologyProduct_actual_cycleClass, hhead,
      ih (fun i => t i.succ)]
    exact (RelativeEtaleCartierMultiplicativity.inverseCartierIso_wedgeProduct w hw p 1 q α β).symm

/-- In every original degree, actual homology of the exterior map of SAME xi is
the actual geometric-beta native inverse Cartier isomorphism. -/
theorem classMap_eq_inverseCartier (q : ℕ) :
    classMap p c a b F hF ha hc w hw q =
      (RelativeNativeAllAlgebraCartier.inverseCartierIso w hw p q).hom := by
  classical
  by_cases h : Nontrivial B
  · let := h
    let : CharP B p := charP_of_injective_algebraMap (algebraMap K B).injective p
    apply (cancel_mono (RelativeNativeAllAlgebraCartier.homologyIso_native w hw p q).hom).1
    rw [RelativeNativeAllAlgebraCartier.inverseCartierIso_eq_native]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply ModuleCat.hom_ext
    apply ((RelativeEtaleCartierDomain.cotangentBasis w hw p).exteriorPower q).ext
    intro s
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    have hvec : (RelativeEtaleCartierDomain.cotangentBasis w hw p) ∘
        (Set.powersetCard.ofFinEmbEquiv.symm s) =
        fun i => KaehlerDifferential.D K (RelativeFrobenius.twist (algebraMap K B) p)
          ((RelativeFrobenius.sourceMap (algebraMap K B) p).hom
            (w (Set.powersetCard.ofFinEmbEquiv.symm s i))) := by
      funext i
      exact RelativeEtaleCartierDomain.cotangentBasis_D w hw p _
    rw [hvec]
    exact (classMap_comparison p c a b F hF ha hc w hw q _).trans
      (nativeClass_sourceWedge p c a b F hF ha hc w hw q
        (fun i => w (Set.powersetCard.ofFinEmbEquiv.symm s i)))
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    exact (RelativeNativeAllAlgebraCartier.actualHomology_isZero w hw p q).eq_of_tgt _ _

/-- The actual whole exterior cochain map of the SAME original canonical xi is
a genuine local quasi-isomorphism, with every homology map proved by Cartier. -/
theorem quasiIso_cochainMap : _root_.QuasiIso (cochainMap p c a b F hF ha hc w hw) := by
  rw [_root_.quasiIso_iff]
  intro q
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso ((sourceHomologyIso (K := K) (B := B) p q).inv ≫
      HomologicalComplex.homologyMap (cochainMap p c a b F hF ha hc w hw) q) := by
    change IsIso (classMap p c a b F hF ha hc w hw q)
    rw [classMap_eq_inverseCartier]
    infer_instance
  exact IsIso.of_isIso_comp_left (sourceHomologyIso (K := K) (B := B) p q).inv _

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationResidueCartier

