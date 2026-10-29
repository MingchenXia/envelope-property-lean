import EnvelopeProperty.ComplexGeometry.Schemes.ProjectiveTwistingSheaf
import Mathlib.RingTheory.Localization.FractionRing

/-! # Actual polynomial-Proj twisting sections and homogeneous coordinates

The base-field action is produced by actual constant homogeneous polynomials.
The coordinate expressions use actual basic-open regular section isomorphisms,
actual coordinate localizations, and the proved homogeneous-fraction frame.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace
open scoped DirectSum

namespace ComplexSchemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K I : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual constant polynomial ring map takes values in the true degree-zero part. -/
def homogeneousPolynomialDegreeZeroConstants :
    K →+* MvPolynomial.homogeneousSubmodule I K 0 where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C I r⟩
  map_zero' := Subtype.ext (MvPolynomial.C.map_zero)
  map_one' := Subtype.ext (MvPolynomial.C.map_one)
  map_add' r s := Subtype.ext (MvPolynomial.C.map_add r s)
  map_mul' r s := Subtype.ext (MvPolynomial.C.map_mul r s)

/-- Actual constants are actual regular homogeneous fractions on each true Proj open. -/
def homogeneousPolynomialProjConstants
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    K →+* Γ(Proj (MvPolynomial.homogeneousSubmodule I K), U) where
  toFun r := ⟨fun x => HomogeneousLocalization.fromZeroRingHom _
    x.val.asHomogeneousIdeal.toIdeal.primeCompl (homogeneousPolynomialDegreeZeroConstants r), by
      intro x
      refine ⟨U, x.property, 𝟙 U, 0, homogeneousPolynomialDegreeZeroConstants r,
        ⟨1, SetLike.one_mem_graded _⟩,
        fun y => y.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, fun _ => rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_zero
  map_one' := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_one
  map_add' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_add r s
  map_mul' r s := by
    apply Subtype.ext
    funext x
    exact ((HomogeneousLocalization.fromZeroRingHom _ _).comp
      homogeneousPolynomialDegreeZeroConstants).map_mul r s

/-- The actual regular Proj section rings carry their produced base-field algebra. -/
instance homogeneousPolynomialProjRegularAlgebra
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    Algebra K Γ(Proj (MvPolynomial.homogeneousSubmodule I K), U) :=
  (homogeneousPolynomialProjConstants U).toAlgebra

/-- Genuine constants commute with genuine restrictions. -/
theorem homogeneousPolynomialProjConstants_restrict
    {U V : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens} (i : V ⟶ U) (r : K) :
    (Proj (MvPolynomial.homogeneousSubmodule I K)).presheaf.map i.op
      (homogeneousPolynomialProjConstants U r) = homogeneousPolynomialProjConstants V r := rfl

/-- Actual homogeneous localizations use the same produced constant polynomial scalars. -/
instance homogeneousPolynomialHomogeneousLocalizationAlgebra
    (S : Submonoid (MvPolynomial I K)) :
    Algebra K (HomogeneousLocalization (MvPolynomial.homogeneousSubmodule I K) S) :=
  ((HomogeneousLocalization.fromZeroRingHom _ _).comp
    (homogeneousPolynomialDegreeZeroConstants (K := K) (I := I))).toAlgebra

/-- Actual shifted fraction section modules retain the produced base-field scalar action. -/
instance homogeneousPolynomialTwistingSectionsModule (k : ℕ)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    Module K (projectiveTwistingSections (MvPolynomial.homogeneousSubmodule I K) k U) :=
  Module.compHom _ (homogeneousPolynomialProjConstants U)

/-- The actual sheaf section module is over the actual base field. -/
instance homogeneousPolynomialTwistingBundleSectionsModule (k : ℕ)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    Module K (bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) U) :=
  inferInstanceAs (Module K
    (projectiveTwistingSections (MvPolynomial.homogeneousSubmodule I K) k U))

/-- The produced base-field action agrees with the actual regular-function action. -/
instance homogeneousPolynomialTwistingSectionsScalarTower (k : ℕ)
    (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) :
    IsScalarTower K Γ(Proj (MvPolynomial.homogeneousSubmodule I K), U)
      (projectiveTwistingSections (MvPolynomial.homogeneousSubmodule I K) k U) where
  smul_assoc r q s := by
    change ((homogeneousPolynomialProjConstants U r) * q) • s =
      homogeneousPolynomialProjConstants U r • (q • s)
    exact mul_smul _ _ _

/-- The produced homogeneous-localization constants have their actual ordinary localization values. -/
theorem homogeneousPolynomialLocalization_algebraMap_val
    (S : Submonoid (MvPolynomial I K)) (r : K) :
    (algebraMap K (HomogeneousLocalization (MvPolynomial.homogeneousSubmodule I K) S) r).val =
      algebraMap K (Localization S) r := by
  change Localization.mk (MvPolynomial.C r) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  rfl

section FiniteCoordinates

variable [Fintype I]

/-- A genuine homogeneous polynomial acquires exactly its degree in the Laurent inclusion. -/
theorem polynomialToProjectiveLaurent_homogeneous {k : ℕ} (p : MvPolynomial I K)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule I K k) :
    polynomialToProjectiveLaurent p ∈
      AddMonoidAlgebra.supported K K {d : I → ℤ | (∑ i, d i) = k} := by
  classical
  apply AddMonoidAlgebra.mem_supported.mpr
  intro d hd
  change d ∈ ((AddMonoidAlgebra.coeff p).mapDomain polynomialExponentToInt).support at hd
  obtain ⟨e, he, hd⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hd)
  rw [← hd]
  change (∑ i, (e i : ℤ)) = (k : ℤ)
  rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum]
  congr 1
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported] at hp
  exact (AddMonoidAlgebra.mem_supported.mp hp) he

/-- The actual integer exponent of a coordinate power has the expected total degree. -/
theorem polynomialCoordinateExponent_total (i : I) (n : ℕ) :
    (∑ j, (n • polynomialExponentToInt (Finsupp.single i 1)) j) = (n : ℤ) := by
  classical
  simp [polynomialExponentToInt, Finsupp.single_apply, Pi.smul_apply]

/-- Genuine degree-zero homogeneous coordinate fractions have degree zero in the Laurent algebra. -/
theorem homogeneousPolynomialAway_degree_zero (i : I)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K)
      (MvPolynomial.X i)) :
    coordinateLocalizationToLaurent i z.val ∈
      AddMonoidAlgebra.supported K K {d : I → ℤ | (∑ j, d j) = 0} := by
  classical
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.isHomogeneous_X K i) z
  have hp' : p ∈ MvPolynomial.homogeneousSubmodule I K n := by simpa using hp
  have hfrac := IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X i : MvPolynomial I K))
    p (⟨MvPolynomial.X i ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (MvPolynomial.X i))
  have hmap := congrArg (coordinateLocalizationToLaurent (K := K) i) hfrac
  rw [map_mul, coordinateLocalizationToLaurent_algebraMap,
    coordinateLocalizationToLaurent_algebraMap, map_pow,
    polynomialToProjectiveLaurent_X, AddMonoidAlgebra.single_pow, one_pow] at hmap
  apply AddMonoidAlgebra.mem_supported.mpr
  intro d hd
  have hc := congrArg (fun f : projectiveLaurentAlgebra K I =>
    f.coeff (d + n • polynomialExponentToInt (Finsupp.single i 1))) hmap
  rw [AddMonoidAlgebra.coeff_mul_single_add, mul_one] at hc
  have hn : (polynomialToProjectiveLaurent p).coeff
      (d + n • polynomialExponentToInt (Finsupp.single i 1)) ≠ 0 := by
    rw [← hc]
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk'] at hd
    exact Finsupp.mem_support_iff.mp hd
  have hdeg := (AddMonoidAlgebra.mem_supported.mp
    (polynomialToProjectiveLaurent_homogeneous p hp')) (Finsupp.mem_support_iff.mpr hn)
  change (∑ j, (d + n • polynomialExponentToInt (Finsupp.single i 1)) j) = (n : ℤ) at hdeg
  simp only [Pi.add_apply, Finset.sum_add_distrib,
    polynomialCoordinateExponent_total] at hdeg
  change (∑ j, d j) = 0
  omega

/-- Multiplication by an actual coordinate power gives a genuine shifted localized linear map. -/
def homogeneousPolynomialAwayShift (k : ℕ) (i : I) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) →ₗ[K]
      Localization.Away (MvPolynomial.X i : MvPolynomial I K) where
  toFun z := z.val * algebraMap (MvPolynomial I K)
    (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i ^ k)
  map_add' z w := by rw [HomogeneousLocalization.val_add, add_mul]
  map_smul' r z := by
    rw [Algebra.smul_def, HomogeneousLocalization.val_mul,
      homogeneousPolynomialLocalization_algebraMap_val, Algebra.smul_def, mul_assoc]
    rfl

/-- The shifted actual coordinate-localization element has its proved total degree k. -/
theorem homogeneousPolynomialAwayShift_degree (k : ℕ) (i : I)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) :
    homogeneousPolynomialAwayShift k i z ∈ coordinateHomogeneousLocalization (K := K) k i := by
  classical
  change coordinateLocalizationToLaurent i
    (z.val * algebraMap (MvPolynomial I K)
      (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i ^ k)) ∈
    AddMonoidAlgebra.supported K K {d : I → ℤ | (∑ j, d j) = k}
  rw [map_mul, coordinateLocalizationToLaurent_algebraMap, map_pow,
    polynomialToProjectiveLaurent_X, AddMonoidAlgebra.single_pow, one_pow]
  apply AddMonoidAlgebra.mem_supported.mpr
  intro d hd
  have hc : ((coordinateLocalizationToLaurent i z.val) *
      AddMonoidAlgebra.single (k • polynomialExponentToInt (Finsupp.single i 1)) 1).coeff d ≠ 0 :=
    Finsupp.mem_support_iff.mp hd
  rw [AddMonoidAlgebra.coeff_mul_single_apply, mul_one] at hc
  have hdeg := (AddMonoidAlgebra.mem_supported.mp (homogeneousPolynomialAway_degree_zero i z))
    (Finsupp.mem_support_iff.mpr hc)
  change (∑ j, (d - k • polynomialExponentToInt (Finsupp.single i 1)) j) = 0 at hdeg
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, polynomialCoordinateExponent_total] at hdeg
  change (∑ j, d j) = (k : ℤ)
  omega

/-- The actual shifted chart expression takes values in the actual homogeneous localization degree piece. -/
def homogeneousPolynomialAwayShiftToDegree (k : ℕ) (i : I) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) →ₗ[K]
      coordinateHomogeneousLocalization (K := K) k i :=
  (homogeneousPolynomialAwayShift k i).codRestrict _
    (homogeneousPolynomialAwayShift_degree k i)

/-- The actual polynomial-Proj basic-open/Away isomorphism respects actual constant scalars. -/
def homogeneousPolynomialBasicOpenAwayEquiv (i : I) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) ≃ₐ[K]
      Γ(Proj (MvPolynomial.homogeneousSubmodule I K),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) := by
  let e := (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X K i) (by decide)).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro r
  apply Subtype.ext
  funext x
  rfl

/-- True twisting chart sections have their produced actual degree-k coordinate expression. -/
def homogeneousPolynomialTwistingChartCoordinate (k : ℕ) (i : I) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) →ₗ[K]
      coordinateHomogeneousLocalization (K := K) k i :=
  (homogeneousPolynomialAwayShiftToDegree k i).comp
    ((homogeneousPolynomialBasicOpenAwayEquiv i).symm.toLinearMap.comp
      (LinearEquiv.restrictScalars K (projectiveTwistingChartSectionsFrame (MvPolynomial.homogeneousSubmodule I K) k
        ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) le_rfl)).toLinearMap)

/-- The actual coordinate chart expression is faithful, from coordinate invertibility
and the actual regular/Away equivalence; no injectivity data is supplied. -/
theorem homogeneousPolynomialTwistingChartCoordinate_injective (k : ℕ) (i : I) :
    Function.Injective (homogeneousPolynomialTwistingChartCoordinate (K := K) k i) := by
  have hshift : Function.Injective (homogeneousPolynomialAwayShiftToDegree (K := K) k i) := by
    intro z w h
    apply HomogeneousLocalization.val_injective
    apply ((IsLocalization.Away.algebraMap_isUnit
      (MvPolynomial.X i : MvPolynomial I K)).pow k).mul_left_inj.mp
    have h' := congrArg Subtype.val h
    change z.val * algebraMap (MvPolynomial I K)
      (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i ^ k) =
        w.val * algebraMap (MvPolynomial I K)
          (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i ^ k) at h'
    simpa only [map_pow] using h'
  exact hshift.comp ((homogeneousPolynomialBasicOpenAwayEquiv i).symm.injective.comp
    (projectiveTwistingChartSectionsFrame (MvPolynomial.homogeneousSubmodule I K) k
      ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) le_rfl).injective)

/-- Genuine coordinate localization specializes to an actual Proj prime localization. -/
def homogeneousPolynomialCoordinateAtPoint (i : I)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) :
    Localization.Away (MvPolynomial.X i : MvPolynomial I K) →+*
      projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x :=
  IsLocalization.map (M := Submonoid.powers (MvPolynomial.X i : MvPolynomial I K))
    (T := x.asHomogeneousIdeal.toIdeal.primeCompl)
    (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x)
    (RingHom.id (MvPolynomial I K))
    (Submonoid.powers_le.mpr ((Proj.mem_basicOpen _ _ _).mp hx))

omit [Fintype I] in
/-- Genuine coordinate specialization extends the actual ordinary polynomial map. -/
theorem homogeneousPolynomialCoordinateAtPoint_algebraMap (i : I)
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i))
    (p : MvPolynomial I K) :
    homogeneousPolynomialCoordinateAtPoint i x hx
      (algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) p) =
        algebraMap (MvPolynomial I K)
          (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x) p :=
  IsLocalization.map_eq _ _

omit [Fintype I] in
/-- Actual regular/Away sections evaluate by the genuine coordinate specialization map. -/
theorem homogeneousPolynomialBasicOpenAwayEquiv_eval (i : I)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i))
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) :
    ((homogeneousPolynomialBasicOpenAwayEquiv i z).val ⟨x, hx⟩).val =
      homogeneousPolynomialCoordinateAtPoint i x hx z.val :=
  ProjectiveSpectrum.Proj.awayToSection_apply
    (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) z ⟨x, hx⟩

/-- The actual shifted coordinate expression evaluates to the original actual twisting section. -/
theorem homogeneousPolynomialTwistingChartCoordinate_eval (k : ℕ) (i : I)
    (s : bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)))
    (x : Proj (MvPolynomial.homogeneousSubmodule I K))
    (hx : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) :
    homogeneousPolynomialCoordinateAtPoint i x hx
      (homogeneousPolynomialTwistingChartCoordinate k i s).val = s.val ⟨x, hx⟩ := by
  let F := projectiveTwistingChartSectionsFrame (MvPolynomial.homogeneousSubmodule I K) k
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) le_rfl
  let z := (homogeneousPolynomialBasicOpenAwayEquiv i).symm (F s)
  have he := congrArg (fun r => (r.val ⟨x, hx⟩).val)
    ((homogeneousPolynomialBasicOpenAwayEquiv i).apply_symm_apply (F s))
  have hf := congrArg (fun t : projectiveTwistingSections
      (MvPolynomial.homogeneousSubmodule I K) k
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)) => t.val ⟨x, hx⟩)
    (F.symm_apply_apply s)
  change homogeneousPolynomialCoordinateAtPoint i x hx
    (z.val * algebraMap (MvPolynomial I K)
      (Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i ^ k)) = _
  rw [map_mul, homogeneousPolynomialCoordinateAtPoint_algebraMap]
  rw [homogeneousPolynomialBasicOpenAwayEquiv_eval] at he
  rw [he]
  exact hf

/-- An actual zero homogeneous prime supplies a genuine common point of all polynomial coordinate charts. -/
def homogeneousPolynomialZeroPrime [Nonempty I] :
    Proj (MvPolynomial.homogeneousSubmodule I K) where
  asHomogeneousIdeal := ⊥
  isPrime := by change (⊥ : Ideal (MvPolynomial I K)).IsPrime; infer_instance
  not_irrelevant_le := by
    intro h
    let i : I := Classical.arbitrary I
    have hi := HomogeneousIdeal.mem_irrelevant_of_mem (MvPolynomial.homogeneousSubmodule I K)
      (show 0 < 1 from Nat.zero_lt_one) (MvPolynomial.isHomogeneous_X K i)
    have hz : MvPolynomial.X i = (0 : MvPolynomial I K) := h hi
    exact MvPolynomial.X_ne_zero i hz

omit [Fintype I] in
/-- The true zero homogeneous prime belongs to every true homogeneous coordinate chart. -/
theorem homogeneousPolynomialZeroPrime_mem [Nonempty I] (i : I) :
    homogeneousPolynomialZeroPrime (K := K) (I := I) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i) := by
  apply (Proj.mem_basicOpen _ _ _).mpr
  exact MvPolynomial.X_ne_zero i

omit [Fintype I] in
/-- Actual polynomial evaluation in the prime localization at the zero Proj point is faithful. -/
theorem homogeneousPolynomialZeroPrime_algebraMap_injective [Nonempty I] :
    Function.Injective (algebraMap (MvPolynomial I K)
      (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K)
        (homogeneousPolynomialZeroPrime (K := K) (I := I)))) :=
  IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors
    (homogeneousPolynomialZeroPrime (K := K) (I := I)).asHomogeneousIdeal.toIdeal)


omit [Fintype I] in
/-- Equality in the actual zero-prime localization forces equality of genuine
coordinate-localized Laurent expressions. Both actual denominators are cleared
before using polynomial faithfulness and actual coordinate units. -/
theorem homogeneousPolynomialCoordinateAtZero_compare [Nonempty I] (i j : I)
    (z : Localization.Away (MvPolynomial.X i : MvPolynomial I K))
    (w : Localization.Away (MvPolynomial.X j : MvPolynomial I K))
    (h : homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
        (homogeneousPolynomialZeroPrime_mem i) z =
      homogeneousPolynomialCoordinateAtPoint j homogeneousPolynomialZeroPrime
        (homogeneousPolynomialZeroPrime_mem j) w) :
    coordinateLocalizationToLaurent i z = coordinateLocalizationToLaurent j w := by
  classical
  obtain ⟨m, p, hp⟩ := IsLocalization.Away.surj (R := MvPolynomial I K)
    (S := Localization.Away (MvPolynomial.X i : MvPolynomial I K)) (MvPolynomial.X i) z
  obtain ⟨l, q, hq⟩ := IsLocalization.Away.surj (R := MvPolynomial I K)
    (S := Localization.Away (MvPolynomial.X j : MvPolynomial I K)) (MvPolynomial.X j) w
  have hp0 := congrArg (homogeneousPolynomialCoordinateAtPoint i homogeneousPolynomialZeroPrime
    (homogeneousPolynomialZeroPrime_mem i)) hp
  have hq0 := congrArg (homogeneousPolynomialCoordinateAtPoint j homogeneousPolynomialZeroPrime
    (homogeneousPolynomialZeroPrime_mem j)) hq
  rw [map_mul, map_pow, homogeneousPolynomialCoordinateAtPoint_algebraMap,
    homogeneousPolynomialCoordinateAtPoint_algebraMap] at hp0 hq0
  have hcross : p * MvPolynomial.X j ^ l = q * MvPolynomial.X i ^ m := by
    apply homogeneousPolynomialZeroPrime_algebraMap_injective
    rw [map_mul, map_mul, map_pow, map_pow, ← hp0, ← hq0, h]
    ring
  have hpL := congrArg (coordinateLocalizationToLaurent (K := K) i) hp
  have hqL := congrArg (coordinateLocalizationToLaurent (K := K) j) hq
  rw [map_mul, map_pow, coordinateLocalizationToLaurent_algebraMap,
    coordinateLocalizationToLaurent_algebraMap] at hpL hqL
  have hcrossL := congrArg (polynomialToProjectiveLaurent (K := K) (I := I)) hcross
  rw [map_mul, map_mul, map_pow, map_pow] at hcrossL
  apply (((polynomialToProjectiveLaurent_X_isUnit (K := K) i).pow m).mul
    ((polynomialToProjectiveLaurent_X_isUnit (K := K) j).pow l)).mul_left_inj.mp
  calc
    coordinateLocalizationToLaurent i z *
        (polynomialToProjectiveLaurent (MvPolynomial.X i) ^ m *
          polynomialToProjectiveLaurent (MvPolynomial.X j) ^ l) =
      polynomialToProjectiveLaurent p * polynomialToProjectiveLaurent (MvPolynomial.X j) ^ l := by
        rw [← mul_assoc, hpL]
    _ = polynomialToProjectiveLaurent q * polynomialToProjectiveLaurent (MvPolynomial.X i) ^ m :=
      hcrossL
    _ = coordinateLocalizationToLaurent j w *
        (polynomialToProjectiveLaurent (MvPolynomial.X i) ^ m *
          polynomialToProjectiveLaurent (MvPolynomial.X j) ^ l) := by
        rw [← hqL]
        ring

/-- Restriction of actual twisting sections respects the produced actual base-field scalars. -/
def homogeneousPolynomialTwistingRestriction (k : ℕ)
    {U V : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens} (i : V ⟶ U) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) U →ₗ[K]
      bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) V where
  toFun s := (projectiveTwistingPresheaf (MvPolynomial.homogeneousSubmodule I K) k).map i.op s
  map_add' s t := by apply Subtype.ext; funext x; rfl
  map_smul' r s := by apply Subtype.ext; funext x; rfl

/-- Actual global twisting sections have actual coordinate-localized expressions. -/
def homogeneousPolynomialTwistingGlobalToCharts (k : ℕ) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤ →ₗ[K]
      (∀ i : I, coordinateHomogeneousLocalization (K := K) k i) :=
  LinearMap.pi (fun i => (homogeneousPolynomialTwistingChartCoordinate k i).comp
    (homogeneousPolynomialTwistingRestriction k
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)).leTop))

/-- Cech compatibility of actual global coordinate expressions is derived by
actual zero-prime evaluation and actual localization faithfulness. -/
theorem homogeneousPolynomialTwistingGlobalToCharts_compatible [Nonempty I] (k : ℕ)
    (s : bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤) :
    homogeneousPolynomialTwistingGlobalToCharts k s ∈
      coordinateHomogeneousCech (K := K) (I := I) k := by
  intro i j
  apply homogeneousPolynomialCoordinateAtZero_compare
  exact (homogeneousPolynomialTwistingChartCoordinate_eval k i
    (homogeneousPolynomialTwistingRestriction k
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)).leTop s)
    homogeneousPolynomialZeroPrime (homogeneousPolynomialZeroPrime_mem i)).trans
      (homogeneousPolynomialTwistingChartCoordinate_eval k j
        (homogeneousPolynomialTwistingRestriction k
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X j)).leTop s)
        homogeneousPolynomialZeroPrime (homogeneousPolynomialZeroPrime_mem j)).symm

/-- The actual global twisting section map enters the genuine homogeneous localization Cech kernel. -/
def homogeneousPolynomialTwistingGlobalToCech [Nonempty I] (k : ℕ) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤ →ₗ[K]
      coordinateHomogeneousCech (K := K) (I := I) k :=
  (homogeneousPolynomialTwistingGlobalToCharts k).codRestrict _
    (homogeneousPolynomialTwistingGlobalToCharts_compatible k)

/-- The actual sheaf axiom and the derived coordinate cover give faithful global sections. -/
theorem homogeneousPolynomialTwistingGlobalToCech_injective [Nonempty I] (k : ℕ) :
    Function.Injective (homogeneousPolynomialTwistingGlobalToCech (K := K) (I := I) k) := by
  intro s t h
  let U : I → (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens :=
    fun i => Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)
  have hcover : iSup U = ⊤ := Proj.iSup_basicOpen_eq_top _ _
    homogeneousPolynomial_irrelevant_le_coordinates
  apply TopCat.Presheaf.IsSheaf.section_ext
    (F := (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).presheaf)
    (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k).isSheaf
  intro x hx
  have hx' : x ∈ iSup U := by simpa only [hcover] using hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  refine ⟨U i, le_top, hi, ?_⟩
  apply homogeneousPolynomialTwistingChartCoordinate_injective k i
  exact congrArg (fun z : coordinateHomogeneousCech (K := K) (I := I) k => z.val i) h

/-- Finite-dimensionality of actual global sections of the actual polynomial-Proj
O(k) sheaf is produced from the genuine finite localization Cech kernel. -/
theorem homogeneousPolynomialTwistingGlobalSections_finite [Nontrivial I] (k : ℕ) :
    Module.Finite K
      (bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤) := by
  let : Module.Finite K (coordinateHomogeneousCech (K := K) (I := I) k) :=
    coordinateHomogeneousCech_finite k
  exact FiniteDimensional.of_injective (K := K)
    (V := bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤)
    (V₂ := coordinateHomogeneousCech (K := K) (I := I) k)
    (homogeneousPolynomialTwistingGlobalToCech (K := K) (I := I) k)
    (homogeneousPolynomialTwistingGlobalToCech_injective (K := K) (I := I) k)


/-- Every actual homogeneous polynomial defines a genuine global shifted-fraction section. -/
def homogeneousPolynomialToTwistingGlobal (k : ℕ) :
    MvPolynomial.homogeneousSubmodule I K k →ₗ[K]
      bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤ where
  toFun p := by
    refine ⟨fun x => algebraMap (MvPolynomial I K)
      (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x.val) p.val, ?_⟩
    change (twistingFractionLocal (MvPolynomial.homogeneousSubmodule I K) k).pred
      (fun x : (⊤ : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens) =>
        algebraMap (MvPolynomial I K)
          (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x.val) p.val)
    apply PrelocalPredicate.sheafifyOf
    refine ⟨0, ⟨p.val, ?_⟩, ⟨1, SetLike.one_mem_graded _⟩,
      fun x => x.val.asHomogeneousIdeal.toIdeal.primeCompl.one_mem, ?_⟩
    · simp only [zero_add]
      exact p.property
    · intro x
      exact (Localization.mk_one_eq_algebraMap _).symm
  map_add' p q := by
    apply Subtype.ext
    funext x
    exact map_add _ _ _
  map_smul' r p := by
    apply Subtype.ext
    funext x
    change algebraMap (MvPolynomial I K)
        (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x.val) (r • p.val) =
      algebraMap (MvPolynomial I K)
        (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x.val) (MvPolynomial.C r) *
      algebraMap (MvPolynomial I K)
        (projectiveTwistingFiber (MvPolynomial.homogeneousSubmodule I K) x.val) p.val
    rw [Algebra.smul_def, map_mul]
    rfl

omit [Fintype I] in
/-- Actual specialization at the genuine zero homogeneous prime is faithful on each coordinate localization. -/
theorem homogeneousPolynomialCoordinateAtZero_injective [Nonempty I] (i : I) :
    Function.Injective (homogeneousPolynomialCoordinateAtPoint (K := K) i
      homogeneousPolynomialZeroPrime (homogeneousPolynomialZeroPrime_mem i)) := by
  intro z w h
  exact coordinateLocalizationToLaurent_injective i
    (homogeneousPolynomialCoordinateAtZero_compare i i z w h)

/-- The produced chart expression of a genuine polynomial section is its actual coordinate-localized polynomial. -/
theorem homogeneousPolynomialTwistingGlobalToCharts_polynomial [Nonempty I] (k : ℕ)
    (p : MvPolynomial.homogeneousSubmodule I K k) (i : I) :
    (homogeneousPolynomialTwistingGlobalToCharts k
      (homogeneousPolynomialToTwistingGlobal k p) i).val =
        algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) p.val := by
  apply homogeneousPolynomialCoordinateAtZero_injective i
  rw [homogeneousPolynomialCoordinateAtPoint_algebraMap]
  exact homogeneousPolynomialTwistingChartCoordinate_eval k i
    (homogeneousPolynomialTwistingRestriction k
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule I K) (MvPolynomial.X i)).leTop
      (homogeneousPolynomialToTwistingGlobal k p))
    homogeneousPolynomialZeroPrime (homogeneousPolynomialZeroPrime_mem i)

/-- Every actual compatible coordinate-degree tuple comes from a genuine global polynomial section. -/
theorem homogeneousPolynomialTwistingGlobalToCech_surjective [Nontrivial I] (k : ℕ) :
    Function.Surjective (homogeneousPolynomialTwistingGlobalToCech (K := K) (I := I) k) := by
  classical
  intro s
  let f := homogeneousChartCechEquiv (K := K) (I := I) k
    (coordinateHomogeneousCechToChart k s)
  obtain ⟨p, hp⟩ := homogeneousPolynomial_preimage k f
  have heq (i : I) : f.val = coordinateLocalizationToLaurent i (s.val i).val :=
    s.property (Classical.arbitrary I) i
  refine ⟨homogeneousPolynomialToTwistingGlobal k p, ?_⟩
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply coordinateLocalizationToLaurent_injective i
  change coordinateLocalizationToLaurent i
    (homogeneousPolynomialTwistingGlobalToCharts k
      (homogeneousPolynomialToTwistingGlobal k p) i).val = _
  calc
    _ = coordinateLocalizationToLaurent i
        (algebraMap (MvPolynomial I K) (Localization.Away (MvPolynomial.X i)) p.val) :=
      congrArg (coordinateLocalizationToLaurent (K := K) i)
        (homogeneousPolynomialTwistingGlobalToCharts_polynomial k p i)
    _ = coordinateLocalizationToLaurent i (s.val i).val := by
      rw [coordinateLocalizationToLaurent_algebraMap, hp, heq]

/-- Genuine global O(k) sections are exactly the actual degree-k coordinate localization Cech kernel. -/
def homogeneousPolynomialTwistingGlobalCechEquiv [Nontrivial I] (k : ℕ) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤ ≃ₗ[K]
      coordinateHomogeneousCech (K := K) (I := I) k :=
  LinearEquiv.ofBijective (homogeneousPolynomialTwistingGlobalToCech k)
    ⟨homogeneousPolynomialTwistingGlobalToCech_injective k,
      homogeneousPolynomialTwistingGlobalToCech_surjective k⟩

/-- Actual global sections of the actual polynomial-Proj O(k) sheaf equal the true homogeneous polynomial piece. -/
def homogeneousPolynomialTwistingGlobalPolynomialEquiv [Nontrivial I] (k : ℕ) :
    bundleSections (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule I K) k) ⊤ ≃ₗ[K]
      MvPolynomial.homogeneousSubmodule I K k :=
  (homogeneousPolynomialTwistingGlobalCechEquiv k).trans
    (coordinateHomogeneousCechPolynomialEquiv k)

end FiniteCoordinates

end

end ComplexSchemes
