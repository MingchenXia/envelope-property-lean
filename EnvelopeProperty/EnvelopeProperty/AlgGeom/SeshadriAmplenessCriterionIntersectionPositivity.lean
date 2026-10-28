import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionMixedEulerDifferences
import EnvelopeProperty.AlgGeom.CurveLineDegrees
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.AlgGeom.OriginalAmpleSerreVanishing
import Mathlib.Analysis.Polynomial.Basic

/-! Actual original intersection algebra and nonnegativity from native ampleness. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace Filter Topology
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open SchemeCoherentEulerCharacteristic SchemeCoherentEulerIndex SchemeCoherentEulerExact
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
variable (f : X ⟶ Spec (.of k))

theorem mixedEulerDifference_perm {ls ms : List X.Modules} (h : ls.Perm ms) (F : X.Modules) :
    mixedEulerDifference f ls F = mixedEulerDifference f ms F := by
  induction h generalizing F with
  | nil => rfl
  | cons L h ih =>
    change mixedEulerDifference f _ (F ⊗ L) - mixedEulerDifference f _ F =
      mixedEulerDifference f _ (F ⊗ L) - mixedEulerDifference f _ F
    rw [ih (F ⊗ L), ih F]
  | swap L M ls => exact mixedEulerDifference_swap f M L ls F
  | trans _ _ ih ih' => exact (ih F).trans (ih' F)

theorem mixedEulerDifference_singleton_eq_degree (L : X.Modules) :
    mixedEulerDifference f [L] (unitObj X) = CurveLineDegrees.degree f L := by
  change eulerCharacteristic f (unitObj X ⊗ L) - eulerCharacteristic f (unitObj X) =
    eulerCharacteristic f L - eulerCharacteristic f (unitObj X)
  let e : unitObj X ⊗ L ≅ L :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl L) ≪≫ λ_ L
  rw [eulerCharacteristic_eq_of_iso f e]

private theorem mixedEulerDifference_cons_iso {L M : X.Modules} (e : L ≅ M)
    (ls : List X.Modules) (F : X.Modules) :
    mixedEulerDifference f (L :: ls) F = mixedEulerDifference f (M :: ls) F := by
  change mixedEulerDifference f ls (F ⊗ L) - mixedEulerDifference f ls F =
    mixedEulerDifference f ls (F ⊗ M) - mixedEulerDifference f ls F
  rw [mixedEulerDifference_eq_of_iso f ls (Iso.refl F ⊗ᵢ e)]

theorem mixedEulerDifference_unit_cons (ls : List X.Modules) (F : X.Modules) :
    mixedEulerDifference f (unitObj X :: ls) F = 0 := by
  let e : F ⊗ unitObj X ≅ F :=
    (Iso.refl F ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ F
  change mixedEulerDifference f ls (F ⊗ unitObj X) - mixedEulerDifference f ls F = 0
  rw [mixedEulerDifference_eq_of_iso f ls e, sub_self]

theorem mixedEulerDifference_tensorPower_cons [X.IsSeparated] [IsProjective f]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (L : X.Modules) (hL : IsInvertible L)
    (ls : List X.Modules) (hlen : ls.length + 1 = d) (hls : ∀ K ∈ ls, IsInvertible K)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ) :
    mixedEulerDifference f (CanonicalGeometry.bundleTensorPower L r :: ls) F =
      (r : ℤ) * mixedEulerDifference f (L :: ls) F := by
  induction r with
  | zero =>
    change mixedEulerDifference f (unitObj X :: ls) F = (0 : ℤ) * _
    rw [mixedEulerDifference_unit_cons, zero_mul]
  | succ r ih =>
    let e : CanonicalGeometry.bundleTensorPower L (r + 1) ≅
        CanonicalGeometry.bundleTensorPower L r ⊗ L :=
      (ModularCurves.monoidalTensorObjIso (CanonicalGeometry.bundleTensorPower L r) L).symm
    rw [mixedEulerDifference_cons_iso f e]
    rw [mixedEulerDifference_tensor_add f d hdim _ L
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) hL ls hlen hls F, ih]
    push_cast
    ring

theorem eulerCharacteristic_eq_finrank_of_native_vanishing [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (h : ∀ q : ℕ, Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1))) :
    eulerCharacteristic f M = (Module.finrank k (fieldSections f M) : ℤ) := by
  let U := finiteAffineOpens X
  have hU := finiteAffineOpens_cover X
  have hUa := finiteAffineOpens_isAffine X
  have hz (q : ℕ) : IsZero (fieldCech f M U (q + 1)) := by
    have hn := cechComplex_exactAt_succ_of_affine_openCover M U hU hUa q (h q)
    have hb := (baseCechComplex_exactAt_iff f M U (q + 1)).mpr hn
    have hzero := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hb
    exact (ModuleCat.restrictScalars (baseScalar (k := k))).map_isZero hzero
  unfold eulerCharacteristic coverEuler
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]
    exact congrArg (fun n : ℕ => (n : ℤ))
      (fieldSectionsCechZeroIso f M U hU).toLinearEquiv.finrank_eq.symm
  · intro n _ hn
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    let : Subsingleton (fieldCech f M U (q + 1)) := ModuleCat.subsingleton_of_isZero (hz q)
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]
  · intro hn
    exact (hn (by simp)).elim

theorem exists_eulerCharacteristic_power_nonneg_of_isAmple [X.IsSeparated]
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hA : SchemeLineAmpleness.IsAmple f L) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      0 ≤ eulerCharacteristic f (F ⊗ CanonicalGeometry.bundleTensorPower L m) := by
  obtain ⟨hL, r, hr, d, i, hi, _hbase, ⟨η⟩⟩ := hA
  let : IsClosedImmersion i := hi
  obtain ⟨N, hN⟩ := @OriginalAmpleSerreVanishing.exists_sheafCohomology_bound
    k _ _ (Fin (d + 1)) _ X i hi F L inferInstance inferInstance
      hL r hr (0 : Fin (d + 1)) η.symm
  refine ⟨N, fun m hm => ?_⟩
  let P := F ⊗ CanonicalGeometry.bundleTensorPower L m
  let : P.IsQuasicoherent := SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight F _
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL m)
  rw [eulerCharacteristic_eq_finrank_of_native_vanishing f P (hN m hm)]
  exact Int.natCast_nonneg _

theorem polynomial_coeff_nonneg_of_eventual_nat_nonneg (p : Polynomial ℚ) (d : ℕ)
    (hdeg : p.natDegree ≤ d) (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ p.eval (n : ℚ)) :
    0 ≤ p.coeff d := by
  by_cases heq : p.natDegree = d
  · have hc : p.coeff d = p.leadingCoeff := by rw [← heq]; rfl
    rw [hc]
    obtain ⟨N, hN⟩ := h
    by_cases hd : d = 0
    · have hp := Polynomial.eq_C_of_natDegree_eq_zero (heq.trans hd)
      have hval := hN N le_rfl
      rw [hp, Polynomial.eval_C] at hval
      simpa only [Polynomial.leadingCoeff, heq, hd] using hval
    · by_contra hneg
      have hneg : p.leadingCoeff < 0 := lt_of_not_ge hneg
      have hpdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
      have ht : Tendsto (fun n : ℕ => p.eval (n : ℚ)) atTop atBot :=
        (p.tendsto_atBot_of_leadingCoeff_nonpos hpdeg hneg.le).comp tendsto_natCast_atTop_atTop
      have hnn : ∀ᶠ n : ℕ in atTop, 0 ≤ p.eval (n : ℚ) := eventually_atTop.mpr ⟨N, hN⟩
      obtain ⟨n, hn, hn'⟩ := ((ht.eventually_lt_atBot 0).and hnn).exists
      exact (not_lt_of_ge hn') hn
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

theorem mixedEulerDifference_replicate_nonneg_of_isAmple [X.IsSeparated] [IsProjective f]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F L : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hA : SchemeLineAmpleness.IsAmple f L) :
    0 ≤ mixedEulerDifference f (List.replicate d L) F := by
  obtain ⟨N, hN⟩ := exists_eulerCharacteristic_power_nonneg_of_isAmple f F L hA
  have hc := polynomial_coeff_nonneg_of_eventual_nat_nonneg (eulerPolynomial f F L hA.1) d
    (eulerPolynomial_natDegree_le f F L hA.1 d hdim) ⟨N, fun n hn => by
      rw [eulerPolynomial_eval]
      exact_mod_cast hN n hn⟩
  have hz : (0 : ℚ) ≤ (mixedEulerDifference f (List.replicate d L) F : ℚ) := by
    rw [mixedEulerDifference_replicate_eq_factorial_mul_coeff f d hdim F L hA.1]
    exact mul_nonneg (Nat.cast_nonneg _) hc
  exact_mod_cast hz

#check @mixedEulerDifference_perm
#print axioms mixedEulerDifference_perm
#check @mixedEulerDifference_singleton_eq_degree
#print axioms mixedEulerDifference_singleton_eq_degree
#check @mixedEulerDifference_unit_cons
#print axioms mixedEulerDifference_unit_cons
#check @mixedEulerDifference_tensorPower_cons
#print axioms mixedEulerDifference_tensorPower_cons
#check @eulerCharacteristic_eq_finrank_of_native_vanishing
#print axioms eulerCharacteristic_eq_finrank_of_native_vanishing
#check @exists_eulerCharacteristic_power_nonneg_of_isAmple
#print axioms exists_eulerCharacteristic_power_nonneg_of_isAmple
#check @polynomial_coeff_nonneg_of_eventual_nat_nonneg
#print axioms polynomial_coeff_nonneg_of_eventual_nat_nonneg
#check @mixedEulerDifference_replicate_nonneg_of_isAmple
#print axioms mixedEulerDifference_replicate_nonneg_of_isAmple
end EnvelopeProperty.SeshadriAmplenessCriterion
