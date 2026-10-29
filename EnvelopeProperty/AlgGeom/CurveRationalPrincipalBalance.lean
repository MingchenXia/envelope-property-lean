import EnvelopeProperty.AlgGeom.SchemeRationalDenominatorSections
import EnvelopeProperty.AlgGeom.CurveDenominatorCartier
import EnvelopeProperty.AlgGeom.CurveCartierLocalOrders

/-! # Genuine native orders and principal weighted balance on the original curve -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open scoped nonZeroDivisors
universe u
namespace EnvelopeProperty.CurveRationalPrincipalBalance
open RationalDenominatorIdeals SchemeRationalDenominators CurveCartierLocalOrders
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem reciprocal_span (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (f : K) (hf : f ≠ 0) (c : R)
    (hc : denominatorIdeal R K f = Ideal.span {c}) :
    let a : denominatorIdeal R K f := ⟨c, hc.symm ▸ Ideal.mem_span_singleton_self c⟩
    denominatorIdeal R K f⁻¹ = Ideal.span {clearedNumerator R K f a} := by
  let a₀ : denominatorIdeal R K f := ⟨c, hc.symm ▸ Ideal.mem_span_singleton_self c⟩
  change denominatorIdeal R K f⁻¹ = Ideal.span {clearedNumerator R K f a₀}
  apply le_antisymm
  · intro b hb
    obtain ⟨a, ha⟩ := (reciprocalEquiv R K f hf).surjective ⟨b, hb⟩
    have hamem : (a : R) ∈ Ideal.span {c} := hc ▸ a.property
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hamem
    have hba : algebraMap R K b = algebraMap R K a * f :=
      (congrArg (fun z : denominatorIdeal R K f⁻¹ => algebraMap R K z) ha).symm.trans
        (reciprocalEquiv_coefficient R K f hf a)
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨r, IsFractionRing.injective R K ?_⟩
    calc
      algebraMap R K (r * clearedNumerator R K f a₀) =
          algebraMap R K r * (algebraMap R K c * f) := by rw [map_mul, algebraMap_clearedNumerator]
      _ = algebraMap R K (r * c) * f := by rw [map_mul, mul_assoc]
      _ = algebraMap R K a * f := by rw [hr]
      _ = algebraMap R K b := hba.symm
  · apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr ((reciprocalMap R K f hf a₀).property)

section LocalOrders
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The native order of the SAME arbitrary original rational function is
the actual reciprocal-denominator local order minus the denominator order. -/
theorem ord_eq_denominator_difference (f : X.functionField) (hf : f ≠ 0)
    (hI : (idealSheaf X f).IsInvertible) (hJ : (idealSheaf X f⁻¹).IsInvertible) (x : X) :
    X.ord f x = localOrder (idealSheaf X f⁻¹) hJ x - localOrder (idealSheaf X f) hI x := by
  let I := idealSheaf X f
  let J := idealSheaf X f⁻¹
  let U := equationChart I hI x
  let c : Γ(X, U) := equation I hI x
  let : Nonempty U.1 := ⟨⟨x, mem_equationChart I hI x⟩⟩
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  have hc : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp (equation_mem_nonZeroDivisors I hI x)
  have hcI : denominatorIdeal Γ(X, U) X.functionField f = Ideal.span {c} := by
    rw [← idealSheaf_ideal]
    exact equation_span I hI x
  let a : denominatorIdeal Γ(X, U) X.functionField f :=
    ⟨c, hcI.symm ▸ Ideal.mem_span_singleton_self c⟩
  let b : Γ(X, U) := clearedNumerator Γ(X, U) X.functionField f a
  have hbval : X.germToFunctionField U.1 b = X.germToFunctionField U.1 c * f :=
    algebraMap_clearedNumerator Γ(X, U) X.functionField f a
  have hcK : X.germToFunctionField U.1 c ≠ 0 := by
    exact (map_ne_zero_iff _ (X.germToFunctionField_injective U.1)).mpr hc
  have hb : b ≠ 0 := by
    intro hb0
    have hz := hbval
    rw [hb0, map_zero] at hz
    exact mul_ne_zero hcK hf hz.symm
  have hJgen : J.ideal U = Ideal.span {b} := by
    rw [idealSheaf_ideal]
    exact reciprocal_span Γ(X, U) X.functionField f hf c hcI
  have hIord := localOrder_eq_ord_of_local_equation I hI U c hc
    (equation_span I hI x) x (mem_equationChart I hI x)
  have hJord := localOrder_eq_ord_of_local_equation J hJ U b hb hJgen x
    (mem_equationChart I hI x)
  have horder : X.ord (X.germToFunctionField U.1 b) x =
      X.ord (X.germToFunctionField U.1 c) x + X.ord f x := by
    rw [hbval]
    exact X.ord_mul hcK hf
  change X.ord f x = localOrder J hJ x - localOrder I hI x
  rw [hIord, hJord]
  omega

/-- On the actual original normal curve both Cartier denominators in the
native order formula are DERIVED, without a supplied Cartier premise. -/
theorem ord_eq_normal_denominator_difference (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X.functionField) (hf : f ≠ 0) (x : X) :
    X.ord f x =
      localOrder (idealSheaf X f⁻¹) (CurveDenominatorCartier.denominator_isInvertible hdim hNormal f⁻¹) x -
        localOrder (idealSheaf X f) (CurveDenominatorCartier.denominator_isInvertible hdim hNormal f) x :=
  ord_eq_denominator_difference f hf _ _ x


/-- Native original rational order, weighted by the actual ORIGINAL ambient
residue field and the literal original coefficient action. -/
def weightedOrder {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    (f : X.functionField) (x : X) : ℤ :=
  letI := AffineSchemeLocalDegrees.residueAlgebra p x
  X.ord f x * (Module.finrank k (X.residueField x) : ℤ)

end LocalOrders

variable {X : Scheme.{u}} [IsIntegral X]

private theorem finite_weightedLocalOrder [AlgebraicGeometry.IsNoetherian X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.IsInvertible) :
    Function.HasFiniteSupport (weightedLocalOrder p I hI) := by
  let : Finite I.subscheme := CurveFiniteClosedSubschemes.finite_subscheme hdim I
    (CurveCartierIdealDegrees.support_ne_top I hI)
  have hs : (I.support : Set X).Finite := by
    rw [← I.range_subschemeι]
    exact Set.finite_range I.subschemeι
  apply hs.subset
  intro x hx
  by_contra hnot
  apply hx
  unfold weightedLocalOrder
  rw [localOrder_eq_zero_of_not_mem_support I hI x hnot, zero_mul]


private theorem finite_localOrder [AlgebraicGeometry.IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.IsInvertible) :
    Function.HasFiniteSupport (localOrder I hI) := by
  let : Finite I.subscheme := CurveFiniteClosedSubschemes.finite_subscheme hdim I
    (CurveCartierIdealDegrees.support_ne_top I hI)
  have hs : (I.support : Set X).Finite := by
    rw [← I.range_subschemeι]
    exact Set.finite_range I.subschemeι
  apply hs.subset
  intro x hx
  by_contra hnot
  exact hx (localOrder_eq_zero_of_not_mem_support I hI x hnot)

/-- Actual finite support of the SAME native rational order on a normal
Noetherian original integral curve, derived from genuine Cartier denominators. -/
theorem hasFiniteSupport_ord [AlgebraicGeometry.IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X.functionField) (hf : f ≠ 0) : Function.HasFiniteSupport (X.ord f) := by
  let I := idealSheaf X f
  let J := idealSheaf X f⁻¹
  let hI : I.IsInvertible := CurveDenominatorCartier.denominator_isInvertible hdim hNormal f
  let hJ : J.IsInvertible := CurveDenominatorCartier.denominator_isInvertible hdim hNormal f⁻¹
  have heq : X.ord f = fun x => localOrder J hJ x - localOrder I hI x :=
    funext (ord_eq_denominator_difference f hf hI hJ)
  rw [heq]
  exact (finite_localOrder hdim J hJ).sub (finite_localOrder hdim I hI)

/-- The literal original residue-weighted rational orders have genuinely
finite support, with no finiteness premise for the final principal sum. -/
theorem hasFiniteSupport_weightedOrder [AlgebraicGeometry.IsNoetherian X]
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X.functionField) (hf : f ≠ 0) : Function.HasFiniteSupport (weightedOrder p f) := by
  apply (hasFiniteSupport_ord hdim hNormal f hf).subset
  intro x hx
  by_contra hzero
  apply hx
  unfold weightedOrder
  rw [show X.ord f x = 0 from by simpa only [Function.mem_support, not_not] using hzero, zero_mul]

/-- True weighted principal-divisor balance for EVERY nonzero rational
function on the SAME original normal integral projective curve. All
Cartier denominators, support finiteness and auxiliary geometry are derived. -/
theorem finsum_weightedOrder_eq_zero {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1)
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X.functionField) (hf : f ≠ 0) :
    letI : IsProper p := hp.isProper
    letI : LocallyOfFiniteType p := inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    (∑ᶠ x : X, weightedOrder p f x) = 0 := by
  let : IsProper p := hp.isProper
  let : LocallyOfFiniteType p := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let I := idealSheaf X f
  let J := idealSheaf X f⁻¹
  let hI : I.IsInvertible := CurveDenominatorCartier.denominator_isInvertible hdim hNormal f
  let hJ : J.IsInvertible := CurveDenominatorCartier.denominator_isInvertible hdim hNormal f⁻¹
  have hpoint (x : X) : weightedOrder p f x =
      weightedLocalOrder p J hJ x - weightedLocalOrder p I hI x := by
    unfold weightedOrder weightedLocalOrder
    rw [ord_eq_denominator_difference f hf hI hJ x, sub_mul]
  have hEuler := SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic_eq_of_iso p
    (SchemeRationalDenominatorSections.reciprocalIso X f hf)
  have hIχ := normalizedEulerCharacteristic_eq_neg_finsum p hp hdim I hI
  have hJχ := normalizedEulerCharacteristic_eq_neg_finsum p hp hdim J hJ
  rw [hIχ, hJχ] at hEuler
  have hsum : (∑ᶠ x : X, weightedLocalOrder p J hJ x) =
      (∑ᶠ x : X, weightedLocalOrder p I hI x) := by omega
  calc
    (∑ᶠ x : X, weightedOrder p f x) =
        ∑ᶠ x : X, (weightedLocalOrder p J hJ x - weightedLocalOrder p I hI x) :=
      finsum_congr hpoint
    _ = (∑ᶠ x : X, weightedLocalOrder p J hJ x) -
        (∑ᶠ x : X, weightedLocalOrder p I hI x) :=
      finsum_sub_distrib (finite_weightedLocalOrder p hdim J hJ)
        (finite_weightedLocalOrder p hdim I hI)
    _ = 0 := sub_eq_zero.mpr hsum

end EnvelopeProperty.CurveRationalPrincipalBalance
