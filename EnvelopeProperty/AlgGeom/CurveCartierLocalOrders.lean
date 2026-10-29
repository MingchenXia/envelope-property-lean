import EnvelopeProperty.AlgGeom.CurveCartierIdealDegrees
import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! # Actual original Cartier local equations, native orders and true curve degrees -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules
open scoped nonZeroDivisors
noncomputable section
universe u
namespace EnvelopeProperty.CurveCartierLocalOrders
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- An actual ORIGINAL Cartier affine neighborhood, chosen from the original equations. -/
def equationChart (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) : X.affineOpens :=
  (hI x).choose

/-- The actual ORIGINAL point lies on this ORIGINAL Cartier affine chart. -/
theorem mem_equationChart (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) :
    x ∈ (equationChart I hI x).1 := (hI x).choose_spec.1

/-- The actual ORIGINAL regular Cartier equation on that ORIGINAL chart. -/
def equation (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) :
    Γ(X, (equationChart I hI x).1) := (hI x).choose_spec.2.choose

/-- The actual ORIGINAL equation is a genuine nonzerodivisor. -/
theorem equation_mem_nonZeroDivisors (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) :
    equation I hI x ∈ nonZeroDivisors Γ(X, (equationChart I hI x).1) :=
  (hI x).choose_spec.2.choose_spec.1

/-- The actual ORIGINAL equation generates the SAME ORIGINAL geometric ideal. -/
theorem equation_span (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) :
    I.ideal (equationChart I hI x) = Ideal.span {equation I hI x} :=
  (hI x).choose_spec.2.choose_spec.2

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The native ORIGINAL Scheme.ord of the actual ORIGINAL Cartier local equation. -/
def localOrder (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) : ℤ :=
  letI : Nonempty (equationChart I hI x).1 := ⟨⟨x, mem_equationChart I hI x⟩⟩
  X.ord (X.germToFunctionField (equationChart I hI x).1 (equation I hI x)) x

/-- On every ORIGINAL closed Cartier subscheme point of an actual integral
curve, the actual native local order equals the SAME actual closed-stalk length. -/
theorem localOrder_eq_closed_stalk_length
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.IsInvertible)
    (y : I.subscheme) :
    localOrder I hI (I.subschemeι y) =
      ((Module.length (I.subscheme.presheaf.stalk y) (I.subscheme.presheaf.stalk y)).toNat : ℤ) := by
  let x := I.subschemeι y
  let U := equationChart I hI x
  let : Nonempty U.1 := ⟨⟨x, mem_equationChart I hI x⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hc0 : equation I hI x ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (equation_mem_nonZeroDivisors I hI x)
  have hker : I.subschemeι.ker.ideal U = Ideal.span {equation I hI x} := by
    rw [I.ker_subschemeι]
    exact equation_span I hI x
  have hx : x ≠ genericPoint X := by
    intro hx
    exact CurveFiniteClosedSubschemes.genericPoint_not_mem I.support
      (CurveCartierIdealDegrees.support_ne_top I hI) (hx ▸ y.property)
  change X.ord (X.germToFunctionField U.1 (equation I hI x)) x = _
  exact ClosedImmersionStalkQuotients.ord_eq_closedStalk_length I.subschemeι U.1 U.2
    (equation I hI x) hc0 hker y (mem_equationChart I hI x)
    (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx)

/-- The actual native local Cartier order is zero outside the SAME original support. -/
theorem localOrder_eq_zero_of_not_mem_support
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) (hx : x ∉ I.support) :
    localOrder I hI x = 0 := by
  let U := equationChart I hI x
  let : Nonempty U.1 := ⟨⟨x, mem_equationChart I hI x⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have hc0 : equation I hI x ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (equation_mem_nonZeroDivisors I hI x)
  have hb : x ∈ X.basicOpen (equation I hI x) := by
    have hz : x ∉ X.zeroLocus (U := U.1) (I.ideal U) :=
      fun hz => hx ((I.mem_support_iff_of_mem (mem_equationChart I hI x)).mpr hz)
    rw [equation_span I hI x, X.zeroLocus_span, X.zeroLocus_singleton] at hz
    exact not_not.mp hz
  change X.ord (X.germToFunctionField U.1 (equation I hI x)) x = 0
  by_cases hcodim : Order.coheight x = 1
  · rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length x hcodim U.1
      (mem_equationChart I hI x) (equation I hI x) hc0]
    have hunit := (X.mem_basicOpen (equation I hI x) x (mem_equationChart I hI x)).mp hb
    rw [Ideal.span_singleton_eq_top.mpr hunit]
    simp
  · exact X.ord_eq_zero_of_coheight_neq_one hcodim _

/-- The ACTUAL original local Cartier order weighted by its ORIGINAL
ambient residue-field degree over the SAME original structure field. -/
def weightedLocalOrder {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) : ℤ :=
  letI := AffineSchemeLocalDegrees.residueAlgebra f x
  localOrder I hI x * (Module.finrank k (X.residueField x) : ℤ)

private theorem weightedLocalOrder_eq_zero_of_not_mem_support {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (hI : I.IsInvertible)
    (x : X) (hx : x ∉ I.support) : weightedLocalOrder f I hI x = 0 := by
  unfold weightedLocalOrder
  rw [localOrder_eq_zero_of_not_mem_support I hI x hx, zero_mul]

/-- The sum of the ACTUAL weighted native orders on the WHOLE ORIGINAL
curve is the sum over the SAME original closed subscheme, with no chosen support proxy. -/
theorem finsum_weightedLocalOrder_eq_closed {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (hI : I.IsInvertible) :
    ∑ᶠ x : X, weightedLocalOrder f I hI x =
      ∑ᶠ y : I.subscheme, weightedLocalOrder f I hI (I.subschemeι y) := by
  have hs : Set.univ ∩ Function.support (weightedLocalOrder f I hI) =
      (I.support : Set X) ∩ Function.support (weightedLocalOrder f I hI) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨?_, hx⟩
      by_contra hn
      exact hx (weightedLocalOrder_eq_zero_of_not_mem_support f I hI x hn)
    · exact And.right
  rw [← finsum_mem_univ (weightedLocalOrder f I hI),
    finsum_mem_inter_support_eq (weightedLocalOrder f I hI) Set.univ I.support hs,
    ← I.range_subschemeι, finsum_mem_range I.subschemeι.isEmbedding.injective]

/-- ANY actual original affine generator of the SAME original Cartier ideal
has the SAME native order; no local-frame/order preservation datum is assumed. -/
theorem localOrder_eq_ord_of_local_equation
    (I : X.IdealSheafData) (hI : I.IsInvertible) (U : X.affineOpens) [Nonempty U.1]
    (c : Γ(X, U.1)) (hc : c ≠ 0) (hgen : I.ideal U = Ideal.span {c})
    (x : X) (hx : x ∈ U.1) :
    localOrder I hI x = X.ord (X.germToFunctionField U.1 c) x := by
  let V := equationChart I hI x
  let : Nonempty V.1 := ⟨⟨x, mem_equationChart I hI x⟩⟩
  let : IsDomain Γ(X, V.1) := IsIntegral.component_integral V.1
  have hcV : equation I hI x ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (equation_mem_nonZeroDivisors I hI x)
  change X.ord (X.germToFunctionField V.1 (equation I hI x)) x = _
  by_cases hcodim : Order.coheight x = 1
  · rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length x hcodim V.1
      (mem_equationChart I hI x) (equation I hI x) hcV,
      SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length x hcodim U.1 hx c hc]
    have hspan : Ideal.span {X.presheaf.germ V.1 x (mem_equationChart I hI x) (equation I hI x)} =
        Ideal.span {X.presheaf.germ U.1 x hx c} := by
      calc
        _ = (I.ideal V).map (X.presheaf.germ V.1 x (mem_equationChart I hI x)).hom := by
          rw [equation_span I hI x, Ideal.map_span]
          simp
        _ = I.stalkIdeal x := (I.stalkIdeal_eq_map_germ V (mem_equationChart I hI x)).symm
        _ = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := I.stalkIdeal_eq_map_germ U hx
        _ = _ := by rw [hgen, Ideal.map_span]; simp
    rw [hspan]
  · rw [X.ord_eq_zero_of_coheight_neq_one hcodim,
      X.ord_eq_zero_of_coheight_neq_one hcodim]

omit [IsLocallyNoetherian X] in
/-- TRUE intrinsic full Euler degree equals minus the weighted NATIVE
original local orders on the WHOLE original curve; ALL finiteness is derived. -/
theorem normalizedEulerCharacteristic_eq_neg_finsum {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (hdim : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I.IsInvertible) :
    letI : IsProper f := hf.isProper
    letI : LocallyOfFiniteType f := inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic f I.toModules =
      -(∑ᶠ x : X, weightedLocalOrder f I hI x) := by
  let : IsProper f := hf.isProper
  let : LocallyOfFiniteType f := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : AlgebraicGeometry.IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let : Finite I.subscheme := CurveFiniteClosedSubschemes.finite_subscheme hdim I
    (CurveCartierIdealDegrees.support_ne_top I hI)
  let : Fintype I.subscheme := Fintype.ofFinite _
  let : IsFinite (I.subschemeι ≫ f) := CurveCartierIdealDegrees.subscheme_comp_isFinite f hdim I hI
  have h := GeometricIdealEulerDegree.normalizedEulerCharacteristic_toModules_eq_neg_weighted_sum I f hf
  rw [finsum_weightedLocalOrder_eq_closed]
  have hs : (∑ᶠ y : I.subscheme, weightedLocalOrder f I hI (I.subschemeι y)) =
      ((∑ᶠ y : I.subscheme, letI := AffineSchemeLocalDegrees.residueAlgebra f (I.subschemeι y)
        (Module.length (I.subscheme.presheaf.stalk y) (I.subscheme.presheaf.stalk y)).toNat *
          Module.finrank k (X.residueField (I.subschemeι y))) : ℕ) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _hy
    unfold weightedLocalOrder
    rw [localOrder_eq_closed_stalk_length hdim I hI y, Nat.cast_mul]
  rw [hs]
  exact h

omit [IsLocallyNoetherian X] in
/-- The SAME ORIGINAL Cartier ratio line degree is the difference of TRUE
weighted native orders over EVERY point of the WHOLE original curve. -/
theorem normalizedEulerCharacteristic_ratio_eq_finsum_difference {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (hdim : topologicalKrullDim X ≤ 1) (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    letI : IsProper f := hf.isProper
    letI : LocallyOfFiniteType f := inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic f (I.ratioModule J) =
      (∑ᶠ x : X, weightedLocalOrder f J hJ x) - ∑ᶠ x : X, weightedLocalOrder f I hI x := by
  let : IsProper f := hf.isProper
  let : LocallyOfFiniteType f := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  rw [CurveCartierIdealDegrees.normalizedEulerCharacteristic_ratioModule f hf hdim I J hI hJ,
    normalizedEulerCharacteristic_eq_neg_finsum f hf hdim I hI,
    normalizedEulerCharacteristic_eq_neg_finsum f hf hdim J hJ]
  omega

end EnvelopeProperty.CurveCartierLocalOrders
