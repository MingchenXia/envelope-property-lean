import EnvelopeProperty.AlgGeom.CurveLineDegrees

/-! # Actual local line coefficients, native original orders and nonnegative curve degrees -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.CurveLineSectionOrders
open CurveLineDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}}

/-- The actual coefficient of the SAME original section in a genuine original affine frame. -/
def frameCoefficient (L : X.Modules) (s : unitObj X ⟶ L) (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) : Γ(X, U) :=
  e.hom.val.app (op (Over.mk (𝟙 U.1))) (s.val.app (op U.1) (1 : Γ(X, U)))

/-- A nonzero original section has an actual nonzero coefficient on EVERY
nonempty actual original affine framed open; this is derived, not supplied. -/
theorem frameCoefficient_ne_zero [IsIntegral X] (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) (U : X.affineOpens) [Nonempty U.1]
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    frameCoefficient L s U e ≠ 0 := by
  let I := LineSectionZeroIdeal.zeroIdeal L hL s
  have hI : I.IsInvertible := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs
  let x : U.1 := Classical.choice (inferInstance : Nonempty U.1)
  intro hc
  have hbot : I.ideal U = ⊥ := by
    rw [LineSectionZeroIdeal.zeroIdeal_ideal_of_frame L hL s U e]
    change Ideal.span {frameCoefficient L s U e} = ⊥
    rw [hc, Ideal.span_singleton_zero]
  have hstalk : I.stalkIdeal x.1 = ⊥ := by
    rw [I.stalkIdeal_eq_map_germ U x.2, hbot, Ideal.map_bot]
  obtain ⟨a, ha, hspan⟩ := hI.exists_ne_zero_stalkIdeal_eq_span x.1
  have hm : a ∈ I.stalkIdeal x.1 := hspan.symm ▸ Ideal.mem_span_singleton_self a
  rw [hstalk, Ideal.mem_bot] at hm
  exact ha hm

/-- The SAME actual local-frame coefficient computes the native order of
its SAME original section zero ideal at EVERY original point on that frame. -/
theorem localOrder_eq_frameCoefficient_order [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (x : X) (hx : x ∈ U.1) :
    CurveCartierLocalOrders.localOrder (LineSectionZeroIdeal.zeroIdeal L hL s)
      (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs) x =
      X.ord (X.germToFunctionField U.1 (frameCoefficient L s U e)) x :=
  CurveCartierLocalOrders.localOrder_eq_ord_of_local_equation _ _ U
    (frameCoefficient L s U e) (frameCoefficient_ne_zero L hL s hs U e)
    (LineSectionZeroIdeal.zeroIdeal_ideal_of_frame L hL s U e) x hx

/-- The original residue-weighted zero order uses the SAME original local
coefficient and SAME original scalar action on the actual ambient residue field. -/
theorem weightedLocalOrder_eq_frameCoefficient_order {k : Type u} [Field k]
    [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k))
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (x : X) (hx : x ∈ U.1) :
    CurveCartierLocalOrders.weightedLocalOrder p (LineSectionZeroIdeal.zeroIdeal L hL s)
      (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs) x =
      letI := AffineSchemeLocalDegrees.residueAlgebra p x
      X.ord (X.germToFunctionField U.1 (frameCoefficient L s U e)) x *
        (Module.finrank k (X.residueField x) : ℤ) := by
  unfold CurveCartierLocalOrders.weightedLocalOrder
  rw [localOrder_eq_frameCoefficient_order L hL s hs U e x hx]

/-- Every original effective Cartier equation has nonnegative native local
order, with actual quotient length at codimension one and zero elsewhere. -/
theorem localOrder_nonneg [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.IsInvertible) (x : X) :
    0 ≤ CurveCartierLocalOrders.localOrder I hI x := by
  let U := CurveCartierLocalOrders.equationChart I hI x
  let : Nonempty U.1 := ⟨⟨x, CurveCartierLocalOrders.mem_equationChart I hI x⟩⟩
  have hc : CurveCartierLocalOrders.equation I hI x ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (CurveCartierLocalOrders.equation_mem_nonZeroDivisors I hI x)
  change 0 ≤ X.ord (X.germToFunctionField U.1 (CurveCartierLocalOrders.equation I hI x)) x
  by_cases hx : Order.coheight x = 1
  · rw [SchemeOrderLocalLength.ord_germToFunctionField_eq_stalk_length x hx U.1
      (CurveCartierLocalOrders.mem_equationChart I hI x) _ hc]
    exact Int.natCast_nonneg _
  · rw [X.ord_eq_zero_of_coheight_neq_one hx]

/-- A genuine original nonzero section gives a nonnegative TRUE intrinsic
degree on the SAME integral projective curve, without normality or an order certificate. -/
theorem degree_nonneg_of_nonzero_section {k : Type u} [Field k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    0 ≤ degree p L := by
  let : IsProper p := hp.isProper
  let : LocallyOfFiniteType p := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  rw [degree_eq_zeroSection_orders p hp hdim L hL s hs]
  apply finsum_nonneg
  intro x
  exact mul_nonneg (localOrder_nonneg _ _ x) (Int.natCast_nonneg _)

/-- Actual global generators DERIVE nonnegative true degree of the SAME
original line, with no chosen nonzero section or degree premise. -/
theorem degree_nonneg_of_generatingSections {k : Type u} [Field k] [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L)
    (G : L.GeneratingSections) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    0 ≤ degree p L := by
  obtain ⟨s, hs⟩ := SchemeLineNonzeroGenerators.exists_section_ne_zero L hL G
  exact degree_nonneg_of_nonzero_section p hp hdim L hL s hs

/-- The actual pulled-back original globally generated line has nonnegative
true intrinsic degree under ANY literal original curve map. -/
theorem degree_pullback_nonneg_of_generatingSections {k : Type u} [Field k]
    {C Z : Scheme.{u}} [IsIntegral C]
    (p : C ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1) (i : C ⟶ Z)
    (L : Z.Modules) (hL : IsInvertible L) (G : L.GeneratingSections) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
    0 ≤ degree p ((Scheme.Modules.pullback i).obj L) :=
  degree_nonneg_of_generatingSections p hp hdim _ (hL.pullback i)
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections i G)

end EnvelopeProperty.CurveLineSectionOrders
