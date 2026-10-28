import EnvelopeProperty.AlgGeom.ClosedImmersionStalkQuotients
import EnvelopeProperty.AlgGeom.CurveFiniteClosedSubschemes
import EnvelopeProperty.AlgGeom.GaussRegularSurfaceValuationFractions
import EnvelopeProperty.Algebra.SemilinearPrincipalLengths

/-! # The SAME original central curve carries the canonical leading field and full order -/

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open scoped nonZeroDivisors WithZero
noncomputable section
universe u

namespace EnvelopeProperty.CentralCurveLeadingOrders

/-- A whole original ring isomorphism preserves the exact native order on ALL fractions. -/
theorem ordFrac_ringEquiv {R A K L : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (e : R ≃+* A) (f : K) :
    Ring.ordFrac R f =
      Ring.ordFrac A (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e f) := by
  have hcoeff (a : R) :
      Ring.ordFrac R (algebraMap R K a) =
        Ring.ordFrac A (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := L) e
          (algebraMap R K a)) := by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    by_cases ha : a = 0
    · subst a
      simp
    have hea : e a ≠ 0 := (map_ne_zero_iff e e.injective).mpr ha
    rw [Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord A hea,
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero ha),
      Ring.ordMonoidWithZeroHom_eq_ord (mem_nonZeroDivisors_of_ne_zero hea),
      SemilinearPrincipalLengths.ord_ringEquiv e a]
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R f
  simp only [map_div₀, hcoeff]

variable {Y C : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i] (x : C)

local notation "S" => Y.presheaf.stalk (i x)
local notation "A" => C.presheaf.stalk x

/-- The actual original closed-immersion stalk map constructs its true principal quotient. -/
def stalkQuotientEquiv (π : S)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    (S ⧸ Ideal.span {π}) ≃+* A :=
  (Ideal.quotEquivOfEq hker.symm).trans
    ((i.stalkMap x).hom.quotientKerEquivOfSurjective (i.stalkMap_surjective x))

/-- Every original stalk coefficient retains its literal original closed-immersion image. -/
theorem stalkQuotientEquiv_mk (π : S)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (s : S) :
    stalkQuotientEquiv i x π hker (Ideal.Quotient.mk _ s) = i.stalkMap x s := by
  simp [stalkQuotientEquiv]

variable [IsIntegral C] [IsDomain (Y.presheaf.stalk (i x))]

/-- The actual original quotient/stalk map extends canonically to the SAME curve function field. -/
def residualFractionEquiv (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    FractionRing (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) ≃+*
      C.functionField :=
  IsFractionRing.ringEquivOfRingEquiv (stalkQuotientEquiv i x π hker)

omit [IsDomain (Y.presheaf.stalk (i x))] in
/-- The genuine fraction extension preserves EVERY original ambient-stalk coefficient. -/
theorem residualFractionEquiv_coefficient (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (s : S) :
    residualFractionEquiv i x π z hπ hz hm hker
      (algebraMap (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) _
        (GaussRegularSurfaceValuationOrders.residualCoefficientMap π z hπ hz hm s)) =
      algebraMap A C.functionField (i.stalkMap x s) := by
  change IsFractionRing.ringEquivOfRingEquiv (stalkQuotientEquiv i x π hker)
    (algebraMap (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) _
      (Ideal.Quotient.mk _ s)) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, stalkQuotientEquiv_mk]

/-- The old canonical vertical residue field is the SAME original central curve's function field. -/
def verticalResidueCurveFieldEquiv (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    ResidueField (GaussRegularSurfaceValuationOrders.verticalRing π hπ) ≃+* C.functionField :=
  (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm).trans
    (residualFractionEquiv i x π z hπ hz hm hker)

omit [IsDomain (Y.presheaf.stalk (i x))] in
/-- The canonical leading FIELD map retains the literal original coefficient square for ALL s. -/
theorem verticalResidueCurveFieldEquiv_coefficient (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (s : S) :
    verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
      (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s)) =
      algebraMap A C.functionField (i.stalkMap x s) := by
  change residualFractionEquiv i x π z hπ hz hm hker
    (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
      (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s))) = _
  rw [GaussRegularSurfaceValuationFractions.verticalResidueEquiv_coefficient,
    residualFractionEquiv_coefficient]

variable [IsNoetherianRing (Y.presheaf.stalk (i x))] [IsLocallyNoetherian C]

omit [IsDomain (Y.presheaf.stalk (i x))] in
/-- ALL residual fractions, including zero, have the SAME original curve order homomorphism. -/
theorem residualOrder_eq_curveOrdHom (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (hdim : topologicalKrullDim C ≤ 1) (hx : x ≠ genericPoint C)
    (r : FractionRing (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm)) :
    GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm r =
      C.ordHom x (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx)
        (residualFractionEquiv i x π z hπ hz hm hker r) := by
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  let : IsDiscreteValuationRing (S ⧸ Ideal.span {π}) :=
    GaussRegularSurfaceValuationOrders.residual_isDVR π z hπ hz hm
  let : Ring.KrullDimLE 1 A :=
    krullDimLE_of_coheight_le (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx).le
  change Ring.ordFrac (GaussRegularSurfaceValuationOrders.residualRing π z hπ hz hm) r =
    Ring.ordFrac A (residualFractionEquiv i x π z hπ hz hm hker r)
  exact ordFrac_ringEquiv (stalkQuotientEquiv i x π hker) r

omit [IsDomain (Y.presheaf.stalk (i x))] in
/-- An actual vertical unit has a nonzero leading function on the SAME curve;
its exact native residual order is the exponential of the SAME curve's integer order. -/
theorem leadingResidue_order_eq_curveOrd (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (hdim : topologicalKrullDim C ≤ 1) (hx : x ≠ genericPoint C)
    (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ) :
    GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
      (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
        (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
          (u : GaussRegularSurfaceValuationOrders.verticalRing π hπ))) =
      WithZero.exp (C.ord
        (verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
          (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
            (u : GaussRegularSurfaceValuationOrders.verticalRing π hπ))) x) := by
  have hu : residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
      (u : GaussRegularSurfaceValuationOrders.verticalRing π hπ) ≠ 0 :=
    (u.isUnit.map (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ))).ne_zero
  have hlead : verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
      (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
        (u : GaussRegularSurfaceValuationOrders.verticalRing π hπ)) ≠ 0 :=
    (map_ne_zero_iff _ (verticalResidueCurveFieldEquiv i x π z hπ hz hm hker).injective).mpr hu
  rw [residualOrder_eq_curveOrdHom i x π z hπ hz hm hker hdim hx]
  exact (C.ord_eq_iff (CurveFiniteClosedSubschemes.coheight_eq_one hdim x hx) hlead).mp rfl

/-- The old eventual family now has the true original curve order as its exact constant term,
including possible poles, without a supplied residue/order/slope comparison. -/
theorem exists_eventual_fieldOrder_curve (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (hdim : topologicalKrullDim C ≤ 1) (hx : x ≠ genericPoint C)
    (f : FractionRing S) (hf : f ≠ 0) :
    ∃ (a : ℤ) (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ),
      f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ
          (u : GaussRegularSurfaceValuationOrders.verticalRing π hπ) *
          (algebraMap S (FractionRing S) π) ^ a ∧
      GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = WithZero.exp a ∧
      ∃ M : ℕ, ∀ (N : ℕ) (hN : 0 < N), M < N →
        GaussRegularSurfaceValuationFractions.weightedOrder π z hπ hz hm N hN f =
          WithZero.exp (a * (N : ℤ) + C.ord
            (verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
              (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
                (u : GaussRegularSurfaceValuationOrders.verticalRing π hπ))) x) := by
  obtain ⟨a,b,u,hfactor,hvertical,hres,M,heventual⟩ :=
    GaussRegularSurfaceValuationFractions.exists_eventual_fieldOrder π z hπ hz hm f hf
  have hb := WithZero.exp_injective
    (hres.symm.trans (leadingResidue_order_eq_curveOrd i x π z hπ hz hm hker hdim hx u))
  refine ⟨a,u,hfactor,hvertical,M,?_⟩
  intro N hN hMN
  rw [heventual N hN hMN, hb]

end EnvelopeProperty.CentralCurveLeadingOrders

