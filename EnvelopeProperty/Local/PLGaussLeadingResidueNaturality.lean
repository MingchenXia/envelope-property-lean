import EnvelopeProperty.AlgGeom.CentralCurveLeadingOrders
import EnvelopeProperty.AlgGeom.GaussCommonVerticalStalks

/-! # Original leading residues under the SAME global vertical DVR

Both comparison squares come from the original stalk maps and localization.
No residue, field, order or unit-transition matching certificate is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Order
open scoped Classical WithZero

universe u
namespace EnvelopeProperty.GaussLeadingResidueNaturality

variable {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
  (i : C ⟶ Y) [IsClosedImmersion i] (x : C)

local notation "S" => Y.presheaf.stalk (i x)
local notation "D" => Y.presheaf.stalk (i (genericPoint C))
local notation "T(" π "," hπ ")" => GaussRegularSurfaceValuationOrders.verticalRing π hπ

/-- ALL original vertical-localization elements retain the SAME actual central generic image. -/
theorem componentStalk_residual_apply (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (w : T(π,hπ)) :
    CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
      (residue T(π,hπ) w) =
      i.stalkMap (genericPoint C) (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker w) := by
  let r : T(π,hπ) →+* C.functionField :=
    (CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i x π z hπ hz hm hker).toRingHom.comp
      (residue T(π,hπ))
  let s : T(π,hπ) →+* C.functionField :=
    (i.stalkMap (genericPoint C)).hom.comp
      (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker).toRingHom
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have hrs : r = s := by
    apply IsLocalization.ringHom_ext (Ideal.span {π}).primeCompl
    ext a
    change CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
      (residue T(π,hπ) (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ a)) =
      i.stalkMap (genericPoint C) (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ a))
    rw [CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv_coefficient,
      GaussCommonVerticalStalks.componentStalkEquiv_coefficient]
    exact (i.stalkSpecializes_stalkMap_apply (genericPoint C) x
      ((genericPoint_spec C).specializes trivial) a).symm
  exact RingHom.congr_fun hrs w

/-- The whole actual vertical fraction inclusion agrees with the SAME original function field. -/
theorem componentStalk_fraction_apply (π : S) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (w : T(π,hπ)) :
    FractionRing.algEquiv (A := S) Y.functionField
      (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ w) =
      algebraMap D Y.functionField
        (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker w) := by
  let r : T(π,hπ) →+* Y.functionField :=
    (FractionRing.algEquiv (A := S) Y.functionField).toRingHom.comp
      (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ)
  let s : T(π,hπ) →+* Y.functionField :=
    (algebraMap D Y.functionField).comp
      (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker).toRingHom
  let : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have hrs : r = s := by
    apply IsLocalization.ringHom_ext (Ideal.span {π}).primeCompl
    ext a
    change FractionRing.algEquiv (A := S) Y.functionField
      (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ a)) =
      algebraMap D Y.functionField (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ a))
    rw [GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient,
      (FractionRing.algEquiv (A := S) Y.functionField).commutes,
      GaussCommonVerticalStalks.componentStalkEquiv_coefficient]
    change Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) a =
      (Y.presheaf.stalkSpecializes
        (i.base.hom.map_specializes ((genericPoint_spec C).specializes trivial)) ≫
        Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial)) a
    rw [Y.presheaf.stalkSpecializes_comp]
  exact RingHom.congr_fun hrs w

variable [IsNoetherianRing (Y.presheaf.stalk (i x))]

/-- ALL original fractions have the SAME exact global vertical order, including zero. -/
theorem verticalOrder_genericField (π : S) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (f : FractionRing S) :
    letI : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
    GaussRegularSurfaceValuationFractions.verticalOrder π hπ f =
      Ring.ordFrac D (FractionRing.algEquiv (A := S) Y.functionField f) := by
  let : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
  let : Algebra T(π,hπ) (FractionRing S) :=
    (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ).toAlgebra
  let : IsFractionRing T(π,hπ) (FractionRing S) :=
    GaussRegularSurfaceValuationFractions.verticalFractionRing π hπ
  have hext :
      (IsFractionRing.ringEquivOfRingEquiv (K := FractionRing S) (L := Y.functionField)
        (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker)).toRingHom =
      (FractionRing.algEquiv (A := S) Y.functionField).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := T(π,hπ))
    intro w
    change IsFractionRing.ringEquivOfRingEquiv (K := FractionRing S) (L := Y.functionField)
      (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker)
        (algebraMap T(π,hπ) (FractionRing S) w) =
      FractionRing.algEquiv (A := S) Y.functionField
        (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ w)
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact (componentStalk_fraction_apply i x π hπ hker w).symm
  have h := CentralCurveLeadingOrders.ordFrac_ringEquiv
    (K := FractionRing S) (L := Y.functionField)
    (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker) f
  change GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = _ at h
  rw [show IsFractionRing.ringEquivOfRingEquiv (K := FractionRing S) (L := Y.functionField)
      (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker) f =
      FractionRing.algEquiv (A := S) Y.functionField f from RingHom.congr_fun hext f] at h
  exact h

private theorem fraction_factor_order {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ : Irreducible ϖ) (f : K) (hf : f ≠ 0) :
    ∃ (a : ℤ) (U : Rˣ),
      f = algebraMap R K U * (algebraMap R K ϖ) ^ a ∧ Ring.ordFrac R f = WithZero.exp a := by
  obtain ⟨a,U,hfU⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hf
  have hfactor : f = algebraMap R K U * (algebraMap R K ϖ) ^ a := by
    simpa only [Units.smul_def,Algebra.smul_def] using hfU
  refine ⟨a,U,hfactor,?_⟩
  rw [hfactor,map_mul,map_zpow₀,Ring.ordFrac_of_isUnit (R := R) U.isUnit,
    Ring.ordFrac_irreducible (R := R) hϖ,one_mul,← WithZero.exp_zsmul]
  simp

/-- The SAME actual generic stalk internally supplies ONE uniformizer and ALL global factors. -/
theorem exists_globalLeadingFactorization (π : S) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    letI : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
    ∃ ϖ : D, Irreducible ϖ ∧ ∀ (f : Y.functionField), f ≠ 0 →
      ∃ (a : ℤ) (U : Dˣ), f = algebraMap D Y.functionField U * (algebraMap D Y.functionField ϖ) ^ a ∧
        Ring.ordFrac D f = WithZero.exp a ∧ i.stalkMap (genericPoint C) U ≠ 0 := by
  let : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
  obtain ⟨ϖ,hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  refine ⟨ϖ,hϖ,?_⟩
  intro f hf
  obtain ⟨a,U,hfac,hord⟩ := fraction_factor_order ϖ hϖ f hf
  exact ⟨a,U,hfac,hord,(U.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero⟩

/-- Every local original component parameter differs from the ONE global parameter by a true unit. -/
theorem exists_parameterUnit (π : S) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (ϖ : D) (hϖ : Irreducible ϖ) :
    ∃ v : Dˣ, GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
      (GaussRegularSurfaceValuationOrders.verticalParameter π hπ) = ϖ * v := by
  let : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
  have hE : Irreducible (GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
      (GaussRegularSurfaceValuationOrders.verticalParameter π hπ)) :=
    (MulEquiv.irreducible_iff _).mpr
      (GaussRegularSurfaceValuationOrders.verticalParameter_irreducible π hπ)
  obtain ⟨v,hv⟩ := IsDiscreteValuationRing.associated_of_irreducible D hϖ hE
  exact ⟨v,hv.symm⟩

/-- An actual nonzero element of the true vertical maximal ideal has a POSITIVE natural exponent. -/
theorem exists_verticalParameterFactorization (π : S) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) (ϖ : D) (hϖ : Irreducible ϖ)
    (t : D) (ht : t ≠ 0) (htm : t ∈ maximalIdeal D) :
    ∃ (e : ℕ) (U : Dˣ), 0 < e ∧ t = U * ϖ ^ e ∧ i.stalkMap (genericPoint C) U ≠ 0 := by
  let : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
  obtain ⟨e,U,hfactor⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
  have he : 0 < e := by
    by_contra! h
    have he0 : e = 0 := Nat.eq_zero_of_le_zero h
    have hunit : IsUnit t := by
      rw [hfactor,he0,pow_zero,mul_one]
      exact U.isUnit
    have hnot : ¬ IsUnit t := by simpa only [mem_maximalIdeal,mem_nonunits_iff] using htm
    exact hnot hunit
  exact ⟨e,U,he,hfactor,(U.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero⟩

omit [IsNoetherianRing (Y.presheaf.stalk (i x))] in
private theorem residue_of_global_factor (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (ϖ : D) (hϖ : Irreducible ϖ) (f : Y.functionField) (a : ℤ) (U v : Dˣ)
    (u : T(π,hπ)ˣ)
    (hv : GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
      (GaussRegularSurfaceValuationOrders.verticalParameter π hπ) = ϖ * v)
    (hglobal : f = algebraMap D Y.functionField U * (algebraMap D Y.functionField ϖ) ^ a)
    (hlocal : (FractionRing.algEquiv (A := S) Y.functionField).symm f =
      GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
        (algebraMap S (FractionRing S) π) ^ a) :
    CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
      (residue T(π,hπ) u) = i.stalkMap (genericPoint C) U *
        (i.stalkMap (genericPoint C) v) ^ (-a) := by
  let E := GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
  let Eu : Dˣ := Units.map E.toMonoidHom u
  let q : Dˣ →* Y.functionField := (algebraMap D Y.functionField).toMonoidHom.comp (Units.coeHom D)
  have hϖK : algebraMap D Y.functionField ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective D Y.functionField)).mpr hϖ.ne_zero
  have hqπ : FractionRing.algEquiv (A := S) Y.functionField
      (algebraMap S (FractionRing S) π) = algebraMap D Y.functionField ϖ * q v := by
    rw [← GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ π,
      componentStalk_fraction_apply]
    change algebraMap D Y.functionField (E (GaussRegularSurfaceValuationOrders.verticalParameter π hπ)) = _
    rw [hv,map_mul]
    rfl
  have hlocal' : f = q Eu * (algebraMap D Y.functionField ϖ * q v) ^ a := by
    have h := congrArg (FractionRing.algEquiv (A := S) Y.functionField) hlocal
    rw [AlgEquiv.apply_symm_apply,map_mul,map_zpow₀,hqπ,
      componentStalk_fraction_apply i x π hπ hker] at h
    exact h
  have hu : Eu * v ^ a = U := by
    apply Units.ext
    apply IsFractionRing.injective D Y.functionField
    change q (Eu * v ^ a) = q U
    rw [map_mul,map_zpow]
    apply mul_right_cancel₀ (zpow_ne_zero a hϖK)
    calc
      (q Eu * q v ^ a) * (algebraMap D Y.functionField ϖ) ^ a =
          q Eu * (algebraMap D Y.functionField ϖ * q v) ^ a := by rw [mul_zpow]; ring
      _ = f := hlocal'.symm
      _ = q U * (algebraMap D Y.functionField ϖ) ^ a := hglobal
  have hu' : Eu = U * v ^ (-a) := by
    calc
      Eu = (Eu * v ^ a) * (v ^ a)⁻¹ := by group
      _ = U * v ^ (-a) := by rw [hu,zpow_neg]
  rw [componentStalk_residual_apply]
  change i.stalkMap (genericPoint C) (Eu : D) = _
  rw [hu',Units.val_mul,map_mul]
  congr 1
  exact (((i.stalkMap (genericPoint C)).hom.toMonoidHom.comp (Units.coeHom D)).map_zpow v (-a))

private theorem local_factor_data [IsDiscreteValuationRing D]
    (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z) (hm : maximalIdeal S = Ideal.span {π,z})
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (ϖ : D) (hϖ : Irreducible ϖ) (f : Y.functionField) (hf : f ≠ 0)
    (a : ℤ) (U v : Dˣ)
    (hv : GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
      (GaussRegularSurfaceValuationOrders.verticalParameter π hπ) = ϖ * v)
    (hglobal : f = algebraMap D Y.functionField U * (algebraMap D Y.functionField ϖ) ^ a)
    (horder : Ring.ordFrac D f = WithZero.exp a) :
    ∃ (b : ℤ) (u : T(π,hπ)ˣ),
      (FractionRing.algEquiv (A := S) Y.functionField).symm f =
        GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
          (algebraMap S (FractionRing S) π) ^ a ∧
      GaussRegularSurfaceValuationFractions.verticalOrder π hπ
        ((FractionRing.algEquiv (A := S) Y.functionField).symm f) = WithZero.exp a ∧
      GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
        (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm (residue T(π,hπ) u)) =
          WithZero.exp b ∧
      CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i x π z hπ hz hm hker
        (residue T(π,hπ) u) = i.stalkMap (genericPoint C) U *
          (i.stalkMap (genericPoint C) v) ^ (-a) := by
  have hf' : (FractionRing.algEquiv (A := S) Y.functionField).symm f ≠ 0 :=
    (map_ne_zero_iff _ (FractionRing.algEquiv (A := S) Y.functionField).symm.injective).mpr hf
  obtain ⟨a',b,u,hfac,hord,hres,-⟩ :=
    GaussRegularSurfaceValuationFractions.exists_eventual_fieldOrder π z hπ hz hm _ hf'
  have haa : a' = a := WithZero.exp_injective <| hord.symm.trans <| by
    rw [verticalOrder_genericField i x π hπ hker,AlgEquiv.apply_symm_apply]
    exact horder
  subst a'
  exact ⟨b,u,hfac,hord,hres,residue_of_global_factor i x π z hπ hz hm hker ϖ hϖ f a U v u hv hglobal hfac⟩

/-- The global factor is chosen BEFORE all original component points and their unchanged local units. -/
theorem exists_localLeadingFactorization (π : S) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (ϖ : D) (hϖ : Irreducible ϖ) (f : Y.functionField) (hf : f ≠ 0) :
    ∃ (a : ℤ) (U : Dˣ),
      f = algebraMap D Y.functionField U * (algebraMap D Y.functionField ϖ) ^ a ∧
      ∀ (y : C) (_ : IsNoetherianRing (Y.presheaf.stalk (i y)))
        (π z : Y.presheaf.stalk (i y)) (hπ : Prime π) (hz : ¬ π ∣ z)
        (hm : maximalIdeal (Y.presheaf.stalk (i y)) = Ideal.span {π,z})
        (hker : RingHom.ker (i.stalkMap y).hom = Ideal.span {π}),
        ∃ (b : ℤ) (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ) (v : Dˣ),
          GaussCommonVerticalStalks.componentStalkEquiv i y π hπ hker
            (GaussRegularSurfaceValuationOrders.verticalParameter π hπ) = ϖ * v ∧
          (FractionRing.algEquiv (A := Y.presheaf.stalk (i y)) Y.functionField).symm f =
            GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
              (algebraMap (Y.presheaf.stalk (i y)) (FractionRing (Y.presheaf.stalk (i y))) π) ^ a ∧
          CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i y π z hπ hz hm hker
            (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) u) =
              i.stalkMap (genericPoint C) U * (i.stalkMap (genericPoint C) v) ^ (-a) ∧
          GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
            (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
              (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) u)) = WithZero.exp b := by
  let : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π hπ hker
  obtain ⟨a,U,hfac,hord⟩ := fraction_factor_order ϖ hϖ f hf
  refine ⟨a,U,hfac,?_⟩
  intro y hnoeth π' z' hπ' hz' hm' hker'
  let : IsNoetherianRing (Y.presheaf.stalk (i y)) := hnoeth
  obtain ⟨v,hv⟩ := exists_parameterUnit i y π' hπ' hker' ϖ hϖ
  obtain ⟨b,u,hu,-,hres,hr⟩ := local_factor_data i y π' z' hπ' hz' hm' hker' ϖ hϖ f hf a U v hv hfac hord
  exact ⟨b,u,v,hv,hu,hr,hres⟩

omit [IsIntegral Y] [IsClosedImmersion i] in
/-- The actual SAME-curve leading quotient cancels both original parameter transition powers. -/
theorem leadingQuotient_eq_global (U W v : Dˣ) (a e : ℤ) :
    (i.stalkMap (genericPoint C) U * (i.stalkMap (genericPoint C) v) ^ (-a)) ^ e /
      (i.stalkMap (genericPoint C) W * (i.stalkMap (genericPoint C) v) ^ (-e)) ^ a =
      (i.stalkMap (genericPoint C) U) ^ e / (i.stalkMap (genericPoint C) W) ^ a := by
  have hv : i.stalkMap (genericPoint C) v ≠ 0 :=
    (v.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero
  simp only [mul_zpow,← zpow_mul]
  rw [show (-a) * e = (-e) * a by ring]
  exact mul_div_mul_right _ _ (zpow_ne_zero _ hv)

private theorem curve_ord_zpow [IsLocallyNoetherian C] (y : C) (hy : coheight y = 1)
    (r : C.functionField) (hr : r ≠ 0) (n : ℤ) : C.ord (r ^ n) y = n * C.ord r y := by
  apply (C.ord_eq_iff hy (zpow_ne_zero n hr)).mpr
  rw [map_zpow₀,show C.ordHom y hy r = WithZero.exp (C.ord r y) from (C.ord_eq_iff hy hr).mp rfl,
    ← WithZero.exp_zsmul]
  rfl

private theorem curve_ord_div [IsLocallyNoetherian C] (y : C) (hy : coheight y = 1)
    (r s : C.functionField) (hr : r ≠ 0) (hs : s ≠ 0) :
    C.ord (r / s) y = C.ord r y - C.ord s y := by
  have hi : C.ord s⁻¹ y = - C.ord s y := by
    simpa only [zpow_neg_one,neg_one_mul] using curve_ord_zpow y hy s hs (-1)
  rw [div_eq_mul_inv,C.ord_mul hr (inv_ne_zero hs),hi,sub_eq_add_neg]

/-- ONE global uniformizer, positive actual parameter degree and global factors are chosen
before EVERY component point. The unchanged native local leading integers have exactly
the corrected orders of the SAME whole-curve functions, including negative orders. -/
theorem exists_correctedLeadingOrders [IsLocallyNoetherian C]
    (π₀ : S) (hπ₀ : Prime π₀)
    (hker₀ : RingHom.ker (i.stalkMap x).hom = Ideal.span {π₀})
    (t : D) (ht : t ≠ 0) (htm : t ∈ maximalIdeal D)
    (hdim : topologicalKrullDim C ≤ 1) :
    ∃ (ϖ : D) (e : ℕ) (Ut : Dˣ), Irreducible ϖ ∧ 0 < e ∧ t = Ut * ϖ ^ e ∧
      ∀ (f : Y.functionField), f ≠ 0 → ∃ (a : ℤ) (Uf : Dˣ),
        f = algebraMap D Y.functionField Uf * (algebraMap D Y.functionField ϖ) ^ a ∧
        ∀ (y : C) (_ : IsNoetherianRing (Y.presheaf.stalk (i y))) (_hy : y ≠ genericPoint C)
          (π z : Y.presheaf.stalk (i y)) (hπ : Prime π) (hz : ¬ π ∣ z)
          (hm : maximalIdeal (Y.presheaf.stalk (i y)) = Ideal.span {π,z})
          (hker : RingHom.ker (i.stalkMap y).hom = Ideal.span {π}),
          let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
          let R : T →+* C.functionField :=
            (CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i y π z hπ hz hm hker).toRingHom.comp
              (residue T)
          let J := FractionRing.algEquiv (A := Y.presheaf.stalk (i y)) Y.functionField
          let Bf := i.stalkMap (genericPoint C) Uf
          let Bt := i.stalkMap (genericPoint C) Ut
          ∃ (b c : ℤ) (u w : Tˣ) (v : Dˣ),
            GaussCommonVerticalStalks.componentStalkEquiv i y π hπ hker
              (GaussRegularSurfaceValuationOrders.verticalParameter π hπ) = ϖ * v ∧
            J.symm f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
              (algebraMap (Y.presheaf.stalk (i y)) (FractionRing (Y.presheaf.stalk (i y))) π) ^ a ∧
            J.symm (algebraMap D Y.functionField t) =
              GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ w *
                (algebraMap (Y.presheaf.stalk (i y)) (FractionRing (Y.presheaf.stalk (i y))) π) ^ (e : ℤ) ∧
            R u = Bf * (i.stalkMap (genericPoint C) v) ^ (-a) ∧
            R w = Bt * (i.stalkMap (genericPoint C) v) ^ (-(e : ℤ)) ∧
            GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
              (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm (residue T u)) =
                WithZero.exp b ∧
            GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
              (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm (residue T w)) =
                WithZero.exp c ∧
            (R u) ^ (e : ℤ) / (R w) ^ a = Bf ^ (e : ℤ) / Bt ^ a ∧
            (e : ℤ) * b - a * c = C.ord (Bf ^ (e : ℤ) / Bt ^ a) y ∧
            (b : ℝ) - (a : ℝ) / (e : ℝ) * (c : ℝ) =
              (C.ord Bf y : ℝ) - (a : ℝ) / (e : ℝ) * (C.ord Bt y : ℝ) := by
  let : IsDiscreteValuationRing D := GaussCommonVerticalStalks.componentStalk_isDVR i x π₀ hπ₀ hker₀
  obtain ⟨ϖ,hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D
  obtain ⟨e,Ut,he,htfac,-⟩ := exists_verticalParameterFactorization i x π₀ hπ₀ hker₀ ϖ hϖ t ht htm
  have htK : algebraMap D Y.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective D Y.functionField)).mpr ht
  have htfacK : algebraMap D Y.functionField t =
      algebraMap D Y.functionField Ut * (algebraMap D Y.functionField ϖ) ^ (e : ℤ) := by
    rw [htfac,map_mul,map_pow,zpow_natCast]
  have htord : Ring.ordFrac D (algebraMap D Y.functionField t) = WithZero.exp (e : ℤ) := by
    rw [htfacK,map_mul,map_zpow₀,Ring.ordFrac_of_isUnit Ut.isUnit,
      Ring.ordFrac_irreducible hϖ,one_mul,← WithZero.exp_zsmul]
    simp
  refine ⟨ϖ,e,Ut,hϖ,he,htfac,?_⟩
  intro f hf
  obtain ⟨a,Uf,hfac,hord⟩ := fraction_factor_order ϖ hϖ f hf
  refine ⟨a,Uf,hfac,?_⟩
  intro y hnoeth hy π z hπ hz hm hker
  let : IsNoetherianRing (Y.presheaf.stalk (i y)) := hnoeth
  dsimp only
  obtain ⟨v,hv⟩ := exists_parameterUnit i y π hπ hker ϖ hϖ
  obtain ⟨b,u,hfu,-,hresf,hrf⟩ := local_factor_data i y π z hπ hz hm hker ϖ hϖ f hf a Uf v hv hfac hord
  obtain ⟨c,w,htw,-,hrest,hrt⟩ := local_factor_data i y π z hπ hz hm hker ϖ hϖ
    (algebraMap D Y.functionField t) htK (e : ℤ) Ut v hv htfacK htord
  have hy1 := CurveFiniteClosedSubschemes.coheight_eq_one hdim y hy
  have hUf : i.stalkMap (genericPoint C) Uf ≠ 0 := (Uf.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero
  have hUt : i.stalkMap (genericPoint C) Ut ≠ 0 := (Ut.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero
  have hV : i.stalkMap (genericPoint C) v ≠ 0 := (v.isUnit.map (i.stalkMap (genericPoint C)).hom).ne_zero
  have hb : b = C.ord (i.stalkMap (genericPoint C) Uf) y - a * C.ord (i.stalkMap (genericPoint C) v) y := by
    have hb₀ := WithZero.exp_injective <| hresf.symm.trans
      (CentralCurveLeadingOrders.leadingResidue_order_eq_curveOrd i y π z hπ hz hm hker hdim hy u)
    rw [hrf,C.ord_mul hUf (zpow_ne_zero (-a) hV),curve_ord_zpow y hy1 _ hV] at hb₀
    exact hb₀.trans (by ring)
  have hc : c = C.ord (i.stalkMap (genericPoint C) Ut) y - (e : ℤ) * C.ord (i.stalkMap (genericPoint C) v) y := by
    have hc₀ := WithZero.exp_injective <| hrest.symm.trans
      (CentralCurveLeadingOrders.leadingResidue_order_eq_curveOrd i y π z hπ hz hm hker hdim hy w)
    rw [hrt,C.ord_mul hUt (zpow_ne_zero (-(e : ℤ)) hV),curve_ord_zpow y hy1 _ hV] at hc₀
    exact hc₀.trans (by ring)
  refine ⟨b,c,u,w,v,hv,hfu,htw,hrf,hrt,hresf,hrest,?_,?_,?_⟩
  · change (CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i y π z hπ hz hm hker
        (residue T(π,hπ) u)) ^ (e : ℤ) /
        (CentralCurveLeadingOrders.verticalResidueCurveFieldEquiv i y π z hπ hz hm hker
          (residue T(π,hπ) w)) ^ a = _
    rw [hrf,hrt]
    exact leadingQuotient_eq_global i Uf Ut v a (e : ℤ)
  · rw [curve_ord_div y hy1 _ _ (zpow_ne_zero _ hUf) (zpow_ne_zero _ hUt),
      curve_ord_zpow y hy1 _ hUf,curve_ord_zpow y hy1 _ hUt,hb,hc]
    ring
  · have hbR : (b : ℝ) = (C.ord (i.stalkMap (genericPoint C) Uf) y : ℝ) -
        (a : ℝ) * (C.ord (i.stalkMap (genericPoint C) v) y : ℝ) := by exact_mod_cast hb
    have hcR : (c : ℝ) = (C.ord (i.stalkMap (genericPoint C) Ut) y : ℝ) -
        (e : ℝ) * (C.ord (i.stalkMap (genericPoint C) v) y : ℝ) := by exact_mod_cast hc
    have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    rw [hbR,hcR]
    field_simp
    ring

end EnvelopeProperty.GaussLeadingResidueNaturality
