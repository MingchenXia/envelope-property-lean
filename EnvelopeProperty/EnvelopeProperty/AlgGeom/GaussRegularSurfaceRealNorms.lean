import EnvelopeProperty.AlgGeom.GaussRegularSurfaceValuationFractions
import EnvelopeProperty.Berkovich.DVRNormalizedParameter

/-! # Actual scaled norms on the SAME original regular-surface field

The scalar action and every DVR embedding are the actual original maps.
No norm family, Gauss restriction or convergence certificate is an input.
-/

noncomputable section
open IsLocalRing IsDiscreteValuationRing Filter
open scoped Classical NNReal Topology WithZero

universe u v
namespace EnvelopeProperty.GaussRegularSurfaceRealNorms

variable {k : Type v} [Field k] {S : Type u} [CommRing S] [IsDomain S] [Algebra k S]
  [IsNoetherianRing S]

private theorem nativeOrder_of_addVal {A K : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (x : A) (n : ℕ) (h : addVal A x = n) :
    Ring.ordFrac A (algebraMap A K x) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_valuation_inv,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,h,inv_inv]
  rfl

private theorem dvrFractionPoint_log_of_order {k A K : Type*} [Field k]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra k A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]
    {c : ℝ} (hc : 0 < c) (f : K) (hf : f ≠ 0) (a : ℤ)
    (ha : Ring.ordFrac A f = WithZero.exp a) :
    Real.log (((Berk.dvrFractionPoint (k := k) (V := A) hc).val f : ℝ≥0) : ℝ) =
      -c * (a : ℝ) := by
  obtain ⟨x,y,hy,heq⟩ := IsFractionRing.div_surjective A f
  have hx : x ≠ 0 := by
    intro hx
    apply hf
    rw [← heq,hx,map_zero,zero_div]
  have hy0 : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := A)).not.mpr hx)
  obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp ((addVal_eq_top_iff (R := A)).not.mpr hy0)
  have horder : Ring.ordFrac A f = WithZero.exp ((m : ℤ) - (n : ℤ)) := by
    rw [← heq,map_div₀,nativeOrder_of_addVal x m hm.symm,
      nativeOrder_of_addVal y n hn.symm,← WithZero.exp_sub]
  have hmn : (m : ℤ) - (n : ℤ) = a := WithZero.exp_inj.mp (horder.symm.trans ha)
  have hreal : (m : ℝ) - (n : ℝ) = (a : ℝ) := by exact_mod_cast hmn
  rw [← heq,map_div₀,Berk.dvrFractionPoint_val_algebraMap,
    Berk.dvrFractionPoint_val_algebraMap,← hm,← hn,expOrd_coe,expOrd_coe,
    NNReal.coe_div,NNReal.coe_pow,NNReal.coe_pow]
  change Real.log (Real.exp (-c) ^ m / Real.exp (-c) ^ n) = _
  rw [Real.log_div (pow_ne_zero _ (Real.exp_ne_zero _))
    (pow_ne_zero _ (Real.exp_ne_zero _)),Real.log_pow,Real.log_pow,Real.log_exp]
  rw [← hreal]
  ring

/-- The actual positive-scale point of the SAME original vertical DVR. -/
def verticalPoint (π : S) (hπ : Prime π) {c : ℝ} (hc : 0 < c) :
    Berk k (FractionRing S) := by
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let j := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  let e := GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ
  let : Algebra T (FractionRing S) := e.toAlgebra
  let : IsFractionRing T (FractionRing S) :=
    GaussRegularSurfaceValuationFractions.verticalFractionRing π hπ
  let : IsScalarTower k T (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S T a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ _).symm
  exact Berk.dvrFractionPoint (k := k) (V := T) hc

/-- The exact original coefficient norm, with the original vertical additive order. -/
theorem verticalPoint_coefficient (π : S) (hπ : Prime π) {c : ℝ} (hc : 0 < c) (s : S) :
    (verticalPoint (k := k) π hπ hc).val (algebraMap S (FractionRing S) s) =
      expOrd (expNeg c) (addVal (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ s)) := by
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let j := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  let e := GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ
  let : Algebra T (FractionRing S) := e.toAlgebra
  let : IsFractionRing T (FractionRing S) :=
    GaussRegularSurfaceValuationFractions.verticalFractionRing π hπ
  let : IsScalarTower k T (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S T a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ _).symm
  change (Berk.dvrFractionPoint (k := k) (V := T) hc).val _ = _
  rw [← GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ s]
  exact Berk.dvrFractionPoint_val_algebraMap hc (j s)

/-- Every original S coefficient is bounded in the actual vertical point. -/
theorem verticalPoint_coefficient_le_one (π : S) (hπ : Prime π) {c : ℝ} (hc : 0 < c)
    (s : S) : (verticalPoint (k := k) π hπ hc).val (algebraMap S (FractionRing S) s) ≤ 1 := by
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let j := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  let e := GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ
  let : Algebra T (FractionRing S) := e.toAlgebra
  let : IsFractionRing T (FractionRing S) :=
    GaussRegularSurfaceValuationFractions.verticalFractionRing π hπ
  let : IsScalarTower k T (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S T a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ _).symm
  change (Berk.dvrFractionPoint (k := k) (V := T) hc).val _ ≤ 1
  rw [← GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ s]
  exact Berk.dvrFractionPoint_val_algebraMap_le_one hc (j s)

/-- The TRUE whole-field native vertical order gives the actual ordinary logarithm. -/
theorem verticalPoint_log_of_order (π : S) (hπ : Prime π) {c : ℝ} (hc : 0 < c)
    (f : FractionRing S) (hf : f ≠ 0) (a : ℤ)
    (ha : GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = WithZero.exp a) :
    Real.log (((verticalPoint (k := k) π hπ hc).val f : ℝ≥0) : ℝ) = -c * (a : ℝ) := by
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let j := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  let e := GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ
  let : Algebra T (FractionRing S) := e.toAlgebra
  let : IsFractionRing T (FractionRing S) :=
    GaussRegularSurfaceValuationFractions.verticalFractionRing π hπ
  let : IsScalarTower k T (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S T a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ _).symm
  exact dvrFractionPoint_log_of_order hc f hf a ha

variable [IsLocalRing S]

/-- The actual positive-scale point of the SAME original weighted chart DVR. -/
def weightedPoint (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    {c : ℝ} (hc : 0 < c) : Berk k (FractionRing S) := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  let e := GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN
  let : Algebra V (FractionRing S) := e.toAlgebra
  let : IsFractionRing V (FractionRing S) :=
    GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  let : IsScalarTower k V (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S V a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN _).symm
  exact Berk.dvrFractionPoint (k := k) (V := V) hc

/-- The exact original coefficient norm, with the actual weighted-chart additive order. -/
theorem weightedPoint_coefficient (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    {c : ℝ} (hc : 0 < c) (s : S) :
    (weightedPoint (k := k) π z hπ hz hm N hN hc).val (algebraMap S (FractionRing S) s) =
      expOrd (expNeg c) (addVal (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)
        (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN s)) := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  let e := GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN
  let : Algebra V (FractionRing S) := e.toAlgebra
  let : IsFractionRing V (FractionRing S) :=
    GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  let : IsScalarTower k V (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S V a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN _).symm
  change (Berk.dvrFractionPoint (k := k) (V := V) hc).val _ = _
  rw [← GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN s]
  exact Berk.dvrFractionPoint_val_algebraMap hc (j s)

/-- EVERY original coefficient stays bounded under its literal original field map. -/
theorem weightedPoint_coefficient_le_one (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    {c : ℝ} (hc : 0 < c) (s : S) :
    (weightedPoint (k := k) π z hπ hz hm N hN hc).val (algebraMap S (FractionRing S) s) ≤ 1 := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  let e := GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN
  let : Algebra V (FractionRing S) := e.toAlgebra
  let : IsFractionRing V (FractionRing S) :=
    GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  let : IsScalarTower k V (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S V a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN _).symm
  change (Berk.dvrFractionPoint (k := k) (V := V) hc).val _ ≤ 1
  rw [← GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN s]
  exact Berk.dvrFractionPoint_val_algebraMap_le_one hc (j s)

/-- The TRUE whole-field native weighted order gives the actual ordinary logarithm. -/
theorem weightedPoint_log_of_order (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    {c : ℝ} (hc : 0 < c) (f : FractionRing S) (hf : f ≠ 0) (a : ℤ)
    (ha : GaussRegularSurfaceValuationFractions.weightedOrder π z hπ hz hm N hN f = WithZero.exp a) :
    Real.log (((weightedPoint (k := k) π z hπ hz hm N hN hc).val f : ℝ≥0) : ℝ) =
      -c * (a : ℝ) := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  let e := GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN
  let : Algebra V (FractionRing S) := e.toAlgebra
  let : IsFractionRing V (FractionRing S) :=
    GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  let : IsScalarTower k V (FractionRing S) := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S (FractionRing S) a,
      IsScalarTower.algebraMap_apply k S V a]
    change algebraMap S (FractionRing S) (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN _).symm
  exact dvrFractionPoint_log_of_order hc f hf a ha

/-- A genuine original nonzero vertical parameter internally gives POSITIVE
vertical order and the actual e*N+c weighted-chart formula. -/
theorem exists_parameter_orders (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (t : S) (ht : t ≠ 0) (hπt : π ∣ t) :
    ∃ e c : ℕ, 0 < e ∧
      addVal (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ t) = e ∧
      ∀ (N : ℕ) (hN : 0 < N), c < N →
        addVal (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)
          (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN t) = e * N + c := by
  obtain ⟨e,c,he,hN⟩ := GaussRegularSurfaceValuationOrders.exists_eventual_addVal π z hπ hz hm t ht
  refine ⟨e,c,?_,he,hN⟩
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let j := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  have hdiv : j π ∣ j t := map_dvd j hπt
  have hle : (1 : ℕ∞) ≤ addVal T (j t) := by
    rw [← addVal_uniformizer (GaussRegularSurfaceValuationOrders.verticalParameter_irreducible π hπ)]
    exact addVal_le_iff_dvd.mpr hdiv
  rw [he] at hle
  have hnat : 1 ≤ e := by exact_mod_cast hle
  omega

/-- The actual finite native vertical parameter order, without a chosen exponent. -/
def verticalParameterOrder (π : S) (hπ : Prime π) (t : S) : ℕ :=
  (addVal (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
    (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ t)).toNat

/-- The actual finite native weighted parameter order for EVERY positive N. -/
def weightedParameterOrder (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N) (t : S) : ℕ :=
  (addVal (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)
    (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN t)).toNat

omit [IsLocalRing S] in
/-- Finiteness and positivity are derived from the actual original vertical map. -/
theorem verticalParameterOrder_spec (π : S) (hπ : Prime π) (t : S) (ht : t ≠ 0)
    (hπt : π ∣ t) :
    addVal (GaussRegularSurfaceValuationOrders.verticalRing π hπ)
        (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ t) =
        verticalParameterOrder π hπ t ∧ 0 < verticalParameterOrder π hπ t := by
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let j := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  have hne : j t ≠ 0 := by
    intro he
    have he' := congrArg (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ) he
    rw [GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient,map_zero] at he'
    exact ((map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr ht) he'
  have hfin := (addVal_eq_top_iff (R := T)).not.mpr hne
  have hle : (1 : ℕ∞) ≤ addVal T (j t) := by
    rw [← addVal_uniformizer (GaussRegularSurfaceValuationOrders.verticalParameter_irreducible π hπ)]
    exact addVal_le_iff_dvd.mpr (map_dvd j hπt)
  exact ⟨(ENat.natCast_toNat hfin).symm,ENat.toNat_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hle)) hfin⟩

/-- Finiteness and positivity hold for EVERY actual positive weighted chart. -/
theorem weightedParameterOrder_spec (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    (t : S) (ht : t ≠ 0) (hπt : π ∣ t) :
    addVal (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)
        (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN t) =
        weightedParameterOrder π z hπ hz hm N hN t ∧
      0 < weightedParameterOrder π z hπ hz hm N hN t := by
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  have hne : j t ≠ 0 := by
    intro he
    have he' := congrArg (GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN) he
    rw [GaussRegularSurfaceValuations.fractionEmbedding_coefficient,map_zero] at he'
    exact ((map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr ht) he'
  have hfin := (addVal_eq_top_iff (R := V)).not.mpr hne
  have hle : (N : ℕ∞) ≤ addVal V (j t) := by
    rw [← GaussRegularSurfaceValuations.vertical_addVal π z hπ hz N hm hN]
    exact addVal_le_iff_dvd.mpr (map_dvd j hπt)
  have hpos : (0 : ℕ∞) < addVal V (j t) := lt_of_lt_of_le (by exact_mod_cast hN) hle
  exact ⟨(ENat.natCast_toNat hfin).symm,ENat.toNat_pos hpos.ne' hfin⟩

private theorem normalization_pos {r : ℝ≥0} (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) (hn : 0 < n) : 0 < -Real.log (r : ℝ) / (n : ℝ) := by
  apply div_pos
  · exact neg_pos.mpr (Real.log_neg (by exact_mod_cast hr0) (by exact_mod_cast hr1))
  · exact_mod_cast hn

private theorem expNeg_normalization_pow {r : ℝ≥0} (hr0 : 0 < r)
    (n : ℕ) (hn : 0 < n) : expNeg (-Real.log (r : ℝ) / (n : ℝ)) ^ n = r := by
  apply NNReal.eq
  change Real.exp (-(-Real.log (r : ℝ) / (n : ℝ))) ^ n = (r : ℝ)
  rw [← Real.exp_nat_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (n : ℝ) * (-(-Real.log (r : ℝ) / (n : ℝ))) = Real.log (r : ℝ) := by
    field_simp
  rw [he,Real.exp_log (by exact_mod_cast hr0)]

/-- The actual vertical norm normalized at the ORIGINAL parameter t and radius r. -/
def normalizedVerticalPoint (π : S) (hπ : Prime π) (t : S) (ht : t ≠ 0) (hπt : π ∣ t)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) : Berk k (FractionRing S) :=
  verticalPoint π hπ (normalization_pos hr0 hr1 _ (verticalParameterOrder_spec π hπ t ht hπt).2)

/-- EVERY actual weighted chart gives an actual original fixed-radius point. -/
def normalizedWeightedPoint (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    (t : S) (ht : t ≠ 0) (hπt : π ∣ t) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    Berk k (FractionRing S) :=
  weightedPoint π z hπ hz hm N hN
    (normalization_pos hr0 hr1 _ (weightedParameterOrder_spec π z hπ hz hm N hN t ht hπt).2)

omit [IsLocalRing S] in
/-- The SAME actual vertical point preserves EVERY original Gauss-base polynomial. -/
theorem normalizedVerticalPoint_gauss (π : S) (hπ : Prime π) (t : S) (ht : t ≠ 0)
    (hπt : π ∣ t) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    let w := normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1
    w.val (algebraMap S (FractionRing S) t) = r ∧
      (∀ s : S, w.val (algebraMap S (FractionRing S) s) ≤ 1) ∧
      ∀ F : Polynomial k, w.val (Polynomial.aeval (algebraMap S (FractionRing S) t) F) =
        gaussValuation (1 : Valuation k ℝ≥0) r F := by
  dsimp only
  have hval : (normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1).val
      (algebraMap S (FractionRing S) t) = r := by
    rw [normalizedVerticalPoint,verticalPoint_coefficient,
      (verticalParameterOrder_spec π hπ t ht hπt).1,expOrd_coe]
    exact expNeg_normalization_pow hr0 _ (verticalParameterOrder_spec π hπ t ht hπt).2
  refine ⟨hval,fun s => verticalPoint_coefficient_le_one π hπ _ s,fun F => ?_⟩
  simpa only [hval] using Berk.valuation_aeval_eq_gauss_of_lt_one
    (normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1) (algebraMap S (FractionRing S) t)
    (hval.symm ▸ hr0) (hval.symm ▸ hr1) F

/-- The SAME actual weighted points preserve the literal radius and ALL Gauss polynomials. -/
theorem normalizedWeightedPoint_gauss (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    (t : S) (ht : t ≠ 0) (hπt : π ∣ t) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    let w := normalizedWeightedPoint (k := k) π z hπ hz hm N hN t ht hπt r hr0 hr1
    w.val (algebraMap S (FractionRing S) t) = r ∧
      (∀ s : S, w.val (algebraMap S (FractionRing S) s) ≤ 1) ∧
      ∀ F : Polynomial k, w.val (Polynomial.aeval (algebraMap S (FractionRing S) t) F) =
        gaussValuation (1 : Valuation k ℝ≥0) r F := by
  dsimp only
  have hval : (normalizedWeightedPoint (k := k) π z hπ hz hm N hN t ht hπt r hr0 hr1).val
      (algebraMap S (FractionRing S) t) = r := by
    rw [normalizedWeightedPoint,weightedPoint_coefficient,
      (weightedParameterOrder_spec π z hπ hz hm N hN t ht hπt).1,expOrd_coe]
    exact expNeg_normalization_pow hr0 _ (weightedParameterOrder_spec π z hπ hz hm N hN t ht hπt).2
  refine ⟨hval,fun s => weightedPoint_coefficient_le_one π z hπ hz hm N hN _ s,fun F => ?_⟩
  simpa only [hval] using Berk.valuation_aeval_eq_gauss_of_lt_one
    (normalizedWeightedPoint (k := k) π z hπ hz hm N hN t ht hπt r hr0 hr1)
    (algebraMap S (FractionRing S) t) (hval.symm ▸ hr0) (hval.symm ▸ hr1) F

/-- The true parameter orders and canonical leading residues INTERNALLY give
the exact whole-field fixed-base corrected logarithmic profiles. -/
theorem exists_normalized_log_profile (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (t : S) (ht : t ≠ 0) (hπt : π ∣ t)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ e c : ℕ, 0 < e ∧ e = verticalParameterOrder π hπ t ∧
      ∀ (f : FractionRing S), f ≠ 0 →
      ∃ (a b : ℤ) (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ),
        f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
          (algebraMap S (FractionRing S) π) ^ a ∧
        GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = WithZero.exp a ∧
        GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
          (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
            (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) u)) = WithZero.exp b ∧
        Real.log (((normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1).val f : ℝ≥0) : ℝ) =
          (a : ℝ) / (e : ℝ) * Real.log (r : ℝ) ∧
        ∀ᶠ n : ℕ in atTop,
          weightedParameterOrder π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t = e * (n+1) + c ∧
          Real.log (((normalizedWeightedPoint (k := k) π z hπ hz hm (n+1)
            (Nat.zero_lt_succ n) t ht hπt r hr0 hr1).val f : ℝ≥0) : ℝ) =
              (a : ℝ) / (e : ℝ) * Real.log (r : ℝ) -
                (-Real.log (r : ℝ) / ((e : ℝ) * (n+1 : ℕ) + (c : ℝ))) *
                  ((b : ℝ) - (a : ℝ) / (e : ℝ) * (c : ℝ)) := by
  obtain ⟨e,c,he,hvert,htail⟩ := exists_parameter_orders π z hπ hz hm t ht hπt
  have heq : e = verticalParameterOrder π hπ t := by
    exact_mod_cast hvert.symm.trans (verticalParameterOrder_spec π hπ t ht hπt).1
  refine ⟨e,c,he,heq,?_⟩
  intro f hf
  obtain ⟨a,b,u,hfu,hfa,hfb,M,hfN⟩ :=
    GaussRegularSurfaceValuationFractions.exists_eventual_fieldOrder π z hπ hz hm f hf
  refine ⟨a,b,u,hfu,hfa,hfb,?_,?_⟩
  · calc
      _ = -(-Real.log (r : ℝ) / (verticalParameterOrder π hπ t : ℝ)) * (a : ℝ) :=
        verticalPoint_log_of_order π hπ _ f hf a hfa
      _ = _ := by rw [← heq]; ring
  · filter_upwards [eventually_gt_atTop (max M c)] with n hn
    have hNc : c < n+1 := by omega
    have hNM : M < n+1 := by omega
    have hd : weightedParameterOrder π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t =
        e * (n+1) + c := by
      exact_mod_cast (weightedParameterOrder_spec π z hπ hz hm (n+1)
        (Nat.zero_lt_succ n) t ht hπt).1.symm.trans (htail (n+1) (Nat.zero_lt_succ n) hNc)
    refine ⟨hd,?_⟩
    have hlog := weightedPoint_log_of_order (k := k) π z hπ hz hm (n+1)
      (Nat.zero_lt_succ n)
      (normalization_pos hr0 hr1 _
        (weightedParameterOrder_spec π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t ht hπt).2)
      f hf (a * (n+1 : ℕ) + b) (hfN (n+1) (Nat.zero_lt_succ n) hNM)
    change Real.log (((normalizedWeightedPoint (k := k) π z hπ hz hm (n+1)
      (Nat.zero_lt_succ n) t ht hπt r hr0 hr1).val f : ℝ≥0) : ℝ) = _ at hlog
    rw [hlog,hd]
    push_cast
    have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have hden : (e : ℝ) * ((n : ℝ) + 1) + (c : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- WHOLE genuine fixed-Gauss field points converge to the SAME actual vertical point
in the original evaluation topology, not only on a selected list of functions. -/
theorem tendsto_normalizedWeightedPoint (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (t : S) (ht : t ≠ 0) (hπt : π ∣ t)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => normalizedWeightedPoint (k := k) π z hπ hz hm (n+1)
      (Nat.zero_lt_succ n) t ht hπt r hr0 hr1) atTop
      (𝓝 (normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1)) := by
  let w := fun n : ℕ => normalizedWeightedPoint (k := k) π z hπ hz hm (n+1)
    (Nat.zero_lt_succ n) t ht hπt r hr0 hr1
  let w0 := normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1
  obtain ⟨e,c,he,_,H⟩ := exists_normalized_log_profile (k := k) π z hπ hz hm t ht hπt r hr0 hr1
  apply Berk.isInducing_toFun.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro f
  change Tendsto (fun n : ℕ => (w n).val f) atTop (𝓝 (w0.val f))
  by_cases hf : f = 0
  · subst f
    simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0)) atTop (𝓝 0))
  obtain ⟨a,b,_,_,_,_,h0,htail⟩ := H f hf
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hden : Tendsto (fun n : ℕ => (e : ℝ) * (n+1 : ℕ) + (c : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (c : ℝ) (Tendsto.const_mul_atTop (by exact_mod_cast he) hN)
  have hε : Tendsto (fun n : ℕ => -Real.log (r : ℝ) / ((e : ℝ) * (n+1 : ℕ) + (c : ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hlog : Tendsto (fun n : ℕ => Real.log (((w n).val f : ℝ≥0) : ℝ)) atTop
      (𝓝 (Real.log ((w0.val f : ℝ≥0) : ℝ))) := by
    rw [show Real.log ((w0.val f : ℝ≥0) : ℝ) = (a : ℝ) / (e : ℝ) * Real.log (r : ℝ) from h0]
    have hp := (tendsto_const_nhds (x := (a : ℝ) / (e : ℝ) * Real.log (r : ℝ))).sub
      (hε.mul_const ((b : ℝ) - (a : ℝ) / (e : ℝ) * (c : ℝ)))
    simp only [zero_mul,sub_zero] at hp
    exact hp.congr' (htail.mono fun n hn => hn.2.symm)
  apply NNReal.tendsto_coe.mp
  have hvn (n : ℕ) : 0 < (((w n).val f : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (((map_ne_zero (w n).val).mpr hf).pos)
  have hv0 : 0 < ((w0.val f : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (((map_ne_zero w0.val).mpr hf).pos)
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  change Tendsto (fun n : ℕ => Real.exp (Real.log (((w n).val f : ℝ≥0) : ℝ))) atTop
    (𝓝 (Real.exp (Real.log ((w0.val f : ℝ≥0) : ℝ)))) at hexp
  have heqn : (fun n : ℕ => Real.exp (Real.log (((w n).val f : ℝ≥0) : ℝ))) =
      fun n : ℕ => (((w n).val f : ℝ≥0) : ℝ) := by
    funext n
    exact Real.exp_log (hvn n)
  rw [heqn,Real.exp_log hv0] at hexp
  exact hexp

/-- The TRUE actual negative-log difference quotient is eventually the intrinsic
corrected residual order, with genuine vertical and leading-residue data produced
internally. In vertical order zero this is literally the native residual order. -/
theorem exists_normalized_log_quotient (π z : S) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal S = Ideal.span {π,z}) (t : S) (ht : t ≠ 0) (hπt : π ∣ t)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) (f : FractionRing S) (hf : f ≠ 0) :
    let Q := fun n : ℕ =>
      (Real.log (((normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1).val f : ℝ≥0) : ℝ) -
        Real.log (((normalizedWeightedPoint (k := k) π z hπ hz hm (n+1)
          (Nat.zero_lt_succ n) t ht hπt r hr0 hr1).val f : ℝ≥0) : ℝ)) /
            (-Real.log (r : ℝ) /
              (weightedParameterOrder π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t : ℝ))
    ∃ (e c : ℕ) (a b : ℤ) (u : (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ),
      0 < e ∧ e = verticalParameterOrder π hπ t ∧
      f = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ u *
        (algebraMap S (FractionRing S) π) ^ a ∧
      GaussRegularSurfaceValuationFractions.verticalOrder π hπ f = WithZero.exp a ∧
      GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
        (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
          (residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) u)) = WithZero.exp b ∧
      (∀ᶠ n : ℕ in atTop,
        weightedParameterOrder π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t = e * (n+1) + c ∧
          Q n = (b : ℝ) - (a : ℝ) / (e : ℝ) * (c : ℝ)) ∧
      Tendsto Q atTop (𝓝 ((b : ℝ) - (a : ℝ) / (e : ℝ) * (c : ℝ))) := by
  let Q := fun n : ℕ =>
    (Real.log (((normalizedVerticalPoint (k := k) π hπ t ht hπt r hr0 hr1).val f : ℝ≥0) : ℝ) -
      Real.log (((normalizedWeightedPoint (k := k) π z hπ hz hm (n+1)
        (Nat.zero_lt_succ n) t ht hπt r hr0 hr1).val f : ℝ≥0) : ℝ)) /
          (-Real.log (r : ℝ) /
            (weightedParameterOrder π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t : ℝ))
  obtain ⟨e,c,he,heq,H⟩ := exists_normalized_log_profile (k := k) π z hπ hz hm t ht hπt r hr0 hr1
  obtain ⟨a,b,u,hfactor,hvert,hres,h0,htail⟩ := H f hf
  have hquot : ∀ᶠ n : ℕ in atTop, Q n = (b : ℝ) - (a : ℝ) / (e : ℝ) * (c : ℝ) := by
    filter_upwards [htail] with n hn
    have hdR : (weightedParameterOrder π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t : ℝ) =
        (e : ℝ) * (n+1 : ℕ) + (c : ℝ) := by exact_mod_cast hn.1
    have hln := hn.2
    rw [← hdR] at hln
    have hpos := normalization_pos hr0 hr1 _
      (weightedParameterOrder_spec π z hπ hz hm (n+1) (Nat.zero_lt_succ n) t ht hπt).2
    apply (div_eq_iff hpos.ne').mpr
    rw [hln,h0]
    ring
  refine ⟨e,c,a,b,u,he,heq,hfactor,hvert,hres,?_,?_⟩
  · exact (htail.and hquot).mono fun _ hn => ⟨hn.1.1,hn.2⟩
  · exact tendsto_const_nhds.congr' (hquot.mono fun _ h => h.symm)

end EnvelopeProperty.GaussRegularSurfaceRealNorms
