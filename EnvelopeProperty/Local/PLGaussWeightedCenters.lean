import EnvelopeProperty.Local.PLGaussCommonVerticalPoints

/-! # The SAME original weighted Gauss points have their TRUE original closed centers -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open scoped Classical NNReal
universe u
namespace EnvelopeProperty.GaussWeightedCenters
open Berkovich
variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
  {f : Y ⟶ Spec (CommRingCat.of (Polynomial k))} [IsProper f]

private theorem gauss_le_one {r : ℝ≥0} (hr : r ≤ 1) (F : Polynomial k) :
    gaussValuation (1 : Valuation k ℝ≥0) r F ≤ 1 := by
  change gaussFun (1 : Valuation k ℝ≥0) r F ≤ 1
  apply (gaussFun_le_iff _ _ _ _).mpr
  intro n
  by_cases hn : F.coeff n = 0
  · simp only [hn,map_zero,zero_mul,zero_le]
  · rw [Valuation.one_apply_of_ne_zero hn,one_mul]
    exact pow_le_one₀ (show 0 ≤ r from zero_le) hr

omit [IsIntegral Y] [IsProper f] in
private theorem actualCoefficientMap_eq_old (p : Y) :
    GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f p =
      SchemeStalkCoefficients.coefficientMap f p := by
  apply RingHom.ext
  intro a
  change Y.presheaf.germ ⊤ p trivial
    (Y.presheaf.map (homOfLE (le_refl (⊤ : Y.Opens))).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv a))) =
    Y.presheaf.germ ⊤ p trivial (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv a))
  simp only [homOfLE_refl, op_id]
  exact congrArg (fun q : Γ(Y,⊤) ⟶ Γ(Y,⊤) =>
    Y.presheaf.germ ⊤ p (show p ∈ (⊤ : Y.Opens) from trivial)
      (q (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv a))))
    (Y.presheaf.map_id (Opposite.op (⊤ : Y.Opens)))

omit [IsIntegral Y] [IsProper f] in
private theorem fromSpecStalk_actualCoefficients (p : Y) :
    Y.fromSpecStalk p ≫ f = Spec.map (CommRingCat.ofHom
      (GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f p)) := by
  rw [actualCoefficientMap_eq_old]
  exact SchemeStalkCoefficients.fromSpecStalk_structureMap f p

omit [IsIntegral Y] in
private theorem center_eq_of_same_underlying
    {v w : Valuation (Polynomial k) ℝ≥0} (hv : ∀ a, v a ≤ 1) (hw : ∀ a, w a ≤ 1)
    (y : RelativeSchemeValuedPoint v f) (z : RelativeSchemeValuedPoint w f)
    (h : y.1 = z.1) :
    RelativeSchemeValuedPoint.center hv y = RelativeSchemeValuedPoint.center hw z := by
  have hbase := y.2.symm.trans ((congrArg (SchemeValuedPoint.map f) h).trans z.2)
  have hval : v = w := by
    apply Valuation.ext
    intro a
    have he := congrArg (fun b : SchemeValuedPoint (Spec (CommRingCat.of (Polynomial k))) =>
      (SchemeValuedPoint.spectrumHomeomorph b).val a) hbase
    simpa only [SchemeValuedPoint.basePoint, Homeomorph.apply_symm_apply,
      Spectrum.ofValuation_val] using he
  cases hval
  have hyz : y = z := Subtype.ext h
  cases hyz
  rfl

/-- The ORIGINAL weighted DVR morphism, through the SAME original stalk. -/
def weightedMorphism (p : Y) (π z : Y.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal (Y.presheaf.stalk p) = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N) :
    Spec (CommRingCat.of (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom
    (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN)) ≫ Y.fromSpecStalk p

/-- Its actual original closed point maps to the SAME original p. -/
theorem weightedMorphism_closedPoint (p : Y) (π z : Y.presheaf.stalk p)
    (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal (Y.presheaf.stalk p) = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N) :
    weightedMorphism p π z hπ hz hm N hN
      (closedPoint (GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN)) = p := by
  let S := Y.presheaf.stalk p
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  have hclosed : Spec.map (CommRingCat.ofHom j) (closedPoint V) = closedPoint S := by
    apply PrimeSpectrum.ext
    exact GaussRegularSurfaceValuations.localCenter π z hπ hz N hm hN
  change Y.fromSpecStalk p (Spec.map (CommRingCat.ofHom j) (closedPoint V)) = p
  rw [hclosed]
  exact Scheme.fromSpecStalk_closedPoint

private theorem genericMap_from_weightedMorphism (p : Y) (π z : Y.presheaf.stalk p)
    (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal (Y.presheaf.stalk p) = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N) :
    letI : Algebra Y.functionField (FractionRing (Y.presheaf.stalk p)) :=
      (GaussRegularSurfaceConvexProfiles.genericFieldMap p).toAlgebra
    SpecifiedFieldSchemeNormalization.genericMap Y (FractionRing (Y.presheaf.stalk p)) =
      Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN)) ≫
        weightedMorphism p π z hπ hz hm N hN := by
  let : Algebra Y.functionField (FractionRing (Y.presheaf.stalk p)) :=
    (GaussRegularSurfaceConvexProfiles.genericFieldMap p).toAlgebra
  have hleft :
      Spec.map (CommRingCat.ofHom (GaussRegularSurfaceConvexProfiles.genericFieldMap p)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk p) Y.functionField)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk p) (FractionRing (Y.presheaf.stalk p)))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext s
    exact (FractionRing.algEquiv (A := Y.presheaf.stalk p) Y.functionField).symm.commutes s
  have hright :
      Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN)) ≫
        Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk p) (FractionRing (Y.presheaf.stalk p)))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext s
    exact GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN s
  change Spec.map (CommRingCat.ofHom (GaussRegularSurfaceConvexProfiles.genericFieldMap p)) ≫
    Y.fromSpecStalk (genericPoint Y) = _
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y).specializes
    (show p ∈ (Set.univ : Set Y) from trivial))]
  change Spec.map (CommRingCat.ofHom (GaussRegularSurfaceConvexProfiles.genericFieldMap p)) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk p) Y.functionField)) ≫
      Y.fromSpecStalk p) = _
  change _ = Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN)) ≫
    (Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN)) ≫
      Y.fromSpecStalk p)
  rw [← Category.assoc, hleft, ← Category.assoc, hright]

/-- EVERY original positive-index weighted point has the derived TRUE original center p. -/
theorem center_nativeWeightedPoint (p : Y) [IsNoetherianRing (Y.presheaf.stalk p)]
    (π z : Y.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : maximalIdeal (Y.presheaf.stalk p) = Ideal.span {π,z}) (N : ℕ) (hN : 0 < N)
    (ht : GaussRegularSurfaceConvexProfiles.stalkParameter f p ≠ 0)
    (hπt : π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    RelativeSchemeValuedPoint.center (gauss_le_one hr1.le)
      (GaussRegularSurfaceConvexProfiles.nativeWeightedPoint f p π z hπ hz hm N hN ht hπt r hr0 hr1) =
      p := by
  let S := Y.presheaf.stalk p
  let : Algebra k S := ((GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f p).comp Polynomial.C).toAlgebra
  let V := GaussRegularSurfaceValuations.localRing π z hπ hz N hm hN
  let j := GaussRegularSurfaceValuations.localCoefficientMap π z hπ hz N hm hN
  let e := GaussRegularSurfaceValuations.fractionEmbedding π z hπ hz N hm hN
  let K := FractionRing S
  let : IsDiscreteValuationRing V := GaussRegularSurfaceValuations.localRing_isDVR π z hπ hz N hm hN
  let : Algebra V K := e.toAlgebra
  let : IsFractionRing V K := GaussRegularSurfaceValuations.localFractionRing π z hπ hz N hm hN
  let : IsScalarTower k V K := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S K a,IsScalarTower.algebraMap_apply k S V a]
    change algebraMap S K (algebraMap k S a) = e (j (algebraMap k S a))
    exact (GaussRegularSurfaceValuations.fractionEmbedding_coefficient π z hπ hz N hm hN _).symm
  let c := -Real.log (r : ℝ) /
    (GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm N hN
      (GaussRegularSurfaceConvexProfiles.stalkParameter f p) : ℝ)
  have hc : 0 < c := by
    apply div_pos
    · exact neg_pos.mpr (Real.log_neg (by exact_mod_cast hr0) (by exact_mod_cast hr1))
    · exact_mod_cast (GaussRegularSurfaceRealNorms.weightedParameterOrder_spec π z hπ hz hm N hN
        (GaussRegularSurfaceConvexProfiles.stalkParameter f p) ht hπt).2
  let q := weightedMorphism p π z hπ hz hm N hN
  let φ := j.comp (GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f p)
  have hq : q ≫ f = Spec.map (CommRingCat.ofHom φ) := by
    change (Spec.map (CommRingCat.ofHom j) ≫ Y.fromSpecStalk p) ≫ f = _
    rw [Category.assoc,fromSpecStalk_actualCoefficients,← Spec.map_comp]
    rfl
  let n := RelativeSchemeValuedPoint.nativeDVRPoint (k := k) (f := f) q φ hq hc
  let y := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint f p π z hπ hz hm N hN ht hπt r hr0 hr1
  let vV := (Berk.dvrPoint (AlgHom.id k V) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val
  have hbn : ∀ a, (vV.comap φ) a ≤ 1 := by
    intro a
    change expOrd (expNeg c) (IsDiscreteValuationRing.addVal V (φ a)) ≤ 1
    exact expOrd_le_one (ProjBerk.expNeg_le_one hc.le) _
  let : Algebra Y.functionField K := (GaussRegularSurfaceConvexProfiles.genericFieldMap p).toAlgebra
  have hpoint : y.1 = n.1 := by
    change SchemeValuedPoint.map (SpecifiedFieldSchemeNormalization.genericMap Y K)
        (SchemeValuedPoint.basePoint (Berk.dvrFractionPoint (k := k) (V := V) (K := K) hc).val) =
      SchemeValuedPoint.map q (SchemeValuedPoint.basePoint vV)
    rw [genericMap_from_weightedMorphism p π z hπ hz hm N hN,SchemeValuedPoint.map_comp]
    apply congrArg (SchemeValuedPoint.map q)
    exact SchemeValuedPoint.map_basePoint e
      (fun a => Berk.dvrFractionPoint_val_algebraMap hc a)
  change RelativeSchemeValuedPoint.center (gauss_le_one hr1.le) y = _
  exact (center_eq_of_same_underlying (gauss_le_one hr1.le) hbn y n hpoint).trans
    ((RelativeSchemeValuedPoint.center_nativeDVRPoint (k := k) (V := V) (f := f) q φ hq hc).trans
      (weightedMorphism_closedPoint p π z hπ hz hm N hN))

end EnvelopeProperty.GaussWeightedCenters
