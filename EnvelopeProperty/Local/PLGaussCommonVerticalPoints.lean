import EnvelopeProperty.AlgGeom.GaussCommonVerticalStalks
import EnvelopeProperty.Local.PLGaussRegularSurfaceConvexProfiles
import EnvelopeProperty.Berkovich.SchemeDVRModelPoints
import EnvelopeProperty.Berkovich.SchemeGenericCenterValuations
import EnvelopeProperty.Berkovich.SchemeVerticalCenteredPoints
import EnvelopeProperty.Berkovich.SchemeRelativeBaseChange

/-! # The same original normalized vertical point on a whole original component -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open scoped Classical NNReal Polynomial WithZero

universe u
namespace EnvelopeProperty.GaussCommonVerticalPoints
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

/-- Actual DVR-center geometry DERIVES the original generic support. -/
theorem genericSupport_of_verticalDVRCenter (η : Y)
    [IsDiscreteValuationRing (Y.presheaf.stalk η)]
    (hη : Polynomial.X ∈ (f η).asIdeal) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1)
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f)
    (hc : RelativeSchemeValuedPoint.center (gauss_le_one hr1.le) y = η) :
    y.1.point = genericPoint Y := by
  let D := Y.presheaf.stalk η
  let : IsDomain D := inferInstanceAs (IsDomain (Y.presheaf.stalk η))
  let g := Y.fromSpecStalk η
  let zeroPoint : Spec D := (⊥ : PrimeSpectrum D)
  have htwo (q : Spec D) : q = zeroPoint ∨ q = closedPoint D := by
    by_cases hq : q.asIdeal = ⊥
    · exact Or.inl (PrimeSpectrum.ext hq)
    · right
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (q.isPrime.isMaximal_of_ne_bot hq)
  have hηne : η ≠ genericPoint Y := by
    intro he
    apply IsDiscreteValuationRing.not_a_field (Y.presheaf.stalk η)
    exact (congrArg (fun q : Y => maximalIdeal (Y.presheaf.stalk q) = ⊥) he).mpr
      (IsLocalRing.maximalIdeal_eq_bot (R := Y.functionField))
  have hgen : genericPoint Y ∈ Set.range g := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec Y).specializes trivial
  obtain ⟨a,ha⟩ := hgen
  have hgzero : g zeroPoint = genericPoint Y := by
    obtain hbot | hclosed := htwo a
    · simpa only [hbot] using ha
    · have he : η = genericPoint Y := by
        simpa only [hclosed, g, D, Scheme.fromSpecStalk_closedPoint] using ha
      exact (hηne he).elim
  have hpointne : y.1.point ≠ η := by
    intro he
    have hbase := congrArg SchemeValuedPoint.point y.2
    change f y.1.point = (SchemeValuedPoint.basePoint
      (gaussValuation (1 : Valuation k ℝ≥0) r)).point at hbase
    have hzero : Polynomial.X ∈ (SchemeValuedPoint.basePoint
        (gaussValuation (1 : Valuation k ℝ≥0) r)).point.asIdeal := by
      rw [← hbase, he]
      exact hη
    change gaussValuation (1 : Valuation k ℝ≥0) r Polynomial.X = 0 at hzero
    change gaussFun (1 : Valuation k ℝ≥0) r Polynomial.X = 0 at hzero
    rw [gaussFun_X] at hzero
    exact hr0.ne' hzero
  have hyrange : y.1.point ∈ Set.range g := by
    rw [Scheme.range_fromSpecStalk]
    change y.1.point ⤳ η
    simpa only [hc] using RelativeSchemeValuedPoint.support_specializes_center
      (gauss_le_one hr1.le) y
  obtain ⟨a,ha⟩ := hyrange
  obtain hbot | hclosed := htwo a
  · exact ha.symm.trans (hbot ▸ hgzero)
  · have he : η = y.1.point := by
      simpa only [hclosed,g,D,Scheme.fromSpecStalk_closedPoint] using ha
    exact (hpointne he.symm).elim

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

variable {C : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i] [IsIntegral C] (x : C)

private def verticalMorphism (π : Y.presheaf.stalk (i x)) (hπ : Prime π) :
    Spec (CommRingCat.of (GaussRegularSurfaceValuationOrders.verticalRing π hπ)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ)) ≫
    Y.fromSpecStalk (i x)

/-- The original vertical DVR's actual closed image is the SAME component generic point. -/
theorem verticalMorphism_closedPoint (π : Y.presheaf.stalk (i x)) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}) :
    verticalMorphism i x π hπ
      (closedPoint (GaussRegularSurfaceValuationOrders.verticalRing π hπ)) = i (genericPoint C) := by
  let e := GaussCommonVerticalStalks.componentStalkEquiv i x π hπ hker
  let h : i (genericPoint C) ⤳ i x :=
    i.base.hom.map_specializes ((genericPoint_spec C).specializes trivial)
  let j := GaussCommonVerticalStalks.generizationMap h
  let ρ := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  have hring : e.symm.toRingHom.comp j = ρ := by
    ext s
    apply e.injective
    change e (e.symm (j s)) = e (ρ s)
    rw [RingEquiv.apply_symm_apply]
    exact (GaussCommonVerticalStalks.componentStalkEquiv_coefficient i x π hπ hker s).symm
  have hmaps : Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom j) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact hring.symm
  have hwhole : verticalMorphism i x π hπ =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Y.fromSpecStalk (i (genericPoint C)) := by
    change Spec.map (CommRingCat.ofHom ρ) ≫ Y.fromSpecStalk (i x) = _
    rw [hmaps, Category.assoc]
    change _ ≫ (Spec.map (Y.presheaf.stalkSpecializes h) ≫ Y.fromSpecStalk (i x)) = _
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  let : IsLocalHom (CommRingCat.ofHom e.symm.toRingHom).hom :=
    IsLocalHom.of_surjective _ e.symm.surjective
  have hclosed : Spec.map (CommRingCat.ofHom e.symm.toRingHom)
      (closedPoint (GaussRegularSurfaceValuationOrders.verticalRing π hπ)) =
      closedPoint (Y.presheaf.stalk (i (genericPoint C))) := AlgebraicGeometry.Spec_closedPoint
  calc
    verticalMorphism i x π hπ (closedPoint (GaussRegularSurfaceValuationOrders.verticalRing π hπ)) =
        (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Y.fromSpecStalk (i (genericPoint C)))
          (closedPoint (GaussRegularSurfaceValuationOrders.verticalRing π hπ)) :=
      congrArg (fun q => q (closedPoint (GaussRegularSurfaceValuationOrders.verticalRing π hπ))) hwhole
    _ = Y.fromSpecStalk (i (genericPoint C))
        (Spec.map (CommRingCat.ofHom e.symm.toRingHom)
          (closedPoint (GaussRegularSurfaceValuationOrders.verticalRing π hπ))) := rfl
    _ = Y.fromSpecStalk (i (genericPoint C)) (closedPoint (Y.presheaf.stalk (i (genericPoint C)))) :=
      congrArg (Y.fromSpecStalk (i (genericPoint C))) hclosed
    _ = i (genericPoint C) := Scheme.fromSpecStalk_closedPoint

omit [IsClosedImmersion i] [IsIntegral C] in
private theorem genericMap_from_verticalMorphism (π : Y.presheaf.stalk (i x)) (hπ : Prime π) :
    letI : Algebra Y.functionField (FractionRing (Y.presheaf.stalk (i x))) :=
      (GaussRegularSurfaceConvexProfiles.genericFieldMap (i x)).toAlgebra
    SpecifiedFieldSchemeNormalization.genericMap Y (FractionRing (Y.presheaf.stalk (i x))) =
      Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ)) ≫
        verticalMorphism i x π hπ := by
  let : Algebra Y.functionField (FractionRing (Y.presheaf.stalk (i x))) :=
    (GaussRegularSurfaceConvexProfiles.genericFieldMap (i x)).toAlgebra
  have hleft :
      Spec.map (CommRingCat.ofHom (GaussRegularSurfaceConvexProfiles.genericFieldMap (i x))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (i x)) Y.functionField)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk (i x)) (FractionRing (Y.presheaf.stalk (i x))))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext s
    exact (FractionRing.algEquiv (A := Y.presheaf.stalk (i x)) Y.functionField).symm.commutes s
  have hright :
      Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ)) ≫
        Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ)) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (Y.presheaf.stalk (i x)) (FractionRing (Y.presheaf.stalk (i x))))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext s
    exact GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ s
  change Spec.map (CommRingCat.ofHom (GaussRegularSurfaceConvexProfiles.genericFieldMap (i x))) ≫
    Y.fromSpecStalk (genericPoint Y) = _
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y).specializes
    (show i x ∈ (Set.univ : Set Y) from trivial))]
  change Spec.map (CommRingCat.ofHom (GaussRegularSurfaceConvexProfiles.genericFieldMap (i x))) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (i x)) Y.functionField)) ≫
      Y.fromSpecStalk (i x)) = _
  change _ = Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ)) ≫
    (Spec.map (CommRingCat.ofHom (GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ)) ≫
      Y.fromSpecStalk (i x))
  rw [← Category.assoc, hleft, ← Category.assoc, hright]

/-- The EXISTING normalized original point has the derived SAME true component center. -/
theorem center_nativeVerticalPoint [IsNoetherianRing (Y.presheaf.stalk (i x))]
    (π : Y.presheaf.stalk (i x)) (hπ : Prime π)
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (ht : GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) ≠ 0)
    (hπt : π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter f (i x))
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    RelativeSchemeValuedPoint.center (gauss_le_one hr1.le)
      (GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f (i x) π hπ ht hπt r hr0 hr1) =
      i (genericPoint C) := by
  let p := i x
  let S := Y.presheaf.stalk p
  let : Algebra k S := ((GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f p).comp Polynomial.C).toAlgebra
  let T := GaussRegularSurfaceValuationOrders.verticalRing π hπ
  let ρ := GaussRegularSurfaceValuationOrders.verticalCoefficientMap π hπ
  let e := GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ
  let K := FractionRing S
  let : IsDiscreteValuationRing T := GaussRegularSurfaceValuationOrders.vertical_isDVR π hπ
  let : Algebra T K := e.toAlgebra
  let : IsFractionRing T K := GaussRegularSurfaceValuationFractions.verticalFractionRing π hπ
  let : IsScalarTower k T K := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k S K a, IsScalarTower.algebraMap_apply k S T a]
    change algebraMap S K (algebraMap k S a) = e (ρ (algebraMap k S a))
    exact (GaussRegularSurfaceValuationFractions.verticalFractionEmbedding_coefficient π hπ _).symm
  let c := -Real.log (r : ℝ) /
    (GaussRegularSurfaceRealNorms.verticalParameterOrder π hπ
      (GaussRegularSurfaceConvexProfiles.stalkParameter f p) : ℝ)
  have hc : 0 < c := by
    apply div_pos
    · exact neg_pos.mpr (Real.log_neg (by exact_mod_cast hr0) (by exact_mod_cast hr1))
    · exact_mod_cast (GaussRegularSurfaceRealNorms.verticalParameterOrder_spec
        π hπ (GaussRegularSurfaceConvexProfiles.stalkParameter f p) ht hπt).2
  let q := verticalMorphism i x π hπ
  let φ := ρ.comp (GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f p)
  have hq : q ≫ f = Spec.map (CommRingCat.ofHom φ) := by
    change (Spec.map (CommRingCat.ofHom ρ) ≫ Y.fromSpecStalk p) ≫ f = _
    rw [Category.assoc, fromSpecStalk_actualCoefficients, ← Spec.map_comp]
    rfl
  let n := RelativeSchemeValuedPoint.nativeDVRPoint (k := k) (f := f) q φ hq hc
  let y := GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f p π hπ ht hπt r hr0 hr1
  let vT := (Berk.dvrPoint (AlgHom.id k T) (expNeg c) (ProjBerk.expNeg_le_one hc.le)).val
  have hbn : ∀ a, (vT.comap φ) a ≤ 1 := by
    intro a
    change expOrd (expNeg c) (IsDiscreteValuationRing.addVal T (φ a)) ≤ 1
    exact expOrd_le_one (ProjBerk.expNeg_le_one hc.le) _
  let : Algebra Y.functionField K := (GaussRegularSurfaceConvexProfiles.genericFieldMap p).toAlgebra
  have hpoint : y.1 = n.1 := by
    change SchemeValuedPoint.map (SpecifiedFieldSchemeNormalization.genericMap Y K)
        (SchemeValuedPoint.basePoint (Berk.dvrFractionPoint (k := k) (V := T) (K := K) hc).val) =
      SchemeValuedPoint.map q (SchemeValuedPoint.basePoint vT)
    rw [genericMap_from_verticalMorphism i x π hπ, SchemeValuedPoint.map_comp]
    apply congrArg (SchemeValuedPoint.map q)
    exact SchemeValuedPoint.map_basePoint e
      (fun a => Berk.dvrFractionPoint_val_algebraMap hc a)
  change RelativeSchemeValuedPoint.center (gauss_le_one hr1.le) y = _
  exact (center_eq_of_same_underlying (gauss_le_one hr1.le) hbn y n hpoint).trans
    ((RelativeSchemeValuedPoint.center_nativeDVRPoint (k := k) (V := T) (f := f) q φ hq hc).trans
      (verticalMorphism_closedPoint i x π hπ hker))

private theorem exists_scale_at_center (η : Y)
    [IsDiscreteValuationRing (Y.presheaf.stalk η)]
    (r : ℝ≥0) (hr1 : r < 1)
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f)
    (hy : y.1.point = genericPoint Y)
    (hc : RelativeSchemeValuedPoint.center (gauss_le_one hr1.le) y = η) :
    ∃ s : ℝ≥0, 0 < s ∧ SchemeValuedPoint.genericValuation y.1 hy =
      DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (Y.presheaf.stalk η)).valuation Y.functionField) s := by
  cases hc
  exact (RelativeSchemeValuedPoint.existsUnique_genericCenter_functionField_realScale
    (gauss_le_one hr1.le) y hy).exists

/-- The actual parameter value fixes the scale, hence the WHOLE original native point. -/
theorem eq_of_same_verticalDVRCenter (η : Y)
    [IsDiscreteValuationRing (Y.presheaf.stalk η)]
    (hη : Polynomial.X ∈ (f η).asIdeal) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1)
    (y z : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f)
    (hy : RelativeSchemeValuedPoint.center (gauss_le_one hr1.le) y = η)
    (hz : RelativeSchemeValuedPoint.center (gauss_le_one hr1.le) z = η) : y = z := by
  have hygen := genericSupport_of_verticalDVRCenter η hη r hr0 hr1 y hy
  have hzgen := genericSupport_of_verticalDVRCenter η hη r hr0 hr1 z hz
  obtain ⟨s,hs,hvs⟩ := exists_scale_at_center η r hr1 y hygen hy
  obtain ⟨t,ht,hvt⟩ := exists_scale_at_center η r hr1 z hzgen hz
  let τ := GaussRegularSurfaceConvexProfiles.stalkParameter f η
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨η,trivial⟩⟩
  have hparam (w : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f)
      (hw : w.1.point = genericPoint Y) :
      SchemeValuedPoint.genericValuation w.1 hw
        (algebraMap (Y.presheaf.stalk η) Y.functionField τ) = r := by
    change SchemeValuedPoint.genericValuation w.1 hw
      (algebraMap (Y.presheaf.stalk η) Y.functionField
        (Y.presheaf.germ ⊤ η trivial (SchemeValuedPoint.sectionBaseMap f ⊤ Polynomial.X))) = r
    have hfield := congrArg (SchemeValuedPoint.genericValuation w.1 hw)
      (Y.algebraMap_germ_eq_germToFunctionField (show η ∈ (⊤ : Y.Opens) from trivial)
        (SchemeValuedPoint.sectionBaseMap f ⊤ Polynomial.X))
    have heval := SchemeValuedPoint.genericValuation_eval w.1 hw ⊤
      (show w.1.point ∈ (⊤ : Y.Opens) from trivial)
      (SchemeValuedPoint.sectionBaseMap f ⊤ Polynomial.X)
    have hbase := RelativeSchemeValuedPoint.eval_sectionBaseMap w ⊤
      (show w.1.point ∈ (⊤ : Y.Opens) from trivial) Polynomial.X
    have hgauss : gaussValuation (1 : Valuation k ℝ≥0) r Polynomial.X = r :=
      gaussFun_X _ _
    exact hfield.trans (heval.trans (hbase.trans hgauss))
  have hτ : τ ≠ 0 := by
    intro he
    apply hr0.ne'
    rw [← hparam y hygen, he, map_zero, map_zero]
  have hmem : τ ∈ maximalIdeal (Y.presheaf.stalk η) := by
    change GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f η Polynomial.X ∈ _
    rw [actualCoefficientMap_eq_old]
    change Polynomial.X ∈ (maximalIdeal (Y.presheaf.stalk η)).comap
      (SchemeStalkCoefficients.coefficientMap f η)
    rw [SchemeStalkCoefficients.maximalIdeal_comap_coefficientMap]
    exact hη
  obtain ⟨e,he⟩ := ENat.ne_top_iff_exists.mp
    ((IsDiscreteValuationRing.addVal_eq_top_iff (R := Y.presheaf.stalk η)).not.mpr hτ)
  have he0 : e ≠ 0 := by
    intro hez
    have hord : IsDiscreteValuationRing.addVal (Y.presheaf.stalk η) τ = 0 := by
      rw [← he, hez, Nat.cast_zero]
    exact (mem_maximalIdeal τ).mp hmem (IsDiscreteValuationRing.addVal_eq_zero_iff.mp hord)
  have heR : (0 : ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he0)
  have hnative : (IsDiscreteValuationRing.maximalIdeal (Y.presheaf.stalk η)).valuation
      Y.functionField (algebraMap (Y.presheaf.stalk η) Y.functionField τ) =
      WithZero.exp (-(e : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal, ← he]
    change (WithZero.exp (e : ℤ))⁻¹ = WithZero.exp (-(e : ℤ))
    rw [WithZero.exp_neg]
  have hlog (a : ℝ≥0) :
      Real.log ((DiscreteValuationRealScale.valuation
        ((IsDiscreteValuationRing.maximalIdeal (Y.presheaf.stalk η)).valuation Y.functionField) a
        (algebraMap (Y.presheaf.stalk η) Y.functionField τ) : ℝ≥0) : ℝ) =
      -(a : ℝ) * (e : ℝ) := by
    change Real.log ((DiscreteValuationRealScale.scale a
      ((IsDiscreteValuationRing.maximalIdeal (Y.presheaf.stalk η)).valuation Y.functionField
        (algebraMap (Y.presheaf.stalk η) Y.functionField τ)) : ℝ≥0) : ℝ) = _
    rw [hnative, DiscreteValuationRealScale.log_scale_exp]
    simp only [Int.cast_neg, Int.cast_natCast]
    ring
  have hslog : Real.log (r : ℝ) = -(s : ℝ) * (e : ℝ) := by
    rw [← hparam y hygen, hvs]
    exact hlog s
  have htlog : Real.log (r : ℝ) = -(t : ℝ) * (e : ℝ) := by
    rw [← hparam z hzgen, hvt]
    exact hlog t
  have hst : s = t := NNReal.eq (by nlinarith [hslog,htlog,heR])
  rw [hst] at hvs
  exact Subtype.ext (SchemeValuedPoint.eq_of_genericValuation_eq y.1 z.1 hygen hzgen
    (hvs.trans hvt.symm))

private theorem actualParameter_facts [IsDominant f]
    (π : Y.presheaf.stalk (i x))
    (hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π})
    (hη : Polynomial.X ∈ (f (i (genericPoint C))).asIdeal) :
    GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) ≠ 0 ∧
      π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) := by
  constructor
  · change GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f (i x) Polynomial.X ≠ 0
    rw [actualCoefficientMap_eq_old]
    exact (map_ne_zero_iff _ (SchemeStalkCoefficients.coefficientMap_injective f (i x))).mpr
      Polynomial.X_ne_zero
  · let h : i (genericPoint C) ⤳ i x :=
      i.base.hom.map_specializes ((genericPoint_spec C).specializes trivial)
    have hcomm : GaussCommonVerticalStalks.generizationMap h
        (GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)) =
        GaussRegularSurfaceConvexProfiles.stalkParameter f (i (genericPoint C)) := by
      exact congrArg (fun φ : Γ(Y,⊤) ⟶ Y.presheaf.stalk (i (genericPoint C)) =>
        φ (SchemeValuedPoint.sectionBaseMap f ⊤ Polynomial.X))
        (Y.presheaf.germ_stalkSpecializes (show i x ∈ (⊤ : Y.Opens) from trivial) h)
    have hmem : GaussRegularSurfaceConvexProfiles.stalkParameter f (i (genericPoint C)) ∈
        maximalIdeal (Y.presheaf.stalk (i (genericPoint C))) := by
      change GaussRegularSurfaceConvexProfiles.stalkCoefficientMap f (i (genericPoint C)) Polynomial.X ∈ _
      rw [actualCoefficientMap_eq_old]
      change Polynomial.X ∈ (maximalIdeal (Y.presheaf.stalk (i (genericPoint C)))).comap
        (SchemeStalkCoefficients.coefficientMap f (i (genericPoint C)))
      rw [SchemeStalkCoefficients.maximalIdeal_comap_coefficientMap]
      exact hη
    have hp : GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) ∈
        (maximalIdeal (Y.presheaf.stalk (i (genericPoint C)))).comap
          (GaussCommonVerticalStalks.generizationMap h) := by
      change GaussCommonVerticalStalks.generizationMap h
        (GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)) ∈
        maximalIdeal (Y.presheaf.stalk (i (genericPoint C)))
      exact (congrArg (fun a : Y.presheaf.stalk (i (genericPoint C)) =>
        a ∈ maximalIdeal (Y.presheaf.stalk (i (genericPoint C)))) hcomm).mpr hmem
    have hpπ : GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) ∈ Ideal.span {π} :=
      GaussCommonVerticalStalks.component_generizationPrime i x π hker ▸ hp
    exact Ideal.mem_span_singleton.mp hpπ

private theorem paperRadius_pos : 0 < ProjBerk.gaussRadius := by
  change (0 : ℝ) < Real.exp (-1)
  exact Real.exp_pos _

private theorem paperRadius_lt_one : ProjBerk.gaussRadius < 1 := by
  change Real.exp (-1) < (1 : ℝ)
  exact Real.exp_lt_one_iff.mpr (by norm_num)

private theorem genericValuation_congr (a b : SchemeValuedPoint Y)
    (ha : a.point = genericPoint Y) (hb : b.point = genericPoint Y) (h : a = b) :
    SchemeValuedPoint.genericValuation a ha = SchemeValuedPoint.genericValuation b hb := by
  cases h
  rfl

/-- ONE old original global vertex is the unchanged local vertical point at EVERY original point;
even the local original parameter conditions are internally derived. -/
theorem exists_commonVerticalPoint [IsDominant f]
    (x₀ : C) [IsNoetherianRing (Y.presheaf.stalk (i x₀))]
    (π₀ : Y.presheaf.stalk (i x₀)) (hπ₀ : Prime π₀)
    (hker₀ : RingHom.ker (i.stalkMap x₀).hom = Ideal.span {π₀})
    (hη : Polynomial.X ∈ (f (i (genericPoint C))).asIdeal) :
    ∃ (y : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) ProjBerk.gaussRadius) f)
      (hy : y.1.point = genericPoint Y),
      RelativeSchemeValuedPoint.center ProjBerk.gaussModelCoefficient_le_one y = i (genericPoint C) ∧
      ∀ (x : C) [IsNoetherianRing (Y.presheaf.stalk (i x))]
        (π : Y.presheaf.stalk (i x)) (hπ : Prime π)
        (_hker : RingHom.ker (i.stalkMap x).hom = Ideal.span {π}),
        ∃ (ht : GaussRegularSurfaceConvexProfiles.stalkParameter f (i x) ≠ 0)
          (hπt : π ∣ GaussRegularSurfaceConvexProfiles.stalkParameter f (i x)),
          let q := GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f (i x)
            π hπ ht hπt ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one
          q = y ∧ ∀ a : Y.functionField,
            SchemeValuedPoint.genericValuation q.1
              (GaussRegularSurfaceConvexProfiles.nativeVerticalPoint_underlying f (i x)
                π hπ ht hπt ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one) a =
              SchemeValuedPoint.genericValuation y.1 hy a := by
  let η := i (genericPoint C)
  let : IsDiscreteValuationRing (Y.presheaf.stalk η) :=
    GaussCommonVerticalStalks.componentStalk_isDVR i x₀ π₀ hπ₀ hker₀
  obtain ⟨y,hycenter⟩ := RelativeSchemeValuedPoint.exists_gaussPoint_center_of_vertical f η hη
  have hygen := genericSupport_of_verticalDVRCenter η hη ProjBerk.gaussRadius
    paperRadius_pos paperRadius_lt_one y hycenter
  refine ⟨y,hygen,hycenter,?_⟩
  intro x hNoeth π hπ hker
  let : IsNoetherianRing (Y.presheaf.stalk (i x)) := hNoeth
  obtain ⟨ht,hπt⟩ := actualParameter_facts i x π hker hη
  refine ⟨ht,hπt,?_⟩
  let q := GaussRegularSurfaceConvexProfiles.nativeVerticalPoint f (i x)
    π hπ ht hπt ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one
  have hqc := center_nativeVerticalPoint i x π hπ hker ht hπt
    ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one
  have heq : q = y := eq_of_same_verticalDVRCenter η hη ProjBerk.gaussRadius
    paperRadius_pos paperRadius_lt_one q y hqc hycenter
  refine ⟨heq,?_⟩
  intro a
  have hwhole : q.1 = y.1 := congrArg Subtype.val heq
  have hvals := genericValuation_congr q.1 y.1
    (GaussRegularSurfaceConvexProfiles.nativeVerticalPoint_underlying f (i x)
      π hπ ht hπt ProjBerk.gaussRadius paperRadius_pos paperRadius_lt_one) hygen hwhole
  exact congrArg (fun v : Valuation Y.functionField ℝ≥0 => v a) hvals

end EnvelopeProperty.GaussCommonVerticalPoints
