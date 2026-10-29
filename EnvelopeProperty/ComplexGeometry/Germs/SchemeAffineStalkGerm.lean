import EnvelopeProperty.ComplexGeometry.Germs.SchemeAffineNativeEvaluation
import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateGlobalGerm

/-!
# The SAME original stalk map on arbitrary actual affine regular functions

Actual open-immersion stalk naturality and the SAME native principal-refinement
fraction identity compare the already manufactured original stalk map with
literal arbitrary-affine evaluation. No new stalk compatibility is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter Set
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open scoped Topology Manifold

private def actualAffineRegularStalk {X : Scheme} {A : CommRingCat}
    (c : Spec A ⟶ X) [IsOpenImmersion c] (y : Spec A) (x : X) (hxy : c y = x) :
    A ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ y trivial ≫
    inv (c.stalkMap y) ≫ (X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom

private theorem actualAffineRegularStalk_naturality {X : Scheme} {A B : CommRingCat}
    (c : Spec A ⟶ X) [IsOpenImmersion c] (d : Spec B ⟶ X) [IsOpenImmersion d]
    (u : Spec B ⟶ Spec A) [IsOpenImmersion u] (hu : u ≫ c = d)
    (z : Spec B) (x : X) (hcx : c (u z) = x) (hdx : d z = x) :
    actualAffineRegularStalk c (u z) x hcx =
      Spec.preimage u ≫ actualAffineRegularStalk d z x hdx := by
  subst d
  subst x
  have hnat : (Scheme.ΓSpecIso A).inv ≫
      (Spec A).presheaf.germ ⊤ (u z) trivial ≫ u.stalkMap z =
        Spec.preimage u ≫ (Scheme.ΓSpecIso B).inv ≫
          (Spec B).presheaf.germ ⊤ z trivial := by
    rw [Scheme.Hom.germ_stalkMap]
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Spec.map_preimage]
    rfl
  have hnat' : (Scheme.ΓSpecIso A).inv ≫
      (Spec A).presheaf.germ ⊤ (u z) trivial =
        Spec.preimage u ≫ (Scheme.ΓSpecIso B).inv ≫
          (Spec B).presheaf.germ ⊤ z trivial ≫ inv (u.stalkMap z) := by
    have h := congrArg (fun k : A ⟶ (Spec B).presheaf.stalk z =>
      k ≫ inv (u.stalkMap z)) hnat
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using h
  simp only [actualAffineRegularStalk, TopCat.Presheaf.stalkCongr_hom,
    Scheme.Hom.stalkMap_comp, IsIso.inv_comp,
    Category.assoc, TopCat.Presheaf.stalkSpecializes_refl, Category.comp_id]
  erw [Category.comp_id]
  simpa only [Category.assoc] using
    congrArg (fun k : A ⟶ (Spec A).presheaf.stalk (u z) =>
      k ≫ inv (c.stalkMap (u z))) hnat'

private theorem actualAffineRegularStalk_point {X : Scheme} {A : CommRingCat}
    (c : Spec A ⟶ X) [IsOpenImmersion c] (y y' : Spec A) (e : y = y')
    (x : X) (h : c y = x) (h' : c y' = x) :
    actualAffineRegularStalk c y x h = actualAffineRegularStalk c y' x h' := by
  subst y'
  rfl

private theorem actualAffineRegularStalk_spec {X : Scheme} {A : CommRingCat}
    (c : Spec A ⟶ X) [IsOpenImmersion c] (y : Spec A) (x : X) (hxy : c y = x) :
    actualAffineRegularStalk c y x hxy =
      CommRingCat.ofHom (algebraMap A (Localization.AtPrime y.asIdeal)) ≫
        (Spec.stalkIso A y).inv ≫ inv (c.stalkMap y) ≫
          (X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom := by
  rw [Spec.algebraMap_stalkIso_inv_assoc]
  rfl

/-- Restriction of an ACTUAL original open regular section to an ACTUAL affine
chart contained in that open, using the original structural presheaf. -/
def schemeAffineSectionCoefficient {X : Scheme} (c : ComplexAffineChart X)
    (U : X.Opens) (hc : Set.range c.map ⊆ U) : Γ(X, U) →+* c.ring :=
  ((c.map.appLE U ⊤ (fun y _ => hc ⟨y, rfl⟩)) ≫ (Scheme.ΓSpecIso c.ring).hom).hom

private theorem actualAffineRegularStalk_section {X : Scheme} {A : CommRingCat}
    (c : Spec A ⟶ X) [IsOpenImmersion c] (y : Spec A) (x : X) (hxy : c y = x)
    (U : X.Opens) (hc : Set.range c ⊆ U) (r : Γ(X, U)) :
    (actualAffineRegularStalk c y x hxy).hom
      ((Scheme.ΓSpecIso A).hom (c.appLE U ⊤ (fun y _ => hc ⟨y, rfl⟩) r)) =
        X.presheaf.germ U x (hxy ▸ hc ⟨y, rfl⟩) r := by
  have h : c.appLE U ⊤ (fun y _ => hc ⟨y, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫
      actualAffineRegularStalk c y x hxy = X.presheaf.germ U x (hxy ▸ hc ⟨y, rfl⟩) := by
    simp only [actualAffineRegularStalk, Iso.hom_inv_id_assoc]
    unfold Scheme.Hom.appLE
    rw [Category.assoc, TopCat.Presheaf.germ_res_assoc]
    rw [← c.germ_stalkMap_assoc, IsIso.hom_inv_id_assoc]
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
  exact congrArg (fun h : Γ(X, U) ⟶ X.presheaf.stalk x => h r) h

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- A regular function in an ACTUAL affine chart maps to its ORIGINAL scheme
stalk through the native affine germ and actual open-immersion stalk isomorphism. -/
def schemeAffineOriginalRegularStalk (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) :
    c.ring →+* X.presheaf.stalk (schemeComplexPointImage f (complexAffineChartPointMap f c z)) :=
  (actualAffineRegularStalk c.map (schemeComplexPointImage (c.map ≫ f) z)
    (schemeComplexPointImage f (complexAffineChartPointMap f c z))
      (schemeComplexPointImage_chart f c z).symm).hom

/-- The restricted coefficient has exactly the original open section's stalk. -/
theorem schemeAffineOriginalRegularStalk_section (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (U : X.Opens) (hc : Set.range c.map ⊆ U)
    (r : Γ(X, U)) :
    schemeAffineOriginalRegularStalk f c z (schemeAffineSectionCoefficient c U hc r) =
      X.presheaf.germ U (schemeComplexPointImage f (complexAffineChartPointMap f c z))
        ((schemeComplexPointImage_chart f c z).symm ▸
          hc ⟨schemeComplexPointImage (c.map ≫ f) z, rfl⟩) r :=
  actualAffineRegularStalk_section c.map _ _ (schemeComplexPointImage_chart f c z).symm U hc r

variable (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance affineStalkTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance affineStalkCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance affineStalkManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

local instance affineStalkComplexAlgebra (p : SchemeComplexPoint f) :
    Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

private theorem preferred_actualAffineRegularStalk (p : SchemeComplexPoint f)
    (a : SchemeCoordinateAffineRing f n p) :
    schemeNativeStalkGerm f n p
      ((actualAffineRegularStalk (standardSmoothComplexAffineChart f n p).val.map
        (schemeCoordinateAlgebraicPoint f n p) (schemeComplexPointImage f p)
        (schemeCoordinateAlgebraicPoint_map f n p)).hom a) =
      schemeNativeRegularGerm f n p a := by
  rw [actualAffineRegularStalk_spec]
  exact schemeNativeStalkGerm_regular f n p a

private def preferredAffinePoint (p : SchemeComplexPoint f) :
    ComplexAffineChartPoint f (standardSmoothComplexAffineChart f n p).val :=
  (affineSchemePointHomeomorphOfStructure
    ((standardSmoothComplexAffineChart f n p).val.map ≫ f)).symm
      (standardSmoothComplexAlgebraPoint f n p)

omit [IsSeparated f] [QuasiCompact f] in
private theorem preferredAffinePoint_map (p : SchemeComplexPoint f) :
    complexAffineChartPointMap f (standardSmoothComplexAffineChart f n p).val
      (preferredAffinePoint f n p) = p :=
  standardSmoothComplexAlgebraPoint_map f n p

omit [IsSeparated f] [QuasiCompact f] in
private theorem preferredAffinePoint_image (p : SchemeComplexPoint f) :
    schemeComplexPointImage ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
      (preferredAffinePoint f n p) = schemeCoordinateAlgebraicPoint f n p := by
  let d := (standardSmoothComplexAffineChart f n p).val
  let w := preferredAffinePoint f n p
  have he : Spec.preimage w.val =
      CommRingCat.ofHom (standardSmoothComplexAlgebraPoint f n p).toRingHom := by
    ext a
    exact (affineSchemePointEquivOfStructure_apply (d.map ≫ f) w a).symm.trans
      (congrArg (fun v => v a)
        ((affineSchemePointHomeomorphOfStructure (d.map ≫ f)).apply_symm_apply
          (standardSmoothComplexAlgebraPoint f n p)))
  have hv : w.val = Spec.map
      (CommRingCat.ofHom (standardSmoothComplexAlgebraPoint f n p).toRingHom) :=
    (Spec.map_preimage w.val).symm.trans (congrArg Spec.map he)
  exact (congrArg (fun h : Spec (.of ℂ) ⟶ Spec d.ring => h default) hv).trans
    (schemeCoordinateAlgebraicPoint_specMap f n p)

omit [IsSeparated f] [QuasiCompact f] in
private theorem preferredAffineEvaluation_source (p : SchemeComplexPoint f)
    (a : SchemeCoordinateAffineRing f n p) :
    schemeAffineRegularEvaluation f (standardSmoothComplexAffineChart f n p).val
      (preferredAffinePoint f n p) a =ᶠ[𝓝 p]
        (fun q => standardSmoothComplexPointOpenChart f n p q a) := by
  let d := (standardSmoothComplexAffineChart f n p).val
  let w := preferredAffinePoint f n p
  filter_upwards [(standardSmoothComplexPointOpenChart f n p).open_source.mem_nhds
    (standardSmoothComplexPointOpenChart_point_mem_source f n p)] with q hq
  have hqn : q ∈ (nativeComplexAffinePointOpenChart f d w).source := by
    rw [nativeComplexAffinePointOpenChart_source, complexAffineChartPointMap_range]
    rw [standardSmoothComplexPointOpenChart_source] at hq
    exact hq
  have he : affineSchemePointHomeomorphOfStructure (d.map ≫ f)
      (nativeComplexAffinePointOpenChart f d w q) =
        standardSmoothComplexPointOpenChart f n p q := by
    apply (complexAffineAlgebraPointMap_isOpenEmbedding f d).injective
    calc
      _ = q := by
        change complexAffineChartPointMap f d
          ((affineSchemePointHomeomorphOfStructure (d.map ≫ f)).symm
            (affineSchemePointHomeomorphOfStructure (d.map ≫ f)
              (nativeComplexAffinePointOpenChart f d w q))) = q
        rw [Homeomorph.symm_apply_apply]
        rw [← nativeComplexAffinePointOpenChart_symm f d w]
        exact (nativeComplexAffinePointOpenChart f d w).left_inv hqn
      _ = _ := by
        rw [← standardSmoothComplexPointOpenChart_symm f n p]
        exact ((standardSmoothComplexPointOpenChart f n p).left_inv hq).symm
  exact congrArg (fun v => v a) he

namespace SmoothSchemeGerms

private theorem actual_stalk_affine_evaluation (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (a : c.ring) :
    schemeNativeStalkGerm f n (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a) = affineRegularGerm f n c z a := by
  let p := complexAffineChartPointMap f c z
  let d := (standardSmoothComplexAffineChart f n p).val
  let w := preferredAffinePoint f n p
  have hwp : complexAffineChartPointMap f d w = p := preferredAffinePoint_map f n p
  obtain ⟨r, hr, q, hqy, hqc, hden⟩ :=
    exists_complexAffine_common_overlap_point f c d z w hwp
  obtain ⟨k, b, hab⟩ := complexAffine_overlap_ringMap_fraction c d r hr a
  let y := schemeComplexPointImage (complexPrincipalSchemeMap r ≫ (d.map ≫ f)) q
  let x := schemeComplexPointImage f p
  have hcq : complexAffine_overlap_lift c d r hr y =
      schemeComplexPointImage (c.map ≫ f) z := by
    exact (Scheme.Hom.comp_apply q.val (complexAffine_overlap_lift c d r hr) default).symm.trans
      (congrArg (schemeComplexPointImage (c.map ≫ f)) hqc)
  have hdq : complexPrincipalSchemeMap r y = schemeCoordinateAlgebraicPoint f n p := by
    exact ((Scheme.Hom.comp_apply q.val (complexPrincipalSchemeMap r) default).symm.trans
      (congrArg (schemeComplexPointImage (d.map ≫ f)) hqy)).trans
        (preferredAffinePoint_image f n p)
  have hyx : (complexPrincipalSchemeMap r ≫ d.map) y = x := by
    exact (Scheme.Hom.comp_apply (complexPrincipalSchemeMap r) d.map y).trans
      ((congrArg d.map hdq).trans (schemeCoordinateAlgebraicPoint_map f n p))
  let : IsOpenImmersion (complexAffine_overlap_lift c d r hr) := by
    unfold complexAffine_overlap_lift
    infer_instance
  let ρ := (actualAffineRegularStalk (complexPrincipalSchemeMap r ≫ d.map) y x hyx).hom
  have hca : schemeNativeStalkGerm f n p
      (ρ ((Spec.preimage (complexAffine_overlap_lift c d r hr)).hom a)) =
        schemeNativeStalkGerm f n p (schemeAffineOriginalRegularStalk f c z a) := by
    have hcx : c.map (complexAffine_overlap_lift c d r hr y) = x := by
      rw [hcq]
      exact (schemeComplexPointImage_chart f c z).symm
    have ht := actualAffineRegularStalk_naturality c.map (complexPrincipalSchemeMap r ≫ d.map)
      (complexAffine_overlap_lift c d r hr) (complexAffine_overlap_lift_fac c d r hr)
      y x hcx hyx
    have ht' := (actualAffineRegularStalk_point c.map _ _ hcq x hcx
      (schemeComplexPointImage_chart f c z).symm).symm.trans ht
    exact congrArg (schemeNativeStalkGerm f n p)
      (congrArg (fun h : c.ring ⟶ X.presheaf.stalk x => h a) ht').symm
  have hdb (v : d.ring) : schemeNativeStalkGerm f n p
      (ρ (algebraMap d.ring (Localization.Away r) v)) = schemeNativeRegularGerm f n p v := by
    have hdx : d.map (complexPrincipalSchemeMap r y) = x := by
      rw [hdq]
      exact schemeCoordinateAlgebraicPoint_map f n p
    have ht := actualAffineRegularStalk_naturality d.map (complexPrincipalSchemeMap r ≫ d.map)
      (complexPrincipalSchemeMap r) rfl y x hdx hyx
    have ht' := (actualAffineRegularStalk_point d.map _ _ hdq x hdx
      (schemeCoordinateAlgebraicPoint_map f n p)).symm.trans ht
    have hv := congrArg (fun h : d.ring ⟶ X.presheaf.stalk x => h v) ht'
    change _ = ρ ((Spec.preimage (complexPrincipalSchemeMap r)).hom v) at hv
    rw [complexPrincipalSchemeMap, Spec.preimage_map] at hv
    exact (congrArg (schemeNativeStalkGerm f n p) hv).symm.trans
      (preferred_actualAffineRegularStalk f n p v)
  have hα := congrArg ((schemeNativeStalkGerm f n p).comp ρ) hab
  simp only [RingHom.comp_apply, map_mul, map_pow] at hα
  rw [hca, hdb, hdb] at hα
  have hγ : affineRegularGerm f n c z a *
      schemeNativeRegularGerm f n p r ^ k = schemeNativeRegularGerm f n p b := by
    apply Subtype.ext
    change (affineRegularGerm f n c z a : Germ (𝓝 p) ℂ) *
      (schemeNativeRegularGerm f n p r : Germ (𝓝 p) ℂ) ^ k =
        (schemeNativeRegularGerm f n p b : Germ (𝓝 p) ℂ)
    rw [affineRegularGerm_source, schemeNativeRegularGerm_source,
      schemeNativeRegularGerm_source]
    change ((fun v => schemeAffineRegularEvaluation f c z a v *
      standardSmoothComplexPointOpenChart f n p v r ^ k) : Germ (𝓝 p) ℂ) =
        ((fun v => standardSmoothComplexPointOpenChart f n p v b) : Germ (𝓝 p) ℂ)
    apply Germ.coe_eq.mpr
    have hspc : p ∈ (nativeComplexAffinePointOpenChart f c z).source := by
      rw [nativeComplexAffinePointOpenChart_source]
      exact ⟨z, rfl⟩
    have hspd : p ∈ (nativeComplexAffinePointOpenChart f d w).source := by
      rw [nativeComplexAffinePointOpenChart_source]
      exact ⟨w, hwp⟩
    have hdenp : schemeAffineRegularEvaluation f d w r p ≠ 0 := by
      rw [← hwp, schemeAffineRegularEvaluation_point]
      exact hden
    have hcont : ContinuousAt (schemeAffineRegularEvaluation f d w r) p :=
      (affineRegularEvaluation_holomorphicAt_source f n d w r p ⟨w, hwp⟩).mdifferentiableAt.continuousAt
    have hdenev : ∀ᶠ v in 𝓝 p, schemeAffineRegularEvaluation f d w r v ≠ 0 :=
      hcont.eventually (isClosed_singleton.isOpen_compl.mem_nhds hdenp)
    filter_upwards [(nativeComplexAffinePointOpenChart f c z).open_source.mem_nhds hspc,
      (nativeComplexAffinePointOpenChart f d w).open_source.mem_nhds hspd, hdenev,
      preferredAffineEvaluation_source f n p r, preferredAffineEvaluation_source f n p b]
      with v hvc hvd hvr hpr hpb
    have hxy : complexAffineChartPointMap f d (nativeComplexAffinePointOpenChart f d w v) =
        complexAffineChartPointMap f c (nativeComplexAffinePointOpenChart f c z v) := by
      rw [← nativeComplexAffinePointOpenChart_symm f d w,
        ← nativeComplexAffinePointOpenChart_symm f c z]
      exact ((nativeComplexAffinePointOpenChart f d w).left_inv hvd).trans
        ((nativeComplexAffinePointOpenChart f c z).left_inv hvc).symm
    have hf := complexAffine_common_overlap_eval_fraction f c d r hr
      (nativeComplexAffinePointOpenChart f c z v) (nativeComplexAffinePointOpenChart f d w v)
      hxy hvr a k b hab
    rw [← hpr, ← hpb]
    exact (eq_div_iff (pow_ne_zero k hvr)).mp hf
  have hr0 : schemeNativeRegularGerm f n p r ≠ 0 := by
    intro hz
    have he := congrArg NativeHolGerm.eval hz
    rw [schemeNativeRegularGerm_eval, map_zero] at he
    apply hden
    simpa only [d, w, preferredAffinePoint, Homeomorph.apply_symm_apply] using he
  exact mul_right_cancel₀ (pow_ne_zero k hr0) (hα.trans hγ.symm)

/-- Actual arbitrary-affine regular functions read through the ALREADY produced
original stalk map. The SAME principal denominator identity drives both sides. -/
theorem affineRegularGerm_eq_stalk (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (a : c.ring) :
    schemeNativeStalkGerm f n (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a) = affineRegularGerm f n c z a := by
  exact actual_stalk_affine_evaluation f n c z a

/-- WHOLE original-function germ readback for the SAME original algebraic stalk. -/
theorem affineStalkGerm_source (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (a : c.ring) :
    ((schemeNativeStalkGerm f n (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a) :
        NativeHolGerm n (SchemeComplexPoint f) (complexAffineChartPointMap f c z)) :
          Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) =
      (schemeAffineRegularEvaluation f c z a : Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) := by
  rw [affineRegularGerm_eq_stalk]
  exact affineRegularGerm_source f n c z a

/-- The old original stalk map retains the literal actual affine-point value. -/
theorem affineStalkGerm_eval (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (a : c.ring) :
    NativeHolGerm.eval (schemeNativeStalkGerm f n (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a)) =
        affineSchemePointHomeomorphOfStructure (c.map ≫ f) z a := by
  rw [affineRegularGerm_eq_stalk]
  exact affineRegularGerm_eval f n c z a

omit [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f] in
private theorem actualAffineEvaluation_germ_default (c : ComplexAffineChart X)
    (z w : ComplexAffineChartPoint f c) (a : c.ring) :
    (schemeAffineRegularEvaluation f c z a : Germ (𝓝 (complexAffineChartPointMap f c w)) ℂ) =
      (schemeAffineRegularEvaluation f c w a : Germ (𝓝 (complexAffineChartPointMap f c w)) ℂ) := by
  apply Germ.coe_eq.mpr
  have hs : complexAffineChartPointMap f c w ∈ (nativeComplexAffinePointOpenChart f c z).source := by
    rw [nativeComplexAffinePointOpenChart_source]
    exact ⟨w, rfl⟩
  filter_upwards [(nativeComplexAffinePointOpenChart f c z).open_source.mem_nhds hs] with q hq
  have hqw : q ∈ (nativeComplexAffinePointOpenChart f c w).source := by
    rw [nativeComplexAffinePointOpenChart_source] at hq ⊢
    exact hq
  have hp : nativeComplexAffinePointOpenChart f c z q = nativeComplexAffinePointOpenChart f c w q := by
    apply complexAffineChartPointMap_injective f c
    calc
      _ = q := by
        rw [← nativeComplexAffinePointOpenChart_symm f c z]
        exact (nativeComplexAffinePointOpenChart f c z).left_inv hq
      _ = _ := by
        rw [← nativeComplexAffinePointOpenChart_symm f c w]
        exact ((nativeComplexAffinePointOpenChart f c w).left_inv hqw).symm
  exact congrArg (fun y => affineSchemePointHomeomorphOfStructure (c.map ≫ f) y a) hp

/-- One literal affine evaluation function reads the SAME original open-section
stalk at EVERY point of its actual affine source, independently of totalization. -/
theorem affineStalkGerm_section_source (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c)
    (U : X.Opens) (hc : Set.range c.map ⊆ U) (r : Γ(X, U))
    (q : SchemeComplexPoint f) (hq : q ∈ Set.range (complexAffineChartPointMap f c))
    (hqU : schemeComplexPointImage f q ∈ U) :
    ((schemeNativeStalkGerm f n q (X.presheaf.germ U (schemeComplexPointImage f q) hqU r) :
      NativeHolGerm n (SchemeComplexPoint f) q) : Germ (𝓝 q) ℂ) =
      (schemeAffineRegularEvaluation f c z (schemeAffineSectionCoefficient c U hc r) : Germ (𝓝 q) ℂ) := by
  obtain ⟨w, rfl⟩ := hq
  rw [← schemeAffineOriginalRegularStalk_section f c w U hc r]
  rw [affineRegularGerm_eq_stalk]
  exact (affineRegularGerm_source f n c w _).trans
    (actualAffineEvaluation_germ_default f c z w _).symm

/-- Every ACTUAL open regular section internally manufactures a holomorphic
local function with WHOLE original-stalk readback at every nearby point. -/
theorem regularSection_locally_holomorphic
    (U : X.Opens) (r : Γ(X, U)) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    ∃ V : Set (SchemeComplexPoint f), IsOpen V ∧ p ∈ V ∧
      V ⊆ schemeComplexPointImage f ⁻¹' U ∧ ∃ H : SchemeComplexPoint f → ℂ,
        MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) H V ∧
        ∀ q ∈ V, ∀ hqU : schemeComplexPointImage f q ∈ U,
          ((schemeNativeStalkGerm f n q (X.presheaf.germ U (schemeComplexPointImage f q) hqU r) :
            NativeHolGerm n (SchemeComplexPoint f) q) : Germ (𝓝 q) ℂ) = (H : Germ (𝓝 q) ℂ) := by
  obtain ⟨A, c, hc, hpC, hCU⟩ := Scheme.exists_affine_mem_range_and_range_subset hp
  let C : ComplexAffineChart X := ⟨A, c, hc⟩
  have hp' : p ∈ Set.range (complexAffineChartPointMap f C) := by
    rw [complexAffineChartPointMap_range]
    exact hpC
  obtain ⟨z, hzp⟩ := hp'
  let V := Set.range (complexAffineChartPointMap f C)
  let H := schemeAffineRegularEvaluation f C z (schemeAffineSectionCoefficient C U hCU r)
  refine ⟨V, complexAffineChartPointMap_isOpen_range f C, ⟨z, hzp⟩, ?_, H, ?_, ?_⟩
  · intro q hq
    change q ∈ Set.range (complexAffineChartPointMap f C) at hq
    rw [complexAffineChartPointMap_range] at hq
    exact hCU hq
  · intro q hq
    exact (affineRegularEvaluation_holomorphicAt_source f n C z _ q hq).mdifferentiableAt.mdifferentiableWithinAt
  · intro q hq hqU
    exact affineStalkGerm_section_source f n C z U hCU r q hq hqU

end SmoothSchemeGerms

omit [IsSeparated f] [QuasiCompact f] in
/-- Actual arbitrary-affine regular functions read through the ALREADY produced
original stalk map. The SAME principal denominator identity drives both sides. -/
theorem schemeAffineNativeRegularGerm_eq_stalk (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (E : ClosedProjectiveEmbedding f) (a : c.ring) :
    let := E.isSeparated
    let := E.quasiCompact
    schemeNativeStalkGerm f n (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a) = schemeAffineNativeRegularGerm f n c z E a := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.affineRegularGerm_eq_stalk f n c z a

omit [IsSeparated f] [QuasiCompact f] in
/-- WHOLE original-function germ readback for the SAME original algebraic stalk. -/
theorem schemeAffineNativeStalkGerm_source (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (E : ClosedProjectiveEmbedding f) (a : c.ring) :
    let := E.isSeparated
    let := E.quasiCompact
    ((schemeNativeStalkGerm f n (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a) :
        NativeHolGerm n (SchemeComplexPoint f) (complexAffineChartPointMap f c z)) :
          Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) =
      (schemeAffineRegularEvaluation f c z a : Germ (𝓝 (complexAffineChartPointMap f c z)) ℂ) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.affineStalkGerm_source f n c z a

omit [IsSeparated f] [QuasiCompact f] in
/-- The old original stalk map retains the literal actual affine-point value. -/
theorem schemeAffineNativeStalkGerm_eval (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (E : ClosedProjectiveEmbedding f) (a : c.ring) :
    let := E.isSeparated
    let := E.quasiCompact
    NativeHolGerm.eval (schemeNativeStalkGerm f n (complexAffineChartPointMap f c z)
      (schemeAffineOriginalRegularStalk f c z a)) =
        affineSchemePointHomeomorphOfStructure (c.map ≫ f) z a := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.affineStalkGerm_eval f n c z a

omit [IsSeparated f] [QuasiCompact f] in
/-- One literal affine evaluation function reads the SAME original open-section
stalk at EVERY point of its actual affine source, independently of totalization. -/
theorem schemeAffineNativeStalkGerm_section_source (c : ComplexAffineChart X)
    (z : ComplexAffineChartPoint f c) (E : ClosedProjectiveEmbedding f)
    (U : X.Opens) (hc : Set.range c.map ⊆ U) (r : Γ(X, U))
    (q : SchemeComplexPoint f) (hq : q ∈ Set.range (complexAffineChartPointMap f c))
    (hqU : schemeComplexPointImage f q ∈ U) :
    let := E.isSeparated
    let := E.quasiCompact
    ((schemeNativeStalkGerm f n q (X.presheaf.germ U (schemeComplexPointImage f q) hqU r) :
      NativeHolGerm n (SchemeComplexPoint f) q) : Germ (𝓝 q) ℂ) =
      (schemeAffineRegularEvaluation f c z (schemeAffineSectionCoefficient c U hc r) : Germ (𝓝 q) ℂ) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.affineStalkGerm_section_source f n c z U hc r q hq hqU

omit [IsSeparated f] [QuasiCompact f] in
/-- Every ACTUAL open regular section internally manufactures a holomorphic
local function with WHOLE original-stalk readback at every nearby point. -/
theorem schemeRegularSection_locally_holomorphic (E : ClosedProjectiveEmbedding f)
    (U : X.Opens) (r : Γ(X, U)) (p : SchemeComplexPoint f)
    (hp : schemeComplexPointImage f p ∈ U) :
    let := E.isSeparated
    let := E.quasiCompact
    ∃ V : Set (SchemeComplexPoint f), IsOpen V ∧ p ∈ V ∧
      V ⊆ schemeComplexPointImage f ⁻¹' U ∧ ∃ H : SchemeComplexPoint f → ℂ,
        MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) H V ∧
        ∀ q ∈ V, ∀ hqU : schemeComplexPointImage f q ∈ U,
          ((schemeNativeStalkGerm f n q (X.presheaf.germ U (schemeComplexPointImage f q) hqU r) :
            NativeHolGerm n (SchemeComplexPoint f) q) : Germ (𝓝 q) ℂ) = (H : Germ (𝓝 q) ℂ) := by
  let := E.isSeparated
  let := E.quasiCompact
  exact SmoothSchemeGerms.regularSection_locally_holomorphic f n U r p hp

end HolomorphicGerms
