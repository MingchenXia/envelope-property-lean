import EnvelopeProperty.ComplexGeometry.Germs.SchemeAnalyticMorphism

/-!
# Actual native inverse maps of original open immersions

Local actual affine factorizations derive native holomorphy. The application
uses the genuine universal property of the SAME original open immersion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry Algebra ComplexSchemes Filter Manifold
open ComplexGeometry.Pluripotential
open scoped Topology Manifold ContDiff

variable {X Y : Scheme} (f : X ⟶ Spec (.of ℂ)) (g : Y ⟶ Spec (.of ℂ))
  (n m : ℕ) [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m g]

local instance inverseSourceTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance inverseTargetTopology : TopologicalSpace (SchemeComplexPoint g) :=
  schemeAnalyticPointTopology g
local instance inverseSourceCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n
local instance inverseTargetCharts : ChartedSpace (ComplexModel m) (SchemeComplexPoint g) :=
  schemeAnalyticComplexChartedSpace g m

/-- A literal local affine scheme factorization proves native holomorphy at its actual point. -/
theorem schemeNativeLocallyAffine_contMDiffAt (F : SchemeComplexPoint f → SchemeComplexPoint g)
    (x : SchemeComplexPoint f) (c : ComplexAffineChart X)
    (hx : x ∈ Set.range (complexAffineChartPointMap f c))
    (l : Spec c.ring ⟶ Spec (standardSmoothComplexAffineChart g m (F x)).val.ring)
    (hl : l ≫ (standardSmoothComplexAffineChart g m (F x)).val.map ≫ g = c.map ≫ f)
    (hF : ∀ z, F (complexAffineChartPointMap f c z) =
      complexAffineChartPointMap g (standardSmoothComplexAffineChart g m (F x)).val
        (schemeComplexPointMap (c.map ≫ f)
          ((standardSmoothComplexAffineChart g m (F x)).val.map ≫ g) l hl z))
    (k : WithTop ℕ∞) :
    ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) k F x := by
  let d := (standardSmoothComplexAffineChart g m (F x)).val
  let L := schemeComplexPointMap (c.map ≫ f) (d.map ≫ g) l hl
  obtain ⟨z, hz⟩ := hx
  have hcont : ContinuousAt F x := by
    rw [← hz]
    apply (complexAffineChartPointMap_isOpenEmbedding f c).continuousAt_iff.mp
    have he : F ∘ complexAffineChartPointMap f c = complexAffineChartPointMap g d ∘ L := by
      funext w
      exact hF w
    rw [he]
    exact ((complexAffineChartPointMap_continuous g d).comp
      (affineSchemePointMap_over_continuous (c.map ≫ f) (d.map ≫ g) l hl)).continuousAt
  let t := schemeAnalyticCoordinateChart f n x x
  have hxS := schemeAnalyticCoordinateChart_point_mem_source f n x
  have ht : t ∈ (schemeAnalyticCoordinateChart f n x).target :=
    (schemeAnalyticCoordinateChart f n x).map_source hxS
  have hz' : complexAffineChartPointMap f c z = (schemeAnalyticCoordinateChart f n x).symm t := by
    rw [(schemeAnalyticCoordinateChart f n x).left_inv hxS]
    exact hz
  have hnear : ∀ᶠ u in 𝓝 t,
      F ((schemeAnalyticCoordinateChart f n x).symm u) ∈
        (schemeAnalyticCoordinateChart g m (F x)).source := by
    have hcont' : ContinuousAt F ((schemeAnalyticCoordinateChart f n x).symm t) := by
      simpa only [t, (schemeAnalyticCoordinateChart f n x).left_inv hxS] using hcont
    have hcx := hcont'.comp ((schemeAnalyticCoordinateChart f n x).continuousAt_symm ht)
    have hmem : (F ∘ (schemeAnalyticCoordinateChart f n x).symm) t ∈
        (schemeAnalyticCoordinateChart g m (F x)).source := by
      simpa only [Function.comp_apply, t, (schemeAnalyticCoordinateChart f n x).left_inv hxS]
        using schemeAnalyticCoordinateChart_point_mem_source g m (F x)
    exact hcx.eventually ((schemeAnalyticCoordinateChart g m (F x)).open_source.mem_nhds
      hmem)
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ g)
  have hcoord : AnalyticAt ℂ (fun u => schemeAnalyticCoordinateChart g m (F x)
      (F ((schemeAnalyticCoordinateChart f n x).symm u))) t := by
    apply AnalyticAt.pi
    intro j
    let a : d.ring := standardSmoothComplexChartFreeGenerator g m (F x) j
    have ha := nativeSchemeCoordinateAffineLift_eval_analyticAt f n x c z t ht hz'
      ((Spec.preimage l).hom a)
    apply ha.congr
    filter_upwards [hnear, nativeSchemeCoordinateAffineLift_eventually_map f n x c z t ht hz']
      with u hu hsource
    have himage : L (nativeSchemeCoordinateAffineLift f n x c z u) =
        schemeAnalyticCoordinateAffineSourcePoint g m (F x)
          (F ((schemeAnalyticCoordinateChart f n x).symm u)) := by
      apply complexAffineChartPointMap_injective g d
      exact (hF _).symm.trans ((congrArg F hsource).trans
        (schemeAnalyticCoordinateAffineSourcePoint_map g m (F x) _ hu).symm)
    have hev := congrArg (fun q => q a) (affineSchemeOverAlgebraMap_naturality
      (d.map ≫ g) (c.map ≫ f) l hl (nativeSchemeCoordinateAffineLift f n x c z u))
    change affineSchemePointHomeomorphOfStructure (d.map ≫ g)
      (L (nativeSchemeCoordinateAffineLift f n x c z u)) a =
      affineSchemePointHomeomorphOfStructure (c.map ≫ f)
        (nativeSchemeCoordinateAffineLift f n x c z u) ((Spec.preimage l).hom a) at hev
    change affineSchemePointHomeomorphOfStructure (c.map ≫ f)
      (nativeSchemeCoordinateAffineLift f n x c z u) ((Spec.preimage l).hom a) = _
    rw [← hev, himage]
    simpa [d, L, a, schemeAnalyticCoordinateAffineSourcePoint] using
      (schemeAnalyticCoordinateChart_apply g m (F x) _ hu j).symm
  have hL : AnalyticAt ℂ (schemeCoordinateModelEquiv n)
      (schemeAnalyticComplexChart f n x x) :=
    (schemeCoordinateModelEquiv n).toContinuousLinearMap.analyticAt _
  have ht' : schemeCoordinateModelEquiv n (schemeAnalyticComplexChart f n x x) = t := by
    change schemeCoordinateModelEquiv n ((schemeCoordinateModelEquiv n).symm t) = t
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hcoord' := hcoord
  rw [← ht'] at hcoord'
  have hComp := hcoord'.comp hL
  have hInv : AnalyticAt ℂ (schemeCoordinateModelEquiv m).symm
      (schemeAnalyticCoordinateChart g m (F x)
        (F ((schemeAnalyticCoordinateChart f n x).symm
          (schemeCoordinateModelEquiv n (schemeAnalyticComplexChart f n x x))))) :=
    (schemeCoordinateModelEquiv m).symm.toContinuousLinearMap.analyticAt _
  have hTot := AnalyticAt.comp
    (f := fun u : ComplexModel n => schemeAnalyticCoordinateChart g m (F x)
      (F ((schemeAnalyticCoordinateChart f n x).symm (schemeCoordinateModelEquiv n u))))
    (g := ((schemeCoordinateModelEquiv m).symm : (Fin m → ℂ) → ComplexModel m))
    (x := schemeAnalyticComplexChart f n x x) hInv hComp
  rw [contMDiffAt_iff]
  refine ⟨hcont, ?_⟩
  simp only [mfld_simps]
  change ContDiffAt ℂ k (fun u => schemeAnalyticComplexChart g m (F x)
    (F ((schemeAnalyticComplexChart f n x).symm u))) (schemeAnalyticComplexChart f n x x)
  simpa only [schemeAnalyticComplexChart, mfld_simps, Function.comp_def,
    ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.coe_symm_toHomeomorph,
    ContinuousLinearEquiv.symm_symm] using
    hTot.contDiffAt

section OriginalInverse

variable {U : Scheme} (r : U ⟶ X) [IsOpenImmersion r] (h : U ⟶ Y)
  (heq : h ≫ g = r ≫ f) (p₀ : SchemeComplexPoint g)

/-- The totalized inverse-locus map is manufactured from the original open immersion lift.
Its value off the original open image is an actual source point. -/
def schemeNativeOpenInverseMap (x : SchemeComplexPoint f) : SchemeComplexPoint g := by
  classical
  exact if hx : schemeComplexPointImage f x ∈ Set.range r then
    schemeComplexPointMap (r ≫ f) g h heq (schemeComplexPointLift f r x hx)
  else p₀

/-- On the original open image the inverse is literally the original lift followed by the original morphism. -/
theorem schemeNativeOpenInverseMap_val (x : SchemeComplexPoint f)
    (hx : schemeComplexPointImage f x ∈ Set.range r) :
    (schemeNativeOpenInverseMap f g r h heq p₀ x).val =
      (schemeComplexPointLift f r x hx).val ≫ h := by
  simp only [schemeNativeOpenInverseMap, dif_pos hx]
  rfl

/-- The actual original inverse-locus map has an actual affine local scheme factorization. -/
theorem exists_schemeNativeOpenInverse_affine (x : SchemeComplexPoint f)
    (hx : schemeComplexPointImage f x ∈ Set.range r) :
    ∃ c : ComplexAffineChart X,
      x ∈ Set.range (complexAffineChartPointMap f c) ∧
      ∃ (l : Spec c.ring ⟶ Spec
          (standardSmoothComplexAffineChart g m (schemeNativeOpenInverseMap f g r h heq p₀ x)).val.ring)
        (hl : l ≫ (standardSmoothComplexAffineChart g m
            (schemeNativeOpenInverseMap f g r h heq p₀ x)).val.map ≫ g = c.map ≫ f),
        ∀ z, schemeNativeOpenInverseMap f g r h heq p₀ (complexAffineChartPointMap f c z) =
          complexAffineChartPointMap g
            (standardSmoothComplexAffineChart g m
              (schemeNativeOpenInverseMap f g r h heq p₀ x)).val
            (schemeComplexPointMap (c.map ≫ f)
              ((standardSmoothComplexAffineChart g m
                (schemeNativeOpenInverseMap f g r h heq p₀ x)).val.map ≫ g) l
                hl z) := by
  let F := schemeNativeOpenInverseMap f g r h heq p₀
  let d := (standardSmoothComplexAffineChart g m (F x)).val
  let u : SchemeComplexPoint (h ≫ g) :=
    ⟨(schemeComplexPointLift f r x hx).val, by rw [heq]; exact (schemeComplexPointLift f r x hx).property⟩
  have hgeo : h (schemeComplexPointImage (h ≫ g) u) ∈ Set.range d.map := by
    have hv := schemeNativeOpenInverseMap_val f g r h heq p₀ x hx
    have hi := congrArg (fun q : Spec (.of ℂ) ⟶ Y => q default) hv
    rw [Scheme.Hom.comp_apply] at hi
    exact hi ▸ (standardSmoothComplexAffineChart g m (F x)).property.1
  obtain ⟨cU, huc, l, hl⟩ := exists_schemeMorphism_affine_source g h d u hgeo
  let c : ComplexAffineChart X := ⟨cU.ring, cU.map ≫ r, inferInstance⟩
  have hxc : x ∈ Set.range (complexAffineChartPointMap f c) := by
    rw [complexAffineChartPointMap_range]
    obtain ⟨z, hz⟩ := huc
    refine ⟨z, ?_⟩
    change (cU.map ≫ r) z = schemeComplexPointImage f x
    rw [Scheme.Hom.comp_apply, hz]
    exact congrArg (fun q : Spec (.of ℂ) ⟶ X => q default)
      (schemeComplexPointLift_fac f r x hx)
  have hls : l ≫ d.map ≫ g = c.map ≫ f := by
    rw [← Category.assoc, hl, Category.assoc, heq]
    rfl
  refine ⟨c, hxc, l, hls, ?_⟩
  intro z
  have hz : schemeComplexPointImage f (complexAffineChartPointMap f c z) ∈ Set.range r := by
    refine ⟨(z.val ≫ cU.map) default, ?_⟩
    change r ((z.val ≫ cU.map) default) = (z.val ≫ (cU.map ≫ r)) default
    simp only [Scheme.Hom.comp_apply]
  apply Subtype.ext
  rw [schemeNativeOpenInverseMap_val f g r h heq p₀ _ hz]
  have hlift : (schemeComplexPointLift f r (complexAffineChartPointMap f c z) hz).val =
      z.val ≫ cU.map := by
    apply (cancel_mono r).mp
    rw [schemeComplexPointLift_fac, Category.assoc]
    rfl
  rw [hlift]
  change (z.val ≫ cU.map) ≫ h = (z.val ≫ l) ≫ d.map
  exact (Category.assoc z.val cU.map h).trans
    ((congrArg (fun a : Spec cU.ring ⟶ Y => z.val ≫ a) hl.symm).trans
      (Category.assoc z.val l d.map).symm)

/-- The original inverse-locus map is holomorphic in the SAME actual source and target atlases. -/
theorem schemeNativeOpenInverseMap_contMDiffOn (k : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) k
      (schemeNativeOpenInverseMap f g r h heq p₀)
      {x | schemeComplexPointImage f x ∈ Set.range r} := by
  intro x hx
  obtain ⟨c, hxc, l, hl, hF⟩ := exists_schemeNativeOpenInverse_affine f g m r h heq p₀ x hx
  exact (schemeNativeLocallyAffine_contMDiffAt f g n m
    (schemeNativeOpenInverseMap f g r h heq p₀) x c hxc l hl hF k).contMDiffWithinAt

/-- The actual original section identity gives the literal inverse identity over the original open locus. -/
theorem schemeNativeOpenInverseMap_right_inv (π : Y ⟶ X) (hπ : π ≫ f = g)
    (hsec : h ≫ π = r) (x : SchemeComplexPoint f)
    (hx : schemeComplexPointImage f x ∈ Set.range r) :
    schemeComplexPointMap g f π hπ (schemeNativeOpenInverseMap f g r h heq p₀ x) = x := by
  apply Subtype.ext
  change (schemeNativeOpenInverseMap f g r h heq p₀ x).val ≫ π = x.val
  rw [schemeNativeOpenInverseMap_val f g r h heq p₀ x hx]
  exact (Category.assoc (schemeComplexPointLift f r x hx).val h π).trans
    ((congrArg (fun a : U ⟶ X => (schemeComplexPointLift f r x hx).val ≫ a) hsec).trans
      (schemeComplexPointLift_fac f r x hx))

/-- The SAME original open source embedding gives the second literal inverse identity. -/
theorem schemeNativeOpenInverseMap_left_inv [IsOpenImmersion h]
    (π : Y ⟶ X) (hπ : π ≫ f = g) (hsec : h ≫ π = r)
    (y : SchemeComplexPoint g) (hy : schemeComplexPointImage g y ∈ Set.range h) :
    schemeNativeOpenInverseMap f g r h heq p₀ (schemeComplexPointMap g f π hπ y) = y := by
  let u := schemeComplexPointLift g h y hy
  have hcomp : u.val ≫ r = y.val ≫ π := by
    exact (congrArg (fun a : U ⟶ X => u.val ≫ a) hsec.symm).trans
      ((Category.assoc u.val h π).symm.trans
        (congrArg (fun a : Spec (.of ℂ) ⟶ Y => a ≫ π) (schemeComplexPointLift_fac g h y hy)))
  have hx : schemeComplexPointImage f (schemeComplexPointMap g f π hπ y) ∈ Set.range r := by
    refine ⟨u.val default, ?_⟩
    simpa only [schemeComplexPointMap, schemeComplexPointImage, Scheme.Hom.comp_apply]
      using congrArg (fun a : Spec (.of ℂ) ⟶ X => a default) hcomp
  have hlift : (schemeComplexPointLift f r (schemeComplexPointMap g f π hπ y) hx).val = u.val := by
    apply (cancel_mono r).mp
    exact (schemeComplexPointLift_fac f r (schemeComplexPointMap g f π hπ y) hx).trans hcomp.symm
  apply Subtype.ext
  rw [schemeNativeOpenInverseMap_val f g r h heq p₀ _ hx, hlift]
  exact schemeComplexPointLift_fac g h y hy

end OriginalInverse

end HolomorphicGerms
