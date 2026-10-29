import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticAtlas

/-! # Genuine algebra maps on affine analytic overlaps

The map between two affine charts is the native open-immersion lift on an
actual principal refinement. Its complex algebra compatibility follows from
the structural morphism. Its values are genuine localization fractions, and
the denominator is nonzero at every actual point of that refinement.
-/

open CategoryTheory AlgebraicGeometry
open scoped Topology

namespace ComplexSchemes

noncomputable section

/-- An actual affine morphism over the specified complex structural maps gives
its literal contravariant complex algebra homomorphism. -/
def affineSchemeOverAlgebraMap {A B : CommRingCat}
    (f : Spec B ⟶ Spec (.of ℂ)) (g : Spec A ⟶ Spec (.of ℂ))
    (h : Spec A ⟶ Spec B) (hh : h ≫ f = g) :
    let := affinePointFieldAlgebra f
    let := affinePointFieldAlgebra g
    B →ₐ[ℂ] A := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra g
  exact
    { (Spec.preimage h).hom with
      commutes' c := by
        change (Spec.preimage h).hom ((Spec.preimage f).hom c) =
          (Spec.preimage g).hom c
        rw [← hh, Spec.preimage_comp]
        rfl }

/-- The algebra map recovers exactly the original scheme morphism. -/
theorem affineSchemeOverAlgebraMap_spec {A B : CommRingCat}
    (f : Spec B ⟶ Spec (.of ℂ)) (g : Spec A ⟶ Spec (.of ℂ))
    (h : Spec A ⟶ Spec B) (hh : h ≫ f = g) :
    let := affinePointFieldAlgebra f
    let := affinePointFieldAlgebra g
    Spec.map (CommRingCat.ofHom (affineSchemeOverAlgebraMap f g h hh).toRingHom) = h := by
  exact Spec.map_preimage h

/-- Under the inherited affine point homeomorphisms, the genuine scheme-point
map is literal algebra-homomorphism pullback. -/
theorem affineSchemeOverAlgebraMap_naturality {A B : CommRingCat}
    (f : Spec B ⟶ Spec (.of ℂ)) (g : Spec A ⟶ Spec (.of ℂ))
    (h : Spec A ⟶ Spec B) (hh : h ≫ f = g) (p : SchemeComplexPoint g) :
    let := affinePointFieldAlgebra f
    let := affinePointFieldAlgebra g
    affineSchemePointHomeomorphOfStructure f (schemeComplexPointMap g f h hh p) =
      (affineSchemePointHomeomorphOfStructure g p).comp
        (affineSchemeOverAlgebraMap f g h hh) := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra g
  apply AlgHom.ext
  intro a
  change affineSchemePointEquivOfStructure f (schemeComplexPointMap g f h hh p) a =
    (affineSchemePointEquivOfStructure g p).comp (affineSchemeOverAlgebraMap f g h hh) a
  rw [affineSchemePointEquivOfStructure_apply, AlgHom.comp_apply,
    affineSchemePointEquivOfStructure_apply]
  change (Spec.preimage (p.val ≫ h)).hom a =
    (Spec.preimage p.val).hom ((Spec.preimage h).hom a)
  rw [Spec.preimage_comp]
  rfl

/-- The overlap lift gives a genuine complex algebra map with the inherited
complex structures of both charts. -/
def complexAffine_overlap_algebraMap {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) :
    let := affinePointFieldAlgebra (c.map ≫ f)
    let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
    c.ring →ₐ[ℂ] Localization.Away r :=
  affineSchemeOverAlgebraMap (c.map ≫ f) (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
    (complexAffine_overlap_lift c d r hr)
    ((complexAffine_overlap_lift_over f c d r hr).trans (Category.assoc _ _ _))

/-- The overlap algebra map is the actual contravariant ring map. -/
theorem complexAffine_overlap_algebraMap_apply {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) (a : c.ring) :
    let := affinePointFieldAlgebra (c.map ≫ f)
    let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
    complexAffine_overlap_algebraMap f c d r hr a =
      (Spec.preimage (complexAffine_overlap_lift c d r hr)).hom a := rfl

/-- Actual overlap points are sent to algebra pullbacks under the inherited
point homeomorphisms. -/
theorem complexAffine_overlap_algebraMap_naturality {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map)
    (p : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (d.map ≫ f))) :
    let := affinePointFieldAlgebra (c.map ≫ f)
    let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
    affineSchemePointHomeomorphOfStructure (c.map ≫ f)
        (complexAffine_overlap_pointMap f c d r hr p) =
      (affineSchemePointHomeomorphOfStructure (complexPrincipalSchemeMap r ≫ (d.map ≫ f)) p).comp
        (complexAffine_overlap_algebraMap f c d r hr) :=
  affineSchemeOverAlgebraMap_naturality _ _ _ _ p

/-- Evaluation on the target chart is actual evaluation of its overlap image. -/
theorem complexAffine_overlap_algebraMap_eval {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map)
    (p : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (d.map ≫ f))) (a : c.ring) :
    let := affinePointFieldAlgebra (c.map ≫ f)
    let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
    affineSchemePointHomeomorphOfStructure (c.map ≫ f)
        (complexAffine_overlap_pointMap f c d r hr p) a =
      affineSchemePointHomeomorphOfStructure (complexPrincipalSchemeMap r ≫ (d.map ≫ f)) p
        (complexAffine_overlap_algebraMap f c d r hr a) := by
  exact congrArg (fun q => q a) (complexAffine_overlap_algebraMap_naturality f c d r hr p)

/-- Restricting a localization point evaluates original elements by their
actual native localization images. -/
theorem complexPrincipalSchemePointMap_eval {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (r : A)
    (p : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ f)) (a : A) :
    let := affinePointFieldAlgebra f
    let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)
    affineSchemePointHomeomorphOfStructure f
        (schemeComplexPointMap (complexPrincipalSchemeMap r ≫ f) f
          (complexPrincipalSchemeMap r) rfl p) a =
      affineSchemePointHomeomorphOfStructure (complexPrincipalSchemeMap r ≫ f) p
        (algebraMap A (Localization.Away r) a) := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)
  change affineSchemePointEquivOfStructure f
      (schemeComplexPointMap (complexPrincipalSchemeMap r ≫ f) f
        (complexPrincipalSchemeMap r) rfl p) a =
    affineSchemePointEquivOfStructure (complexPrincipalSchemeMap r ≫ f) p
      (algebraMap A (Localization.Away r) a)
  rw [affineSchemePointEquivOfStructure_apply, affineSchemePointEquivOfStructure_apply]
  change (Spec.preimage (p.val ≫ complexPrincipalSchemeMap r)).hom a =
    (Spec.preimage p.val).hom (algebraMap A (Localization.Away r) a)
  rw [Spec.preimage_comp]
  change (Spec.preimage p.val).hom
    ((Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))))).hom a) = _
  rw [Spec.preimage_map]
  rfl

/-- The denominator is nonzero at every actual localization point. -/
theorem complexPrincipalSchemePointMap_denominator_ne_zero {A : CommRingCat}
    (f : Spec A ⟶ Spec (.of ℂ)) (r : A)
    (p : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ f)) :
    let := affinePointFieldAlgebra f
    affineSchemePointHomeomorphOfStructure f
      (schemeComplexPointMap (complexPrincipalSchemeMap r ≫ f) f
        (complexPrincipalSchemeMap r) rfl p) r ≠ 0 := by
  let := affinePointFieldAlgebra f
  let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ f)
  rw [complexPrincipalSchemePointMap_eval]
  exact ((IsLocalization.Away.algebraMap_isUnit r).map
    (affineSchemePointHomeomorphOfStructure (complexPrincipalSchemeMap r ≫ f) p)).ne_zero

/-- Every genuine target-chart element has an actual fraction on a principal
refinement of the overlap. -/
theorem complexAffine_overlap_algebraMap_fraction {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) (a : c.ring) :
    let := affinePointFieldAlgebra (c.map ≫ f)
    let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
    ∃ n : ℕ, ∃ b : d.ring,
      complexAffine_overlap_algebraMap f c d r hr a *
        algebraMap d.ring (Localization.Away r) r ^ n =
      algebraMap d.ring (Localization.Away r) b :=
  IsLocalization.Away.surj r (complexAffine_overlap_algebraMap f c d r hr a)

/-- Evaluation of an actual overlap fraction is the literal quotient of
source-chart evaluations, with nonvanishing supplied by the actual point. -/
theorem complexAffine_overlap_eval_fraction {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map)
    (p : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (d.map ≫ f)))
    (a : c.ring) (n : ℕ) (b : d.ring)
    (hab : (Spec.preimage (complexAffine_overlap_lift c d r hr)).hom a *
      algebraMap d.ring (Localization.Away r) r ^ n =
      algebraMap d.ring (Localization.Away r) b) :
    let := affinePointFieldAlgebra (c.map ≫ f)
    let := affinePointFieldAlgebra (d.map ≫ f)
    affineSchemePointHomeomorphOfStructure (c.map ≫ f)
        (complexAffine_overlap_pointMap f c d r hr p) a =
      affineSchemePointHomeomorphOfStructure (d.map ≫ f)
        (schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
          (d.map ≫ f) (complexPrincipalSchemeMap r) rfl p) b /
      affineSchemePointHomeomorphOfStructure (d.map ≫ f)
        (schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
          (d.map ≫ f) (complexPrincipalSchemeMap r) rfl p) r ^ n := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ f)
  let := affinePointFieldAlgebra (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
  apply (eq_div_iff (pow_ne_zero n (complexPrincipalSchemePointMap_denominator_ne_zero
    (d.map ≫ f) r p))).mpr
  rw [complexAffine_overlap_algebraMap_eval, complexPrincipalSchemePointMap_eval,
    complexPrincipalSchemePointMap_eval]
  have heq := congrArg
    (affineSchemePointHomeomorphOfStructure (complexPrincipalSchemeMap r ≫ (d.map ≫ f)) p) hab
  simpa only [map_mul, map_pow, complexAffine_overlap_algebraMap_apply] using heq

/-- The actual overlap ring map has genuine denominators, independently of
any algebra-structure transport in its notation. -/
theorem complexAffine_overlap_ringMap_fraction {X : Scheme} (c d : ComplexAffineChart X)
    (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map) (a : c.ring) :
    ∃ n : ℕ, ∃ b : d.ring,
      (Spec.preimage (complexAffine_overlap_lift c d r hr)).hom a *
        algebraMap d.ring (Localization.Away r) r ^ n =
      algebraMap d.ring (Localization.Away r) b :=
  IsLocalization.Away.surj r ((Spec.preimage (complexAffine_overlap_lift c d r hr)).hom a)

/-- Every actual point lying over a second affine chart admits an actual
principal overlap lift, with its nonzero denominator evaluated at that point. -/
theorem exists_complexAffine_overlap_point {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (c d : ComplexAffineChart X) (p : ComplexAffineChartPoint f d)
    (hp : d.map (schemeComplexPointImage (d.map ≫ f) p) ∈ Set.range c.map) :
    letI := affinePointFieldAlgebra (d.map ≫ f)
    ∃ r : d.ring,
      ∃ _hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map,
      ∃ q : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (d.map ≫ f)),
        schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
          (d.map ≫ f) (complexPrincipalSchemeMap r) rfl q = p ∧
        affineSchemePointHomeomorphOfStructure (d.map ≫ f) p r ≠ 0 := by
  let := affinePointFieldAlgebra (d.map ≫ f)
  obtain ⟨r, hyr, hr⟩ := exists_complexAffine_overlap_principal c d
    (schemeComplexPointImage (d.map ≫ f) p) hp
  have hpRange : schemeComplexPointImage (d.map ≫ f) p ∈
      Set.range (complexPrincipalSchemeMap r) :=
    Eq.mpr (congrArg (fun S : Set (PrimeSpectrum d.ring) =>
      schemeComplexPointImage (d.map ≫ f) p ∈ S) (complexPrincipalSchemeMap_range r)) hyr
  let q := schemeComplexPointLift (d.map ≫ f) (complexPrincipalSchemeMap r) p hpRange
  have hqp : schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
      (d.map ≫ f) (complexPrincipalSchemeMap r) rfl q = p := by
    apply Subtype.ext
    exact schemeComplexPointLift_fac (d.map ≫ f) (complexPrincipalSchemeMap r) p hpRange
  refine ⟨r, hr, q, hqp, ?_⟩
  exact (affineSchemePointImage_mem_basicOpen (d.map ≫ f) p r).mp hyr

/-- Two genuine affine chart points representing the same global point have
an actual common principal refinement, mapping back to both given points. -/
theorem exists_complexAffine_common_overlap_point {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (c d : ComplexAffineChart X)
    (x : ComplexAffineChartPoint f c) (y : ComplexAffineChartPoint f d)
    (hxy : complexAffineChartPointMap f d y = complexAffineChartPointMap f c x) :
    letI := affinePointFieldAlgebra (d.map ≫ f)
    ∃ r : d.ring,
      ∃ hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map,
      ∃ q : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (d.map ≫ f)),
        schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
          (d.map ≫ f) (complexPrincipalSchemeMap r) rfl q = y ∧
        complexAffine_overlap_pointMap f c d r hr q = x ∧
        affineSchemePointHomeomorphOfStructure (d.map ≫ f) y r ≠ 0 := by
  let := affinePointFieldAlgebra (d.map ≫ f)
  have hc : schemeComplexPointImage f (complexAffineChartPointMap f c x) ∈
      Set.range c.map := (schemeComplexPointChart f c.map x).property
  rw [← hxy, schemeComplexPointImage_chart] at hc
  obtain ⟨r, hr, q, hqy, hden⟩ := exists_complexAffine_overlap_point f c d y hc
  refine ⟨r, hr, q, hqy, ?_, hden⟩
  apply complexAffineChartPointMap_injective f c
  exact (complexAffine_overlap_pointMap_fac f c d r hr q).trans
    ((congrArg (complexAffineChartPointMap f d) hqy).trans hxy)

/-- A fixed genuine overlap fraction evaluates at any two actual chart
points representing the same global point, whenever the actual denominator
is nonzero there. The needed localization point is produced from that point. -/
theorem complexAffine_common_overlap_eval_fraction {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map)
    (x : ComplexAffineChartPoint f c) (y : ComplexAffineChartPoint f d)
    (hxy : complexAffineChartPointMap f d y = complexAffineChartPointMap f c x)
    (hy : letI := affinePointFieldAlgebra (d.map ≫ f)
      affineSchemePointHomeomorphOfStructure (d.map ≫ f) y r ≠ 0)
    (a : c.ring) (n : ℕ) (b : d.ring)
    (hab : (Spec.preimage (complexAffine_overlap_lift c d r hr)).hom a *
      algebraMap d.ring (Localization.Away r) r ^ n =
      algebraMap d.ring (Localization.Away r) b) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := affinePointFieldAlgebra (d.map ≫ f)
    affineSchemePointHomeomorphOfStructure (c.map ≫ f) x a =
      affineSchemePointHomeomorphOfStructure (d.map ≫ f) y b /
        affineSchemePointHomeomorphOfStructure (d.map ≫ f) y r ^ n := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := affinePointFieldAlgebra (d.map ≫ f)
  have hyr : schemeComplexPointImage (d.map ≫ f) y ∈ PrimeSpectrum.basicOpen r :=
    (affineSchemePointImage_mem_basicOpen (d.map ≫ f) y r).mpr hy
  have hyRange : schemeComplexPointImage (d.map ≫ f) y ∈
      Set.range (complexPrincipalSchemeMap r) :=
    Eq.mpr (congrArg (fun S : Set (PrimeSpectrum d.ring) =>
      schemeComplexPointImage (d.map ≫ f) y ∈ S) (complexPrincipalSchemeMap_range r)) hyr
  let q := schemeComplexPointLift (d.map ≫ f) (complexPrincipalSchemeMap r) y hyRange
  have hqy : schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (d.map ≫ f))
      (d.map ≫ f) (complexPrincipalSchemeMap r) rfl q = y := by
    apply Subtype.ext
    exact schemeComplexPointLift_fac (d.map ≫ f) (complexPrincipalSchemeMap r) y hyRange
  have hqx : complexAffine_overlap_pointMap f c d r hr q = x := by
    apply complexAffineChartPointMap_injective f c
    exact (complexAffine_overlap_pointMap_fac f c d r hr q).trans
      ((congrArg (complexAffineChartPointMap f d) hqy).trans hxy)
  have hfrac := complexAffine_overlap_eval_fraction f c d r hr q a n b hab
  rw [hqx, hqy] at hfrac
  exact hfrac

end

end ComplexSchemes
