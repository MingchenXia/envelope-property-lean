import BingWangEntropy.NativeProjectiveAnalyticImmersion
import BingWangEntropy.PrincipalAnalyticTransitions

/-!
# Actual principal refinements for a native closed immersion

The affine inverse image of the actual ambient chart is refined inside the
actual source chart. Finite source coordinates acquire a common denominator;
the native closed-immersion ring map lifts this denominator and the numerators.
Their nonvanishing follows from the given actual complex point.
-/

open Algebra CategoryTheory AlgebraicGeometry
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace BingWangEntropy

noncomputable section

/-- Actual localization fractions for a finite family admit one common exponent. -/
theorem complexAffine_overlap_ringMap_common_denominator {X : Scheme}
    {ι : Type*} [Fintype ι] (c d : ComplexAffineChart X) (r : d.ring)
    (hr : Set.range (complexPrincipalSchemeMap r ≫ d.map) ⊆ Set.range c.map)
    (a : ι → c.ring) :
    ∃ N : ℕ, ∃ b : ι → d.ring, ∀ j,
      (Spec.preimage (complexAffine_overlap_lift c d r hr)).hom (a j) *
        algebraMap d.ring (Localization.Away r) r ^ N =
      algebraMap d.ring (Localization.Away r) (b j) := by
  classical
  choose n b hb using fun j => complexAffine_overlap_ringMap_fraction c d r hr (a j)
  let N := Finset.univ.sup n
  refine ⟨N, fun j => b j * r ^ (N - n j), ?_⟩
  intro j
  have hn : n j ≤ N := Finset.le_sup (Finset.mem_univ j)
  rw [map_mul, map_pow, ← hb j, mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

/-- Actual point data produces a point in the genuine closed affine preimage. -/
theorem exists_closedImmersionAffineSourceChartPoint {X Y : Scheme}
    (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
    (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (x : ComplexAffineChartPoint (i ≫ f) c) (y : ComplexAffineChartPoint f d)
    (hxy : schemeComplexPointMap (i ≫ f) f i rfl
      (complexAffineChartPointMap (i ≫ f) c x) = complexAffineChartPointMap f d y) :
    ∃ z : ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i d),
      complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i d) z =
        complexAffineChartPointMap (i ≫ f) c x ∧
      closedImmersionAffineChartPointMap f i d z = y := by
  have hx : complexAffineChartPointMap (i ≫ f) c x ∈ Set.range
      (complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i d)) := by
    rw [closedImmersionAffineSourceChartPoint_range]
    exact ⟨y, hxy.symm⟩
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, hz, ?_⟩
  apply complexAffineChartPointMap_injective f d
  exact (congrFun (closedImmersionAffineChartPointMap_fac f i d) z).symm.trans
    ((congrArg (schemeComplexPointMap (i ≫ f) f i rfl) hz).trans hxy)

/-- Native closed affine preimages have genuine principal refinements through the actual point. -/
theorem exists_closedImmersion_principal_refinement {X Y : Scheme}
    (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
    (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (x : ComplexAffineChartPoint (i ≫ f) c) (y : ComplexAffineChartPoint f d)
    (hxy : schemeComplexPointMap (i ≫ f) f i rfl
      (complexAffineChartPointMap (i ≫ f) c x) = complexAffineChartPointMap f d y) :
    let e := closedImmersionAffineSourceChart i d
    let _ := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
    ∃ z : ComplexAffineChartPoint (i ≫ f) e,
      complexAffineChartPointMap (i ≫ f) e z = complexAffineChartPointMap (i ≫ f) c x ∧
      closedImmersionAffineChartPointMap f i d z = y ∧
      ∃ r : e.ring,
        ∃ hr : Set.range (complexPrincipalSchemeMap r ≫ e.map) ⊆ Set.range c.map,
        ∃ q : SchemeComplexPoint (complexPrincipalSchemeMap r ≫ (e.map ≫ (i ≫ f))),
          schemeComplexPointMap (complexPrincipalSchemeMap r ≫ (e.map ≫ (i ≫ f)))
            (e.map ≫ (i ≫ f)) (complexPrincipalSchemeMap r) rfl q = z ∧
          complexAffine_overlap_pointMap (i ≫ f) c e r hr q = x ∧
          affineSchemePointHomeomorphOfStructure (e.map ≫ (i ≫ f)) z r ≠ 0 := by
  let e := closedImmersionAffineSourceChart i d
  let := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
  dsimp only
  obtain ⟨z, hz, hzy⟩ := exists_closedImmersionAffineSourceChartPoint f i c d x y hxy
  obtain ⟨r, hr, q, hqz, hqx, hden⟩ :=
    exists_complexAffine_common_overlap_point (i ≫ f) c e x z hz
  exact ⟨z, hz, hzy, r, hr, q, hqz, hqx, hden⟩

/-- Ambient evaluation is literal evaluation of the native closed affine ring pullback. -/
theorem closedImmersionAffineChartPointMap_eval {X Y : Scheme}
    (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
    (d : ComplexAffineChart Y)
    (z : ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i d))
    (b : d.ring) :
    let _ := affinePointFieldAlgebra (d.map ≫ f)
    let _ := affinePointFieldAlgebra
      ((closedImmersionAffineSourceChart i d).map ≫ (i ≫ f))
    affineSchemePointHomeomorphOfStructure (d.map ≫ f)
        (closedImmersionAffineChartPointMap f i d z) b =
      affineSchemePointHomeomorphOfStructure
        ((closedImmersionAffineSourceChart i d).map ≫ (i ≫ f)) z
        ((Spec.preimage (closedImmersionAffineChartMap i d)).hom b) := by
  let := affinePointFieldAlgebra (d.map ≫ f)
  let := affinePointFieldAlgebra
    ((closedImmersionAffineSourceChart i d).map ≫ (i ≫ f))
  exact congrArg (fun p => p b) (affineSchemeOverAlgebraMap_naturality _ _ _
    (closedImmersionAffineChartMap_over f i d) z)

/-- A genuine closed immersion produces ambient lifts of a common source-coordinate fraction. -/
theorem exists_closedImmersion_ambient_common_fraction_lifts {X Y : Scheme}
    {ι : Type*} [Fintype ι]
    (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
    (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (x : ComplexAffineChartPoint (i ≫ f) c) (y : ComplexAffineChartPoint f d)
    (hxy : schemeComplexPointMap (i ≫ f) f i rfl
      (complexAffineChartPointMap (i ≫ f) c x) = complexAffineChartPointMap f d y)
    (a : ι → c.ring) :
    let e := closedImmersionAffineSourceChart i d
    let g := (Spec.preimage (closedImmersionAffineChartMap i d)).hom
    let _ := affinePointFieldAlgebra (d.map ≫ f)
    let _ := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
    ∃ z : ComplexAffineChartPoint (i ≫ f) e,
      complexAffineChartPointMap (i ≫ f) e z = complexAffineChartPointMap (i ≫ f) c x ∧
      closedImmersionAffineChartPointMap f i d z = y ∧
      ∃ r : e.ring,
        ∃ hr : Set.range (complexPrincipalSchemeMap r ≫ e.map) ⊆ Set.range c.map,
        ∃ N : ℕ, ∃ R : d.ring, ∃ B : ι → d.ring,
          g R = r ∧
          (∀ j, (Spec.preimage (complexAffine_overlap_lift c e r hr)).hom (a j) *
            algebraMap e.ring (Localization.Away r) r ^ N =
            algebraMap e.ring (Localization.Away r) (g (B j))) ∧
          affineSchemePointHomeomorphOfStructure (e.map ≫ (i ≫ f)) z r ≠ 0 ∧
          affineSchemePointHomeomorphOfStructure (d.map ≫ f) y R ≠ 0 := by
  classical
  let e := closedImmersionAffineSourceChart i d
  let g := (Spec.preimage (closedImmersionAffineChartMap i d)).hom
  let := affinePointFieldAlgebra (d.map ≫ f)
  let := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
  dsimp only
  obtain ⟨z, hz, hzy, r, hr, _, _, _, hden⟩ :=
    exists_closedImmersion_principal_refinement f i c d x y hxy
  obtain ⟨N, b, hb⟩ := complexAffine_overlap_ringMap_common_denominator c e r hr a
  have hg : Function.Surjective g := affineClosedImmersion_preimage_surjective _
  obtain ⟨R, hR⟩ := hg r
  choose B hB using fun j => hg (b j)
  refine ⟨z, hz, hzy, r, hr, N, R, B, hR, ?_, hden, ?_⟩
  · intro j
    rw [hB j]
    exact hb j
  · rw [← hzy, closedImmersionAffineChartPointMap_eval, hR]
    exact hden

/-- The constructed ambient fractions evaluate correctly at every actual shared point. -/
theorem closedImmersion_ambient_common_fraction_eval {X Y : Scheme}
    (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
    (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (r : (closedImmersionAffineSourceChart i d).ring)
    (hr : Set.range
      (complexPrincipalSchemeMap r ≫ (closedImmersionAffineSourceChart i d).map) ⊆
      Set.range c.map)
    (x : ComplexAffineChartPoint (i ≫ f) c)
    (z : ComplexAffineChartPoint (i ≫ f) (closedImmersionAffineSourceChart i d))
    (hxz : complexAffineChartPointMap (i ≫ f) (closedImmersionAffineSourceChart i d) z =
      complexAffineChartPointMap (i ≫ f) c x)
    (hz : letI := affinePointFieldAlgebra ((closedImmersionAffineSourceChart i d).map ≫ (i ≫ f))
      affineSchemePointHomeomorphOfStructure
        ((closedImmersionAffineSourceChart i d).map ≫ (i ≫ f)) z r ≠ 0)
    (a : c.ring) (N : ℕ) (R B : d.ring)
    (hR : (Spec.preimage (closedImmersionAffineChartMap i d)).hom R = r)
    (ha : (Spec.preimage
      (complexAffine_overlap_lift c (closedImmersionAffineSourceChart i d) r hr)).hom a *
      algebraMap (closedImmersionAffineSourceChart i d).ring (Localization.Away r) r ^ N =
      algebraMap (closedImmersionAffineSourceChart i d).ring (Localization.Away r)
        ((Spec.preimage (closedImmersionAffineChartMap i d)).hom B)) :
    let _ := affinePointFieldAlgebra (c.map ≫ (i ≫ f))
    let _ := affinePointFieldAlgebra (d.map ≫ f)
    affineSchemePointHomeomorphOfStructure (c.map ≫ (i ≫ f)) x a =
      affineSchemePointHomeomorphOfStructure (d.map ≫ f)
        (closedImmersionAffineChartPointMap f i d z) B /
      affineSchemePointHomeomorphOfStructure (d.map ≫ f)
        (closedImmersionAffineChartPointMap f i d z) R ^ N := by
  let := affinePointFieldAlgebra (c.map ≫ (i ≫ f))
  let := affinePointFieldAlgebra (d.map ≫ f)
  let := affinePointFieldAlgebra
    ((closedImmersionAffineSourceChart i d).map ≫ (i ≫ f))
  rw [closedImmersionAffineChartPointMap_eval, closedImmersionAffineChartPointMap_eval, hR]
  exact complexAffine_common_overlap_eval_fraction (i ≫ f) c
    (closedImmersionAffineSourceChart i d) r hr x z hxz hz a N _ ha

section AnalyticFractions

variable {B I J ι : Type*} [CommRing B] [Algebra ℂ B]
  [Fintype I] [Fintype J] [DecidableEq J] [Fintype ι]

/-- Evaluating the actual ambient numerators and denominator in the actual inverse chart. -/
def submersiveAnalyticCommonFractionExtension (Q : SubmersivePresentation ℂ B I J)
    (q : ComplexAlgebraPoint B) (N : ℕ) (R : B) (b : ι → B) :
    (Fin Q.dimension → ℂ) → (ι → ℂ) :=
  fun t j => (submersiveAnalyticComplexPointChart Q q).symm t (b j) /
    (submersiveAnalyticComplexPointChart Q q).symm t R ^ N

/-- Actual common-denominator extensions are analytic on the true nonvanishing target. -/
theorem submersiveAnalyticCommonFractionExtension_analyticOnNhd
    (Q : SubmersivePresentation ℂ B I J) (q : ComplexAlgebraPoint B)
    (N : ℕ) (R : B) (b : ι → B) :
    AnalyticOnNhd ℂ (submersiveAnalyticCommonFractionExtension Q q N R b)
      (submersivePrincipalAnalyticDomain Q q R) := by
  intro t ht
  apply AnalyticAt.pi
  intro j
  exact (submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd Q q (b j) t ht.1).div
    ((submersiveAnalyticComplexPointChart_symm_eval_analyticOnNhd Q q R t ht.1).pow N)
    (pow_ne_zero N ht.2)

/-- Nonvanishing at an actual chart point puts its coordinates in the genuine fraction domain. -/
theorem submersiveAnalyticCommonFractionExtension_point_mem_domain
    (Q : SubmersivePresentation ℂ B I J) (q : ComplexAlgebraPoint B)
    {y : ComplexAlgebraPoint B} (hy : y ∈ (submersiveAnalyticComplexPointChart Q q).source)
    (R : B) (hR : y R ≠ 0) :
    submersiveAnalyticComplexPointChart Q q y ∈ submersivePrincipalAnalyticDomain Q q R := by
  refine ⟨(submersiveAnalyticComplexPointChart Q q).map_source hy, ?_⟩
  change (submersiveAnalyticComplexPointChart Q q).symm
    (submersiveAnalyticComplexPointChart Q q y) R ≠ 0
  rw [(submersiveAnalyticComplexPointChart Q q).left_inv hy]
  exact hR

omit [Fintype ι] in
/-- The extension reads back the literal ambient fraction at every actual chart point. -/
theorem submersiveAnalyticCommonFractionExtension_apply
    (Q : SubmersivePresentation ℂ B I J) (q : ComplexAlgebraPoint B)
    (N : ℕ) (R : B) (b : ι → B)
    {y : ComplexAlgebraPoint B} (hy : y ∈ (submersiveAnalyticComplexPointChart Q q).source)
    (j : ι) :
    submersiveAnalyticCommonFractionExtension Q q N R b
      (submersiveAnalyticComplexPointChart Q q y) j = y (b j) / y R ^ N := by
  unfold submersiveAnalyticCommonFractionExtension
  rw [(submersiveAnalyticComplexPointChart Q q).left_inv hy]

end AnalyticFractions

/-- The literal source free coordinates have actual analytic ambient extensions at the given point. -/
theorem exists_closedImmersion_free_coordinate_ambient_extensions {X Y : Scheme}
    {I J I' J' : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    [Fintype I'] [Fintype J'] [DecidableEq J']
    (f : Y ⟶ Spec (.of ℂ)) (i : X ⟶ Y) [IsClosedImmersion i]
    (c : ComplexAffineChart X) (d : ComplexAffineChart Y)
    (x : ComplexAffineChartPoint (i ≫ f) c) (y : ComplexAffineChartPoint f d)
    (hxy : schemeComplexPointMap (i ≫ f) f i rfl
      (complexAffineChartPointMap (i ≫ f) c x) = complexAffineChartPointMap f d y) :
    let _ := affinePointFieldAlgebra (c.map ≫ (i ≫ f))
    let _ := affinePointFieldAlgebra (d.map ≫ f)
    ∀ (P : SubmersivePresentation ℂ c.ring I J)
      (Q : SubmersivePresentation ℂ d.ring I' J'),
    let p := affineSchemePointHomeomorphOfStructure (c.map ≫ (i ≫ f)) x
    let q := affineSchemePointHomeomorphOfStructure (d.map ≫ f) y
    let e := closedImmersionAffineSourceChart i d
    let g := (Spec.preimage (closedImmersionAffineChartMap i d)).hom
    let _ := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
    ∃ z : ComplexAffineChartPoint (i ≫ f) e,
      complexAffineChartPointMap (i ≫ f) e z = complexAffineChartPointMap (i ≫ f) c x ∧
      closedImmersionAffineChartPointMap f i d z = y ∧
      ∃ r : e.ring,
        ∃ hr : Set.range (complexPrincipalSchemeMap r ≫ e.map) ⊆ Set.range c.map,
        ∃ N : ℕ, ∃ R : d.ring, ∃ B : Fin P.dimension → d.ring,
          g R = r ∧
          (∀ j, (Spec.preimage (complexAffine_overlap_lift c e r hr)).hom
            (P.val ((submersiveFreeIndexEquiv P).symm j)) *
            algebraMap e.ring (Localization.Away r) r ^ N =
            algebraMap e.ring (Localization.Away r) (g (B j))) ∧
          affineSchemePointHomeomorphOfStructure (e.map ≫ (i ≫ f)) z r ≠ 0 ∧
          submersiveAnalyticComplexPointChart Q q q ∈ submersivePrincipalAnalyticDomain Q q R ∧
          AnalyticAt ℂ (submersiveAnalyticCommonFractionExtension Q q N R B)
            (submersiveAnalyticComplexPointChart Q q q) ∧
          submersiveAnalyticCommonFractionExtension Q q N R B
            (submersiveAnalyticComplexPointChart Q q q) =
            submersiveAnalyticComplexPointChart P p p := by
  let := affinePointFieldAlgebra (c.map ≫ (i ≫ f))
  let := affinePointFieldAlgebra (d.map ≫ f)
  dsimp only
  intro P Q
  let p := affineSchemePointHomeomorphOfStructure (c.map ≫ (i ≫ f)) x
  let q := affineSchemePointHomeomorphOfStructure (d.map ≫ f) y
  let e := closedImmersionAffineSourceChart i d
  let := affinePointFieldAlgebra (e.map ≫ (i ≫ f))
  obtain ⟨z, hz, hzy, r, hr, N, R, B, hR, hB, hden, hRden⟩ :=
    exists_closedImmersion_ambient_common_fraction_lifts f i c d x y hxy
      (fun j : Fin P.dimension => P.val ((submersiveFreeIndexEquiv P).symm j))
  have hq : q ∈ (submersiveAnalyticComplexPointChart Q q).source :=
    submersiveAnalyticComplexPointChart_point_mem_source Q q
  have hdomain := submersiveAnalyticCommonFractionExtension_point_mem_domain Q q hq R hRden
  refine ⟨z, hz, hzy, r, hr, N, R, B, hR, hB, hden, hdomain,
    submersiveAnalyticCommonFractionExtension_analyticOnNhd Q q N R B _ hdomain, ?_⟩
  ext j
  rw [submersiveAnalyticCommonFractionExtension_apply Q q N R B hq j,
    submersiveAnalyticComplexPointChart_apply P p p
      (submersiveAnalyticComplexPointChart_point_mem_source P p)]
  have heval := closedImmersion_ambient_common_fraction_eval f i c d r hr x z hz hden
    (P.val ((submersiveFreeIndexEquiv P).symm j)) N R (B j) hR (hB j)
  rw [hzy] at heval
  exact heval.symm

end

end BingWangEntropy
