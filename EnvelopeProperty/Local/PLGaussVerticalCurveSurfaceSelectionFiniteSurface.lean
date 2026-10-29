import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionNormalizedStep
import EnvelopeProperty.Local.PLGaussVerticalCurveSurfaceSelectionClosedDimension

/-! # Dimension induction to a normal horizontal surface

All normal models and closed central curves are internally constructed.
The final original producer has no dimension, surface or family certificate.
-/
noncomputable section
open scoped Classical Polynomial
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open EnvelopeProperty.ProjBerk
universe u
namespace EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionFiniteSurface
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The same whole original native and polynomial coefficient structures agree. -/
theorem nativeStructureMap_eq_homogeneousProjπ {R : Type u} [CommRing R] {n : ℕ} :
    nativeStructureMap (R := R) (n := n) =
      MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 1)) := by
  have hC : homogeneousCoefficientZero R n = algebraMap R (ProjectiveGrading R n 0) := by
    ext r
    rfl
  change (Proj.toSpecZero (ProjectiveGrading R n) ≫
      Spec.map (CommRingCat.ofHom (homogeneousCoefficientZero R n))) =
    (Proj.toSpecZero (ProjectiveGrading R n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ProjectiveGrading R n 0))))
  rw [hC]

/-- Same model normalization retains a closed finite-dominant central curve and whole dimension. -/
theorem exists_original_normalized_model_with_curve
    {k : Type u} [Field k] {n : ℕ} {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) :
    ∃ (N C' : Scheme.{u}) (f : N ⟶ Y) (g : C' ⟶ C) (j : C' ⟶ N),
      IsIntegral N ∧ IsIntegral C' ∧ IsFinite f ∧ IsFinite g ∧ IsDominant g ∧ IsClosedImmersion j ∧
      IsDominant (f ≫ (i ≫ nativeStructureMap)) ∧
      IsProjectiveFactorization (f ≫ (i ≫ nativeStructureMap)) ∧ IsProjectiveFactorization (g ≫ q) ∧
      topologicalKrullDim N = topologicalKrullDim Y ∧ topologicalKrullDim C' = 1 ∧
      j ≫ f = g ≫ c ∧
      j ≫ (f ≫ (i ≫ nativeStructureMap)) =
        (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
      ∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z) := by
  let b : Y ⟶ Spec (CommRingCat.of k[X]) := i ≫ nativeStructureMap
  let p : Y ⟶ Spec (CommRingCat.of k) := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  have hbProj := PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization i
  let : IsProper b := hbProj.isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType p := inferInstance
  have hzero : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Spec.map_comp]
    have hR : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) = 𝟙 (CommRingCat.of k) := by
      ext r
      change Polynomial.evalRingHom (0 : k) (Polynomial.C r) = r
      simp
    rw [hR, Spec.map_id]
  have hcfield : c ≫ p = q := by
    change c ≫ (b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) = q
    rw [← Category.assoc, hc, Category.assoc, hzero, Category.comp_id]
  let N : Scheme.{u} := IntegralSchemeNormalization.normalization Y
  let f : N ⟶ Y := IntegralSchemeNormalization.projection Y
  let : IsIntegral N := inferInstance
  let : IsFinite f := IntegralSchemeNormalization.projection_isFinite k Y p
  let : Surjective f := ⟨IntegralSchemeNormalization.projection_surjective Y⟩
  let : IsDominant f := ⟨f.surjective.denseRange⟩
  have hfb : IsDominant (f ≫ b) := inferInstance
  have hfProj : IsProjectiveFactorization (f ≫ b) :=
    CurveFiniteMapDegrees.finite_comp_projectiveFactorization b hbProj f
  have hNdim : topologicalKrullDim N = topologicalKrullDim Y :=
    PLGaussVerticalCurveSurfaceSelectionNormalizationDimension.normalization_dimension_eq p
  obtain ⟨C', g, j, hCI, hgfin, hgdom, hj, hCdim, hgProj, hjf, _hjfield⟩ :=
    PLGaussVerticalCurveSurfaceSelectionClosedCurveLift.exists_closed_projective_curve_lift
      p q hq hdimC c hcfield f
  have hjcentral : j ≫ (f ≫ b) =
      (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    rw [← Category.assoc, hjf, Category.assoc, hc, ← Category.assoc]
  exact ⟨N, C', f, g, j, inferInstance, hCI, inferInstance, hgfin, hgdom, hj, hfb, hfProj, hgProj,
    hNdim, hCdim, hjf, hjcentral, IntegralSchemeNormalization.stalk_isIntegrallyClosed Y⟩

private theorem exists_surface_of_dimension_nat {k : Type u} [Field k] [Infinite k] (d : ℕ) :
    ∀ {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C] {n : ℕ}
      (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
      [IsDominant (i ≫ nativeStructureMap)]
      (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
      (c : C ⟶ Y) [IsClosedImmersion c],
      c ≫ (i ≫ nativeStructureMap) =
        q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) →
      topologicalKrullDim C = 1 → topologicalKrullDim Y = d →
      ∃ (S C' : Scheme.{u}) (F : S ⟶ Y) (G : C' ⟶ C) (J : C' ⟶ S),
        IsIntegral S ∧ IsIntegral C' ∧ IsFinite F ∧ IsFinite G ∧ IsDominant G ∧ IsClosedImmersion J ∧
        IsDominant (F ≫ (i ≫ nativeStructureMap)) ∧
        IsProjectiveFactorization (F ≫ (i ≫ nativeStructureMap)) ∧ IsProjectiveFactorization (G ≫ q) ∧
        topologicalKrullDim S = 2 ∧ topologicalKrullDim C' = 1 ∧
        J ≫ F = G ≫ c ∧
        J ≫ (F ≫ (i ≫ nativeStructureMap)) =
          (G ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
        ∀ z : S, IsIntegrallyClosed (S.presheaf.stalk z) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro Y C _ _ n i _ _ q hq c _ hc hdimC hdimY
    have hfloor := PLGaussVerticalCurveSurfaceSelectionNormalizedStep.two_le_dimension_of_original_central_curve
      i q c hc hdimC
    rw [hdimY] at hfloor
    have hfloorNat : 2 ≤ d := by exact_mod_cast hfloor
    by_cases htwo : d = 2
    · obtain ⟨S, C', F, G, J, hSI, hCI, hF, hG, hGD, hJ, hFB, hFP, hGP,
        hSdim, hCdim, hJF, hcentral, hnormal⟩ :=
        exists_original_normalized_model_with_curve i q hq c hc hdimC
      have hSdim2 : topologicalKrullDim S = 2 := by simpa [htwo] using hSdim.trans hdimY
      exact ⟨S, C', F, G, J, hSI, hCI, hF, hG, hGD, hJ, hFB, hFP, hGP,
        hSdim2, hCdim, hJF, hcentral, hnormal⟩
    · have hdgt : 2 < d := by omega
      have hdimYgt : 2 < topologicalKrullDim Y := by rw [hdimY]; exact_mod_cast hdgt
      obtain ⟨N, C₁, f, g, j, hNI, hCI, hf, hg, hgdom, hj, hNb, hNP, hgP,
        hNdim, hCdim, hjf, hjcentral, _hnormal⟩ :=
        PLGaussVerticalCurveSurfaceSelectionNormalizedStep.exists_original_normalized_horizontal_step
          i q hq c hc hdimC hdimYgt
      let : IsIntegral N := hNI
      let : IsIntegral C₁ := hCI
      let : IsFinite f := hf
      let : IsFinite g := hg
      let : IsDominant g := hgdom
      let : IsClosedImmersion j := hj
      obtain ⟨r, i₀, hi₀, hbase₀⟩ := hNP
      let iN : N ⟶ NativeProjectiveScheme k[X] r := i₀
      let : IsClosedImmersion iN := hi₀
      have hbase : iN ≫ nativeStructureMap = f ≫ (i ≫ nativeStructureMap) := by
        change i₀ ≫ nativeStructureMap (R := k[X]) (n := r) = f ≫ (i ≫ nativeStructureMap)
        rw [nativeStructureMap_eq_homogeneousProjπ]
        exact hbase₀
      let : IsDominant (iN ≫ nativeStructureMap) := by rw [hbase]; exact hNb
      let pN : N ⟶ Spec (CommRingCat.of k) :=
        (iN ≫ nativeStructureMap) ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
      let : IsProper (iN ≫ nativeStructureMap) :=
        (PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization iN).isProper
      let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
        (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
          (RingHom.finiteType_algebraMap.mpr inferInstance)
      let : LocallyOfFiniteType pN := inferInstance
      obtain ⟨e, he⟩ := PLGaussVerticalCurveSurfaceSelectionClosedDimension.exists_whole_dimension_eq_natCast pN
      have hEq := hNdim
      rw [he, hdimY] at hEq
      have hEqNat : e + 1 = d := by exact_mod_cast hEq
      have helt : e < d := by omega
      have hcentralN : j ≫ (iN ≫ nativeStructureMap) =
          (g ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
        rw [hbase]
        exact hjcentral
      obtain ⟨S, C₂, F₂, G₂, J, hSI, hC₂I, hF₂, hG₂, hG₂D, hJ, hF₂b, hF₂P, hG₂P,
        hSdim, hC₂dim, hJF₂, _hcentral₂, hnormal⟩ := ih e helt iN (g ≫ q) hgP j hcentralN hCdim he
      let : IsFinite F₂ := hF₂
      let : IsFinite G₂ := hG₂
      let : IsDominant G₂ := hG₂D
      have htotalBase : (F₂ ≫ f) ≫ (i ≫ nativeStructureMap) = F₂ ≫ (iN ≫ nativeStructureMap) := by
        rw [Category.assoc, hbase]
      have htotalDom : IsDominant ((F₂ ≫ f) ≫ (i ≫ nativeStructureMap)) := by
        rw [htotalBase]
        exact hF₂b
      have htotalProj : IsProjectiveFactorization ((F₂ ≫ f) ≫ (i ≫ nativeStructureMap)) := by
        rw [htotalBase]
        exact hF₂P
      have hcurveProj : IsProjectiveFactorization ((G₂ ≫ g) ≫ q) := by
        rw [Category.assoc]
        exact hG₂P
      have htriangle : J ≫ (F₂ ≫ f) = (G₂ ≫ g) ≫ c := by
        calc
          J ≫ (F₂ ≫ f) = (J ≫ F₂) ≫ f := (Category.assoc _ _ _).symm
          _ = (G₂ ≫ j) ≫ f := congrArg (fun a => a ≫ f) hJF₂
          _ = G₂ ≫ (j ≫ f) := Category.assoc _ _ _
          _ = G₂ ≫ (g ≫ c) := congrArg (fun a => G₂ ≫ a) hjf
          _ = (G₂ ≫ g) ≫ c := (Category.assoc _ _ _).symm
      have hcentral : J ≫ ((F₂ ≫ f) ≫ (i ≫ nativeStructureMap)) =
          ((G₂ ≫ g) ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
        rw [← Category.assoc, htriangle, Category.assoc, hc, ← Category.assoc]
      exact ⟨S, C₂, F₂ ≫ f, G₂ ≫ g, J, hSI, hC₂I, inferInstance, inferInstance, inferInstance,
        hJ, htotalDom, htotalProj, hcurveProj, hSdim, hC₂dim, htriangle, hcentral, hnormal⟩

/-- The original model internally produces a normal horizontal dimension-two finite surface with a closed finite-dominant central curve. -/
theorem exists_original_normal_horizontal_surface
    {k : Type u} [Field k] [Infinite k] {n : ℕ} {Y C : Scheme.{u}} [IsIntegral Y] [IsIntegral C]
    (i : Y ⟶ NativeProjectiveScheme k[X] n) [IsClosedImmersion i]
    [IsDominant (i ≫ nativeStructureMap)]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (c : C ⟶ Y) [IsClosedImmersion c]
    (hc : c ≫ (i ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))))
    (hdimC : topologicalKrullDim C = 1) :
    ∃ (S C' : Scheme.{u}) (F : S ⟶ Y) (G : C' ⟶ C) (J : C' ⟶ S),
      IsIntegral S ∧ IsIntegral C' ∧ IsFinite F ∧ IsFinite G ∧ IsDominant G ∧ IsClosedImmersion J ∧
      IsDominant (F ≫ (i ≫ nativeStructureMap)) ∧
      IsProjectiveFactorization (F ≫ (i ≫ nativeStructureMap)) ∧ IsProjectiveFactorization (G ≫ q) ∧
      topologicalKrullDim S = 2 ∧ topologicalKrullDim C' = 1 ∧
      J ≫ F = G ≫ c ∧
      J ≫ (F ≫ (i ≫ nativeStructureMap)) =
        (G ≫ q) ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ∧
      ∀ z : S, IsIntegrallyClosed (S.presheaf.stalk z) := by
  let b : Y ⟶ Spec (CommRingCat.of k[X]) := i ≫ nativeStructureMap
  let p : Y ⟶ Spec (CommRingCat.of k) := b ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  let : IsProper b :=
    (PLGaussVerticalCurveSurfaceSelectionNormalizedStep.original_structure_isProjectiveFactorization i).isProper
  let : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : LocallyOfFiniteType p := inferInstance
  obtain ⟨d, hd⟩ := PLGaussVerticalCurveSurfaceSelectionClosedDimension.exists_whole_dimension_eq_natCast p
  exact exists_surface_of_dimension_nat d i q hq c hc hdimC hd

end EnvelopeProperty.PLGaussVerticalCurveSurfaceSelectionFiniteSurface
