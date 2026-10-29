import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalGaussCurveLineDegree
import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalNonflatCurveDegrees
import EnvelopeProperty.Local.PLIdealNormalizedProjectivity
import EnvelopeProperty.Local.PLNormalizedVerticalCenters
import EnvelopeProperty.Local.PLGaussOriginalRegularPairedSurface

/-! # The original prescribed class on the same original central curve

Horizontal-surface and alteration geometry supplies
the regular covering curve. Native whole pullback isomorphisms and the
positive canonical nonflat degree project the proved inequality to the
same original curve, including singular original target curves.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical Polynomial NNReal ENNReal
universe u
namespace EnvelopeProperty.NumericalOriginalCurveDegree
open Scheme.Modules ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem zeroSection_comp_coefficients {k : Type u} [Field k] :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])) =
        𝟙 (Spec (CommRingCat.of k)) := by
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) = 𝟙 (CommRingCat.of k) := by
    ext a
    change Polynomial.evalRingHom (0 : k) (Polynomial.C a) = a
    simp
  rw [h,Spec.map_id]

private def curvePullbackIso {N Y C A : Scheme.{u}}
    (F : Y ⟶ N) (i : A ⟶ Y) (ν : A ⟶ C) (c : C ⟶ N)
    (h : i ≫ F = ν ≫ c) (M : N.Modules) :
    (pullback i).obj ((pullback F).obj M) ≅
      (pullback ν).obj ((pullback c).obj M) :=
  (pullbackComp i F).app M ≪≫ (pullbackCongr h).app M ≪≫
    ((pullbackComp ν c).app M).symm

/-- Original local convexity proves the degree of the same prescribed
line on every original closed integral projective central curve. All
regular covering geometry is constructed internally, including de Jong. -/
theorem exists_prescribedClass_originalCurveDegree_nonneg
    {k : Type u} [Field k] [PerfectField k] [Infinite k] {n : ℕ}
    (X : ProjSubvariety k n) (hX : X.IsProjNormal)
    {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (_hd : 0 < d), (d : ℚ) = r*a ∧
      ∃ (B : ℤ) (I J : X.NativeProductModel.IdealSheafData)
        (hfinAll : ∀ z : RelativeSchemeValuedPoint
            (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
          modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
          modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥),
        let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
        (∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
            (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
          (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
            X.normalizedSimultaneousRatioWeightAt I J hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((B : ℝ) : EReal)) ∧
        ∀ (j : Fin (n+1)),
        let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
        ∀ (C : Scheme.{u}) [IsIntegral C]
          (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
          (_hdim : topologicalKrullDim C = 1)
          (c : C ⟶ X.normalizedSimultaneousIdealBlowup I J hfin) [IsClosedImmersion c]
          (_hc : c ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
            q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))),
          let : IsProper q := hq.isProper
          let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
          0 ≤ CurveLineDegrees.degree q ((pullback c).obj M) := by
  obtain ⟨r,d,hr,hd,hda,B,I,J,hfinAll,heq,H⟩ :=
    NumericalGaussCurveLineDegree.exists_prescribedClass_curveDegree_nonneg X hX ha hconv
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  refine ⟨r,d,hr,hd,hda,B,I,J,hfinAll,heq,?_⟩
  intro j M C hCI q hq hdim c hClosed hc
  let : IsProper q := hq.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  let : IsIntegral (X.normalizedSimultaneousIdealBlowup I J hfin) :=
    X.normalizedSimultaneousIdealBlowup_isIntegral I J hfin
  obtain ⟨m,iN₀,hiN,hbase₀⟩ :=
    X.normalizedSimultaneousIdealBlowupStructure_isProjectiveFactorization I J hfin
  let iN : X.normalizedSimultaneousIdealBlowup I J hfin ⟶
      NativeProjectiveScheme k[X] m := iN₀
  let : IsClosedImmersion iN := hiN
  have hbase : iN ≫ nativeStructureMap =
      X.normalizedSimultaneousIdealBlowupStructure I J hfin := by
    rw [PLGaussVerticalCurveSurfaceSelectionFiniteSurface.nativeStructureMap_eq_homogeneousProjπ]
    exact hbase₀
  let : IsDominant (iN ≫ nativeStructureMap) := by
    rw [hbase]
    exact X.normalizedSimultaneousStructure_isDominant I J hfin hX
  have hc' : c ≫ (iN ≫ nativeStructureMap) =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    rw [hbase]
    exact hc
  obtain ⟨Y,A,hYI,hAI,F,i,ν,_hYreg,_hYdim,_hAreg,hAdim,hAnormal,
    hi,hν,hνdom,hνproj,_hFproper,hproper,hdom,_hflat,htriangle,hcentral,hpoint,hparams⟩ :=
    PLGaussOriginalRegularPairedSurface.exists_original_regular_curve_over_model
      (k := k) (n := m) (Y := X.normalizedSimultaneousIdealBlowup I J hfin) (C := C)
      iN q hq c hc' hdim
  let : IsIntegral Y := hYI
  let : IsIntegral A := hAI
  let : IsClosedImmersion i := hi
  let : IsFinite ν := hν
  let : IsDominant ν := hνdom
  let base := F ≫ (iN ≫ nativeStructureMap)
  let : IsProper base := hproper
  let : IsDominant base := hdom
  let pA := i ≫ base ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
  have hpA : pA = ν ≫ q := by
    dsimp only [pA,base]
    rw [← Category.assoc,hcentral,Category.assoc,zeroSection_comp_coefficients,Category.comp_id]
  have hpAproj : IsProjectiveFactorization pA := by rw [hpA]; exact hνproj
  let : IsProper (ν ≫ q) := hνproj.isProper
  let : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace (ν ≫ q)
  have hg : F ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
      base ≫ Spec.map (CommRingCat.ofHom (RingHom.id (k[X]))) := by
    dsimp only [base]
    rw [hbase]
    change F ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
      (F ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin) ≫
        Spec.map (𝟙 (CommRingCat.of k[X]))
    rw [Spec.map_id,Category.comp_id]
  have hη : Polynomial.X ∈ (base (i (genericPoint A))).asIdeal := by
    change Polynomial.X ∈ ((i ≫ base) (genericPoint A)).asIdeal
    change i ≫ base = _ at hcentral
    rw [hcentral]
    change Polynomial.evalRingHom (0 : k) Polynomial.X ∈ ((ν ≫ q) (genericPoint A)).asIdeal
    simp
  obtain ⟨x₀,hx₀,_hx₀closed⟩ := hpoint
  obtain ⟨π₀,_z₀,hker₀,_hmax₀,hπ₀,_hnot₀,_hrest₀⟩ := hparams x₀ hx₀
  have hSNC : ∀ x : A, x ≠ genericPoint A →
      ∃ π z : Y.presheaf.stalk (i x), Prime π ∧ ¬ π ∣ z ∧
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (i x)) = Ideal.span {π,z} ∧
        RingHom.ker (i.stalkMap x).hom = Ideal.span {π} := by
    intro x hx
    obtain ⟨π,z,hker,hmax,hπ,hn,_hrest⟩ := hparams x hx
    exact ⟨π,z,hπ,hn,hmax,hker⟩
  have hnonneg := H j Y base F hg A i hpAproj (le_of_eq hAdim)
    hAnormal hη x₀ π₀ hπ₀ hker₀ hSNC
  change 0 ≤ CurveLineDegrees.degree pA ((pullback i).obj ((pullback F).obj M)) at hnonneg
  rw [hpA,CurveLineDegrees.degree_eq_of_iso (ν ≫ q) (curvePullbackIso F i ν c htriangle M)] at hnonneg
  rw [NumericalNonflatCurveDegrees.degree_pullback ν q hq (le_of_eq hdim)
    ((pullback c).obj M)
    ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback c)] at hnonneg
  have hN : (0 : ℤ) < NumericalCurveFieldDegree.degree ν := by
    exact_mod_cast NumericalCurveFieldDegree.degree_pos ν
  exact (mul_nonneg_iff_of_pos_left hN).mp hnonneg

end EnvelopeProperty.NumericalOriginalCurveDegree
