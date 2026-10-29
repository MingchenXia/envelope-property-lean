import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalOriginalCurveDegree
import EnvelopeProperty.AlgGeom.NativeNumericalNefCone
import EnvelopeProperty.AlgGeom.NativeProjectivityFromPolynomialFactorization
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberSectionLifting

/-! # The original prescribed class is genuinely nef on its actual central fibre

The whole original scheme-theoretic zero fibre is retained, including its
possibly reducible or nonreduced structure.  The numerical carrier is the
existing native real quotient tested by all original closed integral curves.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Classical Polynomial NNReal ENNReal
universe u

namespace EnvelopeProperty.NumericalOriginalCentralNef
open Scheme.Modules ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
open ProjectiveCentralFiberSectionLifting

/-- The actual scheme-theoretic central fibre of the same normalized model
is native projective, without integrality or reducedness of that fibre. -/
theorem normalizedCentralFiberProjection_isProjective
    {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
    (I J : X.NativeProductModel.IdealSheafData)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥) :
    IsProjective (pullback.snd
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin) (zeroMap k)) := by
  let : Algebra k[X] k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  apply NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization
  change IsProjectiveFactorization
    (FlatGlobalSections.structureMap (S := k)
      (X.normalizedSimultaneousIdealBlowupStructure I J hfin))
  exact ProjectiveFactorizationBaseChange.baseChange (S := k)
    (X.normalizedSimultaneousIdealBlowupStructure I J hfin)
    (X.normalizedSimultaneousIdealBlowupStructure_isProjectiveFactorization I J hfin)

/-- ORIGINAL convexity internally produces the SAME original model, norm
identity and actual central line classes in the genuine closed-curve nef cone.
The choices precede every original reference coordinate and central curve. -/
theorem exists_prescribedClass_originalCentralNef
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
        let ρ := X.normalizedSimultaneousIdealBlowupStructure I J hfin
        let i₀ := zeroInclusion ρ
        let p₀ := pullback.snd ρ (zeroMap k)
        let : IsProjective p₀ := normalizedCentralFiberProjection_isProjective X I J hfin
        ∀ j : Fin (n+1),
          let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
          let hM := X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d
          NativeRealNumericalClasses.lineClass p₀ ((Scheme.Modules.pullback i₀).obj M) (hM.pullback i₀) ∈
            NativeRealNumericalClasses.nefCone p₀ := by
  obtain ⟨r,d,hr,hd,hda,B,I,J,hfinAll,heq,H⟩ :=
    NumericalOriginalCurveDegree.exists_prescribedClass_originalCurveDegree_nonneg X hX ha hconv
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  let ρ := X.normalizedSimultaneousIdealBlowupStructure I J hfin
  let i₀ := zeroInclusion ρ
  let p₀ := pullback.snd ρ (zeroMap k)
  let : IsProjective p₀ := normalizedCentralFiberProjection_isProjective X I J hfin
  refine ⟨r,d,hr,hd,hda,B,I,J,hfinAll,heq,?_⟩
  dsimp only
  intro j
  let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
  let hM : IsInvertible M := X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d
  change NativeRealNumericalClasses.lineClass p₀ ((Scheme.Modules.pullback i₀).obj M) (hM.pullback i₀) ∈
    NativeRealNumericalClasses.nefCone p₀
  apply (NativeRealNumericalClasses.lineClass_mem_nefCone_iff p₀ _ (hM.pullback i₀)).mpr
  intro C
  let : IsIntegral C.carrier := C.integral
  let : IsClosedImmersion C.inclusion := C.closed
  let : IsClosedImmersion i₀ := inferInstance
  let q := C.structureMorphism p₀
  have hq : IsProjectiveFactorization q := C.projectiveFactorization p₀
  let : IsProper q := hq.isProper
  let : CompactSpace C.carrier := QuasiCompact.compactSpace_of_compactSpace q
  change 0 ≤ (CurveLineDegrees.degree q
    ((Scheme.Modules.pullback C.inclusion).obj ((Scheme.Modules.pullback i₀).obj M)) : ℝ)
  have hcentral : i₀ ≫ ρ = p₀ ≫ zeroMap k := pullback.condition
  have hc : (C.inclusion ≫ i₀) ≫ ρ =
      q ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
    change (C.inclusion ≫ i₀) ≫ ρ = (C.inclusion ≫ p₀) ≫ zeroMap k
    simp only [Category.assoc, hcentral]
  have hdegree := H j C.carrier q hq C.dimension (C.inclusion ≫ i₀) hc
  have he := CurveLineDegrees.degree_eq_of_iso q
    ((pullbackComp C.inclusion i₀).app M)
  change CurveLineDegrees.degree q ((Scheme.Modules.pullback C.inclusion).obj ((Scheme.Modules.pullback i₀).obj M)) =
    CurveLineDegrees.degree q ((Scheme.Modules.pullback (C.inclusion ≫ i₀)).obj M) at he
  rw [he]
  exact_mod_cast hdegree

end EnvelopeProperty.NumericalOriginalCentralNef
