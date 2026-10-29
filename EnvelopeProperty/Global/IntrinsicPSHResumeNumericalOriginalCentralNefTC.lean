import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalOriginalCentralNef

/-! # Central nefness for an explicitly given normalized PL model

`NumericalOriginalCentralNef.exists_prescribedClass_originalCentralNef` produces, from
original local `O(a)`-convexity, SOME pair of ideal sheaves `I J` on the product model whose
normalized simultaneous blowup has a nef central twisted ratio line.  The test-configuration
construction (`Local/PLOriginalModelCompatibilityTestConfiguration.lean`) needs these ideals
in the explicit form `X.nativeProductIdeal I'`, `X.nativeProductIdeal J'` of finitely generated,
parameter-scaling invariant homogeneous ideals containing a power of the parameter.

Every step of the production chain
(`exists_prescribedClass_intrinsicConvex_normalizedRatioMetric` →
`…_originalModelMetric` →
`NumericalSectionRegaugingUnitGauge.exists_prescribedClass_nativeRationalGauges`
→ `NumericalGaussCurveLineDegree.exists_prescribedClass_curveDegree_nonneg` →
`NumericalOriginalCurveDegree.exists_prescribedClass_originalCurveDegree_nonneg` →
`exists_prescribedClass_originalCentralNef`) only uses the identity
`r φ = ratio weight + B` of the chosen model, not the way its ideals were produced.  We
restate each step for a GIVEN model (the proofs are the production proofs, unchanged), and
then feed it the model of `ProjSubvariety.IsPL.exists_allProductPoint_monomial_models`,
which keeps the homogeneous ideals.

## Main results

* `NumericalOriginalCentralNef.originalCentralNef_of_ratioWeight`: for ANY ideals `I J`
  with finite Gauss logs and `r φ = ratio weight + B` on the normalized model, the central
  twisted ratio lines of class `d = r a` are nef (FHX §5, the convexity-implies-nef step of the
  proof of Lemma 5.5 / BJ22).
* `NumericalOriginalCentralNef.exists_prescribedClass_originalCentralNef_nativeProductIdeal`:
  the restatement of `exists_prescribedClass_originalCentralNef` whose ideals are
  `X.nativeProductIdeal I`, `X.nativeProductIdeal J` with `I J` finitely generated
  homogeneous, invariant under every parameter scaling, and containing parameter powers.
-/

noncomputable section
universe u

section ModelConvexity
open scoped Classical Polynomial NNReal
open CategoryTheory AlgebraicGeometry
open EnvelopeProperty.Berkovich
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich.RelativeSchemeValuedPoint
variable {k : Type u} [Field k] {n : ℕ} (X : ProjSubvariety k n)
variable (I J : X.NativeProductModel.IdealSheafData)
variable (hfin : ∀ w : X.an,
  modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)

private theorem centralNefTCAdmissibleWeight_isConvexPLOn
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a)
    (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    RelativeSchemeValuedPoint.IsConvexPLOn
      (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
      (fun y =>
        let w := X.normalizedSimultaneousBaseRestrictionAt I J hfin y
        ((φ w - (r : ℝ)⁻¹ * Real.log (w.1.1.val F : ℝ) : ℝ) : EReal)) := by
  have hc := hconv.nativeAdmissibleWeight_comp_mapOverBase X r d hr hd hda F hF hFI
    (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) Polynomial.C
    (fun c => Spectrum.gauss_val_C (Spectrum.ofValuation (1 : Valuation k ℝ≥0)) gaussRadius c)
    (X.normalizedSimultaneousOriginalProjection I J hfin)
    (X.normalizedSimultaneousOriginalProjection_over_base I J hfin)
  apply hc.congr
  intro y _
  rw [← X.nativeAnalyticHomeomorph_normalizedSimultaneousBaseRestrictionAt I J hfin y]
  simp only [nativeAdmissibleWeight,Homeomorph.symm_apply_apply]

private theorem centralNefTCPolarizedWeight_isConvexPLOn
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a) (C : ℤ)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥)
    (heq : ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
      (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt I J hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal))
    (j : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d) (hFI : F ∉ X.ideal) :
    RelativeSchemeValuedPoint.IsConvexPLOn
      (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
      (fun y => X.normalizedSimultaneousPolynomialRatioWeightAt I J hfin y
        (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF) := by
  have hc := (centralNefTCAdmissibleWeight_isConvexPLOn
      X I J hfin hconv r d hr hd hda F hF hFI).smul
    (show 0 ≤ (r : ℚ) from Nat.cast_nonneg r)
  have ht := hc.add_const (-(C : ℚ))
  apply ht.congr
  intro y hy
  have hn := (X.mem_normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F y).mp hy
  have hw :
      (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) - (C : ℝ) : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeightAt I J hfin y
        (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 := by
    have h := congrArg (fun t : EReal => t - ((C : ℝ) : EReal)) (heq y)
    simpa only [EReal.add_sub_cancel_right,← EReal.coe_sub] using h
  rw [X.normalizedSimultaneousPolynomialRatioWeightAt_eq,← hw,ProjBerk.logAbs_eq_coe_log hn]
  simp only [Rat.cast_natCast,Rat.cast_neg,Rat.cast_intCast,← EReal.coe_mul,← EReal.coe_sub,
    ← EReal.coe_add]
  apply congrArg ((↑) : ℝ → EReal)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  ring

/-- Per-model form of
`IsLocallyConvexAll.exists_prescribedClass_intrinsicConvex_originalModelMetric`: for ANY
normalized simultaneous model whose canonical ratio weight is `r φ - C`, the original polarized
`O(d) ⊗ ratio` weights, `d = r a`, are intrinsically convex on every admissible form-open. -/
theorem IsLocallyConvexAll.originalModelMetric_isConvexPLOn_of_ratioWeight
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a) (C : ℤ)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥)
    (heq : let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
      ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
      (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt I J hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((C : ℝ) : EReal)) :
    let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
    ∀ (j : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d),
      F ∉ X.ideal → RelativeSchemeValuedPoint.IsConvexPLOn
        (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
        (fun y => X.normalizedSimultaneousOriginalRatioWeightAt I J hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF) := by
  intro hfin j F hF hFI
  apply (centralNefTCPolarizedWeight_isConvexPLOn X I J hfin hconv r d hr hd hda C hfinAll heq
    j F hF hFI).congr
  intro y _
  exact (X.normalizedSimultaneousOriginalRatioWeightAt_eq I J _ y _ j d F hF).symm

end EnvelopeProperty.ProjSubvariety
end ModelConvexity

section Gauges
open AlgebraicGeometry CategoryTheory Opposite
open scoped Classical NNReal ENNReal
namespace EnvelopeProperty.NumericalSectionRegaugingUnitGauge
open Scheme.Modules SchemeLineSectionEvaluation
open NumericalSectionRegauging NumericalSectionRegaugingOriginal NumericalSectionRegaugingGauge
open Berkovich Berkovich.RelativeSchemeValuedPoint
open ProjBerk

/-- The conclusion of `exists_prescribedClass_nativeRationalGauges` for the given model
`I J` and class `d`: canonical regular-unit gauges of every nonzero generic section, with
convex original model weight. -/
def NativeRationalGaugeProp {k : Type u} [Field k] {n : ℕ}
    (X : ProjSubvariety k n) (I J : X.NativeProductModel.IdealSheafData)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
          (d : ℕ) : Prop :=
  ∀ (j : Fin (n+1)),
  let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
  ∀ (Z : Scheme.{u}) (fZ : Z ⟶ Spec (CommRingCat.of (Polynomial k)))
    [IsProper fZ] [IsIntegral Z]
    (g : Z ⟶ X.normalizedSimultaneousIdealBlowup I J hfin)
    (hg : g ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
      fZ ≫ Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))))
    (y₀ : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
    (hη : y₀.1.point = genericPoint Z)
    (ρ : Γ(genericLineModule y₀ ((pullback g).obj M), ⊤)), ρ ≠ 0 →
    ∃ (l : Fin (n+1)) (hF : (MvPolynomial.X l ^ d : MvPolynomial (Fin (n+1)) k).IsHomogeneous d),
      (X.normalizedSimultaneousBaseRestrictionAt I J hfin
        (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y₀)).1.1.val
          (MvPolynomial.X l ^ d) = 1 ∧ MvPolynomial.X l ^ d ∉ X.ideal ∧
      ∃ (U : (X.normalizedSimultaneousIdealBlowup I J hfin).Opens)
        (δ : unitObj U.toScheme ⟶ (pullback U.ι).obj M), IsIso δ ∧
        ∃ (V : Z.Opens) (_hV : V ∈ Z.affineOpens) (hVU : V ≤ g ⁻¹ᵁ U) (a : Γ(Z,V)ˣ),
          y₀.1.point ∈ V ∧
          (∀ (y : RelativeSchemeValuedPoint
              (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
            (hyη : y.1.point = genericPoint Z), ∃ hyV : y.1.point ∈ V,
              unitPullbackSectionValue g M U δ V hVU a y.1.point hyV =
                (hyη.trans hη.symm).symm ▸ ρ) ∧
          (∀ (y : RelativeSchemeValuedPoint
              (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ)
            (hyV : y.1.point ∈ V),
            -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
              ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
              (unitPullbackSectionValue g M U δ V hVU a y.1.point hyV) : ℝ≥0∞) =
              X.normalizedSimultaneousOriginalRatioWeightAt I J hfin
                (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y)
                (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin
                  (mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg y))).1
                j d (MvPolynomial.X l ^ d) hF -
                SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1) ∧
          y₀ ∈ ((mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg ⁻¹'
            X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin (MvPolynomial.X l ^ d)) ∩
              {y : RelativeSchemeValuedPoint
                (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ | y.1.point ∈ V}) ∧
          Berkovich.RelativeSchemeValuedPoint.IsConvexPLOn
            ((mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg ⁻¹'
              X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin (MvPolynomial.X l ^ d)) ∩
                {y : RelativeSchemeValuedPoint
                (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ | y.1.point ∈ V})
            (fun (y : RelativeSchemeValuedPoint
                (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ) => if hy : y.1.point ∈ V then
              -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
                ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
                (unitPullbackSectionValue g M U δ V hVU a y.1.point hy) : ℝ≥0∞)
              else ⊤)

/-- Per-model form of `exists_prescribedClass_nativeRationalGauges`: intrinsic convexity
of the original model weights of the given model produces its canonical gauges. -/
theorem nativeRationalGauges_of_originalModelConvexity {k : Type u} [Field k] [PerfectField k]
    {n : ℕ} (X : ProjSubvariety k n) (I J : X.NativeProductModel.IdealSheafData)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥) (d : ℕ)
    (hweights : let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
      ∀ (j : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) k) (hF : F.IsHomogeneous d),
        F ∉ X.ideal → RelativeSchemeValuedPoint.IsConvexPLOn
          (X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin F)
          (fun y => X.normalizedSimultaneousOriginalRatioWeightAt I J hfin y
            (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 j d F hF)) :
    NativeRationalGaugeProp X I J hfinAll
      (fun w : X.an => hfinAll (X.nativeProductGaussPoint w)) d := by
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  intro j M Z fZ hProper hIntegral g hg y₀ hη ρ hρ
  obtain ⟨l,hF,hval,hFI,U,δ,hδ,V,hV,hVU,a,hyV,hgeneric,hnorm⟩ :=
    exists_originalPolarized_nativeGauge X I J hfinAll j d Z fZ g hg y₀ hη ρ hρ
  let q : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) fZ →
      RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure I J hfin) :=
    mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg
  have hc := Berkovich.RelativeSchemeValuedPoint.IsConvexPLOn.comp_mapOverBase
      (RingHom.id (Polynomial k))
    (fun _ => rfl) g hg (hweights j (MvPolynomial.X l ^ d) hF hFI)
  have hc' := hc.add_smul_sectionLogAbs V a (-1)
  refine ⟨l,hF,hval,hFI,U,δ,hδ,V,hV,hVU,a,hyV,hgeneric,hnorm,?_,?_⟩
  · refine ⟨?_,hyV⟩
    exact (X.mem_normalizedSimultaneousAdmissibleAnalyticLocus I J hfin _ (q y₀)).mpr
      (by rw [hval]; exact one_ne_zero)
  · apply hc'.congr
    intro y hy
    have hyV : y.1.point ∈ V := hy.2
    let w : EReal := X.normalizedSimultaneousOriginalRatioWeightAt I J hfin
      (q y) (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin (q y))).1
      j d (MvPolynomial.X l ^ d) hF
    have hadj : w + (((-1 : ℚ) : ℝ) : EReal) *
        SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1 =
        w - SchemeValuedPoint.sectionLogAbs V (a : Γ(Z,V)) y.1 := by
      exact congrArg (fun t : EReal => w + t)
        (by simp only [Rat.cast_neg,Rat.cast_one,EReal.coe_neg,EReal.coe_one,neg_one_mul])
    have hcond :
        (if hx : y.1.point ∈ V then
          -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
            ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
            (unitPullbackSectionValue g M U δ V hVU a y.1.point hx) : ℝ≥0∞)
          else ⊤) =
        -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y
          ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g)
          (unitPullbackSectionValue g M U δ V hVU a y.1.point hyV) : ℝ≥0∞) :=
      dif_pos hyV
    exact hadj.trans ((hnorm y hyV).symm.trans hcond.symm)


end EnvelopeProperty.NumericalSectionRegaugingUnitGauge
end Gauges

section CurveDegree
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Filter IsLocalRing
open scoped Classical NNReal ENNReal Topology
namespace EnvelopeProperty.NumericalGaussCurveLineDegree
open Scheme.Modules SchemeLineSectionEvaluation Berkovich Berkovich.RelativeSchemeValuedPoint

private def tcFibreModule {Y : Scheme.{u}} (L : Y.Modules) (p : Y) :
    (Spec (CommRingCat.of (Y.residueField p))).Modules :=
  (pullback (Y.fromSpecResidueField p)).obj L

private theorem tcGenericAt_transport {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (p : Y) (hp : p = genericPoint Y) (q : Y) (hq : q = genericPoint Y)
    (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)) :
    (show Γ(tcFibreModule L q, ⊤) from (hq.trans hp.symm).symm ▸
      (show Γ(tcFibreModule L p, ⊤) from GaussCentralLineNormalization.genericSectionAt L p hp ρ)) =
        GaussCentralLineNormalization.genericSectionAt L q hq ρ := by
  subst p
  subst q
  rfl

private theorem tcGenericAt_ne_zero {Y : Scheme.{u}} [IsIntegral Y]
    (L : Y.Modules) (p : Y) (hp : p = genericPoint Y)
    (ρ : Γ((pullback (Y.fromSpecResidueField (genericPoint Y))).obj L, ⊤)) (hρ : ρ ≠ 0) :
    GaussCentralLineNormalization.genericSectionAt L p hp ρ ≠ 0 := by
  subst p
  exact hρ

private theorem tcWeight_toReal (a : ℝ≥0) :
    (-ENNReal.log (a : ℝ≥0∞)).toReal = -Real.log (a : ℝ) := by
  by_cases ha : a = 0
  · subst a
    simp
  · rw [ENNReal.log_of_nnreal ha,EReal.toReal_neg_eq,EReal.toReal_coe]

private theorem tcExists_frame_at {Y : Scheme.{u}} (L : Y.Modules) (hL : IsInvertible L)
    (p : Y) :
    ∃ (V : Y.Opens) (_hp : p ∈ V)
      (δ : unitObj V.toScheme ⟶ (pullback V.ι).obj L), IsIso δ := by
  obtain ⟨ι,O,hO,hframe⟩ := hL
  have hp : p ∈ iSup O := by rw [hO]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hp
  obtain ⟨e⟩ := hframe j
  exact ⟨O j,hj,e.inv,e.isIso_inv⟩

private theorem tcDegree_real_weighted_order {k : Type u} [Field k]
    {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [CompactSpace C]
    (p : C ⟶ Spec (CommRingCat.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1)
    (hNormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (L : C.Modules) (hL : IsInvertible L)
    (σ : Γ((pullback (C.fromSpecResidueField (genericPoint C))).obj L, ⊤)) (hσ : σ ≠ 0) :
    (CurveLineDegrees.degree p L : ℝ) = ∑ᶠ x : C,
      GaussCommonLeadingDegree.residueWeight p x *
          (CurveGenericSectionOrders.order L hL σ x : ℝ) := by
  let d := CurveGenericSectionOrders.order L hL σ
  let weight := fun x : C =>
    letI := AffineSchemeLocalDegrees.residueAlgebra p x
    (Module.finrank k (C.residueField x) : ℤ)
  have hfinite := CurveGenericSectionOrders.hasFiniteSupport_order p hp hdim hNormal L hL σ hσ
  let S : Finset C := hfinite.toFinset
  have hout (x : C) (hx : x ∉ S) : d x = 0 := by
    by_contra hn
    exact hx (hfinite.mem_toFinset.mpr hn)
  have hsuppZ : Function.support (fun x => d x * weight x) ⊆ (S : Set C) := by
    intro x hx
    by_contra ho
    exact hx (by
      change d x * weight x = 0
      rw [hout x ho,zero_mul])
  have hsuppR : Function.support (fun x => GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ)) ⊆
      (S : Set C) := by
    intro x hx
    by_contra ho
    exact hx (by
      change GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ) = 0
      rw [hout x ho,Int.cast_zero,mul_zero])
  have hpoint (x : C) : (d x * weight x : ℝ) =
      GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ) := by
    dsimp only [weight,GaussCommonLeadingDegree.residueWeight]
    push_cast
    ring
  have heuler := CurveGenericSectionOrders.degree_eq_finsum_order p hp hdim hNormal L hL σ hσ
  change CurveLineDegrees.degree p L = ∑ᶠ x : C,d x * weight x at heuler
  rw [finsum_eq_sum_of_support_subset _ hsuppZ] at heuler
  change (CurveLineDegrees.degree p L : ℝ) =
      ∑ᶠ x : C,GaussCommonLeadingDegree.residueWeight p x * (d x : ℝ)
  rw [finsum_eq_sum_of_support_subset _ hsuppR,heuler]
  push_cast
  exact Finset.sum_congr rfl (fun x _ => hpoint x)

private theorem tcPaperRadius_pos : 0 < ProjBerk.gaussRadius := by
  change (0 : ℝ) < Real.exp (-1)
  exact Real.exp_pos _

private theorem tcPaperRadius_lt_one : ProjBerk.gaussRadius < 1 := by
  change Real.exp (-1) < (1 : ℝ)
  exact Real.exp_lt_one_iff.mpr (by norm_num)

open ProjBerk

/-- The conclusion of `exists_prescribedClass_curveDegree_nonneg` for the given model. -/
def CurveDegreeProp {k : Type u} [Field k] {n : ℕ}
    (X : ProjSubvariety k n) (I J : X.NativeProductModel.IdealSheafData)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
          (d : ℕ) : Prop :=
  ∀ (j : Fin (n+1)),
  let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
  ∀ (Y : Scheme.{u}) (base : Y ⟶ Spec (CommRingCat.of (Polynomial k)))
    [IsProper base] [IsDominant base] [IsIntegral Y]
    (g : Y ⟶ X.normalizedSimultaneousIdealBlowup I J hfin)
    (_hg : g ≫ X.normalizedSimultaneousIdealBlowupStructure I J hfin =
      base ≫ Spec.map (CommRingCat.ofHom (RingHom.id (Polynomial k))))
    (C : Scheme.{u}) [IsIntegral C] (i : C ⟶ Y) [IsClosedImmersion i]
    (hp : IsProjectiveFactorization
      (i ≫ base ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
    (_hdim : topologicalKrullDim C ≤ 1)
    (_hNormal : ∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x))
    (_hη : Polynomial.X ∈ (base (i (genericPoint C))).asIdeal)
    (x₀ : C) (π₀ : Y.presheaf.stalk (i x₀)) (_hπ₀ : Prime π₀)
    (_hker₀ : RingHom.ker (i.stalkMap x₀).hom = Ideal.span {π₀})
    (_hSNC : ∀ x : C, x ≠ genericPoint C →
      ∃ π z : Y.presheaf.stalk (i x), Prime π ∧ ¬ π ∣ z ∧
        maximalIdeal (Y.presheaf.stalk (i x)) = Ideal.span {π,z} ∧
        RingHom.ker (i.stalkMap x).hom = Ideal.span {π}),
    let pC := i ≫ base ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    letI : IsProper pC := hp.isProper
    letI : LocallyOfFiniteType pC := inferInstance
    letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace pC
    0 ≤ CurveLineDegrees.degree pC ((pullback i).obj ((pullback g).obj M))

/-- Per-model form of `exists_prescribedClass_curveDegree_nonneg`. -/
theorem curveDegree_nonneg_of_nativeRationalGauges
    {k : Type u} [Field k] [PerfectField k] {n : ℕ}
    (X : ProjSubvariety k n) (I J : X.NativeProductModel.IdealSheafData)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥) (d : ℕ)
    (Hgauge : NumericalSectionRegaugingUnitGauge.NativeRationalGaugeProp X I J hfinAll
      (fun w : X.an => hfinAll (X.nativeProductGaussPoint w)) d) :
    CurveDegreeProp X I J (fun w : X.an => hfinAll (X.nativeProductGaussPoint w)) d := by
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  intro j M Y base hProper hDominant hIntegral g hg C hC i hClosed hp hdim hNormal hη x₀ π₀ hπ₀
      hker₀ hSNC
  let pC := i ≫ base ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian base
  let : IsProper pC := hp.isProper
  let : LocallyOfFiniteType pC := inferInstance
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian pC
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace pC
  let L : Y.Modules := (pullback g).obj M
  let hL : IsInvertible L :=
      (X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback g
  let LC : C.Modules := (pullback i).obj L
  let hLC : IsInvertible LC := hL.pullback i
  obtain ⟨U₀,hηU₀,δ₀,hδ₀⟩ := tcExists_frame_at L hL (i (genericPoint C))
  let : IsIso δ₀ := hδ₀
  let : Nonempty U₀ := ⟨⟨i (genericPoint C),hηU₀⟩⟩
  let σ := CentralGenericLineSectionLift.closedGenericSection i L U₀ hηU₀ δ₀
  have hσ : σ ≠ 0 := (NumericalGaussCurveSectionOrders.exists_twoFrame_intrinsicOrder
    (base := base) gaussModelCoefficient_le_one i L hL U₀ hηU₀ δ₀ x₀).1
  obtain ⟨y₀,hy₀,hcenter₀,U,hηU,δ,hδ,hcentral,hU,ρ,hρ,hρne,hOne⟩ :=
    GaussCentralLineNormalization.exists_prescribed_section_unit_norm base i x₀ π₀ hπ₀ hker₀
        hη L hL σ hσ
  let : IsIso δ := hδ
  let : Nonempty U := hU
  let ρ₀ : Γ(genericLineModule y₀ L, ⊤) :=
    GaussCentralLineNormalization.genericSectionAt L y₀.1.point hy₀ ρ
  have hρ₀ : ρ₀ ≠ 0 := tcGenericAt_ne_zero L y₀.1.point hy₀ ρ hρne
  obtain ⟨l,hF,hval,hFI,UN,δN,hδN,Vg,hVg,hVU,unit,hyVg,hgeneric,hnorm,huy₀,hu⟩ :=
    Hgauge j Y base g hg y₀ hy₀ ρ₀ hρ₀
  let dom := ((mapOverBase (RingHom.id (Polynomial k)) (fun _ => rfl) g hg ⁻¹'
    X.normalizedSimultaneousAdmissibleAnalyticLocus I J hfin (MvPolynomial.X l ^ d)) ∩
      {y : RelativeSchemeValuedPoint (gaussValuation
          (1 : Valuation k ℝ≥0) gaussRadius) base | y.1.point ∈ Vg})
  let w :
      RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) base → EReal :=
    fun y => if hy : y.1.point ∈ Vg then
      -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y hL
        (NumericalSectionRegaugingUnitGauge.unitPullbackSectionValue
            g M UN δN Vg hVU unit y.1.point hy) : ℝ≥0∞)
      else ⊤
  change Berkovich.RelativeSchemeValuedPoint.IsConvexPLOn dom w at hu
  have hw (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) base)
      (hy : y.1.point = genericPoint Y) :
      w y = -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y hL
        (GaussCentralLineNormalization.genericSectionAt L y.1.point hy ρ) : ℝ≥0∞) := by
    obtain ⟨hyV,hvalue⟩ := hgeneric y hy
    have htransport := tcGenericAt_transport L y₀.1.point hy₀ y.1.point hy ρ
    have hs := hvalue.trans htransport
    change (if hyV : y.1.point ∈ Vg then _ else ⊤) = _
    rw [dif_pos hyV]
    exact congrArg (fun s : Γ(genericLineModule y L, ⊤) =>
      -ENNReal.log (modelLineNorm gaussModelCoefficient_le_one y hL s : ℝ≥0∞)) hs
  have hwreal (y : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) base)
      (hy : y.1.point = genericPoint Y) :
      (w y).toReal = -Real.log ((modelLineNorm gaussModelCoefficient_le_one y hL
        (GaussCentralLineNormalization.genericSectionAt L y.1.point hy ρ) : ℝ≥0) : ℝ) :=
    (congrArg EReal.toReal (hw y hy)).trans (tcWeight_toReal _)
  have hw₀ : w y₀ = 0 := (hw y₀ hy₀).trans (by rw [hOne]; simp)
  let : IsDiscreteValuationRing (Y.presheaf.stalk (i (genericPoint C))) :=
    GaussCommonVerticalStalks.componentStalk_isDVR i x₀ π₀ hπ₀ hker₀
  obtain ⟨y,hy,hcenter,Hcommon⟩ :=
    GaussCommonLeadingDegree.exists_common_leading_degree_nonneg i base hp x₀ π₀ hπ₀ hker₀ hη hdim
        hNormal hu
  have hyy₀ : y = y₀ := GaussCommonVerticalPoints.eq_of_same_verticalDVRCenter
    (f := base) (i (genericPoint C)) hη gaussRadius tcPaperRadius_pos tcPaperRadius_lt_one y y₀
        hcenter hcenter₀
  have hyU : y ∈ dom := by rw [hyy₀]; exact huy₀
  have hwy : w y = 0 := hyy₀ ▸ hw₀
  obtain ⟨W,hW,hyW,hWU,V,hWV,m,units,K,hK,ϖ,e,Ut,A,UF,
    hϖ,he,htfac,hfac,hactive,hform,hbase,hfinite,hgen,hsum,Hlocal⟩ := Hcommon hyU
  let hVy := hWV y hyW
  let : Nonempty V := ⟨⟨y.1.point,hVy⟩⟩
  let β := fun j : (Fin m → ℚ) × ℚ => unitTropAffine units j y hVy
  let direction := fun (j : (Fin m → ℚ) × ℚ) (x : C) =>
    -(∑ l : Fin m, (j.1 l : ℝ) * ((C.ord (i.stalkMap (genericPoint C) (UF l)) x : ℝ) -
      (A l : ℝ) / (e : ℝ) * (C.ord (i.stalkMap (genericPoint C) Ut) x : ℝ)))
  let D := FiniteAffineMax.activeSlope K hK β direction
  have hDgeneric : D (genericPoint C) = 0 := hgen
  have hD (x : C) : D x = (CurveGenericSectionOrders.order LC hLC σ x : ℝ) := by
    by_cases hx : x = genericPoint C
    · subst x
      rw [hDgeneric,CurveGenericSectionOrders.order_generic,Int.cast_zero]
    · obtain ⟨π,z,hπ,hz,hm,hker⟩ := hSNC x hx
      obtain ⟨ht,hπt,hqy,c,hparam,htail,hlim⟩ := Hlocal x hx π z hπ hker hz hm
      let q := fun t : ℕ => GaussRegularSurfaceConvexProfiles.nativeWeightedPoint base (i x)
        π z hπ hz hm (t+1) (Nat.zero_lt_succ t) ht hπt gaussRadius tcPaperRadius_pos
            tcPaperRadius_lt_one
      let ε := fun t : ℕ => GaussRegularSurfaceConvexProfiles.nativeScale base (i x)
        π z hπ hz hm gaussRadius (t+1) (Nat.zero_lt_succ t)
      obtain ⟨T,hNorm⟩ := NumericalGaussCurveOrderSlopes.exists_eventual_modelNorm_intrinsicOrder
        i base L hL U hηU δ x π z hπ hz hm hker hdim hx ht hπt
          gaussRadius tcPaperRadius_pos tcPaperRadius_lt_one
      have hnormTail : ∀ᶠ t : ℕ in atTop,
          -Real.log ((modelLineNorm gaussModelCoefficient_le_one (q t) hL
            (GaussCentralLineNormalization.genericSectionAt L (q t).1.point
              (GaussRegularSurfaceConvexProfiles.nativeWeightedPoint_underlying base (i x)
                π z hπ hz hm (t+1) (Nat.zero_lt_succ t) ht hπt gaussRadius tcPaperRadius_pos
                    tcPaperRadius_lt_one) ρ) : ℝ≥0) : ℝ) =
            ε t * (CurveGenericSectionOrders.order LC hLC σ x : ℝ) := by
        filter_upwards [eventually_ge_atTop T] with t htT
        have h := hNorm (t+1) (Nat.zero_lt_succ t) (Nat.lt_succ_of_le htT)
        rw [← hρ,hcentral] at h
        exact h
      obtain ⟨t,hprofile,hnormValue⟩ := (htail.and hnormTail).exists
      have hyq := GaussRegularSurfaceConvexProfiles.nativeWeightedPoint_underlying base (i x)
        π z hπ hz hm (t+1) (Nat.zero_lt_succ t) ht hπt gaussRadius tcPaperRadius_pos
            tcPaperRadius_lt_one
      have hε : 0 < ε t := GaussRegularSurfaceConvexProfiles.nativeScale_pos base (i x)
        π z hπ hz hm ht hπt gaussRadius tcPaperRadius_pos tcPaperRadius_lt_one (t+1)
            (Nat.zero_lt_succ t)
      have hquot := hprofile.2
      change ((w (q t)).toReal - (w y).toReal) / ε t = D x at hquot
      rw [hwy,EReal.toReal_zero,sub_zero,hwreal (q t) hyq,hnormValue] at hquot
      have hcancel : (ε t * (CurveGenericSectionOrders.order LC hLC σ x : ℝ)) / ε t =
          (CurveGenericSectionOrders.order LC hLC σ x : ℝ) := by field_simp [hε.ne']
      exact hquot.symm.trans hcancel
  have hdegree := tcDegree_real_weighted_order pC hp hdim hNormal LC hLC σ hσ
  have hnonneg : 0 ≤ (CurveLineDegrees.degree pC LC : ℝ) := by
    calc
      0 ≤ ∑ᶠ x : C, GaussCommonLeadingDegree.residueWeight pC x * D x := hsum
      _ = ∑ᶠ x : C, GaussCommonLeadingDegree.residueWeight pC x *
          (CurveGenericSectionOrders.order LC hLC σ x : ℝ) :=
        finsum_congr (fun x =>
            congrArg (fun t : ℝ => GaussCommonLeadingDegree.residueWeight pC x * t) (hD x))
      _ = (CurveLineDegrees.degree pC LC : ℝ) := hdegree.symm
  exact_mod_cast hnonneg

end EnvelopeProperty.NumericalGaussCurveLineDegree
end CurveDegree

section OriginalCurveDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical Polynomial NNReal ENNReal
namespace EnvelopeProperty.NumericalOriginalCurveDegree
open Scheme.Modules ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem tcZeroSection_comp_coefficients {k : Type u} [Field k] :
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

private def tcCurvePullbackIso {N Y C A : Scheme.{u}}
    (F : Y ⟶ N) (i : A ⟶ Y) (ν : A ⟶ C) (c : C ⟶ N)
    (h : i ≫ F = ν ≫ c) (M : N.Modules) :
    (pullback i).obj ((pullback F).obj M) ≅
      (pullback ν).obj ((pullback c).obj M) :=
  (pullbackComp i F).app M ≪≫ (pullbackCongr h).app M ≪≫
    ((pullbackComp ν c).app M).symm


/-- The conclusion of `exists_prescribedClass_originalCurveDegree_nonneg` for the given model. -/
def OriginalCurveDegreeProp {k : Type u} [Field k] {n : ℕ}
    (X : ProjSubvariety k n) (I J : X.NativeProductModel.IdealSheafData)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
          (d : ℕ) : Prop :=
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
    0 ≤ CurveLineDegrees.degree q ((pullback c).obj M)

/-- Per-model form of `exists_prescribedClass_originalCurveDegree_nonneg`. -/
theorem originalCurveDegree_nonneg_of_curveDegree
    {k : Type u} [Field k] [PerfectField k] [Infinite k] {n : ℕ}
    (X : ProjSubvariety k n) (hX : X.IsProjNormal) (I J : X.NativeProductModel.IdealSheafData)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥) (d : ℕ)
    (H : NumericalGaussCurveLineDegree.CurveDegreeProp X I J
      (fun w : X.an => hfinAll (X.nativeProductGaussPoint w)) d) :
    OriginalCurveDegreeProp X I J (fun w : X.an => hfinAll (X.nativeProductGaussPoint w)) d := by
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
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
    rw [← Category.assoc,hcentral,Category.assoc,tcZeroSection_comp_coefficients,Category.comp_id]
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
  rw [hpA,CurveLineDegrees.degree_eq_of_iso (ν ≫ q)
      (tcCurvePullbackIso F i ν c htriangle M)] at hnonneg
  rw [NumericalNonflatCurveDegrees.degree_pullback ν q hq (le_of_eq hdim)
    ((pullback c).obj M)
    ((X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d).pullback c)] at hnonneg
  have hN : (0 : ℤ) < NumericalCurveFieldDegree.degree ν := by
    exact_mod_cast NumericalCurveFieldDegree.degree_pos ν
  exact (mul_nonneg_iff_of_pos_left hN).mp hnonneg

end EnvelopeProperty.NumericalOriginalCurveDegree
end OriginalCurveDegree

section CentralNef
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Classical Polynomial NNReal ENNReal
namespace EnvelopeProperty.NumericalOriginalCentralNef
open Scheme.Modules ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
open ProjectiveCentralFiberSectionLifting
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Per-model form of `exists_prescribedClass_originalCentralNef`: nonnegative degree on
every original central curve is nefness of the whole central class. -/
theorem originalCentralNef_of_originalCurveDegree
    {k : Type u} [Field k] {n : ℕ}
    (X : ProjSubvariety k n) (I J : X.NativeProductModel.IdealSheafData)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥) (d : ℕ)
    (H : NumericalOriginalCurveDegree.OriginalCurveDegreeProp X I J
      (fun w : X.an => hfinAll (X.nativeProductGaussPoint w)) d) :
    let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
    let ρ := X.normalizedSimultaneousIdealBlowupStructure I J hfin
    let i₀ := zeroInclusion ρ
    let p₀ := pullback.snd ρ (zeroMap k)
    let : IsProjective p₀ := normalizedCentralFiberProjection_isProjective X I J hfin
    ∀ j : Fin (n+1),
      let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
      let hM := X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d
      NativeRealNumericalClasses.lineClass p₀ ((Scheme.Modules.pullback i₀).obj M)
          (hM.pullback i₀) ∈
        NativeRealNumericalClasses.nefCone p₀ := by
  intro hfin
  let ρ := X.normalizedSimultaneousIdealBlowupStructure I J hfin
  let i₀ := zeroInclusion ρ
  let p₀ := pullback.snd ρ (zeroMap k)
  let : IsProjective p₀ := normalizedCentralFiberProjection_isProjective X I J hfin
  dsimp only
  intro j
  let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
  let hM : IsInvertible M := X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d
  change NativeRealNumericalClasses.lineClass p₀ ((Scheme.Modules.pullback i₀).obj M)
      (hM.pullback i₀) ∈
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
  change CurveLineDegrees.degree q
      ((Scheme.Modules.pullback C.inclusion).obj ((Scheme.Modules.pullback i₀).obj M)) =
    CurveLineDegrees.degree q ((Scheme.Modules.pullback (C.inclusion ≫ i₀)).obj M) at he
  rw [he]
  exact_mod_cast hdegree

/-- Convexity implies central nefness for a GIVEN model: if the normalized simultaneous
blowup of `I J` has canonical ratio weight `r φ - B` for a locally `O(a)`-convex `φ`, then
the central restrictions of its twisted ratio lines of class `d = r a` are nef. -/
theorem originalCentralNef_of_ratioWeight
    {k : Type u} [Field k] [PerfectField k] [Infinite k] {n : ℕ}
    (X : ProjSubvariety k n) (hX : X.IsProjNormal)
    {a : ℚ} {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ)
    (r d : ℕ) (hr : 0 < r) (hd : 0 < d) (hda : (d : ℚ) = r*a) (B : ℤ)
    (I J : X.NativeProductModel.IdealSheafData)
    (hfinAll : ∀ z : RelativeSchemeValuedPoint
        (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog I gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one z ≠ ⊥)
    (heq : let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
      ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
          (X.normalizedSimultaneousIdealBlowupStructure I J hfin),
        (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt I J hfin y) : ℝ) : EReal) =
          X.normalizedSimultaneousRatioWeightAt I J hfin y
            (hfinAll (X.normalizedSimultaneousProductPointAt I J hfin y)).1 + ((B : ℝ) : EReal)) :
    let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
    let ρ := X.normalizedSimultaneousIdealBlowupStructure I J hfin
    let i₀ := zeroInclusion ρ
    let p₀ := pullback.snd ρ (zeroMap k)
    let : IsProjective p₀ := normalizedCentralFiberProjection_isProjective X I J hfin
    ∀ j : Fin (n+1),
      let M := X.normalizedSimultaneousTwistedRatioLine I J hfin j d
      let hM := X.normalizedSimultaneousTwistedRatioLine_isInvertible I J hfin j d
      NativeRealNumericalClasses.lineClass p₀ ((Scheme.Modules.pullback i₀).obj M)
          (hM.pullback i₀) ∈
        NativeRealNumericalClasses.nefCone p₀ :=
  originalCentralNef_of_originalCurveDegree X I J hfinAll d
    (NumericalOriginalCurveDegree.originalCurveDegree_nonneg_of_curveDegree X hX I J hfinAll d
      (NumericalGaussCurveLineDegree.curveDegree_nonneg_of_nativeRationalGauges X I J hfinAll d
        (NumericalSectionRegaugingUnitGauge.nativeRationalGauges_of_originalModelConvexity X I J
          hfinAll d
          (hconv.originalModelMetric_isConvexPLOn_of_ratioWeight X I J r d hr hd hda B
            hfinAll heq))))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- `exists_prescribedClass_originalCentralNef` with its ideals EXPOSED: the model is the
normalized simultaneous blowup of `X.nativeProductIdeal I`, `X.nativeProductIdeal J` for
finitely generated homogeneous ideals `I J` of `k[t][x₀,…,xₙ]` which are invariant under every
coefficient extension of the parameter scaling `t ↦ c t` and contain powers `t^A₁`, `t^A₂` of
the parameter. These are exactly the inputs of the native test configuration
`ProjSubvariety.normalizedSimultaneousNativeTestConfiguration`. -/
theorem exists_prescribedClass_originalCentralNef_nativeProductIdeal
    {k : Type u} [Field k] [PerfectField k] [Infinite k] {n : ℕ}
    (X : ProjSubvariety k n) (hX : X.IsProjNormal)
    {a : ℚ} (ha : 0 < a) {φ : X.an → ℝ} (hconv : X.IsLocallyConvexAll a φ) :
    ∃ (r d : ℕ) (_hr : 0 < r) (_hd : 0 < d), (d : ℚ) = r*a ∧
      ∃ (B : ℤ) (I J : HomogeneousIdeal (ProjectiveGrading k[X] n))
        (_hfgI : I.toIdeal.FG) (_hfgJ : J.toIdeal.FG)
        (_hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (c : Sˣ),
          (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
            (MvPolynomial.map (parameterScaleHom (c : S))) =
              I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
        (_hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (c : Sˣ),
          (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
            (MvPolynomial.map (parameterScaleHom (c : S))) =
              J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
        (A₁ A₂ : ℕ) (_hA₁pos : 0 < A₁) (_hA₂pos : 0 < A₂)
        (_hA₁ : MvPolynomial.C (Polynomial.X ^ A₁) ∈ I.toIdeal)
        (_hA₂ : MvPolynomial.C (Polynomial.X ^ A₂) ∈ J.toIdeal)
        (hfinAll : ∀ z : RelativeSchemeValuedPoint
            (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
          modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one z ≠ ⊥ ∧
          modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one z ≠ ⊥),
        let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
        (∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
            (X.normalizedSimultaneousIdealBlowupStructure
              (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin),
          (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt
              (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin y) : ℝ) : EReal) =
            X.normalizedSimultaneousRatioWeightAt (X.nativeProductIdeal I)
              (X.nativeProductIdeal J) hfin y
              (hfinAll (X.normalizedSimultaneousProductPointAt
                (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin y)).1 +
              ((B : ℝ) : EReal)) ∧
        let ρ := X.normalizedSimultaneousIdealBlowupStructure
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
        let i₀ := zeroInclusion ρ
        let p₀ := pullback.snd ρ (zeroMap k)
        let : IsProjective p₀ := normalizedCentralFiberProjection_isProjective X
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
        ∀ j : Fin (n+1),
          let M := X.normalizedSimultaneousTwistedRatioLine
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j d
          let hM := X.normalizedSimultaneousTwistedRatioLine_isInvertible
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin j d
          NativeRealNumericalClasses.lineClass p₀ ((Scheme.Modules.pullback i₀).obj M)
              (hM.pullback i₀) ∈
            NativeRealNumericalClasses.nefCone p₀ := by
  have hPL : X.IsPL φ := (hconv.isLocallyConvex ha).isPL
  have hscaled : X.IsPL (fun w => (a.den : ℝ)*φ w) := by
    simpa only [Rat.cast_natCast] using hPL.smul (a.den : ℚ)
  obtain ⟨s,hs,B,I,J,hfgI,hfgJ,⟨A₁,hA₁pos,hA₁⟩,⟨A₂,hA₂pos,hA₂⟩,⟨SI,_hSI,hspanI⟩,
      ⟨SJ,_hSJ,hspanJ⟩,hAll⟩ :=
    hscaled.exists_allProductPoint_monomial_models X
  have hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (c : Sˣ),
      (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
        (MvPolynomial.map (parameterScaleHom (c : S))) =
          I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)) := by
    intro S _ f c
    rw [hspanI]
    exact parameterScale_span_baseChanged_monomials_eq f c
      (SI : Set (MvPolynomial (Fin (n+1)) k × ℕ))
  have hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (c : Sˣ),
      (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
        (MvPolynomial.map (parameterScaleHom (c : S))) =
          J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)) := by
    intro S _ f c
    rw [hspanJ]
    exact parameterScale_span_baseChanged_monomials_eq f c
      (SJ : Set (MvPolynomial (Fin (n+1)) k × ℕ))
  let hfinAll : ∀ z : RelativeSchemeValuedPoint
      (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius) X.nativeProductStructure,
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one z ≠ ⊥ ∧
      modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one z ≠ ⊥ :=
    fun z => (hAll z).1
  let hfin := fun w : X.an => hfinAll (X.nativeProductGaussPoint w)
  have heqs (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :
      (((s : ℝ)*((a.den : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin y)) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin y)).1 +
          ((B : ℝ) : EReal) := by
    rw [X.normalizedSimultaneousRatioWeightAt_eq]
    exact (hAll _).2
  let r := s*a.den
  let d := s*a.num.toNat
  have hnum : 0 < a.num.toNat := by have h := Rat.num_pos.mpr ha; omega
  have hr : 0 < r := Nat.mul_pos hs a.den_pos
  have hd : 0 < d := Nat.mul_pos hs hnum
  have hda : (d : ℚ) = r*a := by
    have hp : (a.num.toNat : ℚ) = a.den*a := by
      rw [mul_comm, Rat.mul_den_eq_num]
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_pos.mpr ha).le
    dsimp only [r,d]
    rw [Nat.cast_mul, Nat.cast_mul, hp, mul_assoc]
  have heq (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :
      (((r : ℝ)*φ (X.normalizedSimultaneousBaseRestrictionAt
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin y) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin y
          (hfinAll (X.normalizedSimultaneousProductPointAt
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin y)).1 +
          ((B : ℝ) : EReal) := by
    simpa only [r, Nat.cast_mul, mul_assoc] using heqs y
  refine ⟨r,d,hr,hd,hda,B,I,J,hfgI,hfgJ,hI,hJ,A₁,A₂,hA₁pos,hA₂pos,hA₁,hA₂,hfinAll,?_⟩
  intro hfin'
  exact ⟨heq, originalCentralNef_of_ratioWeight X hX hconv r d hr hd hda B
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfinAll heq⟩

end EnvelopeProperty.NumericalOriginalCentralNef
end CentralNef
