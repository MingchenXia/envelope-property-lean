import EnvelopeProperty.Char0.RoundedSncIdealSheaf
import EnvelopeProperty.Char0.NativeAffineOpenJacobian
import EnvelopeProperty.Char0.NativeSNCOriginalGenerators
import EnvelopeProperty.Char0.NativeSNCIntegralTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EnvelopeProperty.Char0.NativeBPRoundedMultiplierCriterion
open CategoryTheory AlgebraicGeometry ComplexSchemes Filter MeasureTheory
open ComplexGeometry ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms NativeEtaleCoordinates NativeSNCOriginalGenerators
open NativeSNCCharts NativeAffineOpenJacobian NativePreferredJacobian
open NativeSNCIntegralTransport NativeSNCMultiplierCriterion NativeMultiplierGermTransform
open WeightedHolomorphicGermIdealIntegralClosure
open scoped Topology

/-- The actual original finite tuple in the actual source centered chart has a genuine
quasi-PSH generator logarithm, including its original common zeros. -/
theorem centeredGeneratorLog_quasiPSH {R : Type} [CommRing R] {Y : Scheme}
    (f : Spec (.of R) ⟶ Spec (.of ℂ)) (π : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n (π ≫ f)] [SmoothOfRelativeDimension n f]
    [IsSeparated (π ≫ f)] [QuasiCompact (π ≫ f)] [IsSeparated f] [QuasiCompact f]
    (p : SchemeComplexPoint (π ≫ f)) {s : ℕ} (a : Fin s → R) :
    QuasiPlurisubharmonicAt (generatorLog (fun i => centeredOriginalFunction f π n p (a i))) 0 := by
  let G : Fin s → ComplexModel n → ℂ := fun i => centeredOriginalFunction f π n p (a i)
  have hG : ∀ i, ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (G i) z :=
    fun i => centeredOriginalFunction_holomorphic f π n p (a i)
  obtain ⟨U,hUmem,hU,h0⟩ := mem_nhds_iff.mp (Filter.eventually_all.mpr hG)
  have hGens : HolomorphicGeneratorsAt G (0 : ComplexModel n) :=
    ⟨U,hU,h0,fun i z hz => (hUmem hz i).differentiableWithinAt⟩
  simpa only [EReal.coe_one, one_mul] using
    (plurisubharmonicAt_scaled_generatorLog hGens (show (0 : ℝ) < 1 by norm_num)).quasiPlurisubharmonicAt

private theorem coefficientGerm_congr {B : Type} [CommRing B]
    (f g : Spec (.of B) ⟶ Spec (.of ℂ)) (h : f = g) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n g]
    (p : SchemeComplexPoint f) (q : SchemeComplexPoint g) (hpq : p.val = q.val) :
    coefficientGerm f n p = coefficientGerm g n q := by
  subst g
  have he : p = q := Subtype.ext hpq
  subst q
  rfl

private theorem coordinateGermEquiv_congr {B : Type} [CommRing B]
    (f g : Spec (.of B) ⟶ Spec (.of ℂ)) (h : f = g) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n g]
    (p : SchemeComplexPoint f) (q : SchemeComplexPoint g) (hpq : p.val = q.val)
    (t : Fin n → B)
    (htf : letI := affinePointFieldAlgebra f
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (htg : letI := affinePointFieldAlgebra g
      (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale) :
    coordinateGermEquiv f n p t htf = coordinateGermEquiv g n q t htg := by
  subst g
  have he : p = q := Subtype.ext hpq
  subst q
  rfl

variable {R : Type} [CommRing R] [IsDomain R] [hCR : Algebra ℂ R] (n : ℕ)
variable [hsm : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
  (I : Ideal R) (hI : I ≠ ⊥)

private instance bpSmooth : SmoothOfRelativeDimension n
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  affinePrincipalization_smoothOfRelativeDimension (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI

private instance bpProper : IsProper
    (Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite := by
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := SmoothOfRelativeDimension.smooth n (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
  let : IsLocallyNoetherian (Spec (.of R)) := LocallyOfFiniteType.isLocallyNoetherian (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
  let : IsLocallyNoetherian (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI).X.left := by
    change IsLocallyNoetherian (Spec (.of R))
    infer_instance
  exact (Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).isProper_composite

private instance bpSeparated : IsSeparated
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite
  have hπ : IsSeparated π := inferInstance
  have hf : IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := inferInstance
  exact IsSeparated.stableUnderComposition.comp_mem π (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) hπ hf

private instance bpQuasiCompact : QuasiCompact
    ((Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := by
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite
  let : IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := isAffineHom_of_isAffine (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
  have hf : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) := inferInstance
  exact @quasiCompact_comp _ _ _ π (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) inferInstance hf

omit hsm in
private instance restrictedAffine {Y : Scheme} (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    IsAffineHom ((U.2.fromSpec ≫ π) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) :=
  isAffineHom_of_isAffine _

omit hsm in
private instance restrictedQC {Y : Scheme} (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    QuasiCompact ((U.2.fromSpec ≫ π) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := by
  let : IsAffineHom ((U.2.fromSpec ≫ π) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := isAffineHom_of_isAffine _
  exact quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU => (hU.preimage _).isCompact

omit hsm in
private instance restrictedSeparated {Y : Scheme} (π : Y ⟶ Spec (.of R)) (U : Y.affineOpens) :
    IsSeparated ((U.2.fromSpec ≫ π) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := by
  let : IsAffineHom ((U.2.fromSpec ≫ π) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := isAffineHom_of_isAffine _
  infer_instance

private instance affineRestrictedSmooth {Y : Scheme} (π : Y ⟶ Spec (.of R))
    [SmoothOfRelativeDimension n (π ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))] (U : Y.affineOpens) :
    SmoothOfRelativeDimension n ((U.2.fromSpec ≫ π) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))) := by
  rw [Category.assoc]
  exact (Nat.zero_add n) ▸
    (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) (π ≫ (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))))



private theorem order_comp {κ : Type} [Fintype κ] (ι : κ → Fin n)
    (hι : Function.Injective ι) (b : κ → ℕ) (F : ℕ → ℕ) (hF : F 0 = 0) (j : Fin n) :
    F (coordinateOrder ι b j) = coordinateOrder ι (fun i => F (b i)) j := by
  classical
  by_cases hj : ∃ i, ι i = j
  · obtain ⟨i,rfl⟩ := hj
    have hf : Finset.univ.filter (fun k => ι k = ι i) = {i} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact hι.eq_iff
    simp only [coordinateOrder,hf,Finset.sum_singleton]
  · have hf : Finset.univ.filter (fun k => ι k = j) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ hi
      exact hj ⟨i,hi⟩
    simp only [coordinateOrder,hf,Finset.sum_empty,hF]

private theorem order_prod {κ M : Type} [Fintype κ] [CommMonoid M]
    (ι : κ → Fin n) (b : κ → ℕ) (x : Fin n → M) :
    (∏ j, x j ^ coordinateOrder ι b j) = ∏ i, x (ι i) ^ b i := by
  classical
  calc
    _ = ∏ j, ∏ i ∈ (Finset.univ.filter fun i => ι i = j), x j ^ b i := by
      simp only [coordinateOrder, Finset.prod_pow_eq_pow_sum]
    _ = ∏ j, ∏ i ∈ (Finset.univ.filter fun i => ι i = j), x (ι i) ^ b i := by
      apply Finset.prod_congr rfl
      intro j _
      apply Finset.prod_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.prod_fiberwise Finset.univ ι (fun i => x (ι i) ^ b i)

private theorem floor_rat_mul (r : ℚ) (k : ℕ) :
    ⌊(r : ℝ) * (k : ℝ)⌋₊ = ⌊r * (k : ℚ)⌋₊ := by
  rw [← Int.floor_toNat, ← Int.floor_toNat]
  congr 1
  simpa only [Rat.cast_mul,Rat.cast_natCast] using Rat.floor_cast (α := ℝ) (r * (k : ℚ))

private theorem rounded_order_prod {κ : Type} [Fintype κ] (ι : κ → Fin n)
    (hι : Function.Injective ι) (b : κ → ℕ) (r : ℚ) :
    (∏ j, HironakaHolomorphicJetMonomialSpan.coordinateGerm j ^
      roundedOrder (fun i => (coordinateOrder ι b i : ℝ)) (coordinateOrder ι (fun _ => 0)) (r : ℝ) j) =
      ∏ i, HironakaHolomorphicJetMonomialSpan.coordinateGerm (ι i) ^ ⌊r * (b i : ℚ)⌋₊ := by
  have hexp (j : Fin n) :
      roundedOrder (fun i => (coordinateOrder ι b i : ℝ)) (coordinateOrder ι (fun _ => 0)) (r : ℝ) j =
        coordinateOrder ι (fun i => ⌊r * (b i : ℚ)⌋₊) j := by
    have hz : coordinateOrder ι (fun _ => 0) j = 0 := by simp only [coordinateOrder,Finset.sum_const_zero]
    rw [roundedOrder,hz,Nat.sub_zero,order_comp n ι hι b (fun k => ⌊(r : ℝ)*(k : ℝ)⌋₊) (by simp)]
    apply congrArg (fun b => coordinateOrder ι b j)
    funext i
    exact floor_rat_mul r (b i)
  simp_rw [hexp]
  exact order_prod n ι _ _

omit [IsDomain R] in
private theorem exists_original_rounded_coordinates {Y : Scheme} (π : Y ⟶ Spec (.of R))
    [SmoothOfRelativeDimension n (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    [IsSeparated (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    [QuasiCompact (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))]
    (hSnc : ((specIdealSheaf I).comap π).IsIdealOfSncDivisor)
    {s : ℕ} (a : Fin s → R) (ha : Ideal.span (Set.range a) = I) :
    ∀ p : SchemeComplexPoint (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))),
    ∃ (U : Y.affineOpens) (v : Fin n → Γ(Y,U.1))
      (_hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U.1 v))
      (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
      (ht : letI := affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
        (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale),
      q.val ≫ U.2.fromSpec = p.val ∧
      ∃ (κ : Type) (instκ : Fintype κ), letI := instκ
        ∃ (ι : κ → Fin n) (b : κ → ℕ), Function.Injective ι ∧
          Ideal.span (Set.range fun i => HolGerm.mk
            (centeredOriginalFunction (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) (U.2.fromSpec ≫ π) n q (a i))
            (centeredOriginalFunction_holomorphic (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) (U.2.fromSpec ≫ π) n q (a i))) =
              (Ideal.span {∏ i, HironakaHolomorphicJetMonomialSpan.coordinateGerm (ι i) ^ b i}).map
                (coordinateGermEquiv ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q v ht).toRingHom ∧
          ∀ r : ℚ, ((RoundedSncIdealSheaf.rounded ((specIdealSheaf I).comap π) hSnc r).ideal U).map
              (coefficientGerm ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q) =
            (Ideal.span {∏ i, HironakaHolomorphicJetMonomialSpan.coordinateGerm (ι i) ^ ⌊r * (b i : ℚ)⌋₊}).map
              (coordinateGermEquiv ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q v ht).toRingHom := by
  classical
  intro p
  let f := π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hSncData := hSnc
  obtain ⟨F,e,hF,hJF⟩ := hSncData
  obtain ⟨U,v,qold,htold,hpU,hfac,ι,hι,hcomp,_,habsent⟩ := exists_componentCoordinates f n p hF
  have hC : affinePointFieldAlgebra (U.2.fromSpec ≫ f) = f.sectionsAlgebra U.1 := by
    apply Algebra.algebra_ext
    intro c
    change (Spec.preimage (U.2.fromSpec ≫ f)).hom c = sectionsHom f U.1 c
    rw [fromSpec_comp_eq_specMap_sectionsHom, Spec.preimage_map]
    rfl
  have hv : Etale (toAffineSpace f U.1 v) := by
    apply (etale_toAffineSpace_iff f U.2 v).mpr
    rw [← hC]
    exact htold
  let q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) :=
    ⟨qold.val, by simpa only [Category.assoc] using qold.property⟩
  have ht : letI := affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
      (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale := by
    simpa only [Category.assoc] using htold
  have hγ := coefficientGerm_congr (U.2.fromSpec ≫ f)
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) (Category.assoc _ _ _).symm n qold q rfl
  have hE := coordinateGermEquiv_congr (U.2.fromSpec ≫ f)
    ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    (Category.assoc _ _ _).symm n qold q rfl v htold ht
  have hqold : qold = affineLift f p U hpU := by
    apply Subtype.ext
    apply (cancel_mono U.2.fromSpec).mp
    exact hfac.trans (affineLift_fac f p U hpU).symm
  have hzero i : HolGerm.eval (coefficientGerm (U.2.fromSpec ≫ f) n qold (v (ι i))) = 0 := by
    rw [coefficientGerm_eval,hqold]
    exact affineLift_value_zero f p U hpU (F.component i.1) i.2 (v (ι i))
      (by rw [hcomp i]; exact Ideal.subset_span (Set.mem_singleton _))
  have hround (r : ℚ) := RoundedSncIdealSheaf.rounded_ideal f ((specIdealSheaf I).comap π)
    hSnc hF e hJF r (schemeComplexPointImage f p) U v ι hcomp habsent
  have hroundmap (r : ℚ) : ((RoundedSncIdealSheaf.rounded ((specIdealSheaf I).comap π) hSnc r).ideal U).map
      (coefficientGerm (U.2.fromSpec ≫ f) n qold) =
      (Ideal.span {∏ i, HironakaHolomorphicJetMonomialSpan.coordinateGerm (ι i) ^ ⌊r * (e i.1 : ℚ)⌋₊}).map
        (coordinateGermEquiv (U.2.fromSpec ≫ f) n qold v htold).toRingHom := by
    rw [hround r]
    exact map_active_monomial_ideal (U.2.fromSpec ≫ f) n qold v htold ι _ hzero
  have hwhole : (((specIdealSheaf I).comap π).ideal U).map
      (coefficientGerm (U.2.fromSpec ≫ f) n qold) =
      (Ideal.span {∏ i, HironakaHolomorphicJetMonomialSpan.coordinateGerm (ι i) ^ e i.1}).map
        (coordinateGermEquiv (U.2.fromSpec ≫ f) n qold v htold).toRingHom := by
    simpa only [RoundedSncIdealSheaf.rounded_one,one_mul,Nat.floor_natCast] using hroundmap 1
  rw [hγ,hE] at hwhole
  refine ⟨U,v,hv,q,ht,hfac,_,inferInstance,ι,(fun i => e i.1),hι,?_,?_⟩
  · exact (map_pullback_ideal_eq_centered_span (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) π n I a ha U q).symm.trans hwhole
  · intro r
    simpa only [hγ,hE] using hroundmap r

/-- The WHOLE multiplier ideal on the SAME original BP equals the extension of the WHOLE
original rounded affine ideal, with actual coordinates/rounding all derived internally. -/
theorem exists_original_rounded_multiplier_ideal_chart {s : ℕ} (a : Fin s → R)
    (ha : Ideal.span (Set.range a) = I) :
    let S := Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)
    let π := S.composite
    ∀ p : SchemeComplexPoint (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))),
    ∃ (U : S.last.affineOpens) (v : Fin n → Γ(S.last,U.1))
      (_hv : Etale (toAffineSpace (π ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) U.1 v))
      (q : SchemeComplexPoint ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
      (_ht : letI := affinePointFieldAlgebra ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
        (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale),
      q.val ≫ U.2.fromSpec = p.val ∧
      ∀ (r : ℚ) (hr : (0 : ℝ) < r),
        weightedGermIdeal hr
          (centeredGeneratorLog_quasiPSH (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
            (U.2.fromSpec ≫ π) n q a) volume =
        ((RoundedSncIdealSheaf.rounded ((specIdealSheaf I).comap π)
          (affinePrincipalization_isIdealOfSncDivisor (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI) r).ideal U).map
          (coefficientGerm ((U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n q) := by
  classical
  dsimp only
  let π := (Hironaka.Sequence.BP (affinePrincipalizationTriple (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI)).composite
  intro p
  have hSnc := affinePrincipalization_isIdealOfSncDivisor (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))) n I hI
  obtain ⟨U,v,hv,q,ht,hqp,κ,instκ,ι,b,hι,hGspan,hround⟩ :=
    exists_original_rounded_coordinates n I π hSnc a ha p
  let := instκ
  refine ⟨U,v,hv,q,ht,hqp,?_⟩
  intro r hr
  let fU := (U.2.fromSpec ≫ π) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  let E := coordinateGermEquiv fU n q v ht
  let G := fun i => centeredOriginalFunction (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    (U.2.fromSpec ≫ π) n q (a i)
  let hG := fun i => centeredOriginalFunction_holomorphic (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    (U.2.fromSpec ≫ π) n q (a i)
  have hw := centeredGeneratorLog_quasiPSH (Spec.map (CommRingCat.ofHom (algebraMap ℂ R)))
    (U.2.fromSpec ≫ π) n q a
  have hroundEq : ((RoundedSncIdealSheaf.rounded ((specIdealSheaf I).comap π) hSnc r).ideal U).map
      (coefficientGerm fU n q) =
      Ideal.span {coefficientGerm fU n q (∏ j, centeredOriginal fU n q v j ^
        roundedOrder (fun i => (coordinateOrder ι b i : ℝ)) (coordinateOrder ι (fun _ => 0)) (r : ℝ) j)} := by
    rw [hround r, ← rounded_order_prod n ι hι b r,Ideal.map_span,Set.image_singleton]
    exact congrArg (fun x => Ideal.span {x})
      (coordinateGermEquiv_monomial fU n q v ht _)
  ext h
  obtain ⟨F,hF,rfl⟩ := HolGerm.exists_eq_mk h
  have hAux : Ideal.span {HolGerm.mk (fun _ : ComplexModel n => (1 : ℂ))
      (Eventually.of_forall fun _ => differentiableAt_const (1 : ℂ))} =
      (Ideal.span {∏ i : κ, HironakaHolomorphicJetMonomialSpan.coordinateGerm (ι i) ^ (0 : ℕ)}).map E.toRingHom := by
    simp only [pow_zero,Finset.prod_const_one,Ideal.map_span,Set.image_singleton,map_one]
    rfl
  have hcrit := multiplierIntegrableAt_iff_active_original_rounded_ideal
    fU n q v ht ι b (fun _ => 0) G hG hGspan
    (Eventually.of_forall fun _ => differentiableAt_const (1 : ℂ)) hAux hF hw hr
  rw [hroundEq]
  exact (mem_weightedGermIdeal_iff_source hr hw _ F rfl).trans
    (by simpa only [mul_one] using hcrit)

end EnvelopeProperty.Char0.NativeBPRoundedMultiplierCriterion
