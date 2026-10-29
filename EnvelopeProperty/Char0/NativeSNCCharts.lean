import EnvelopeProperty.Char0.NativeEtaleCoordinates
import EnvelopeProperty.Char0.SNCAffineFactors
import EnvelopeProperty.Char0.AffineTransformIdeals
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # The same original SNC component ideals in actual local holomorphic coordinates -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace EnvelopeProperty.Char0.NativeSNCCharts

open CategoryTheory AlgebraicGeometry ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HolomorphicGerms
open NativeEtaleCoordinates HironakaHolomorphicJetMonomialSpan
open scoped Topology Classical

variable {Y : Scheme} (f : Y ⟶ Spec (.of ℂ))

private theorem affineStructuralAlgebra_eq (U : Y.affineOpens) :
    affinePointFieldAlgebra (U.2.fromSpec ≫ f) = f.sectionsAlgebra U.1 := by
  apply Algebra.algebra_ext
  intro c
  change (Spec.preimage (U.2.fromSpec ≫ f)).hom c = sectionsHom f U.1 c
  rw [fromSpec_comp_eq_specMap_sectionsHom, Spec.preimage_map]
  rfl

/-- The original complex point has a literal lift into its actual original affine SNC model. -/
def affineLift (p : SchemeComplexPoint f) (U : Y.affineOpens)
    (hpU : schemeComplexPointImage f p ∈ U.1) :
    SchemeComplexPoint (U.2.fromSpec ≫ f) :=
  schemeComplexPointLift f U.2.fromSpec p (by rw [U.2.range_fromSpec]; exact hpU)

/-- The actual affine lift retains the entire original scheme-point morphism. -/
theorem affineLift_fac (p : SchemeComplexPoint f) (U : Y.affineOpens)
    (hpU : schemeComplexPointImage f p ∈ U.1) :
    (affineLift f p U hpU).val ≫ U.2.fromSpec = p.val :=
  schemeComplexPointLift_fac f U.2.fromSpec p _

/-- The underlying point of the actual affine model maps to the same original point. -/
theorem affineLift_image (p : SchemeComplexPoint f) (U : Y.affineOpens)
    (hpU : schemeComplexPointImage f p ∈ U.1) :
    U.2.fromSpec (schemeComplexPointImage (U.2.fromSpec ≫ f) (affineLift f p U hpU)) =
      schemeComplexPointImage f p := by
  have he := congrArg (fun a : Spec (.of ℂ) ⟶ Y => a default) (affineLift_fac f p U hpU)
  exact (Scheme.Hom.comp_apply (affineLift f p U hpU).val U.2.fromSpec default).symm.trans he

/-- Every section of an original component ideal through the original point has actual value zero
at the internally manufactured affine lift. -/
theorem affineLift_value_zero (p : SchemeComplexPoint f) (U : Y.affineOpens)
    (hpU : schemeComplexPointImage f p ∈ U.1) (J : Y.IdealSheafData)
    (hpJ : schemeComplexPointImage f p ∈ J.support) (a : Γ(Y, U.1)) (ha : a ∈ J.ideal U) :
    (Spec.preimage (affineLift f p U hpU).val).hom a = 0 := by
  have hnot : schemeComplexPointImage f p ∉ Y.basicOpen a :=
    (Scheme.mem_zeroLocus_iff Y (J.ideal U) _).mp
      ((J.mem_support_iff_of_mem hpU).mp hpJ) a ha
  by_contra hne
  have hbasic : schemeComplexPointImage (U.2.fromSpec ≫ f) (affineLift f p U hpU) ∈
      PrimeSpectrum.basicOpen a :=
    (affineSchemePointImage_mem_basicOpen (U.2.fromSpec ≫ f) (affineLift f p U hpU) a).mpr
      (by rwa [affineSchemePointEquivOfStructure_apply])
  have hbasic' : U.2.fromSpec
      (schemeComplexPointImage (U.2.fromSpec ≫ f) (affineLift f p U hpU)) ∈ Y.basicOpen a := by
    change schemeComplexPointImage (U.2.fromSpec ≫ f) (affineLift f p U hpU) ∈
      U.2.fromSpec ⁻¹ᵁ Y.basicOpen a
    rw [U.2.fromSpec_preimage_basicOpen]
    exact hbasic
  exact hnot ((affineLift_image f p U hpU) ▸ hbasic')

variable (n : ℕ) [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

private instance affineSmoothDimension (U : Y.affineOpens) :
    SmoothOfRelativeDimension n (U.2.fromSpec ≫ f) :=
  (Nat.zero_add n) ▸
    (smoothOfRelativeDimension_comp (f := U.2.fromSpec) (n := 0) (m := n) f)

include n in
private theorem originalPoint_isClosed : IsClosed ({schemeComplexPointImage f p} : Set Y) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hc := (pointEquivClosedPoint f p).property
  change IsClosed ({p.val (IsLocalRing.closedPoint ℂ)} : Set Y) at hc
  have he : p.val default = p.val (IsLocalRing.closedPoint ℂ) :=
    congrArg p.val (Subsingleton.elim _ _)
  simpa only [schemeComplexPointImage, he] using hc

/-- The ORIGINAL SNC geometry and ORIGINAL factor equality manufacture actual local holomorphic
coordinates and the WHOLE original component and factor ideal comparisons at the SAME affine lift. -/
theorem exists_factorCoordinates {F : Scheme.DivisorFamily Y} (hF : F.IsSnc)
    (A B : Y.IdealSheafData) (e : F.ι → ℕ)
    (hprod : A * B = ∏ i, F.component i ^ e i) :
    ∃ (U : Y.affineOpens) (v : Fin n → Γ(Y, U.1))
      (q : SchemeComplexPoint (U.2.fromSpec ≫ f))
      (ht : letI := affinePointFieldAlgebra (U.2.fromSpec ≫ f)
        (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale),
      schemeComplexPointImage f p ∈ U.1 ∧ q.val ≫ U.2.fromSpec = p.val ∧
      ∃ c : {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = Ideal.span {v (c i)}) ∧
        (∀ i, ((F.component i.1).ideal U).map (coefficientGerm (U.2.fromSpec ≫ f) n q) =
          (Ideal.span {coordinateGerm (c i)}).map
            (coordinateGermEquiv (U.2.fromSpec ≫ f) n q v ht).toRingHom) ∧
        (∀ i, schemeComplexPointImage f p ∉ (F.component i).support →
          (F.component i).comap U.1.ι = ⊤) ∧
        ∃ a : {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support} → ℕ,
          (∀ i, a i ≤ e i.1) ∧ A.ideal U = Ideal.span {∏ i, v (c i) ^ a i} ∧
          (A.ideal U).map (coefficientGerm (U.2.fromSpec ≫ f) n q) =
            (Ideal.span {∏ i, (coordinateGerm (c i)) ^ a i}).map
              (coordinateGermEquiv (U.2.fromSpec ≫ f) n q v ht).toRingHom := by
  obtain ⟨U, v, hpU, hv, c, hcinj, hcomp, habsent, a, ha, hA⟩ :=
    exists_snc_etale_chart_monomial_factor f n hF e hprod (originalPoint_isClosed f n p)
  let q := affineLift f p U hpU
  have ht : letI := affinePointFieldAlgebra (U.2.fromSpec ≫ f)
      (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale := by
    rw [affineStructuralAlgebra_eq]
    exact (etale_toAffineSpace_iff f U.2 v).mp hv
  have hz (i : {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support}) :
      HolGerm.eval (coefficientGerm (U.2.fromSpec ≫ f) n q (v (c i))) = 0 := by
    rw [coefficientGerm_eval]
    exact affineLift_value_zero f p U hpU (F.component i.1) i.2 (v (c i))
      (by rw [hcomp i]; exact Ideal.subset_span (Set.mem_singleton _))
  refine ⟨U, v, q, ht, hpU, affineLift_fac f p U hpU,
    c, hcinj, hcomp, ?_, habsent, a, ha, hA, ?_⟩
  · intro i
    rw [hcomp i, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    exact congrArg (fun g => Ideal.span {g})
      (coordinateGermEquiv_coordinate_of_eval_zero (U.2.fromSpec ≫ f) n q v ht (c i) (hz i)).symm
  · rw [hA]
    exact map_active_monomial_ideal (U.2.fromSpec ≫ f) n q v ht c a hz

/-- Every original SNC family produces actual local holomorphic coordinates for its ENTIRE
original component ideals; no original coordinate equations or analytic matching certificate is supplied. -/
theorem exists_componentCoordinates {F : Scheme.DivisorFamily Y} (hF : F.IsSnc) :
    ∃ (U : Y.affineOpens) (v : Fin n → Γ(Y, U.1))
      (q : SchemeComplexPoint (U.2.fromSpec ≫ f))
      (ht : letI := affinePointFieldAlgebra (U.2.fromSpec ≫ f)
        (MvPolynomial.aeval (R := ℂ) v).toRingHom.Etale),
      schemeComplexPointImage f p ∈ U.1 ∧ q.val ≫ U.2.fromSpec = p.val ∧
      ∃ c : {i : F.ι // schemeComplexPointImage f p ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = Ideal.span {v (c i)}) ∧
        (∀ i, ((F.component i.1).ideal U).map (coefficientGerm (U.2.fromSpec ≫ f) n q) =
          (Ideal.span {coordinateGerm (c i)}).map
            (coordinateGermEquiv (U.2.fromSpec ≫ f) n q v ht).toRingHom) ∧
        ∀ i, schemeComplexPointImage f p ∉ (F.component i).support →
          (F.component i).comap U.1.ι = ⊤ := by
  obtain ⟨U, v, q, ht, hpU, hq, c, hcinj, hcomp, hwhole, habsent, _⟩ :=
    exists_factorCoordinates f n p hF ⊤ (∏ i, F.component i) (fun _ => 1) (by simp)
  exact ⟨U, v, q, ht, hpU, hq, c, hcinj, hcomp, hwhole, habsent⟩

end EnvelopeProperty.Char0.NativeSNCCharts
