/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Char0.SNCFactors
import EnvelopeProperty.Char0.PrimeMonomialRounding
import EnvelopeProperty.Char0.SNCCharts
import Mathlib.Algebra.Order.Floor.Ring
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Resolution.Algebraic.Snc.MonomialComponents
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.Snc.TotalTransformOnCentre

/-!
# The actual rounded product of an original SNC presentation

All products below are original whole ideal sheaves. The stalk and affine formulas retain
all original component sections; the chart compatibility is derived from this whole product.
Presentation independence is established separately by prime monomial uniqueness.
-/

noncomputable section
namespace EnvelopeProperty.Char0.RoundedSncIdealSheaf

open AlgebraicGeometry CategoryTheory Ideal
open scoped Classical

universe u
variable {X Y : Scheme.{u}}

/-- The original whole product with the actual rounded multiplicities. -/
def product (F : Scheme.DivisorFamily X) (a : F.ι → ℕ) (q : ℚ) :
    X.IdealSheafData := ∏ i, F.component i ^ ⌊q * (a i : ℚ)⌋₊

/-- The original SNC family itself proves that its rounded product is an SNC divisor ideal. -/
theorem product_isIdealOfSncDivisor {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (q : ℚ) : (product F a q).IsIdealOfSncDivisor :=
  ⟨F, fun i => ⌊q * (a i : ℚ)⌋₊, hF, rfl⟩

/-- Smoothness and the actual SNC presentation derive invertibility of the whole rounded ideal. -/
theorem product_isInvertible {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (q : ℚ) : (product F a q).IsInvertible :=
  (product_isIdealOfSncDivisor hF a q).isInvertible f

/-- The entire original stalk ideal is the rounded monomial in the actual component parameters. -/
theorem product_stalkIdeal {F : Scheme.DivisorFamily X} (a : F.ι → ℕ) (q : ℚ)
    {x : X} {n : ℕ} (z : Fin n → X.presheaf.stalk x)
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hc : ∀ i, (F.component i.1).stalkIdeal x = span {z (c i)}) :
    (product F a q).stalkIdeal x =
      span {∏ i, z (c i) ^ ⌊q * (a i.1 : ℚ)⌋₊} := by
  rw [product, Scheme.IdealSheafData.stalkIdeal_finset_prod]
  simp_rw [Scheme.IdealSheafData.stalkIdeal_pow]
  exact prod_pow_stalkIdeal_eq_span F.component (fun i => ⌊q * (a i : ℚ)⌋₊) c hc

/-- Every point has the actual regular-parameter rounded formula, derived from the SNC family. -/
theorem exists_product_stalk_coordinates {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (q : ℚ) (x : X) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), F.IsSncAt x z ∧
      ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).stalkIdeal x = span {z (c i)}) ∧
        (product F a q).stalkIdeal x =
          span {∏ i, z (c i) ^ ⌊q * (a i.1 : ℚ)⌋₊} := by
  obtain ⟨n, z, hz, c, hcinj, hc⟩ := hF.2 x
  exact ⟨n, z, ⟨hz, c, hcinj, hc⟩, c, hcinj, hc, product_stalkIdeal a q z c hc⟩

private theorem ideal_prod {ι : Type*} (s : Finset ι) (A : ι → X.IdealSheafData)
    (U : X.affineOpens) : (∏ i ∈ s, A i).ideal U = ∏ i ∈ s, (A i).ideal U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top]; rfl
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih]

/-- The whole affine ideal is the rounded monomial on every adapted original component chart. -/
theorem product_ideal {F : Scheme.DivisorFamily X} (a : F.ι → ℕ) (q : ℚ)
    (x : X) (U : X.affineOpens) {n : ℕ} (v : Fin n → Γ(X, U.1))
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hc : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) :
    (product F a q).ideal U = span {∏ i, v (c i) ^ ⌊q * (a i.1 : ℚ)⌋₊} := by
  rw [product, ideal_prod]
  simp_rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : F.ι => x ∈ (F.component i).support)
    (fun i => (F.component i).ideal U ^ ⌊q * (a i : ℚ)⌋₊)]
  have hmissing : ∏ i : {i : F.ι // x ∉ (F.component i).support},
      (F.component i.1).ideal U ^ ⌊q * (a i.1 : ℚ)⌋₊ = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have hunit : (F.component i.1).ideal U = ⊤ :=
      AlgebraicGeometry.ideal_eq_top_of_comap_ι_eq_top _ _ (habsent i.1 i.2)
    rw [hunit, Ideal.top_pow, Ideal.one_eq_top]
  rw [hmissing, mul_one]
  calc (∏ i : {i : F.ι // x ∈ (F.component i).support},
        (F.component i.1).ideal U ^ ⌊q * (a i.1 : ℚ)⌋₊) =
      ∏ i, span {v (c i) ^ ⌊q * (a i.1 : ℚ)⌋₊} := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hc i, Ideal.span_singleton_pow]
    _ = span {∏ i, v (c i) ^ ⌊q * (a i.1 : ℚ)⌋₊} := Ideal.prod_span_singleton _ _

/-- The original rounded product commutes with actual pullback of the same labelled family. -/
theorem product_comap (F : Scheme.DivisorFamily X) (a : F.ι → ℕ) (q : ℚ)
    (g : Y ⟶ X) : (product F a q).comap g = product (F.comap g) a q := by
  unfold product
  rw [Scheme.IdealSheafData.comap_finset_prod]
  exact Finset.prod_congr rfl fun i _ => Scheme.IdealSheafData.comap_pow _ _ _

private theorem parameters_associates_injective {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {n : ℕ} {z : Fin n → A}
    (hz : IsLocalRing.IsRegularSystemOfParameters z)
    {ι : Type*} (c : ι → Fin n) (hc : Function.Injective c) :
    Function.Injective (fun i => Associates.mk (z (c i))) := by
  intro i j hij
  apply hc
  by_contra hne
  exact not_dvd_of_ne hz.1.symm hz.2 hne
    (Associates.mk_eq_mk_iff_associated.mp hij).dvd

/-- Two actual SNC presentations of the SAME original ideal give the SAME whole rounded ideal.
All coordinate matching is derived from primality; none is an additional premise. -/
theorem product_eq_of_presentations {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {J : X.IdealSheafData}
    {F G : Scheme.DivisorFamily X} (hF : F.IsSnc) (hG : G.IsSnc)
    (a : F.ι → ℕ) (b : G.ι → ℕ)
    (hJF : J = ∏ i, F.component i ^ a i) (hJG : J = ∏ j, G.component j ^ b j)
    (q : ℚ) : product F a q = product G b q := by
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro x
  have := isRegularLocalRing_stalk f x
  obtain ⟨n, z, hz, c, hcinj, hc⟩ := hF.2 x
  obtain ⟨m, w, hw, d, hdinj, hd⟩ := hG.2 x
  have hFx : J.stalkIdeal x = span {∏ i, z (c i) ^ a i.1} := by
    rw [hJF, Scheme.IdealSheafData.stalkIdeal_finset_prod]
    simp_rw [Scheme.IdealSheafData.stalkIdeal_pow]
    exact prod_pow_stalkIdeal_eq_span F.component a c hc
  have hGx : J.stalkIdeal x = span {∏ j, w (d j) ^ b j.1} := by
    rw [hJG, Scheme.IdealSheafData.stalkIdeal_finset_prod]
    simp_rw [Scheme.IdealSheafData.stalkIdeal_pow]
    exact prod_pow_stalkIdeal_eq_span G.component b d hd
  rw [product_stalkIdeal a q z c hc, product_stalkIdeal b q w d hd]
  apply Ideal.span_singleton_eq_span_singleton.mpr
  exact PrimeMonomialRounding.associated_rounded_products
    (fun i => z (c i)) (fun j => w (d j))
    (fun i => prime_of_parameters hz.1.symm hz.2 (c i))
    (fun j => prime_of_parameters hw.1.symm hw.2 (d j))
    (parameters_associates_injective hz c hcinj)
    (parameters_associates_injective hw d hdinj)
    (fun i => a i.1) (fun j => b j.1)
    (Ideal.span_singleton_eq_span_singleton.mp (hFx.symm.trans hGx)) q

private theorem exists_presentation (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    Nonempty (Σ F : Scheme.DivisorFamily X,
      {a : F.ι → ℕ // F.IsSnc ∧ J = ∏ i, F.component i ^ a i}) := by
  obtain ⟨F, a, hF, hJF⟩ := hJ
  exact ⟨F, a, hF, hJF⟩

private def presentation (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :=
  Classical.choice (exists_presentation J hJ)

/-- The rounded original ideal, with its actual presentation obtained from the original SNC
condition. The comparison theorem below removes the choice of presentation. -/
def rounded (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    X.IdealSheafData := product (presentation J hJ).1 (presentation J hJ).2.1 q

/-- The canonical rounded ideal equals the rounded product of EVERY actual SNC presentation. -/
theorem rounded_eq_product {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J = ∏ i, F.component i ^ a i) (q : ℚ) :
    rounded J hJ q = product F a q :=
  product_eq_of_presentations f (presentation J hJ).2.2.1 hF
    (presentation J hJ).2.1 a (presentation J hJ).2.2.2 hJF q

/-- The whole original rounded ideal is SNC, directly from the original SNC condition. -/
theorem rounded_isIdealOfSncDivisor (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : (rounded J hJ q).IsIdealOfSncDivisor :=
  product_isIdealOfSncDivisor (presentation J hJ).2.2.1 (presentation J hJ).2.1 q

/-- Actual smoothness derives actual invertibility of the canonical whole rounded ideal. -/
theorem rounded_isInvertible {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) (q : ℚ) : (rounded J hJ q).IsInvertible :=
  (rounded_isIdealOfSncDivisor J hJ q).isInvertible f

/-- On EVERY actual adapted affine chart of EVERY original SNC presentation, the ENTIRE
canonical rounded ideal has exactly the original rounded coordinate monomial. -/
theorem rounded_ideal {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (J : X.IdealSheafData)
    (hJ : J.IsIdealOfSncDivisor) {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J = ∏ i, F.component i ^ a i) (q : ℚ)
    (x : X) (U : X.affineOpens) {n : ℕ} (v : Fin n → Γ(X, U.1))
    (c : {i : F.ι // x ∈ (F.component i).support} → Fin n)
    (hc : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) :
    (rounded J hJ q).ideal U = span {∏ i, v (c i) ^ ⌊q * (a i.1 : ℚ)⌋₊} := by
  rw [rounded_eq_product f J hJ hF a hJF q]
  exact product_ideal a q x U v c hc habsent

/-- Rounding at zero is the actual unit ideal sheaf. -/
theorem rounded_zero (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    rounded J hJ 0 = ⊤ := by
  simp only [rounded, product, zero_mul, Nat.floor_zero, pow_zero, Finset.prod_const_one]
  rfl

/-- Rounding at one gives the SAME original ideal, including all multiplicities. -/
theorem rounded_one (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) :
    rounded J hJ 1 = J := by
  have h := (presentation J hJ).2.2.2
  simpa only [rounded, product, one_mul, Nat.floor_natCast] using h.symm

/-- The actual SNC rounded ideal commutes with smooth pullback of the original divisor ideal. -/
theorem rounded_comap {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [Smooth f] (g : Y ⟶ X) [Smooth g]
    (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    (rounded J hJ q).comap g =
      rounded (J.comap g) (hJ.comap_of_smooth f g) q := by
  let P := presentation J hJ
  have hF : P.1.IsSnc := P.2.2.1
  have hJG : J.comap g = ∏ i, (P.1.comap g).component i ^ P.2.1 i := by
    calc J.comap g = (∏ i, P.1.component i ^ P.2.1 i).comap g :=
        congrArg (fun A : X.IdealSheafData => A.comap g) P.2.2.2
      _ = ∏ i, (P.1.comap g).component i ^ P.2.1 i := by
        rw [Scheme.IdealSheafData.comap_finset_prod]
        exact Finset.prod_congr rfl fun i _ => Scheme.IdealSheafData.comap_pow _ _ _
  rw [rounded_eq_product f J hJ hF P.2.1 P.2.2.2 q, product_comap]
  exact (rounded_eq_product (g ≫ f) (J.comap g) (hJ.comap_of_smooth f g)
    (isSnc_comap_of_smooth f g hF) P.2.1 hJG q).symm

/-- The original SNC hypothesis itself produces an actual finite affine etale cover with both
the ORIGINAL unrounded ideal and its canonical rounded ideal in the SAME actual coordinates.
No cover, coordinate, presentation, overlap or rounding certificate is an endpoint premise. -/
theorem exists_finite_rounded_etale_cover {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] [CompactSpace X]
    (J : X.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ) :
    ∃ (F : Scheme.DivisorFamily X) (a : F.ι → ℕ), F.IsSnc ∧
      J = ∏ i, F.component i ^ a i ∧
      ∃ t : Finset X.affineOpens, (∀ y : X, ∃ U ∈ t, y ∈ U.1) ∧
        ∀ U ∈ t, ∃ (x : X) (v : Fin n → Γ(X, U.1)), IsClosed ({x} : Set X) ∧
          x ∈ U.1 ∧ Etale (toAffineSpace f U.1 v) ∧
          ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
            Function.Injective c ∧
            (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
            (∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
            J.ideal U = span {∏ i, v (c i) ^ a i.1} ∧
            (rounded J hJ q).ideal U =
              span {∏ i, v (c i) ^ ⌊q * (a i.1 : ℚ)⌋₊} := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hdata := hJ
  obtain ⟨F, a, hF, hJF⟩ := hdata
  obtain ⟨t, hcover, hcharts⟩ := exists_finite_snc_etale_cover f n hF
  refine ⟨F, a, hF, hJF, t, hcover, ?_⟩
  intro U hU
  obtain ⟨x, v, hx, hxU, het, c, hcinj, hc, habsent⟩ := hcharts U hU
  refine ⟨x, v, hx, hxU, het, c, hcinj, hc, habsent, ?_,
    rounded_ideal f J hJ hF a hJF q x U v c hc habsent⟩
  have h1 := product_ideal a 1 x U v c hc habsent
  have hprod : product F a 1 = J := by
    simpa only [product, one_mul, Nat.floor_natCast] using hJF.symm
  simpa only [hprod, one_mul, Nat.floor_natCast] using h1

end EnvelopeProperty.Char0.RoundedSncIdealSheaf
