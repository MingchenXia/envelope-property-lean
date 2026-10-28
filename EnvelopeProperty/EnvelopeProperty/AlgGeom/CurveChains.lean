import EnvelopeProperty.Berkovich.AffineLineComponents
import EnvelopeProperty.AlgGeom.PolynomialOnLines
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual curves through points of finite affine maps

This file develops the affine part of `lem:fc-curve-chains` in the fibre constancy
blueprint. A curve step means containment in the same actual prime quotient of Krull
dimension one. Minimal components of actual inverse images of lines provide such steps;
their finite dominant line maps ensure that a step reaches every point of that line.

The coefficient interpolation and irreducible-polynomial contradiction are also proved.
The general theorem that connected finite type schemes are connected by chains of curves
is not asserted here: producing the line factors from curve classes and the reduction
from general schemes to integral affine schemes remain separate obligations.
-/

open scoped Polynomial
noncomputable section

namespace EnvelopeProperty
namespace FcCurveChains

variable {B : Type*} [CommRing B]

/-- Two actual affine scheme points lie on the same irreducible closed curve. -/
def CurveStep (x y : PrimeSpectrum B) : Prop :=
  ∃ P : Ideal B, P.IsPrime ∧ ringKrullDim (B ⧸ P) = 1 ∧
    P ≤ x.asIdeal ∧ P ≤ y.asIdeal

/-- A finite chain of actual irreducible closed affine curves, allowing the empty chain
between a point and itself. -/
def CurveChain (x y : PrimeSpectrum B) : Prop := Relation.ReflTransGen CurveStep x y

/-- In an integral affine curve the entire scheme itself joins every pair of points. -/
theorem curveStep_of_ringKrullDim_eq_one [IsDomain B]
    (hB : ringKrullDim B = 1) (x y : PrimeSpectrum B) : CurveStep x y := by
  refine ⟨⊥, inferInstance, ?_, bot_le, bot_le⟩
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot B), hB]

theorem CurveStep.symm {x y : PrimeSpectrum B} (h : CurveStep x y) : CurveStep y x := by
  obtain ⟨P, hP, hd, hx, hy⟩ := h
  exact ⟨P, hP, hd, hy, hx⟩

theorem CurveChain.refl (x : PrimeSpectrum B) : CurveChain x x :=
  Relation.ReflTransGen.refl

theorem CurveChain.trans {x y z : PrimeSpectrum B}
    (hxy : CurveChain x y) (hyz : CurveChain y z) : CurveChain x z :=
  Relation.ReflTransGen.trans hxy hyz

theorem CurveStep.curveChain {x y : PrimeSpectrum B} (h : CurveStep x y) : CurveChain x y :=
  Relation.ReflTransGen.single h

theorem CurveChain.symm {x y : PrimeSpectrum B} (h : CurveChain x y) : CurveChain y x := by
  induction h with
  | refl => exact CurveChain.refl _
  | tail _hxy hyz ih => exact hyz.symm.curveChain.trans ih

section FiniteLine

variable {F σ : Type*} [Field F] [Fintype σ]
variable [IsDomain B] [Algebra F B]
variable (a b : σ → F) (j : σ) (g : MvPolynomial σ F) (hb : b j ≠ 0)
variable (φ : Localization.Away g →ₐ[F] B)

include hb in
/-- Through every actual point of a line inverse image there is an actual irreducible
closed curve component, and that same component reaches every point of the open line.
This proves steps (i) and (ii) of the affine argument for `lem:fc-curve-chains`, without
assuming a curve component, its dimension, or its dominance as input. -/
theorem exists_curveStep_over_linePoint
    (hg : g ≠ 0) (hline : AffineLine.subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (x : PrimeSpectrum B)
    (hx : (AffineLine.lineIdeal a b j).map
      (φ.toRingHom.comp (algebraMap _ (Localization.Away g))) ≤ x.asIdeal)
    (w : PrimeSpectrum (AffineLine.OpenLineRing (AffineLine.subst a b g))) :
    ∃ y : PrimeSpectrum B, CurveStep x y ∧
      PrimeSpectrum.comap φ.toRingHom y =
        PrimeSpectrum.comap (AffineLine.principalLineHom a b g).toRingHom w := by
  obtain ⟨P, hP, hPx⟩ := Ideal.exists_minimalPrimes_le hx
  obtain ⟨v, hv⟩ := AffineLine.componentLineHom_comap_surjective a b j g hb φ P hP
    hg hline hφ hiφ w
  let y := PrimeSpectrum.comap (Ideal.Quotient.mk P) v
  refine ⟨y, ⟨P, hP.isPrime,
    AffineLine.component_quotient_ringKrullDim_eq_one a b j g hb φ P hP
      hg hline hφ hiφ, hPx, ?_⟩, ?_⟩
  · intro r hr
    change Ideal.Quotient.mk P r ∈ v.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact v.asIdeal.zero_mem
  · apply PrimeSpectrum.ext
    ext r
    change Ideal.Quotient.mk P (φ r) ∈ v.asIdeal ↔
      AffineLine.principalLineHom a b g r ∈ w.asIdeal
    rw [← AffineLine.componentLineHom_principalLineHom a b j g hb φ P hP r]
    change AffineLine.principalLineHom a b g r ∈
      (PrimeSpectrum.comap (AffineLine.componentLineHom a b j g hb φ P hP).toRingHom v).asIdeal ↔ _
    rw [hv]

include hb in
/-- The point reached over a closed line point can itself be taken closed. Consequently
the actual curve-step construction preserves the closed points used in the curve-chain
equivalence relation. -/
theorem exists_closed_curveStep_over_linePoint
    (hg : g ≠ 0) (hline : AffineLine.subst a b g ≠ 0)
    (hφ : φ.toRingHom.Finite) (hiφ : Function.Injective φ)
    (x : PrimeSpectrum B)
    (hx : (AffineLine.lineIdeal a b j).map
      (φ.toRingHom.comp (algebraMap _ (Localization.Away g))) ≤ x.asIdeal)
    (w : PrimeSpectrum (AffineLine.OpenLineRing (AffineLine.subst a b g)))
    (hw : w.asIdeal.IsMaximal) :
    ∃ y : PrimeSpectrum B, y.asIdeal.IsMaximal ∧ CurveStep x y ∧
      PrimeSpectrum.comap φ.toRingHom y =
        PrimeSpectrum.comap (AffineLine.principalLineHom a b g).toRingHom w := by
  obtain ⟨y, hxy, hy⟩ := exists_curveStep_over_linePoint a b j g hb φ
    hg hline hφ hiφ x hx w
  have hb' : b ≠ 0 := by
    intro he
    exact hb (congrFun he j)
  have : w.asIdeal.IsMaximal := hw
  have hbase : (w.asIdeal.comap (AffineLine.principalLineHom a b g).toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (AffineLine.principalLineHom_surjective a b g hb')
  have hmax : (y.asIdeal.comap φ.toRingHom).IsMaximal := by
    change (PrimeSpectrum.comap φ.toRingHom y).asIdeal.IsMaximal
    rw [hy]
    exact hbase
  let : Algebra (Localization.Away g) B := φ.toRingHom.toAlgebra
  have : Module.Finite (Localization.Away g) B := hφ
  exact ⟨y, Ideal.isMaximal_of_isIntegral_of_isMaximal_comap y.asIdeal hmax, hxy, hy⟩

end FiniteLine

section PolynomialFactors

open FcPolynomialOnLines

variable {F : Type*} [Field F] [Infinite F] {n : ℕ}

/-- A polynomial in `Z` with multivariate polynomial coefficients is determined by its
entire specializations on a nonempty Zariski open of the coordinate space. -/
theorem polynomial_eq_of_map_eval_eq_on_open
    (U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) F)))
    (hU : (U : Set (PrimeSpectrum (MvPolynomial (Fin n) F))).Nonempty)
    {P Q : (MvPolynomial (Fin n) F)[X]}
    (h : ∀ x : Fin n → F, rationalPoint x ∈ U →
      P.map (MvPolynomial.eval x) = Q.map (MvPolynomial.eval x)) : P = Q := by
  obtain ⟨z, hz⟩ := hU
  obtain ⟨_, ⟨g, rfl⟩, hzg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp U.isOpen z hz
  have hg : g ≠ 0 := by
    intro he
    simp [he] at hzg
  apply Polynomial.ext
  intro k
  apply eq_of_eval_eq_on_principalOpen hg
  intro x hx
  have he := congrArg (fun p : F[X] => p.coeff k)
    (h x (hgU ((rationalPoint_mem_basicOpen x g).mpr hx)))
  simpa only [Polynomial.coeff_map] using he

/-- Genuine fibrewise factors of one fixed monic polynomial extend to a polynomial
factor family when their linewise coefficient functions come from genuine line factors.
All degree bounds are consequences of divisibility. -/
theorem exists_polynomial_factor_family
    (U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) F)))
    (hU : (U : Set (PrimeSpectrum (MvPolynomial (Fin n) F))).Nonempty)
    (P : (MvPolynomial (Fin n) F)[X]) (hP : P.Monic)
    (q : (Fin n → F) → F[X])
    (hq : ∀ x : Fin n → F, rationalPoint x ∈ U → q x ∣ P.map (MvPolynomial.eval x))
    (hline : ∀ k : Fin (P.natDegree + 1), ∀ a b : Fin n → F, b ≠ 0 →
      ∃ Q : (F[X])[X], Q ∣ P.map (AffineLine.subst a b).toRingHom ∧
        ∀ t : F, rationalPoint (AffineLine.point a b t) ∈ U →
          (q (AffineLine.point a b t)).coeff k = (Q.coeff k).eval t) :
    ∃ R : (MvPolynomial (Fin n) F)[X],
      ∀ x : Fin n → F, rationalPoint x ∈ U → R.map (MvPolynomial.eval x) = q x := by
  classical
  choose r hr using fun k : Fin (P.natDegree + 1) =>
    exists_polynomial_of_lineFactor_coeff n U hU P hP (fun x => (q x).coeff k) k (hline k)
  refine ⟨Polynomial.ofFn (P.natDegree + 1) r, fun x hx => ?_⟩
  have hd : (q x).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_le_of_dvd (hq x hx) (hP.map (MvPolynomial.eval x)).ne_zero).trans
      Polynomial.natDegree_map_le
  apply Polynomial.ext
  intro k
  by_cases hk : k < P.natDegree + 1
  · rw [Polynomial.coeff_map, Polynomial.ofFn_coeff_eq_val_of_lt r hk]
    exact (hr ⟨k, hk⟩ x hx).symm
  · rw [Polynomial.coeff_map,
      Polynomial.ofFn_coeff_eq_zero_of_ge r (Nat.le_of_not_gt hk), map_zero]
    exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (q x).natDegree < k)).symm

/-- Two everywhere complementary nonconstant fibre factors with genuine polynomial line
restrictions contradict irreducibility. This is the algebraic factorization step (v) of
`lem:fc-curve-chains`; producing the factors from curve classes remains geometric work. -/
theorem not_irreducible_of_line_factor_families
    (U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) F)))
    (hU : (U : Set (PrimeSpectrum (MvPolynomial (Fin n) F))).Nonempty)
    (P : (MvPolynomial (Fin n) F)[X]) (hP : P.Monic)
    (q q' : (Fin n → F) → F[X])
    (hprod : ∀ x : Fin n → F, rationalPoint x ∈ U →
      P.map (MvPolynomial.eval x) = q x * q' x)
    (hline : ∀ k : Fin (P.natDegree + 1), ∀ a b : Fin n → F, b ≠ 0 →
      ∃ Q : (F[X])[X], Q ∣ P.map (AffineLine.subst a b).toRingHom ∧
        ∀ t : F, rationalPoint (AffineLine.point a b t) ∈ U →
          (q (AffineLine.point a b t)).coeff k = (Q.coeff k).eval t)
    (hline' : ∀ k : Fin (P.natDegree + 1), ∀ a b : Fin n → F, b ≠ 0 →
      ∃ Q : (F[X])[X], Q ∣ P.map (AffineLine.subst a b).toRingHom ∧
        ∀ t : F, rationalPoint (AffineLine.point a b t) ∈ U →
          (q' (AffineLine.point a b t)).coeff k = (Q.coeff k).eval t)
    (x : Fin n → F) (hx : rationalPoint x ∈ U)
    (hn : 0 < (q x).natDegree) (hn' : 0 < (q' x).natDegree) : ¬ Irreducible P := by
  obtain ⟨R, hR⟩ := exists_polynomial_factor_family U hU P hP q
    (fun y hy => ⟨q' y, hprod y hy⟩) hline
  obtain ⟨R', hR'⟩ := exists_polynomial_factor_family U hU P hP q'
    (fun y hy => ⟨q y, (hprod y hy).trans (mul_comm _ _)⟩) hline'
  have hPprod : P = R * R' := polynomial_eq_of_map_eval_eq_on_open U hU (by
    intro y hy
    rw [Polynomial.map_mul, hR y hy, hR' y hy]
    exact hprod y hy)
  intro hI
  rcases hI.isUnit_or_isUnit hPprod with hunit | hunit
  · have hu := hunit.map (Polynomial.mapRingHom (MvPolynomial.eval x))
    change IsUnit (R.map (MvPolynomial.eval x)) at hu
    rw [hR x hx] at hu
    exact (ne_of_gt hn) (Polynomial.natDegree_eq_zero_of_isUnit hu)
  · have hu := hunit.map (Polynomial.mapRingHom (MvPolynomial.eval x))
    change IsUnit (R'.map (MvPolynomial.eval x)) at hu
    rw [hR' x hx] at hu
    exact (ne_of_gt hn') (Polynomial.natDegree_eq_zero_of_isUnit hu)

end PolynomialFactors

end FcCurveChains
end EnvelopeProperty
