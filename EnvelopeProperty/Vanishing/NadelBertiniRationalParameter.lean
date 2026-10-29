import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties

/-! # Genuine rational parameter selection in original affine coefficient opens

The tuple is produced by a nonzero polynomial and native evaluation over the
original infinite field. The actual spectrum evaluation morphism and its
original base-field structure triangle are retained throughout.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u v w
namespace EnvelopeProperty.Vanishing.NadelBertiniRationalParameter
variable {k : Type u} [Field k] {σ : Type}

/-- The literal actual affine coefficient scheme. -/
abbrev parameterSpace (k : Type u) [Field k] (σ : Type) : Scheme.{u} :=
  Spec (.of (MvPolynomial σ k))

/-- The actual original scheme evaluation morphism of a coefficient tuple. -/
def parameterMap (a : σ → k) : Spec (.of k) ⟶ parameterSpace k σ :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval a))

/-- The actual unique image point of the original evaluation morphism. -/
def parameterPoint (a : σ → k) : parameterSpace k σ :=
  parameterMap a (⊥ : PrimeSpectrum k)

/-- The original evaluation morphism retains its original coefficient structure. -/
theorem parameterMap_structure (a : σ → k) :
    parameterMap a ≫ Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial σ k))) = 𝟙 _ := by
  have hc : CommRingCat.ofHom (algebraMap k (MvPolynomial σ k)) ≫
      CommRingCat.ofHom (MvPolynomial.eval a) = 𝟙 (CommRingCat.of k) := by
    ext c
    exact MvPolynomial.eval_C c
  rw [parameterMap, ← Spec.map_comp, hc]
  simp

/-- A nonzero ORIGINAL polynomial internally produces actual original coefficients. -/
theorem exists_eval_ne_zero [Infinite k] (F : MvPolynomial σ k) (hF : F ≠ 0) :
    ∃ a : σ → k, MvPolynomial.eval a F ≠ 0 := by
  by_contra h
  apply hF
  apply MvPolynomial.funext
  intro a
  simpa using not_exists.mp h a

/-- Membership of the actual original evaluation point in the original basic open
is exactly nonvanishing of the original native polynomial evaluation. -/
theorem parameterPoint_mem_basicOpen_iff (a : σ → k) (F : MvPolynomial σ k) :
    parameterPoint a ∈ PrimeSpectrum.basicOpen F ↔ MvPolynomial.eval a F ≠ 0 := by
  change MvPolynomial.eval a F ∉ (⊥ : Ideal k) ↔ _
  simp only [Ideal.mem_bot]

/-- An actual nonempty original open internally supplies an original nonzero
polynomial whose actual basic open is contained in that same original open. -/
theorem exists_nonzero_basicOpen_le (U : (parameterSpace k σ).Opens)
    (hU : Nonempty U) :
    ∃ F : MvPolynomial σ k, F ≠ 0 ∧ PrimeSpectrum.basicOpen F ≤ U := by
  obtain ⟨x⟩ := hU
  obtain ⟨_, ⟨F, rfl⟩, hxF, hFU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open x.property U.isOpen
  refine ⟨F, ?_, hFU⟩
  intro hF
  subst F
  exact hxF x.val.asIdeal.zero_mem

/-- A whole actual evaluation morphism internally lands in any actual nonempty
open over the original infinite field. -/
theorem exists_parameter_mem_open [Infinite k]
    (U : (parameterSpace k σ).Opens) (hU : Nonempty U) :
    ∃ a : σ → k, ∀ t : Spec (.of k), parameterMap a t ∈ U := by
  obtain ⟨F, hF, hFU⟩ := exists_nonzero_basicOpen_le U hU
  obtain ⟨a, ha⟩ := exists_eval_ne_zero F hF
  refine ⟨a, fun t => ?_⟩
  have ht : t = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
  rw [ht]
  exact hFU ((parameterPoint_mem_basicOpen_iff a F).mpr ha)

/-- A finite intersection of the original opens still contains the actual generic
point; this is the actual opens-lattice intersection, including an empty family. -/
theorem genericPoint_mem_finite_intersection {ι : Type v} [Finite ι]
    (U : ι → (parameterSpace k σ).Opens)
    (hU : ∀ i, genericPoint (parameterSpace k σ) ∈ U i) :
    genericPoint (parameterSpace k σ) ∈ ⨅ i, U i := by
  change genericPoint (parameterSpace k σ) ∈ ((⨅ i, U i : (parameterSpace k σ).Opens) : Set (parameterSpace k σ))
  rw [TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.mpr hU

/-- Actual original rational coefficients in every original member of a finite
family of generic-point-containing opens, with no parameter certificate input. -/
theorem exists_parameter_mem_finite_opens [Infinite k] {ι : Type v} [Finite ι]
    (U : ι → (parameterSpace k σ).Opens)
    (hU : ∀ i, genericPoint (parameterSpace k σ) ∈ U i) :
    ∃ a : σ → k, ∀ i, ∀ t : Spec (.of k), parameterMap a t ∈ U i := by
  have hη := genericPoint_mem_finite_intersection U hU
  obtain ⟨a, ha⟩ := exists_parameter_mem_open (⨅ i, U i) ⟨⟨_, hη⟩⟩
  refine ⟨a, fun i t => ?_⟩
  exact iInf_le U i (ha t)

/-- The same actual original scheme evaluation has top preimage for every
original good open, not just a membership predicate on an auxiliary tuple. -/
theorem exists_parameter_preimages_eq_top [Infinite k] {ι : Type v} [Finite ι]
    (U : ι → (parameterSpace k σ).Opens)
    (hU : ∀ i, genericPoint (parameterSpace k σ) ∈ U i) :
    ∃ a : σ → k, ∀ i, (parameterMap a) ⁻¹ᵁ U i = ⊤ := by
  obtain ⟨a, ha⟩ := exists_parameter_mem_finite_opens U hU
  refine ⟨a, fun i => top_unique (fun t _ => ha i t)⟩

/-- The genuine tuple can simultaneously avoid a finite family of ORIGINAL
nonzero polynomial equations while lying in the same actual original open. -/
theorem exists_parameter_mem_open_avoiding [Infinite k] {τ : Type v} [Fintype τ]
    (U : (parameterSpace k σ).Opens) (hU : Nonempty U)
    (F : τ → MvPolynomial σ k) (hF : ∀ i, F i ≠ 0) :
    ∃ a : σ → k, (∀ t : Spec (.of k), parameterMap a t ∈ U) ∧
      ∀ i, MvPolynomial.eval a (F i) ≠ 0 := by
  obtain ⟨G, hG, hGU⟩ := exists_nonzero_basicOpen_le U hU
  obtain ⟨a, ha⟩ := exists_eval_ne_zero (G * ∏ i, F i)
    (mul_ne_zero hG (Finset.prod_ne_zero_iff.mpr (fun i _ => hF i)))
  have hG_eval : MvPolynomial.eval a G ≠ 0 := by
    intro h
    exact ha (by rw [map_mul, h, zero_mul])
  refine ⟨a, ?_, fun i h => ?_⟩
  · intro t
    have ht : t = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
    rw [ht]
    exact hGU ((parameterPoint_mem_basicOpen_iff a G).mpr hG_eval)
  · have hp : MvPolynomial.eval a (∏ i, F i) = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h
    exact ha (by rw [map_mul, hp, mul_zero])

/-- Finite original good opens and finite original nonzero avoidance polynomials
jointly produce actual coefficients and the whole original evaluation image. -/
theorem exists_parameter_mem_finite_opens_avoiding [Infinite k]
    {ι : Type v} {τ : Type w} [Finite ι] [Fintype τ]
    (U : ι → (parameterSpace k σ).Opens)
    (hU : ∀ i, genericPoint (parameterSpace k σ) ∈ U i)
    (F : τ → MvPolynomial σ k) (hF : ∀ i, F i ≠ 0) :
    ∃ a : σ → k, (∀ i, ∀ t : Spec (.of k), parameterMap a t ∈ U i) ∧
      ∀ i, MvPolynomial.eval a (F i) ≠ 0 := by
  have hη := genericPoint_mem_finite_intersection U hU
  obtain ⟨a, ha, havoid⟩ :=
    exists_parameter_mem_open_avoiding (⨅ i, U i) ⟨⟨_, hη⟩⟩ F hF
  exact ⟨a, fun i t => iInf_le U i (ha t), havoid⟩

end EnvelopeProperty.Vanishing.NadelBertiniRationalParameter
