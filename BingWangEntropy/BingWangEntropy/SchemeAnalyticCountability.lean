import BingWangEntropy.SchemeAnalyticAtlas
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Extension.Generators
import Mathlib.Topology.Bases

/-! # Second countability of actual finite-type complex schemes

Finite algebra generators embed genuine affine complex points into a finite
complex coordinate space. Native quasi-compactness selects a finite affine
cover; its genuine analytic point maps form an open quotient. Zariski
quasi-compactness is used solely to select this cover.
-/

open CategoryTheory AlgebraicGeometry
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace BingWangEntropy

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A] {ι : Type*}

/-- Coordinates are literal evaluations at actual algebra generators. -/
def complexGeneratorsPointCoordinates (P : Algebra.Generators ℂ A ι)
    (p : ComplexAlgebraPoint A) : ι → ℂ := fun i => p (P.val i)

/-- Every actual element evaluation is a polynomial in the generator evaluations. -/
theorem complexGeneratorsPointCoordinates_eval (P : Algebra.Generators ℂ A ι)
    (p : ComplexAlgebraPoint A) (a : A) :
    p a = MvPolynomial.eval (complexGeneratorsPointCoordinates P p) (P.σ a) := by
  have h : p.comp (MvPolynomial.aeval P.val) =
      MvPolynomial.aeval (complexGeneratorsPointCoordinates P p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [complexGeneratorsPointCoordinates]
  have he := congrArg (fun h => h (P.σ a)) h
  simpa only [AlgHom.comp_apply, P.aeval_val_σ, MvPolynomial.aeval_eq_eval] using he

/-- Actual generator coordinates retain the entire genuine evaluation topology. -/
theorem complexGeneratorsPointCoordinates_isEmbedding (P : Algebra.Generators ℂ A ι) :
    Topology.IsEmbedding (complexGeneratorsPointCoordinates P) := by
  have hc : Continuous (complexGeneratorsPointCoordinates P) :=
    continuous_pi_iff.mpr (fun i => complexPoint_evaluation_continuous (P.val i))
  let g : (ι → ℂ) → (A → ℂ) := fun z a => MvPolynomial.eval z (P.σ a)
  have hg : Continuous g :=
    continuous_pi_iff.mpr (fun a => complexPolynomial_continuous (P.σ a))
  have heq : g ∘ complexGeneratorsPointCoordinates P =
      (fun p : ComplexAlgebraPoint A => fun a : A => p a) := by
    funext p a
    exact (complexGeneratorsPointCoordinates_eval P p a).symm
  refine ⟨Topology.IsInducing.of_comp hc hg ?_, ?_⟩
  · rw [heq]
    exact Topology.IsInducing.induced _
  · intro p q hpq
    apply AlgHom.ext
    intro a
    rw [complexGeneratorsPointCoordinates_eval P p a,
      complexGeneratorsPointCoordinates_eval P q a, hpq]

/-- A genuine finitely generated complex algebra has a second-countable point topology. -/
theorem finiteTypeComplexAlgebraPoint_secondCountable [Algebra.FiniteType ℂ A] :
    SecondCountableTopology (ComplexAlgebraPoint A) := by
  obtain ⟨n, ⟨P⟩⟩ := Algebra.FiniteType.iff_exists_generators.mp
    (inferInstance : Algebra.FiniteType ℂ A)
  exact (complexGeneratorsPointCoordinates_isEmbedding P).secondCountableTopology

/-- Native local finite type gives finite generation for each actual inherited affine algebra. -/
theorem complexAffineChart_finiteType {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType f] (c : ComplexAffineChart X) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    Algebra.FiniteType ℂ c.ring := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  have h : LocallyOfFiniteType (Spec.map (Spec.preimage (c.map ≫ f))) := by
    rw [Spec.map_preimage]
    infer_instance
  exact HasRingHomProperty.Spec_iff.mp h

/-- Each genuine affine chart of a locally finite-type complex scheme is second countable. -/
theorem complexAffineChartPoint_secondCountable {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f] (c : ComplexAffineChart X) :
    SecondCountableTopology (ComplexAffineChartPoint f c) := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := complexAffineChart_finiteType f c
  let := finiteTypeComplexAlgebraPoint_secondCountable (A := c.ring)
  exact (affineSchemePointHomeomorphOfStructure (c.map ≫ f)).isEmbedding.secondCountableTopology

/-- A native affine open cover supplies literal Spec charts using its native affine isomorphisms. -/
def complexAffineOpenCoverChart {X : Scheme} (𝒰 : X.OpenCover)
    [∀ i, IsAffine (𝒰.X i)] (i : 𝒰.I₀) : ComplexAffineChart X where
  ring := Γ(𝒰.X i, ⊤)
  map := (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
  isOpenImmersion := inferInstance

/-- The joint complex-point map of a genuine native affine open cover. -/
def complexAffineOpenCoverPointMap {X : Scheme} (f : X ⟶ Spec (.of ℂ))
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    (Σ i : 𝒰.I₀, ComplexAffineChartPoint f (complexAffineOpenCoverChart 𝒰 i)) →
      SchemeComplexPoint f :=
  fun p => complexAffineChartPointMap f (complexAffineOpenCoverChart 𝒰 p.1) p.2

/-- Native affine cover surjectivity lifts actual field-valued points into these charts. -/
theorem complexAffineOpenCoverPointMap_surjective {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    Function.Surjective (complexAffineOpenCoverPointMap f 𝒰) := by
  intro p
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (schemeComplexPointImage f p)
  have hp : schemeComplexPointImage f p ∈ Set.range (complexAffineOpenCoverChart 𝒰 i).map := by
    refine ⟨(𝒰.X i).isoSpec.hom y, ?_⟩
    change (((𝒰.X i).isoSpec.hom ≫ (𝒰.X i).isoSpec.inv) ≫ 𝒰.f i) y = _
    simpa only [Iso.hom_inv_id, Category.id_comp] using hy
  refine ⟨⟨i, schemeComplexPointLift f (complexAffineOpenCoverChart 𝒰 i).map p hp⟩, ?_⟩
  apply Subtype.ext
  exact schemeComplexPointLift_fac f (complexAffineOpenCoverChart 𝒰 i).map p hp

/-- This actual cover point map is continuous in the genuine global analytic topology. -/
theorem complexAffineOpenCoverPointMap_continuous {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    letI := schemeAnalyticPointTopology f
    Continuous (complexAffineOpenCoverPointMap f 𝒰) := by
  let := schemeAnalyticPointTopology f
  exact continuous_sigma_iff.mpr (fun i =>
    complexAffineChartPointMap_continuous f (complexAffineOpenCoverChart 𝒰 i))

/-- The actual point map of the native cover is open. -/
theorem complexAffineOpenCoverPointMap_isOpenMap {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    letI := schemeAnalyticPointTopology f
    IsOpenMap (complexAffineOpenCoverPointMap f 𝒰) := by
  let := schemeAnalyticPointTopology f
  intro V hV
  have heq : complexAffineOpenCoverPointMap f 𝒰 '' V =
      ⋃ i : 𝒰.I₀, complexAffineChartPointMap f (complexAffineOpenCoverChart 𝒰 i) ''
        ((fun q : ComplexAffineChartPoint f (complexAffineOpenCoverChart 𝒰 i) =>
          (⟨i, q⟩ : Σ j : 𝒰.I₀, ComplexAffineChartPoint f (complexAffineOpenCoverChart 𝒰 j))) ⁻¹' V) := by
    ext p
    constructor
    · rintro ⟨⟨i, q⟩, hq, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, q, hq, rfl⟩
    · intro hp
      obtain ⟨i, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
      exact ⟨⟨i, q⟩, hq, rfl⟩
  rw [heq]
  exact isOpen_iUnion (fun i =>
    complexAffineChartPointMap_isOpenMap f (complexAffineOpenCoverChart 𝒰 i) _
      ((isOpen_sigma_iff.mp hV) i))

/-- A countable native affine open cover with native local finite type yields second countability. -/
theorem schemeAnalyticPoint_secondCountable_of_affineOpenCover {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType f]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.X i)] [Countable 𝒰.I₀] :
    letI := schemeAnalyticPointTopology f
    SecondCountableTopology (SchemeComplexPoint f) := by
  let := schemeAnalyticPointTopology f
  let : ∀ i : 𝒰.I₀, SecondCountableTopology
      (ComplexAffineChartPoint f (complexAffineOpenCoverChart 𝒰 i)) :=
    fun i => complexAffineChartPoint_secondCountable f (complexAffineOpenCoverChart 𝒰 i)
  have hq := (complexAffineOpenCoverPointMap_isOpenMap f 𝒰).isQuotientMap
    (complexAffineOpenCoverPointMap_continuous f 𝒰)
    (complexAffineOpenCoverPointMap_surjective f 𝒰)
  exact hq.secondCountableTopology (complexAffineOpenCoverPointMap_isOpenMap f 𝒰)

/-- Actual complex points of a quasi-compact locally finite-type complex scheme are second countable.
Native quasi-compactness is used only to choose a finite native affine open cover. -/
theorem schemeAnalyticPoint_secondCountable {X : Scheme}
    (f : X ⟶ Spec (.of ℂ)) [QuasiCompact f] [LocallyOfFiniteType f] :
    letI := schemeAnalyticPointTopology f
    SecondCountableTopology (SchemeComplexPoint f) := by
  let := schemeAnalyticPointTopology f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact schemeAnalyticPoint_secondCountable_of_affineOpenCover f X.affineCover.finiteSubcover

end

end BingWangEntropy
