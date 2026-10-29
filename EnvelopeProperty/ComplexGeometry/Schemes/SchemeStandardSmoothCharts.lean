import EnvelopeProperty.ComplexGeometry.Schemes.CotangentSmoothLocallyFree
import EnvelopeProperty.ComplexGeometry.Schemes.SchemeAnalyticAtlas
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Genuine standard-smooth complex scheme neighborhoods

Native scheme smoothness derives actual affine open immersions and their
standard-smooth inherited complex algebras. Finite submersive presentations
are reindexed to their actual dimension. Genuine complex scheme points lift
through these open immersions and retain their literal evaluation topology.
-/

open CategoryTheory AlgebraicGeometry Algebra
open scoped Topology

namespace ComplexSchemes

noncomputable section

section FinitePresentations
variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- A native standard-smooth relative-dimension assertion produces an
actual finite submersive presentation with `n+r` variables and `r` relations. -/
theorem exists_standardSmoothFinitePresentation (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    ∃ r : ℕ, Nonempty (SubmersivePresentation R A (Fin (n + r)) (Fin r)) := by
  classical
  obtain ⟨I, J, hJ, hI, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := R) (S := A)
  let := hI
  let := hJ
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  have hle : Fintype.card J ≤ Fintype.card I :=
    Fintype.card_le_of_injective P.map P.map_inj
  have hdimension : Fintype.card I - Fintype.card J = n := by
    simpa only [Presentation.dimension, Nat.card_eq_fintype_card] using hP
  have hcard : Fintype.card I = n + Fintype.card J :=
    (Nat.sub_add_cancel hle).symm.trans
      (congrArg (fun m ↦ m + Fintype.card J) hdimension)
  let eI : I ≃ Fin (n + Fintype.card J) := Fintype.equivFinOfCardEq hcard
  let eJ : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  exact ⟨Fintype.card J, ⟨P.reindex eI.symm eJ.symm⟩⟩

/-- Choose only a presentation whose existence is derived from the native
standard-smooth relative-dimension property. -/
def standardSmoothFinitePresentation (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    Σ r : ℕ, SubmersivePresentation R A (Fin (n + r)) (Fin r) :=
  let h := exists_standardSmoothFinitePresentation R A n
  ⟨h.choose, Classical.choice h.choose_spec⟩

/-- The produced presentation has exactly the prescribed actual dimension. -/
theorem standardSmoothFinitePresentation_dimension (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    (standardSmoothFinitePresentation R A n).2.dimension = n :=
  jacobianPresentation_dimension (standardSmoothFinitePresentation R A n).2.toPreSubmersivePresentation

end FinitePresentations

section SchemeCharts
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- The actual inherited affine complex algebra on a genuine chart is
precisely the algebra defined by the literal structural constant map. -/
theorem affineChart_preimage_structure {V : X.Opens} (hV : IsAffineOpen V) :
    Spec.preimage (hV.fromSpec ≫ f) = (schemeConstantPresheafMap f).app (.op V) := by
  exact (congrArg Spec.preimage (affineChartStructuralMap f hV)).trans
    (Spec.preimage_map ((schemeConstantPresheafMap f).app (.op V)))

/-- Every actual complex point of a smooth scheme lies in a genuine
standard-smooth affine neighborhood with its actual inherited complex algebra. -/
theorem exists_standardSmoothComplexAffineChart (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    ∃ c : ComplexAffineChart X,
      schemeComplexPointImage f p ∈ Set.range c.map ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (Spec.preimage (c.map ≫ f)).hom := by
  obtain ⟨V, hV, hpV, hs⟩ := smooth_cotangent_affine_chart f n (schemeComplexPointImage f p)
  let c : ComplexAffineChart X := ⟨Γ(X, V), hV.fromSpec, inferInstance⟩
  refine ⟨c, ?_, ?_⟩
  · exact Eq.mpr (congrArg (fun S : Set X ↦ schemeComplexPointImage f p ∈ S)
      hV.range_fromSpec) hpV
  · exact (congrArg (fun q ↦ RingHom.IsStandardSmoothOfRelativeDimension n q.hom)
      (affineChart_preimage_structure f hV)).mpr hs

/-- The chosen chart is a genuine open immersion; its point containment and
standard smoothness were derived, rather than supplied by an atlas hypothesis. -/
def standardSmoothComplexAffineChart (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    {c : ComplexAffineChart X // schemeComplexPointImage f p ∈ Set.range c.map ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (Spec.preimage (c.map ≫ f)).hom} :=
  let h := exists_standardSmoothComplexAffineChart f n p
  ⟨h.choose, h.choose_spec⟩

/-- The literal inherited complex algebra on the produced chart is
standard smooth of the actual specified relative dimension. -/
theorem standardSmoothComplexAffineChart_isStandardSmooth (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    Algebra.IsStandardSmoothOfRelativeDimension n ℂ (standardSmoothComplexAffineChart f n p).val.ring :=
  (standardSmoothComplexAffineChart f n p).property.2

/-- The actual standard-smooth neighborhood supplies a genuine finite
submersive presentation, using precisely its inherited complex structure. -/
def standardSmoothComplexChartPresentation (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    Σ r : ℕ, SubmersivePresentation ℂ (standardSmoothComplexAffineChart f n p).val.ring
      (Fin (n + r)) (Fin r) := by
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  letI := standardSmoothComplexAffineChart_isStandardSmooth f n p
  exact standardSmoothFinitePresentation ℂ _ n

/-- The actual produced chart presentation has dimension `n`. -/
theorem standardSmoothComplexChartPresentation_dimension (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    (standardSmoothComplexChartPresentation f n p).2.dimension = n := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  exact jacobianPresentation_dimension
    (standardSmoothComplexChartPresentation f n p).2.toPreSubmersivePresentation

end SchemeCharts

end
end ComplexSchemes

namespace ComplexSchemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- Literal algebra points of a genuine affine chart map to actual global
complex scheme points through its inherited structure and actual open immersion. -/
def complexAffineAlgebraPointMap (c : ComplexAffineChart X) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    ComplexAlgebraPoint c.ring → SchemeComplexPoint f := by
  letI := affinePointFieldAlgebra (c.map ≫ f)
  exact complexAffineChartPointMap f c ∘ (affineSchemePointEquivOfStructure (c.map ≫ f)).symm

/-- The point map is literally the Spec map of the algebra evaluation,
followed by the actual affine open immersion. -/
theorem complexAffineAlgebraPointMap_val (c : ComplexAffineChart X) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    ∀ q : ComplexAlgebraPoint c.ring,
      (complexAffineAlgebraPointMap f c q).val =
        Spec.map (CommRingCat.ofHom q.toRingHom) ≫ c.map := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  intro q
  let p := (affineSchemePointEquivOfStructure (c.map ≫ f)).symm q
  have hp : Spec.preimage p.val = CommRingCat.ofHom q.toRingHom := by
    ext a
    exact (affineSchemePointEquivOfStructure_apply (c.map ≫ f) p a).symm.trans
      (congrArg (fun t : ComplexAlgebraPoint c.ring ↦ t a)
        ((affineSchemePointEquivOfStructure (c.map ≫ f)).apply_symm_apply q))
  exact congrArg (fun h ↦ h ≫ c.map)
    ((Spec.map_preimage p.val).symm.trans (congrArg Spec.map hp))

/-- The literal evaluation point map is an actual analytic open embedding. -/
theorem complexAffineAlgebraPointMap_isOpenEmbedding (c : ComplexAffineChart X) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    letI := schemeAnalyticPointTopology f
    Topology.IsOpenEmbedding (complexAffineAlgebraPointMap f c) := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  let := schemeAnalyticPointTopology f
  exact (complexAffineChartPointMap_isOpenEmbedding f c).comp
    (affineSchemePointHomeomorphOfStructure (c.map ≫ f)).symm.isOpenEmbedding

/-- Its genuine range is exactly the points whose underlying scheme image
lies in the actual affine open immersion. -/
theorem complexAffineAlgebraPointMap_range (c : ComplexAffineChart X) :
    letI := affinePointFieldAlgebra (c.map ≫ f)
    Set.range (complexAffineAlgebraPointMap f c) =
      {p | schemeComplexPointImage f p ∈ Set.range c.map} := by
  let := affinePointFieldAlgebra (c.map ≫ f)
  rw [complexAffineAlgebraPointMap, Set.range_comp,
    Equiv.range_eq_univ, Set.image_univ]
  exact complexAffineChartPointMap_range f c

/-- Native open-immersion lifting produces the actual point of the
standard-smooth affine neighborhood. -/
def standardSmoothComplexChartPoint (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    SchemeComplexPoint ((standardSmoothComplexAffineChart f n p).val.map ≫ f) :=
  schemeComplexPointLift f (standardSmoothComplexAffineChart f n p).val.map p
    (standardSmoothComplexAffineChart f n p).property.1

/-- The produced neighborhood point composes to the original actual
complex scheme morphism. -/
theorem standardSmoothComplexChartPoint_fac (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    (standardSmoothComplexChartPoint f n p).val ≫
      (standardSmoothComplexAffineChart f n p).val.map = p.val :=
  schemeComplexPointLift_fac f _ p _

/-- The actual chart point determines a literal complex algebra evaluation
under precisely the inherited structural complex algebra. -/
def standardSmoothComplexAlgebraPoint (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring :=
  affineSchemePointEquivOfStructure ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    (standardSmoothComplexChartPoint f n p)

/-- The actual algebra point maps back to the exact original complex
scheme point under the actual analytic affine chart embedding. -/
theorem standardSmoothComplexAlgebraPoint_map (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    complexAffineAlgebraPointMap f (standardSmoothComplexAffineChart f n p).val
      (standardSmoothComplexAlgebraPoint f n p) = p := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  have hp : complexAffineChartPointMap f (standardSmoothComplexAffineChart f n p).val
      (standardSmoothComplexChartPoint f n p) = p :=
    Subtype.ext (standardSmoothComplexChartPoint_fac f n p)
  exact (congrArg (complexAffineChartPointMap f (standardSmoothComplexAffineChart f n p).val)
    ((affineSchemePointEquivOfStructure ((standardSmoothComplexAffineChart f n p).val.map ≫ f)).symm_apply_apply
      (standardSmoothComplexChartPoint f n p))).trans hp

end
end ComplexSchemes

namespace ComplexSchemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- The genuine standard-smooth affine neighborhood gives an actual open
partial homeomorphism from global scheme points to its literal algebra points. -/
def standardSmoothComplexPointOpenChart (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    OpenPartialHomeomorph (SchemeComplexPoint f)
      (ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring) := by
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  letI := schemeAnalyticPointTopology f
  letI : Nonempty (ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring) :=
    ⟨standardSmoothComplexAlgebraPoint f n p⟩
  exact ((complexAffineAlgebraPointMap_isOpenEmbedding f (standardSmoothComplexAffineChart f n p).val).toOpenPartialHomeomorph (complexAffineAlgebraPointMap f (standardSmoothComplexAffineChart f n p).val)).symm

/-- Its actual source is precisely the genuine affine neighborhood in the
actual analytic scheme-point topology. -/
theorem standardSmoothComplexPointOpenChart_source (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    (standardSmoothComplexPointOpenChart f n p).source =
      {q | schemeComplexPointImage f q ∈ Set.range (standardSmoothComplexAffineChart f n p).val.map} := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  let : Nonempty (ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring) :=
    ⟨standardSmoothComplexAlgebraPoint f n p⟩
  simp only [standardSmoothComplexPointOpenChart, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact complexAffineAlgebraPointMap_range f (standardSmoothComplexAffineChart f n p).val

/-- Its entire target is the literal algebra-point set with the inherited
evaluation topology. -/
theorem standardSmoothComplexPointOpenChart_target (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    (standardSmoothComplexPointOpenChart f n p).target = Set.univ := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  let : Nonempty (ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring) :=
    ⟨standardSmoothComplexAlgebraPoint f n p⟩
  simp only [standardSmoothComplexPointOpenChart, OpenPartialHomeomorph.symm_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]

/-- The actual original complex point lies in the genuine open source. -/
theorem standardSmoothComplexPointOpenChart_point_mem_source (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    p ∈ (standardSmoothComplexPointOpenChart f n p).source := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  exact Eq.mpr (congrArg (fun S : Set (SchemeComplexPoint f) ↦ p ∈ S)
    (standardSmoothComplexPointOpenChart_source f n p))
    (standardSmoothComplexAffineChart f n p).property.1

/-- The actual open chart takes the original scheme point to precisely its
native lifted algebra evaluation point. -/
theorem standardSmoothComplexPointOpenChart_point (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    standardSmoothComplexPointOpenChart f n p p = standardSmoothComplexAlgebraPoint f n p := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  let : Nonempty (ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring) :=
    ⟨standardSmoothComplexAlgebraPoint f n p⟩
  exact (congrArg (standardSmoothComplexPointOpenChart f n p)
    (standardSmoothComplexAlgebraPoint_map f n p).symm).trans
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
        (complexAffineAlgebraPointMap f (standardSmoothComplexAffineChart f n p).val)
        (complexAffineAlgebraPointMap_isOpenEmbedding f (standardSmoothComplexAffineChart f n p).val))

/-- Its inverse is exactly the actual affine algebra-evaluation point map. -/
theorem standardSmoothComplexPointOpenChart_symm (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ q : ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring,
      (standardSmoothComplexPointOpenChart f n p).symm q =
        complexAffineAlgebraPointMap f (standardSmoothComplexAffineChart f n p).val q := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  let : Nonempty (ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring) :=
    ⟨standardSmoothComplexAlgebraPoint f n p⟩
  intro q
  exact congrFun ((complexAffineAlgebraPointMap_isOpenEmbedding f (standardSmoothComplexAffineChart f n p).val).toOpenPartialHomeomorph_apply (complexAffineAlgebraPointMap f (standardSmoothComplexAffineChart f n p).val)) q

/-- The inverse chart is literally the Spec map of evaluation followed by
the genuine chosen affine open immersion. -/
theorem standardSmoothComplexPointOpenChart_symm_val (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    letI := schemeAnalyticPointTopology f
    ∀ q : ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring,
      ((standardSmoothComplexPointOpenChart f n p).symm q).val =
        Spec.map (CommRingCat.ofHom q.toRingHom) ≫ (standardSmoothComplexAffineChart f n p).val.map := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  let := schemeAnalyticPointTopology f
  intro q
  exact (congrArg Subtype.val (standardSmoothComplexPointOpenChart_symm f n p q)).trans
    (complexAffineAlgebraPointMap_val f (standardSmoothComplexAffineChart f n p).val q)

end
end ComplexSchemes

namespace ComplexSchemes

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (f : X ⟶ Spec (.of ℂ))

/-- The actual unselected presentation indices are exactly `n` free
coordinate choices, derived from the genuine presentation and dimension count. -/
def standardSmoothComplexChartFreeIndexEquiv (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    ((Set.range (standardSmoothComplexChartPresentation f n p).2.map)ᶜ :
      Set (Fin (n + (standardSmoothComplexChartPresentation f n p).1))) ≃ Fin n := by
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  exact (submersiveFreeIndexEquiv (standardSmoothComplexChartPresentation f n p).2).trans
    (finCongr (standardSmoothComplexChartPresentation_dimension f n p))

/-- Each free coordinate is an actual generator of the actual inherited
complex algebra of the genuine standard-smooth affine neighborhood. -/
def standardSmoothComplexChartFreeGenerator (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) (i : Fin n) :
    (standardSmoothComplexAffineChart f n p).val.ring :=
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  (standardSmoothComplexChartPresentation f n p).2.val
    ((standardSmoothComplexChartFreeIndexEquiv f n p).symm i).val

/-- The dimension-`n` coordinate vector consists of literal evaluations
at the actual unselected presentation generators. -/
def standardSmoothComplexChartCoordinates (n : ℕ) [SmoothOfRelativeDimension n f]
    (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    ComplexAlgebraPoint (standardSmoothComplexAffineChart f n p).val.ring → (Fin n → ℂ) :=
  letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  fun q i ↦ q (standardSmoothComplexChartFreeGenerator f n p i)

/-- These literal free coordinates are continuous for the inherited
actual algebra-evaluation topology. -/
theorem standardSmoothComplexChartCoordinates_continuous (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    Continuous (standardSmoothComplexChartCoordinates f n p) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  exact continuous_pi (fun i ↦ complexPoint_evaluation_continuous
    (standardSmoothComplexChartFreeGenerator f n p i))

/-- At the actual lifted complex point, invertibility of the literal
presentation Jacobian is derived from the actual submersive unit condition. -/
theorem standardSmoothComplexChartPresentation_jacobian_isUnit (n : ℕ)
    [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f) :
    letI := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
    IsUnit (standardSmoothComplexAlgebraPoint f n p
      (standardSmoothComplexChartPresentation f n p).2.jacobian) := by
  let := affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)
  exact (standardSmoothComplexChartPresentation f n p).2.jacobian_isUnit.map
    (standardSmoothComplexAlgebraPoint f n p).toMonoidHom

end
end ComplexSchemes
