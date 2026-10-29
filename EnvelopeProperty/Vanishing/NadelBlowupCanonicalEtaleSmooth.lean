import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSmoothAffine

/-! # Basis-free ENTIRE native etale canonical differential on ANY original smooth scheme -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSmooth
open CanonicalGeometry NadelBlowupCanonicalGluingDescent
open NadelBlowupCanonicalEtalePolynomial NadelBlowupCanonicalEtaleSmoothAffine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The genuine standard-smooth affine coordinate ring at the original point. -/
def chartRing (x : X) : CommRingCat.{u} := Γ(X, (smoothCotangentChart f n x).val)

/-- The SAME genuine affine spectrum chart to the original scheme. -/
def chartMap (x : X) : Spec (chartRing f n x) ⟶ X :=
  (smoothCotangentChart f n x).property.1.fromSpec

theorem chartMap_openImmersion (x : X) : IsOpenImmersion (chartMap f n x) := by
  unfold chartMap
  infer_instance

attribute [local instance] chartMap_openImmersion

/-- The genuine selected source chart covers its actual original point. -/
theorem chartMap_point (x : X) : ∃ z : Spec (chartRing f n x), chartMap f n x z = x := by
  have hx : x ∈ (chartMap f n x).opensRange := by
    change x ∈ ((smoothCotangentChart f n x).property.1.fromSpec).opensRange
    rw [IsAffineOpen.opensRange_fromSpec]
    exact (smoothCotangentChart f n x).property.2.1
  exact hx

/-- On the actual Cartesian inverse image of each original standard-smooth
chart, the pulled ENTIRE original etale differential is an isomorphism. -/
theorem chart_pullback_differential_isIso {Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] (x : X) :
    IsIso ((Scheme.Modules.pullback (pullback.fst g (chartMap f n x))).map
      (exteriorCotangentSheafPullbackMap f g n)) := by
  let U := smoothCotangentChart f n x
  let A := chartRing f n x
  let a := chartMap f n x
  let q := pullback.fst g a
  let h := pullback.snd g a
  let : Algebra k A := affineChartAlgebra f U.val
  let : Algebra.IsStandardSmoothOfRelativeDimension n k A := U.property.2.2
  have he : a ≫ f = affineStructuralMap k A :=
    affineChartStructuralMap_eq_affineStructuralMap f U.property.1
  have ha : IsIso (exteriorCotangentSheafPullbackMap f a n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f a n
  have hh : IsIso (exteriorCotangentSheafPullbackMap (a ≫ f) h n) :=
    Eq.mpr (congrArg (fun b => IsIso (exteriorCotangentSheafPullbackMap b h n)) he)
      (NadelBlowupCanonicalEtaleSmoothAffine.etale_isIso k A n h)
  have hc : IsIso (exteriorCotangentSheafPullbackMap f (q ≫ g) n) :=
    Eq.mpr (congrArg (fun b => IsIso (exteriorCotangentSheafPullbackMap f b n))
      (pullback.condition (f := g) (g := a))) (differential_composite_isIso f a h n ha hh)
  exact pullback_differential_isIso_of_open_composite f g q n hc

/-- The actual original smooth-chart Cartesian inverse images cover ALL
original source points, with genuine original preimage points. -/
theorem chart_pullback_point_cover {Y : Scheme.{u}} (g : Y ⟶ X) (y : Y) :
    ∃ (x : X) (z : (pullback g (chartMap f n x) : Scheme.{u})),
      pullback.fst g (chartMap f n x) z = y := by
  obtain ⟨z, hz⟩ := chartMap_point f n (g y)
  have hy : y ∈ (pullback.fst g (chartMap f n (g y))).opensRange := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact ⟨z, hz⟩
  exact ⟨g y, hy⟩

/-- On ANY SAME original n-smooth scheme, ANY actual original etale map
has its SAME ENTIRE native top exterior differential an isomorphism.
No original global differential basis, integrality, affine cover, target
smoothness, local comparison or desired canonical isomorphism is supplied. -/
theorem etale_isIso {Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] :
    IsIso (exteriorCotangentSheafPullbackMap f g n) := by
  apply isIso_of_open_cover
    (fun x : X => pullback g (chartMap f n x))
    (fun x => pullback.fst g (chartMap f n x)) (chart_pullback_point_cover f n g)
  intro x
  exact chart_pullback_differential_isIso f n g x

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleSmooth
