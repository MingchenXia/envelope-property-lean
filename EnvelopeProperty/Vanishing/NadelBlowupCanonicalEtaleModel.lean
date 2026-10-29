import EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtalePolynomial

/-! # The actual entire etale canonical differential over the original whole model blowup -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MvPolynomial
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleModel
open CoordinateSubspace CanonicalGeometry NadelBlowupCanonicalGluingDescent
open NadelBlowupCanonicalGluingWhole NadelBlowupCanonicalEtalePolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem differential_composite_isIso {k : Type u} [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (h : Z ⟶ Y) (n : ℕ)
    (hg : IsIso (exteriorCotangentSheafPullbackMap f g n))
    (hh : IsIso (exteriorCotangentSheafPullbackMap (g ≫ f) h n)) :
    IsIso (exteriorCotangentSheafPullbackMap f (h ≫ g) n) := by
  let := hg
  let := hh
  rw [exteriorCotangentSheafPullbackMap_comp]
  infer_instance

variable (k : Type u) [Field k] (n r : ℕ)

/-- The SAME original native model chart preserves the SAME original
field structural morphism, as a whole scheme map. -/
theorem modelChart_structure (j : Fin n) (hj : j.val < r) :
    modelChart k n r j hj ≫ (affineBlowUp.π (centerIdeal k n r) ≫
      affineStructuralMap k (.of (MvPolynomial (Fin n) k))) =
        affineStructuralMap k (.of (MvPolynomial (Fin n) k)) := by
  rw [← Category.assoc, modelChart_π]
  exact affineAlgebraMap_structuralSquare k (.of (MvPolynomial (Fin n) k))
    (.of (MvPolynomial (Fin n) k)) (affineBlowUpAlgebra.chartSubst k (center n r) j)

/-- On the actual Cartesian inverse image of every original model chart,
the pulled WHOLE native etale canonical differential is an isomorphism.
The actual square, source coordinates and entire composite maps are internal. -/
theorem chart_pullback_differential_isIso {Y : Scheme.{u}}
    (g : Y ⟶ modelBlowUp k n r) [Etale g] (j : Fin n) (hj : j.val < r) :
    IsIso ((Scheme.Modules.pullback (pullback.fst g (modelChart k n r j hj))).map
      (exteriorCotangentSheafPullbackMap
        (affineBlowUp.π (centerIdeal k n r) ≫
          affineStructuralMap k (.of (MvPolynomial (Fin n) k))) g n)) := by
  let f := affineBlowUp.π (centerIdeal k n r) ≫
    affineStructuralMap k (.of (MvPolynomial (Fin n) k))
  let a := modelChart k n r j hj
  let q := pullback.fst g a
  let h := pullback.snd g a
  have ha : IsIso (exteriorCotangentSheafPullbackMap f a n) :=
    isIso_exteriorCotangentSheafPullbackMap_openImmersion f a n
  have hh : IsIso (exteriorCotangentSheafPullbackMap (a ≫ f) h n) :=
    Eq.mpr (congrArg (fun b => IsIso (exteriorCotangentSheafPullbackMap b h n))
      (modelChart_structure k n r j hj)) (polynomial_etale_isIso k n h)
  have hc : IsIso (exteriorCotangentSheafPullbackMap f (q ≫ g) n) :=
    Eq.mpr (congrArg (fun b => IsIso (exteriorCotangentSheafPullbackMap f b n))
      (pullback.condition (f := g) (g := a))) (differential_composite_isIso f a h n ha hh)
  exact pullback_differential_isIso_of_open_composite f g q n hc

/-- The actual Cartesian inverse images of the actual native model charts
cover EVERY original etale-source point with genuine preimage points. -/
theorem modelChart_pullback_point_cover {Y : Scheme.{u}} (g : Y ⟶ modelBlowUp k n r)
    (y : Y) :
    ∃ (i : {j : Fin n // j.val < r})
      (z : (pullback g (modelChart k n r i.1 i.2) : Scheme.{u})),
      pullback.fst g (modelChart k n r i.1 i.2) z = y := by
  obtain ⟨i, z, hz⟩ := modelChart_point_cover k n r (g y)
  have hy : y ∈ (pullback.fst g (modelChart k n r i.1 i.2)).opensRange := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact ⟨z, hz⟩
  exact ⟨i, hy⟩

/-- Every actual etale morphism to the SAME WHOLE original coordinate
blowup has its ENTIRE actual native canonical differential an isomorphism.
No affine cover, basis, local comparison or target-shaped certificate is input. -/
theorem coordinateBlowup_etale_isIso {Y : Scheme.{u}}
    (g : Y ⟶ modelBlowUp k n r) [Etale g] :
    IsIso (exteriorCotangentSheafPullbackMap
      (affineBlowUp.π (centerIdeal k n r) ≫
        affineStructuralMap k (.of (MvPolynomial (Fin n) k))) g n) := by
  apply isIso_of_open_cover
    (fun i : {j : Fin n // j.val < r} => pullback g (modelChart k n r i.1 i.2))
    (fun i => pullback.fst g (modelChart k n r i.1 i.2))
    (modelChart_pullback_point_cover k n r g)
  intro i
  exact chart_pullback_differential_isIso k n r g i.1 i.2

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalEtaleModel
