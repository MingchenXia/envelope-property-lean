import EnvelopeProperty.Vanishing.ArithmeticOriginalLineChart
import EnvelopeProperty.AlgGeom.GeneratedTupleTwistSections
import EnvelopeProperty.AlgGeom.ProjectiveCoordinateSectionRelations
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization

/-! # Actual coordinate sections on arbitrary affine sources over a domain

The comparison is transported from a genuine universal polynomial domain.
No integrality condition is imposed on the original affine source.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open Alterations Alterations.Geometry.FiniteProjective
open Alterations.Geometry.ProjectiveIdeal
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineTuple
open SchemeLineSectionEvaluation SchemeLineSectionFactorization
open GeneratedTupleTwistSections ProjectiveCoordinateSectionRelations

variable {R A : Type u} [CommRing R] [CommRing A] {m : ℕ}

private def universalTuple (i : Fin (m + 1)) : Fin (m + 1) → MvPolynomial (ChartIndex i) R :=
  fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩

private theorem universalTuple_pivot (i : Fin (m + 1)) :
    universalTuple (R := R) i i = 1 := by simp [universalTuple]

private theorem universalTuple_span (i : Fin (m + 1)) :
    Ideal.span (Set.range (universalTuple (R := R) i)) = ⊤ := by
  apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
  exact Ideal.subset_span ⟨i, universalTuple_pivot i⟩

private theorem eval_universalTuple (r : R →+* A) (a : Fin (m + 1) → A)
    (i : Fin (m + 1)) (hi : a i = 1) :
    (fun j => MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1)
      (universalTuple (R := R) i j)) = a := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp [universalTuple, hi]
  · simp only [universalTuple, dif_neg h]
    exact MvPolynomial.eval₂Hom_X' r (fun j : ChartIndex i => a j.1) ⟨j, h⟩

private theorem universalTuple_factor (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1))) ≫
      affineTupleMap MvPolynomial.C (universalTuple (R := R) i) (universalTuple_span i) =
        affineTupleMap r a ha := by
  let q := MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1)
  have hb : Ideal.span (Set.range (fun j => q (universalTuple (R := R) i j))) = ⊤ := by
    rw [eval_universalTuple r a i hi]
    exact ha
  have hqr : q.comp MvPolynomial.C = r := by
    ext c
    exact MvPolynomial.eval₂Hom_C _ _ _
  exact (affineTupleMap_naturality MvPolynomial.C (universalTuple (R := R) i)
    (universalTuple_span i) q hb).trans
      (affineTupleMap_congr hqr (eval_universalTuple r a i hi) hb ha)

private theorem spec_scalar_naturality {B C : Type u} [CommRing B] [CommRing C]
    (q : B →+* C) (b : B) :
    (Spec.map (CommRingCat.ofHom q)).appTop.hom ((Scheme.ΓSpecIso (.of B)).inv.hom b) =
      (Scheme.ΓSpecIso (.of C)).inv.hom (q b) := by
  exact (congrArg (fun f => f.hom b) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q))).symm

variable [IsDomain R]

/-- The original coordinate section indexed by a normalized pivot is an
actual isomorphism after pullback along the original native tuple morphism. -/
theorem pulledPivot_isIso (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (k : Fin (m + 1)) :
    IsIso (pullbackSectionHom (affineTupleMap r a ha)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i))) := by
  let b := universalTuple (R := R) i
  let hb := universalTuple_span (R := R) i
  let hiB := universalTuple_pivot (R := R) i
  have hB : IsIso (pullbackSectionHom (affineTupleMap MvPolynomial.C b hb)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X R i))) :=
    isIso_pullbackSectionHom_factor (chartFactor MvPolynomial.C b hb i hiB)
      (coordinateOpen (R := R) i).ι (affineTupleMap MvPolynomial.C b hb)
      (chartFactor_comp MvPolynomial.C b hb i hiB) _ (sectionHom_isIso_on_own_chart i k)
  exact isIso_pullbackSectionHom_factor
    (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1))))
    (affineTupleMap MvPolynomial.C b hb) (affineTupleMap r a ha)
    (universalTuple_factor r a ha i hi) _ hB

/-- Every original coordinate has its literal original scalar ratio to the
same original normalized pivot, on the whole original affine scheme. -/
theorem pulledCoordinate_relation (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1)
    (k j : Fin (m + 1)) :
    pullbackSectionHom (affineTupleMap r a ha)
      (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X R j)) =
      ModularCurves.unitEndomorphismOfTopSection ((Scheme.ΓSpecIso (.of A)).inv.hom (a j)) ≫
        pullbackSectionHom (affineTupleMap r a ha)
          (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
            (MvPolynomial.isHomogeneous_X R i)) := by
  let b := universalTuple (R := R) i
  let hb := universalTuple_span (R := R) i
  let hiB := universalTuple_pivot (R := R) i
  have hB := factor_scalar_relation (chartFactor MvPolynomial.C b hb i hiB)
    (coordinateOpen (R := R) i).ι (affineTupleMap MvPolynomial.C b hb)
    (chartFactor_comp MvPolynomial.C b hb i hiB)
    (M := coordinateHyperplaneTwist (R := R) k 1)
    (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j))
    (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i)) _ (sectionHom_ratio_on_chart i k j)
  rw [chartFactor_coordinate] at hB
  have h := factor_scalar_relation
    (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1))))
    (affineTupleMap MvPolynomial.C b hb) (affineTupleMap r a ha)
    (universalTuple_factor r a ha i hi) _ _ _ hB
  rw [spec_scalar_naturality] at h
  have hj := congrFun (eval_universalTuple r a i hi) j
  exact (congrArg (fun c => ModularCurves.unitEndomorphismOfTopSection
    ((Scheme.ΓSpecIso (.of A)).inv.hom c) ≫
      pullbackSectionHom (affineTupleMap r a ha)
        (ProjectiveHomogeneousSections.sectionHom (R := R) k 1 (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X R i))) hj).symm ▸ h

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineTuple
