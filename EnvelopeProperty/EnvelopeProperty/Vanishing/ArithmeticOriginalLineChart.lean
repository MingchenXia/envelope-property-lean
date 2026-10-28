import EnvelopeProperty.AlgGeom.GeneratedTupleProjectiveCoordinates

/-! # The original tuple's normalized chart over arbitrary source rings

The domain-source coordinate formula is transported from a genuine free
polynomial domain over the original coefficient domain.  The original affine
source ring need not be a domain.  Both native tuple morphisms and original
coefficient maps are retained.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open DeJongAlterations DeJongAlterations.Geometry.FiniteProjective
open DeJongAlterations.Geometry.ProjectiveIdeal
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalLineChart

variable {R A : Type u} [CommRing R] [IsDomain R] [CommRing A] {m : ℕ}

/-- The actual original normalized tuple morphism has its original coordinate
evaluation formula, without any integrality assumption on its source ring. -/
theorem affineTupleMap_eq_eval_chart (r : R →+* A) (a : Fin (m + 1) → A)
    (ha : Ideal.span (Set.range a) = ⊤) (i : Fin (m + 1)) (hi : a i = 1) :
    affineTupleMap r a ha =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1))) ≫
        DeJongAlterations.Geometry.Segre.coordinateChartInclusion i := by
  classical
  let B := MvPolynomial (ChartIndex i) R
  let b : Fin (m + 1) → B := fun j => if h : j = i then 1 else MvPolynomial.X ⟨j, h⟩
  have hbi : b i = 1 := by simp [b]
  have hb : Ideal.span (Set.range b) = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ isUnit_one
    exact Ideal.subset_span ⟨i, hbi⟩
  let q : B →+* A := MvPolynomial.eval₂Hom r (fun j : ChartIndex i => a j.1)
  have hqb : (fun j => q (b j)) = a := by
    funext j
    by_cases h : j = i
    · subst j
      simp [b, q, hi]
    · simp only [b, dif_neg h]
      exact MvPolynomial.eval₂Hom_X' r (fun j : ChartIndex i => a j.1) ⟨j, h⟩
  have hqa : Ideal.span (Set.range (fun j => q (b j))) = ⊤ := by rw [hqb]; exact ha
  have hqr : q.comp (MvPolynomial.C : R →+* B) = r := by
    ext c
    exact MvPolynomial.eval₂Hom_C _ _ _
  have hn := affineTupleMap_naturality (MvPolynomial.C : R →+* B) b hb q hqa
  rw [EnvelopeProperty.GeneratedTupleProjectiveCoordinates.affineTupleMap_eq_eval_chart
    (MvPolynomial.C : R →+* B) b hb i hbi, ← Category.assoc, ← Spec.map_comp] at hn
  have he : q.comp (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* B)
      (fun j : ChartIndex i => b j.1)) = q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    · intro j
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', b, dif_neg j.2]
  have hc : CommRingCat.ofHom (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* B)
      (fun j : ChartIndex i => b j.1)) ≫ CommRingCat.ofHom q = CommRingCat.ofHom q := by
    exact CommRingCat.hom_ext he
  rw [hc] at hn
  exact (affineTupleMap_congr hqr hqb hqa ha).symm.trans hn.symm

end EnvelopeProperty.Vanishing.ArithmeticOriginalLineChart
