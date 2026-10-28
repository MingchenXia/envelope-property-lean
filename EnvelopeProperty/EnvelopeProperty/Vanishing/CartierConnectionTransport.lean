import Mathlib.Algebra.Homology.HomologicalComplex

/-! # Transport of every original complex differential through actual term isomorphisms -/

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe u v

namespace EnvelopeProperty.Vanishing.CartierConnectionTransport

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c)
    (A : ι → C) (e : ∀ i, K.X i ≅ A i)

/-- The actual differentials in every pair of degrees, transported through the given isomorphisms. -/
def complex : HomologicalComplex C c where
  X := A
  d i j := (e i).inv ≫ K.d i j ≫ (e j).hom
  shape i j h := by rw [K.shape i j h, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      HomologicalComplex.d_comp_d_assoc, comp_zero, zero_comp]

/-- The original term isomorphisms are an isomorphism of whole complexes. -/
def iso : K ≅ complex K A e := by
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j _
  dsimp only [complex]
  simp only [Iso.hom_inv_id_assoc]

/-- Every transported square is zero, including the actual adjacent-degree squares. -/
theorem differential_comp (i j k : ι) :
    ((e i).inv ≫ K.d i j ≫ (e j).hom) ≫
      ((e j).inv ≫ K.d j k ≫ (e k).hom) = 0 :=
  (complex K A e).d_comp_d i j k

end EnvelopeProperty.Vanishing.CartierConnectionTransport
