import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Native homology of finite coproducts of distinct-degree single complexes -/

noncomputable section

namespace EnvelopeProperty.Cartier.DeligneIllusieGradedSourceHomology

open CategoryTheory Category Limits HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
  {I : Type w} [DecidableEq I] {p : ℕ}

/-- The original finite coproduct of the original single complexes. -/
def gradedSource (c : ComplexShape I) (d : Fin p → I) (M : Fin p → C) :
    HomologicalComplex C c :=
  ∐ fun i : Fin p => (single C c (d i)).obj (M i)

private theorem coproduct_inclusion_isIso
    (N : Fin p → C) (i : Fin p) (hN : ∀ j, j ≠ i → IsZero (N j)) :
    IsIso (Sigma.ι N i) := by
  classical
  let π : (∐ N) ⟶ N i :=
    Sigma.desc (fun j => if h : j = i then eqToHom (congrArg N h) else 0)
  refine ⟨⟨π, ?_, ?_⟩⟩
  · dsimp only [π]
    rw [Sigma.ι_desc]
    simp only [dif_pos rfl, eqToHom_refl]
  · apply Sigma.hom_ext
    intro j
    by_cases hji : j = i
    · subst j
      dsimp only [π]
      rw [← assoc, Sigma.ι_desc]
      simp only [dif_pos rfl, eqToHom_refl, id_comp, comp_id]
    · exact (hN j hji).eq_of_src _ _

/-- The canonical inclusion induces an isomorphism on the native homology in its own degree. -/
theorem inclusionHomology_isIso (c : ComplexShape I) (d : Fin p → I) (M : Fin p → C)
    (hd : Function.Injective d) (i : Fin p) :
    IsIso (homologyMap
      (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i) (d i)) := by
  let S : Fin p → HomologicalComplex C c :=
    fun j => (single C c (d j)).obj (M j)
  let H := homologyFunctor C c (d i)
  have hN (j : Fin p) (hji : j ≠ i) : IsZero (H.obj (S j)) := by
    exact isZero_single_obj_homology c (d j) (M j) (d i)
      (fun h => hji (hd h.symm))
  let : IsIso (Sigma.ι (fun j => H.obj (S j)) i) :=
    coproduct_inclusion_isIso _ i hN
  change IsIso (H.map (Sigma.ι S i))
  rw [← ι_comp_sigmaComparison H S i]
  infer_instance

/-- The original inclusion is a quasi-isomorphism at its own degree. -/
theorem inclusion_quasiIsoAt (c : ComplexShape I) (d : Fin p → I) (M : Fin p → C)
    (hd : Function.Injective d) (i : Fin p) :
    QuasiIsoAt (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i) (d i) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact inclusionHomology_isIso c d M hd i

/-- Canonical homology identification, using the inverse of the actual homology inclusion. -/
def homologyIso (c : ComplexShape I) (d : Fin p → I) (M : Fin p → C)
    (hd : Function.Injective d) (i : Fin p) :
    (gradedSource c d M).homology (d i) ≅ M i := by
  letI := inclusionHomology_isIso c d M hd i
  exact (asIso (homologyMap
    (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i) (d i))).symm ≪≫
      singleObjHomologySelfIso c (d i) (M i)

/-- Its inverse is exactly the original single homology inverse followed by the original inclusion. -/
theorem homologyIso_inv (c : ComplexShape I) (d : Fin p → I) (M : Fin p → C)
    (hd : Function.Injective d) (i : Fin p) :
    (homologyIso c d M hd i).inv =
      (singleObjHomologySelfIso c (d i) (M i)).inv ≫
        homologyMap (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i) (d i) := rfl

private theorem coproduct_isZero (N : Fin p → C) (hN : ∀ j, IsZero (N j)) :
    IsZero (∐ N) := by
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ (fun j => (hN j).eq_of_src _ _)

/-- The actual original term is zero outside the chosen degrees, without injectivity assumptions. -/
theorem gradedSource_X_isZero_of_not_mem (c : ComplexShape I) (d : Fin p → I)
    (M : Fin p → C) (q : I) (hq : ∀ i, q ≠ d i) :
    IsZero ((gradedSource c d M).X q) := by
  let S : Fin p → HomologicalComplex C c :=
    fun j => (single C c (d j)).obj (M j)
  let F := eval C c q
  have hN (j : Fin p) : IsZero (F.obj (S j)) :=
    isZero_single_obj_X c (d j) (M j) q (hq j)
  have hZ : IsZero (∐ fun j => F.obj (S j)) := coproduct_isZero _ hN
  exact hZ.of_iso (PreservesCoproduct.iso F S)

/-- Native homology is zero outside the chosen degrees, including an empty finite family. -/
theorem homology_isZero_of_not_mem (c : ComplexShape I) (d : Fin p → I)
    (M : Fin p → C) (q : I) (hq : ∀ i, q ≠ d i) :
    IsZero ((gradedSource c d M).homology q) := by
  let S : Fin p → HomologicalComplex C c :=
    fun j => (single C c (d j)).obj (M j)
  let F := homologyFunctor C c q
  have hN (j : Fin p) : IsZero (F.obj (S j)) :=
    isZero_single_obj_homology c (d j) (M j) q (hq j)
  have hZ : IsZero (∐ fun j => F.obj (S j)) := coproduct_isZero _ hN
  exact hZ.of_iso (PreservesCoproduct.iso F S)

/-- The whole map is a quasi-isomorphism at a chosen degree iff its actual summand is. -/
theorem quasiIsoAt_iff_inclusion (c : ComplexShape I) (d : Fin p → I) (M : Fin p → C)
    (hd : Function.Injective d) {T : HomologicalComplex C c}
    (Φ : gradedSource c d M ⟶ T) (i : Fin p) :
    QuasiIsoAt Φ (d i) ↔
      QuasiIsoAt (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i ≫ Φ) (d i) := by
  let := inclusion_quasiIsoAt c d M hd i
  exact (quasiIsoAt_iff_comp_left
    (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i) Φ (d i)).symm

/-- The criterion uses precisely the class map from the original summand object. -/
theorem quasiIsoAt_iff_classMap_isIso (c : ComplexShape I) (d : Fin p → I)
    (M : Fin p → C) (hd : Function.Injective d) {T : HomologicalComplex C c}
    (Φ : gradedSource c d M ⟶ T) (i : Fin p) :
    QuasiIsoAt Φ (d i) ↔ IsIso
      ((singleObjHomologySelfIso c (d i) (M i)).inv ≫
        homologyMap (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i ≫ Φ) (d i)) := by
  rw [quasiIsoAt_iff_inclusion c d M hd Φ i, quasiIsoAt_iff_isIso_homologyMap]
  exact (isIso_comp_left_iff _ _).symm

/-- Whole quasi-isomorphism is detected by the same finite components and vanishing elsewhere. -/
theorem quasiIso_iff_components (c : ComplexShape I) (d : Fin p → I) (M : Fin p → C)
    (hd : Function.Injective d) {T : HomologicalComplex C c}
    (Φ : gradedSource c d M ⟶ T) :
    QuasiIso Φ ↔
      (∀ i : Fin p,
        QuasiIsoAt (Sigma.ι (fun j : Fin p => (single C c (d j)).obj (M j)) i ≫ Φ) (d i)) ∧
      (∀ q : I, (∀ i, q ≠ d i) → IsZero (T.homology q)) := by
  classical
  constructor
  · intro hΦ
    refine ⟨?_, ?_⟩
    · intro i
      exact (quasiIsoAt_iff_inclusion c d M hd Φ i).mp (hΦ.quasiIsoAt (d i))
    · intro q hq
      let : IsIso (homologyMap Φ q) :=
        (quasiIsoAt_iff_isIso_homologyMap Φ q).mp (hΦ.quasiIsoAt q)
      exact (homology_isZero_of_not_mem c d M q hq).of_iso (asIso (homologyMap Φ q)).symm
  · rintro ⟨hinc, hout⟩
    apply (quasiIso_iff Φ).mpr
    intro q
    by_cases hq : ∃ i, q = d i
    · obtain ⟨i, rfl⟩ := hq
      exact (quasiIsoAt_iff_inclusion c d M hd Φ i).mpr (hinc i)
    · have hn (i : Fin p) : q ≠ d i := fun hi => hq ⟨i, hi⟩
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact (homology_isZero_of_not_mem c d M q hn).isIso (hout q hn) _

end EnvelopeProperty.Cartier.DeligneIllusieGradedSourceHomology
