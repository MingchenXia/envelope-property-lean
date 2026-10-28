import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Sheaf

/-! # Actual sheaf cohomology as derived Hom between displaced single complexes

This comparison retains native `CategoryTheory.Sheaf.H`, which is an Ext group
from the constant free abelian sheaf.  It introduces no cohomology proxy.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section
universe u v w w'

namespace EnvelopeProperty.Vanishing.HypercohomologyExt

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w'} C] [HasExt.{w} C]

/-- The native Ext group is the derived Hom between actual single complexes
in degrees whose difference is the original nonnegative Ext degree. -/
def singleHomEquivExt (A B : C) (i t : ℤ) (n : ℕ) (h : i + n = t) :
    ((DerivedCategory.singleFunctor C t).obj A ⟶
      (DerivedCategory.singleFunctor C i).obj B) ≃ Ext.{w} A B n := by
  let eA : ((DerivedCategory.singleFunctor C t).obj A)⟦t⟧ ≅
      (DerivedCategory.singleFunctor C 0).obj A :=
    ((DerivedCategory.singleFunctors C).shiftIso t 0 t (by simp)).app A
  let eB : ((DerivedCategory.singleFunctor C i).obj B)⟦t⟧ ≅
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(n : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors C).shiftIso t (-(n : ℤ)) i (by omega)).app B ≪≫
      (((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0
        (by omega)).app B).symm
  exact (Functor.FullyFaithful.ofFullyFaithful
      (shiftFunctor (DerivedCategory C) t)).homEquiv.trans
    (eA.homFromEquiv.trans (eB.homToEquiv.trans Ext.homEquiv.symm))

/-- Vanishing of the native Ext group annihilates the corresponding actual
single-term derived Hom group. -/
theorem subsingleton_singleHom_of_ext (A B : C) (i t : ℤ) (n : ℕ)
    (h : i + n = t) (hExt : Subsingleton (Ext.{w} A B n)) :
    Subsingleton ((DerivedCategory.singleFunctor C t).obj A ⟶
      (DerivedCategory.singleFunctor C i).obj B) := by
  let := hExt
  exact (singleHomEquivExt A B i t n h).injective.subsingleton

section Sheaves

variable {T : Type u} [TopologicalSpace T]
  [HasSheafify (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})]
  [HasDerivedCategory.{w'}
    (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})]

/-- The actual free constant abelian sheaf defining native sheaf cohomology. -/
abbrev constantIntegerSheaf :
    Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u} :=
  (constantSheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- The native sheaf cohomology group is exactly the displaced-single
derived Hom group, with its original integer degree difference. -/
def singleHomEquivH
    (B : Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (i t : ℤ) (n : ℕ) (h : i + n = t) :
    ((DerivedCategory.singleFunctor _ t).obj (constantIntegerSheaf (T := T)) ⟶
      (DerivedCategory.singleFunctor _ i).obj B) ≃ CategoryTheory.Sheaf.H B n :=
  singleHomEquivExt (constantIntegerSheaf (T := T)) B i t n h

/-- Native sheaf cohomology vanishing gives precisely the derived Hom
vanishing required on one term of a bounded hypercohomology diagonal. -/
theorem subsingleton_singleHom_of_H
    (B : Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (i t : ℤ) (n : ℕ) (h : i + n = t)
    (hH : Subsingleton (CategoryTheory.Sheaf.H B n)) :
    Subsingleton
      ((DerivedCategory.singleFunctor _ t).obj (constantIntegerSheaf (T := T)) ⟶
        (DerivedCategory.singleFunctor _ i).obj B) :=
  subsingleton_singleHom_of_ext (constantIntegerSheaf (T := T)) B i t n h hH

end Sheaves

end EnvelopeProperty.Vanishing.HypercohomologyExt
