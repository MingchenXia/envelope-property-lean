import EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverChartsAlgebra

/-! # Every original root and the whole affine chart universal property

The proofs are on the actual successive native quotients, at every original
list position. No generator or component is identified with a chosen value.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
open NadelAuxiliaryMulticover
variable {X : Scheme.{u}} (U : X.Opens)

/-- Every ORIGINAL framed section coefficient, with its original list label. -/
def coefficients (D : List (AuxiliarySection X)) (e : Frames U D) (i : Fin D.length) :
    baseRing U := coefficient U (D.get i) (e i)

/-- Every original root in the WHOLE actual affine chart algebra. -/
def root : (D : List (AuxiliarySection X)) → (e : Frames U D) → (i : Fin D.length) → ring U D e
  | [], _, i => Fin.elim0 i
  | E :: D, e, i => Fin.cases
      (CyclicSectionAlgebra.root E.degree
        (structureMap U D (fun j => e j.succ) (coefficient U E (e 0))))
      (fun j => tailMap U E D e (root D (fun k => e k.succ) j)) i

/-- Every original root satisfies its SAME original section equation. -/
theorem root_pow (D : List (AuxiliarySection X)) (e : Frames U D) (i : Fin D.length) :
    root U D e i ^ (D.get i).degree = structureMap U D e (coefficients U D e i) := by
  induction D with
  | nil => exact Fin.elim0 i
  | cons E D ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact CyclicSectionAlgebra.root_pow E.degree _
      · change tailMap U E D e (root U D (fun k => e k.succ) j) ^ (D.get j).degree = _
        rw [← map_pow, ih]
        rfl

variable {S : Type u} [CommRing S]

/-- Equality on the original coefficients and EVERY original root proves
WHOLE algebra equality, including nilpotents and disconnected components. -/
theorem hom_ext (D : List (AuxiliarySection X)) (e : Frames U D)
    (f g : ring U D e →+* S)
    (hc : f.comp (structureMap U D e).hom = g.comp (structureMap U D e).hom)
    (hr : ∀ i, f (root U D e i) = g (root U D e i)) : f = g := by
  induction D with
  | nil => exact hc
  | cons E D ih =>
      apply AdjoinRoot.ringHom_ext
      · apply ih (fun i => e i.succ) (f.comp (tailMap U E D e).hom)
          (g.comp (tailMap U E D e).hom)
        · exact hc
        · intro i
          exact hr i.succ
      · exact hr 0

private def evaluationData (f : baseRing U →+* S) :
    (D : List (AuxiliarySection X)) → (e : Frames U D) →
    (y : Fin D.length → S) →
    (hy : ∀ i, y i ^ (D.get i).degree = f (coefficients U D e i)) →
    { v : ring U D e →+* S // v.comp (structureMap U D e).hom = f }
  | [], _, _, _ => ⟨f, rfl⟩
  | E :: D, e, y, hy => by
      let t := evaluationData f D (fun i => e i.succ) (fun i => y i.succ)
        (fun i => hy i.succ)
      let v : ring U (E :: D) e →+* S := AdjoinRoot.lift t.val (y 0) (by
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
          Polynomial.eval₂_C]
        apply sub_eq_zero.mpr
        exact (hy 0).trans
          (congrArg (fun h : baseRing U →+* S => h (coefficient U E (e 0))) t.property).symm)
      refine ⟨v, ?_⟩
      change (v.comp (tailMap U E D e).hom).comp (structureMap U D (fun i => e i.succ)).hom = f
      have hv : v.comp (tailMap U E D e).hom = t.val := AdjoinRoot.lift_comp_of _
      rw [hv]
      exact t.property

/-- The actual whole original chart-algebra universal evaluation. -/
def evaluate (D : List (AuxiliarySection X)) (e : Frames U D) (f : baseRing U →+* S)
    (y : Fin D.length → S)
    (hy : ∀ i, y i ^ (D.get i).degree = f (coefficients U D e i)) : ring U D e →+* S :=
  (evaluationData U f D e y hy).val

/-- The whole evaluation retains the SAME original coefficient homomorphism. -/
theorem evaluate_structure (D : List (AuxiliarySection X)) (e : Frames U D)
    (f : baseRing U →+* S) (y : Fin D.length → S)
    (hy : ∀ i, y i ^ (D.get i).degree = f (coefficients U D e i)) :
    (evaluate U D e f y hy).comp (structureMap U D e).hom = f :=
  (evaluationData U f D e y hy).property

/-- The whole evaluation retains EVERY original root at its original position. -/
theorem evaluate_root (D : List (AuxiliarySection X)) (e : Frames U D)
    (f : baseRing U →+* S) (y : Fin D.length → S)
    (hy : ∀ i, y i ^ (D.get i).degree = f (coefficients U D e i)) (i : Fin D.length) :
    evaluate U D e f y hy (root U D e i) = y i := by
  induction D with
  | nil => exact Fin.elim0 i
  | cons E D ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · dsimp only [evaluate, evaluationData, root, Fin.cases_zero]
        exact AdjoinRoot.lift_root _
      · change (evaluate U (E :: D) e f y hy).comp (tailMap U E D e).hom
          (root U D (fun k => e k.succ) j) = _
        have hv : (evaluate U (E :: D) e f y hy).comp (tailMap U E D e).hom =
            evaluate U D (fun k => e k.succ) f (fun k => y k.succ) (fun k => hy k.succ) := by
          dsimp only [evaluate, evaluationData]
          exact AdjoinRoot.lift_comp_of _
        rw [hv]
        exact ih (fun k => e k.succ) (fun k => y k.succ) (fun k => hy k.succ) j

end EnvelopeProperty.Vanishing.NadelAuxiliaryMulticoverCharts
