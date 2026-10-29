import EnvelopeProperty.AlgGeom.CurvePicardDegrees

/-! # Actual finite global generators for SAME original projective line classes -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory MvPolynomial
open Scheme.Modules
universe u v
namespace EnvelopeProperty.ProjectiveGeneratedLineClasses
open CurvePicardDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory MvPolynomial.gradedAlgebra

private theorem tensorInvertible {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

/-- Whole original line isomorphisms preserve the actual native Picard class. -/
theorem lineClass_eq_of_iso {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) (e : L ≅ M) :
    lineClass L hL = lineClass M hM := by
  apply Units.ext
  rw [lineClass_val, lineClass_val]
  exact congr_toSkeleton_of_iso e

/-- The original tensor operation is the genuine native Picard multiplication. -/
theorem lineClass_tensor {X : Scheme.{u}} (L M : X.Modules)
    (hL : IsInvertible L) (hM : IsInvertible M) :
    lineClass (L ⊗ M) (tensorInvertible hL hM) = lineClass L hL * lineClass M hM := by
  apply Units.ext
  change (lineClass (L ⊗ M) (tensorInvertible hL hM)).val = (lineClass L hL).val * (lineClass M hM).val
  rw [lineClass_val, lineClass_val, lineClass_val, Skeleton.toSkeleton_tensorObj]

/-- The SAME original structure line has the actual unit Picard class. -/
@[simp] theorem lineClass_unit (X : Scheme.{u}) : lineClass (unitObj X) (isInvertible_unit (X := X)) = 1 := by
  apply Units.ext
  change (lineClass (unitObj X) (isInvertible_unit (X := X))).val = (1 : Skeleton X.Modules)
  rw [lineClass_val]
  exact toSkeleton_unitObj

/-- The actual original dual, with actual evaluation, represents the inverse native class. -/
theorem lineClass_dual {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L) :
    lineClass (dualObj L) hL.dual = (lineClass L hL)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← lineClass_tensor]
  exact (lineClass_eq_of_iso (tensorInvertible hL.dual hL) (isInvertible_unit (X := X))
    ((β_ (dualObj L) L) ≪≫ hL.monoidalEvaluationIso ≪≫
      ModularCurves.monoidalUnitObjIso X)).trans (lineClass_unit X)

/-- EVERY native Picard class has an actual original invertible module representative. -/
theorem exists_line_representative {X : Scheme.{u}} (a : X.Pic) :
    ∃ L : X.Modules, ∃ hL : IsInvertible L, lineClass L hL = a := by
  change (Skeleton X.Modules)ˣ at a
  have hL : IsInvertible a.val.out := isInvertible_of_isUnit_toSkeleton
    (Eq.mpr (congrArg (fun q : Skeleton X.Modules => IsUnit q)
      (show toSkeleton a.val.out = a.val from Quotient.out_eq a.val)) a.isUnit)
  refine ⟨a.val.out, hL, ?_⟩
  apply Units.ext
  rw [lineClass_val]
  exact Quotient.out_eq a.val

/-- A SINGLE actual nonnegative original twist simultaneously gives
true finite global generators to EVERY member of a finite original line family. -/
theorem exists_simultaneous_generating_twist {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}} {ι : Type v} [Fintype ι]
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
    (j : σ) (L : ι → X.Modules) (hL : ∀ a, IsInvertible (L a)) :
    ∃ d : ℕ, ∀ a : ι, ∃ G : ((L a) ⊗ (Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) j (d : ℤ))).GeneratingSections, G.IsFiniteType := by
  classical
  have h (a : ι) : ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ G : ((L a) ⊗ (Scheme.Modules.pullback i).obj
        (coordinateHyperplaneTwist (R := R) j (d : ℤ))).GeneratingSections, G.IsFiniteType := by
    let : (L a).IsQuasicoherent := (hL a).isQuasicoherent
    let : (L a).IsFinitePresentation := (hL a).isFinitePresentation
    let : (L a).IsFiniteType := inferInstance
    exact ClosedProjectiveGlobalGeneration.exists_eventual_generatingSections i (L a) j
  choose N hN using h
  refine ⟨Finset.univ.sup N, fun a => hN a _ ?_⟩
  exact Finset.le_sup (f := N) (Finset.mem_univ a)

/-- The SAME original nonnegative projective twist has true finite global
generators after ANY original whole pullback. -/
theorem exists_twist_finite_generatingSections {R : Type u} [CommRing R]
    {σ : Type} [Fintype σ] {X : Scheme.{u}}
    (i : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (d : ℕ) :
    ∃ G : ((Scheme.Modules.pullback i).obj
      (coordinateHyperplaneTwist (R := R) j (d : ℤ))).GeneratingSections, G.IsFiniteType := by
  let G := ProjectiveTwistGlobalGeneration.generatingSections (R := R) j d
  let : G.IsFiniteType := ProjectiveTwistGlobalGeneration.generatingSections_isFiniteType j d
  exact ⟨ClosedProjectiveGlobalGeneration.pullback_generatingSections i G,
    ClosedProjectiveGlobalGeneration.pullback_generatingSections_isFiniteType i G⟩

/-- The SAME actual original denominator line, with actual original evaluation,
gives the whole original line as its honest tensor quotient. -/
def generatedTwistQuotientIso {X : Scheme.{u}} (L T : X.Modules) (hT : IsInvertible T) :
    L ≅ (L ⊗ T) ⊗ dualObj T :=
  ((α_ L T (dualObj T)) ≪≫ whiskerLeftIso L hT.monoidalEvaluationIso ≪≫ ρ_ L).symm

/-- EVERY finite original projective line family has a SINGLE actual
original denominator with internally produced finite global generators;
EVERY actual numerator is genuinely finitely generated as well. -/
theorem exists_simultaneous_generated_quotients {R : Type u} [CommRing R]
    {X : Scheme.{u}} {ι : Type v} [Fintype ι]
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p)
    (L : ι → X.Modules) (hL : ∀ a, IsInvertible (L a)) :
    ∃ T : X.Modules, ∃ _hT : IsInvertible T, ∃ H : T.GeneratingSections,
      H.IsFiniteType ∧ ∀ a : ι,
        ∃ G : ((L a) ⊗ T).GeneratingSections, G.IsFiniteType ∧
          Nonempty ((L a) ≅ ((L a) ⊗ T) ⊗ dualObj T) := by
  obtain ⟨m, i, hi, _⟩ := hp
  let : IsClosedImmersion i := hi
  obtain ⟨d, hd⟩ := exists_simultaneous_generating_twist i (0 : Fin (m+1)) L hL
  let T := (Scheme.Modules.pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (m+1)) (d : ℤ))
  let hT : IsInvertible T := (coordinateHyperplaneTwist_isInvertible (0 : Fin (m+1)) (d : ℤ)).pullback i
  obtain ⟨H, hH⟩ := exists_twist_finite_generatingSections i (0 : Fin (m+1)) d
  refine ⟨T, hT, H, hH, fun a => ?_⟩
  obtain ⟨G, hG⟩ := hd a
  exact ⟨G, hG, ⟨generatedTwistQuotientIso (L a) T hT⟩⟩

/-- EVERY original invertible projective line is a whole quotient of TWO
actual original invertible lines with genuine finite global generators. -/
theorem exists_generated_quotient {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p) (L : X.Modules) (hL : IsInvertible L) :
    ∃ M T : X.Modules, ∃ _hM : IsInvertible M, ∃ _hT : IsInvertible T,
      ∃ G : M.GeneratingSections, ∃ H : T.GeneratingSections,
        G.IsFiniteType ∧ H.IsFiniteType ∧ Nonempty (L ≅ M ⊗ dualObj T) := by
  obtain ⟨T, hT, H, hH, h⟩ := exists_simultaneous_generated_quotients p hp
    (fun _ : Unit => L) (fun _ => hL)
  obtain ⟨G, hG, he⟩ := h ()
  exact ⟨L ⊗ T, T, tensorInvertible hL hT, hT, G, H, hG, hH, he⟩

/-- EVERY SAME native original projective Picard class is the quotient of
two SAME original finite-globally-generated line classes, all produced internally. -/
theorem exists_generated_class_quotient {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p) (a : X.Pic) :
    ∃ M T : X.Modules, ∃ hM : IsInvertible M, ∃ hT : IsInvertible T,
      ∃ G : M.GeneratingSections, ∃ H : T.GeneratingSections,
        G.IsFiniteType ∧ H.IsFiniteType ∧ a = lineClass M hM * (lineClass T hT)⁻¹ := by
  obtain ⟨L, hL, ha⟩ := exists_line_representative a
  obtain ⟨M, T, hM, hT, G, H, hG, hH, ⟨e⟩⟩ := exists_generated_quotient p hp L hL
  refine ⟨M, T, hM, hT, G, H, hG, hH, ha.symm.trans ?_⟩
  exact (lineClass_eq_of_iso hL (tensorInvertible hM hT.dual) e).trans
    ((lineClass_tensor M (dualObj T) hM hT.dual).trans
      (congrArg (fun b => lineClass M hM * b) (lineClass_dual T hT)))

end EnvelopeProperty.ProjectiveGeneratedLineClasses
