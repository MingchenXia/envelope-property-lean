import EnvelopeProperty.AlgGeom.SegreProjectiveTwist
import EnvelopeProperty.AlgGeom.GeneratedLineArbitrarySchemeTwist
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence

/-! # Actual very ampleness on whole, possibly disconnected covering schemes

The original scheme is arbitrary.  The genuine generator-to-projective map
and Segre embedding retain every component.
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules Alterations
open MvPolynomial
open Alterations.Geometry.Segre
noncomputable section
universe u
namespace EnvelopeProperty.SchemeVeryAmpleTensorGeneratingSections
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

private theorem originalBaseTriangle {C : Type*} [Category C] {X P Y Z B : C}
    (q : X ⟶ P) (s : P ⟶ Y) (a : P ⟶ Z) (b : Z ⟶ B) (c : Y ⟶ B)
    (i : X ⟶ Z) (p : X ⟶ B) (hs : s ≫ c = a ≫ b)
    (hq : q ≫ a = i) (hi : i ≫ b = p) : (q ≫ s) ≫ c = p := by
  rw [Category.assoc, hs, ← Category.assoc, hq, hi]

/-- An actual original very-ample line tensored by ANY original finitely
globally generated line has an internally constructed true closed embedding. -/
theorem isVeryAmple_tensor {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (A B : X.Modules) (hA : SchemeLineAmpleness.IsVeryAmple p A)
    (hB : IsInvertible B) (G : B.GeneratingSections) (hG : G.IsFiniteType) :
    SchemeLineAmpleness.IsVeryAmple p (A ⊗ B) := by
  obtain ⟨m, i, hi, hip, ⟨eA⟩⟩ := hA
  let : Finite G.I := hG.finite
  let : Fintype G.I := Fintype.ofFinite G.I
  let n := Fintype.card G.I
  let j := GeneratedLineProjectiveMap.projectiveMap p hB G
  let eB := GeneratedLineArbitrarySchemeTwist.projectiveTwistIso p hB G (0 : Fin (n + 1))
  have hjp : j ≫ projectiveSpaceStructure R n = p :=
    GeneratedLineProjectiveMap.projectiveMap_structure p hB G
  let δ : X ⟶ projectiveProduct R m n := pullback.lift i j (hip.trans hjp.symm)
  have hδi : δ ≫ pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) = i :=
    pullback.lift_fst _ _ _
  have hδj : δ ≫ pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) = j :=
    pullback.lift_snd _ _ _
  have hproj : IsSeparated (pullback.fst (projectiveSpaceStructure R m)
      (projectiveSpaceStructure R n)) :=
    IsSeparated.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)).flip
      (Alterations.projectiveSpaceStructure_isProper R n).toIsSeparated
  have hcomp : IsClosedImmersion (δ ≫
      pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)) := by
    rw [hδi]
    exact hi
  have hδ : IsClosedImmersion δ := @IsClosedImmersion.of_comp _ _ _ δ
    (pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)) hcomp hproj
  let : IsClosedImmersion δ := hδ
  refine ⟨Algebra.Segre.dimension m n, δ ≫ segre R m n, inferInstance, ?_, ?_⟩
  · exact originalBaseTriangle δ (segre R m n)
      (pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
      (projectiveSpaceStructure R m) (projectiveSpaceStructure R (Algebra.Segre.dimension m n))
      i p segre_structure hδi hip
  · exact ⟨((Scheme.Modules.pullbackComp δ (segre R m n)).app _).symm ≪≫
      (Scheme.Modules.pullback δ).mapIso (SegreProjectiveTwist.twistIso R m n) ≪≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback δ)
        (SegreProjectiveTwist.leftLine R m n) (SegreProjectiveTwist.rightLine R m n)).symm ≪≫
      ((frameFactorIso δ (pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
          i hδi (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1) ≪≫ eA) ⊗ᵢ
        (frameFactorIso δ (pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
          j hδj (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≪≫ eB))⟩

attribute [local instance] Scheme.Modules.symmetricCategory

theorem isVeryAmple_of_inverse_twist_generated {R : Type u} [CommRing R]
    {W : Scheme.{u}} (q : W ⟶ Spec (.of R)) (H B : W.Modules)
    (hH : SchemeLineAmpleness.IsVeryAmple q H) (hB : IsInvertible B)
    (G : (dualObj H ⊗ B).GeneratingSections) (hG : G.IsFiniteType) :
    SchemeLineAmpleness.IsVeryAmple q B := by
  have hHB : IsInvertible (dualObj H ⊗ B) :=
    (hH.isInvertible.dual.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso (dualObj H) B)
  have hV := isVeryAmple_tensor q H (dualObj H ⊗ B) hH hHB G hG
  obtain ⟨n, i, hi, hip, ⟨e⟩⟩ := hV
  exact ⟨n, i, hi, hip, ⟨e ≪≫
    ((α_ H (dualObj H) B).symm ≪≫ (hH.isInvertible.monoidalEvaluationIso ⊗ᵢ Iso.refl B) ≪≫ λ_ B)⟩⟩
end EnvelopeProperty.SchemeVeryAmpleTensorGeneratingSections
