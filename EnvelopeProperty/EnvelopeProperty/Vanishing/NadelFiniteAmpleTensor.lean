import EnvelopeProperty.AlgGeom.SegreProjectiveTwist
import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveTwist
import EnvelopeProperty.AlgGeom.GeneratedLineFamilyProjectiveEmbedding
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineGenerated

/-! # Actual very ampleness on whole, possibly disconnected covering schemes

The original scheme is arbitrary.  The genuine generator-to-projective map
and Segre embedding retain every component.
-/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules DeJongAlterations
open MvPolynomial
open DeJongAlterations.Geometry.Segre
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelFiniteAmpleTensor
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := Scheme.Modules.pullbackMonoidal f

/-- An actual original very-ample line tensored by ANY original finitely
globally generated line has an internally constructed true closed embedding. -/
theorem isVeryAmple_tensor {R : Type u} [CommRing R] [IsDomain R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (A B : X.Modules) (hA : SchemeLineAmpleness.IsVeryAmple p A)
    (hB : IsInvertible B) (G : B.GeneratingSections) (hG : G.IsFiniteType) :
    SchemeLineAmpleness.IsVeryAmple p (A ⊗ B) := by
  obtain ⟨m, i, hi, hip, ⟨eA⟩⟩ := hA
  obtain ⟨n, j, eB, hjp⟩ :=
    ArithmeticOriginalLineGenerated.exists_projective_morphism p hB G hG
  let δ : X ⟶ projectiveProduct R m n := pullback.lift i j (hip.trans hjp.symm)
  have hδi : δ ≫ pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) = i :=
    pullback.lift_fst _ _ _
  have hδj : δ ≫ pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n) = j :=
    pullback.lift_snd _ _ _
  let : IsProper (projectiveSpaceStructure R n) :=
    (GeneratedLineFamilyProjectiveEmbedding.polynomialFamily_isProjectiveFactorization R
      (fun _ : Fin 1 => n) 0).isProper
  let : IsClosedImmersion i := hi
  have hδ : IsClosedImmersion δ := by
    have : IsClosedImmersion (δ ≫
        pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n)) := by
      rw [hδi]
      infer_instance
    exact IsClosedImmersion.of_comp δ
      (pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
  let : IsClosedImmersion δ := hδ
  refine ⟨Algebra.Segre.dimension m n, δ ≫ segre R m n, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, segre_structure, ← Category.assoc, hδi, hip]
  · exact ⟨((Scheme.Modules.pullbackComp δ (segre R m n)).app _).symm ≪≫
      (Scheme.Modules.pullback δ).mapIso (SegreProjectiveTwist.twistIso R m n) ≪≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback δ)
        (SegreProjectiveTwist.leftLine R m n) (SegreProjectiveTwist.rightLine R m n)).symm ≪≫
      ((frameFactorIso δ (pullback.fst (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
          i hδi (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) 1) ≪≫ eA) ⊗ᵢ
        (frameFactorIso δ (pullback.snd (projectiveSpaceStructure R m) (projectiveSpaceStructure R n))
          j hδj (coordinateHyperplaneTwist (R := R) (0 : Fin (n + 1)) 1) ≪≫ eB))⟩
end EnvelopeProperty.Vanishing.NadelFiniteAmpleTensor
