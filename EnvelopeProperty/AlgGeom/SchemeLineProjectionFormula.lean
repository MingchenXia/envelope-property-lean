import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
import EnvelopeProperty.AlgGeom.CartierEvaluationTransport
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Genuine projection formula for the SAME actual original line sheaf -/
open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u v
namespace EnvelopeProperty.SchemeLineProjectionFormula
open SchemeInvertibleTensorEquivalence
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A true monoidal left adjoint and a genuine inverse tensor pair derive
projection formula for the SAME original right adjoint, with no projection certificate. -/
def projectionFormulaOfTensorInverse
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) [F.Monoidal]
    (L Q : C) (e : L ⊗ Q ≅ 𝟙_ C) :
    G ⋙ tensorRight L ≅ tensorRight (F.obj L) ⋙ G := by
  let E := rightTensorEquivalence L Q e
  let E' := rightTensorEquivalence (F.obj L) (F.obj Q)
    (Functor.Monoidal.μIso F L Q ≪≫ F.mapIso e ≪≫ (Functor.Monoidal.εIso F).symm)
  exact conjugateIsoEquiv (E.symm.toAdjunction.comp adj)
    (adj.comp E'.symm.toAdjunction) (Functor.Monoidal.commTensorRight F Q)

noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X
noncomputable local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Scheme.Modules.symmetricCategory X
noncomputable local instance {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.Modules.pullback g).Monoidal := Scheme.Modules.pullbackMonoidal g

/-- Actual original whole pushforward and tensoring by the original line
satisfy genuine projection formula along EVERY original scheme morphism. -/
def lineProjectionFormula {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.pushforward g ⋙ tensorRight L ≅
      tensorRight ((Scheme.Modules.pullback g).obj L) ⋙ Scheme.Modules.pushforward g :=
  projectionFormulaOfTensorInverse (Scheme.Modules.pullback g) (Scheme.Modules.pushforward g)
    (Scheme.Modules.pullbackPushforwardAdjunction g) L (Scheme.Modules.dualObj L)
    hL.monoidalEvaluationIso

/-- The genuine whole projection formula keeps the SAME original module,
line, morphism, pullback and pushforward. -/
def lineProjectionFormulaObj {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (N : Y.Modules) :
    (Scheme.Modules.pushforward g).obj N ⊗ L ≅
      (Scheme.Modules.pushforward g).obj (N ⊗ (Scheme.Modules.pullback g).obj L) :=
  (lineProjectionFormula g L hL).app N

end EnvelopeProperty.SchemeLineProjectionFormula
