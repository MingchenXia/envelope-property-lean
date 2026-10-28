import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent

/-! # Tensoring by an actual invertible sheaf preserves finite type -/

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.SchemeInvertibleTensorFiniteType

attribute [local instance] Scheme.Modules.monoidalCategory

/-- Finite local generators of the original module and actual line frames
derive finite type of their original tensor on every scheme. -/
theorem isFiniteType_tensorRight {X : Scheme.{u}} (M L : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (hL : IsInvertible L) :
    (M ⊗ L).IsFiniteType := by
  classical
  let N := M ⊗ L
  obtain ⟨ι, U, hU, e⟩ :=
    SchemeInvertibleTensorQuasicoherent.exists_affine_trivializing_cover L hL
  choose G hG using fun i =>
    exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen M (U i)
  let ρ (i : ι) : N.restrict (U i).1.ι ≅ M.restrict (U i).1.ι :=
    SchemeInvertibleTensorQuasicoherent.restrictTensorIsoOfFrame M L (U i).1 (e i).some
  let H (i : ι) : (N.restrict (U i).1.ι).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso (ρ i).symm (G i)
  have hH (i : ι) : (H i).IsFiniteType := by
    constructor
    change Finite (G i).I
    exact (hG i).finite
  let q : N.LocalGeneratorsData :=
    { I := ι
      X := fun i => (U i).1
      coversTop := by rw [Opens.coversTop_iff]; exact hU
      generators := fun i => generatingSectionsOverOfRestrict N (U i).1 (H i) }
  have hq : q.IsFiniteType := by
    constructor
    intro i
    let : (H i).IsFiniteType := hH i
    exact generatingSectionsOverOfRestrict_isFiniteType N (U i).1 (H i)
  have hqShrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q.shrink, hqShrink⟩

end EnvelopeProperty.SchemeInvertibleTensorFiniteType
