/-
Copyright (c) 2026. All rights reserved.
-/
import ModularCurves.ForMathlib.PullbackCompMonoidal

/-! # Coherence of the actual canonical tensor pullback -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y Z : Scheme.{u}}

/-- The actual inverse tensorators of original pullback functors respect
true native pullback composition on the whole original module sheaves. -/
theorem pullbackComp_inverse_tensorator (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    letI : MonoidalCategory X.Modules := monoidalCategory X
    letI : MonoidalCategory Y.Modules := monoidalCategory Y
    letI : MonoidalCategory Z.Modules := monoidalCategory Z
    letI : (pullback f).Monoidal := pullbackMonoidal f
    letI : (pullback g).Monoidal := pullbackMonoidal g
    letI : (pullback (f ≫ g)).Monoidal := pullbackMonoidal (f ≫ g)
    (pullback f).map (Functor.Monoidal.μIso (pullback g) M N).inv ≫
        (Functor.Monoidal.μIso (pullback f) ((pullback g).obj M) ((pullback g).obj N)).inv ≫
        ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app N) =
      (pullbackComp f g).hom.app (M ⊗ N) ≫
        (Functor.Monoidal.μIso (pullback (f ≫ g)) M N).inv := by
  let : MonoidalCategory X.Modules := monoidalCategory X
  let : MonoidalCategory Y.Modules := monoidalCategory Y
  let : MonoidalCategory Z.Modules := monoidalCategory Z
  let : (pullback f).Monoidal := pullbackMonoidal f
  let : (pullback g).Monoidal := pullbackMonoidal g
  let : (pullback (f ≫ g)).Monoidal := pullbackMonoidal (f ≫ g)
  let : (pullback g ⋙ pullback f).Monoidal := inferInstance
  have : (pullbackComp f g).hom.IsMonoidal := pullbackComp_hom_isMonoidal f g
  apply (cancel_epi (Functor.Monoidal.μIso (pullback g ⋙ pullback f) M N).hom).mp
  have hμ := NatTrans.IsMonoidal.tensor (τ := (pullbackComp f g).hom) M N
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
    Functor.LaxMonoidal.comp_μ] at hμ ⊢
  simp only [Category.assoc, ← Functor.map_comp_assoc, Functor.Monoidal.μ_δ]
  rw [(pullback f).map_id, Category.id_comp, Functor.Monoidal.μ_δ_assoc]
  simpa only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id] using
    (congrArg (fun q => q ≫ Functor.OplaxMonoidal.δ (pullback (f ≫ g)) M N) hμ).symm

end AlgebraicGeometry.Scheme.Modules
