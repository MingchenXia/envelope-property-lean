import EnvelopeProperty.AlgGeom.SchemePointClosureCurve
import EnvelopeProperty.AlgGeom.DominantFunctionFieldMaps
import Hironaka.Scheme.Smooth.SubschemeStalk

/-! # The actual SAME original point-closure stalk ideal is the native maximal ideal -/
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemePointClosureStalkIdeal
variable {X : Scheme.{u}}

/-- The actual native point-closure generic point maps to the SAME original point. -/
theorem inclusion_genericPoint (c : X) :
    letI := SchemePointClosureCurve.closure_isIntegral c
    SchemePointClosureCurve.inclusion c (genericPoint (SchemePointClosureCurve.closure c)) = c := by
  let C := SchemePointClosureCurve.closure c
  let := SchemePointClosureCurve.closure_isIntegral c
  let g := SchemePointClosureCurve.genericMap c
  let : QuasiCompact (X.fromSpecResidueField c) :=
    ⟨fun U _ _ => (Set.toFinite ((X.fromSpecResidueField c) ⁻¹' U)).isCompact⟩
  let : IsDominant g := by
    dsimp only [g,SchemePointClosureCurve.genericMap]
    infer_instance
  have hg : g (closedPoint (X.residueField c)) = genericPoint C := by
    rw [show closedPoint (X.residueField c) = genericPoint (Spec (X.residueField c)) from
      Subsingleton.elim _ _]
    exact DominantFunctionFieldMaps.genericPoint_map g
  have hi := congrArg (fun a : Spec (X.residueField c) ⟶ X =>
    a (closedPoint (X.residueField c))) (SchemePointClosureCurve.genericMap_inclusion c)
  change SchemePointClosureCurve.inclusion c (g (closedPoint (X.residueField c))) =
    X.fromSpecResidueField c (closedPoint (X.residueField c)) at hi
  rwa [hg,Scheme.fromSpecResidueField_apply] at hi

/-- At the true generic point of an integral closed subscheme, its ENTIRE
actual stalk ideal is the native maximal ideal of the SAME original ambient stalk. -/
theorem stalkIdeal_at_genericPoint (J : X.IdealSheafData) [IsIntegral J.subscheme] :
    J.stalkIdeal (J.subschemeι (genericPoint J.subscheme)) =
      maximalIdeal (X.presheaf.stalk (J.subschemeι (genericPoint J.subscheme))) := by
  have hk := J.ker_stalkMap_subschemeι (genericPoint J.subscheme)
  have hm := IsLocalRing.ker_eq_maximalIdeal
    (J.subschemeι.stalkMap (genericPoint J.subscheme)).hom
    (J.subschemeι.stalkMap_surjective (genericPoint J.subscheme))
  exact hk.symm.trans hm

/-- The actual native schematic point-closure ideal at the SAME original
point is exactly the whole maximal ideal of that original native stalk. -/
theorem stalkIdeal_eq_maximalIdeal (c : X) :
    (X.fromSpecResidueField c).ker.stalkIdeal c = maximalIdeal (X.presheaf.stalk c) := by
  let J := (X.fromSpecResidueField c).ker
  let : IsIntegral J.subscheme := SchemePointClosureCurve.closure_isIntegral c
  have hc : J.subschemeι (genericPoint J.subscheme) = c := inclusion_genericPoint c
  have h := stalkIdeal_at_genericPoint J
  rwa [hc] at h

end EnvelopeProperty.SchemePointClosureStalkIdeal
