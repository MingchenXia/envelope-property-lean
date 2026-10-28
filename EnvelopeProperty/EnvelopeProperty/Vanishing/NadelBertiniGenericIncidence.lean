import EnvelopeProperty.Vanishing.NadelBertiniGenericOpen
import EnvelopeProperty.Vanishing.NadelBertiniUniversal
import Mathlib.AlgebraicGeometry.Noetherian

/-! # The actual original projective-incidence parameter good open

Properness and finite presentation of the original incidence parameter map are
produced from its actual zero-ideal inclusion and its actual product projection.
The good open is the actual complement of the bad image for this same map.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniGenericIncidence
open NadelBertiniUniversal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}

/-- Properness of the original source implies properness of its actual original
incidence parameter projection; the actual zero-ideal inclusion is closed. -/
theorem toParameters_proper (p : X ⟶ Spec (.of R)) [IsProper p]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (s : Fin (m + 1) → Γ(L, ⊤)) : IsProper (toParameters p L hL s) := by
  unfold toParameters
  infer_instance

/-- The original closed projective embedding produces the actual proper incidence
parameter map, with no separate properness or family-model certificate. -/
instance projectiveToParameters_proper (j : X ⟶ DeJongAlterations.projectiveSpace R m)
    [IsClosedImmersion j] : IsProper (projectiveToParameters j) := by
  unfold projectiveToParameters
  exact toParameters_proper _ _ _ _

/-- Over a field the actual parameter affine space is Noetherian, so the same
actual proper incidence map is locally of finite presentation. -/
instance projectiveToParameters_locallyOfFinitePresentation {k : Type u} [Field k]
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j] :
    LocallyOfFinitePresentation (projectiveToParameters j) := by
  let : IsProper (projectiveToParameters j) := projectiveToParameters_proper j
  infer_instance

/-- The original projective incidence's actual good coefficient-parameter open. -/
def projectiveGoodOpen {k : Type u} [Field k]
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j] :
    (Spec (.of (parameterRing k m))).Opens := by
  let : IsProper (projectiveToParameters j) := projectiveToParameters_proper j
  let : LocallyOfFinitePresentation (projectiveToParameters j) :=
    projectiveToParameters_locallyOfFinitePresentation j
  exact NadelBertiniGenericOpen.goodOpen (projectiveToParameters j)

/-- Smoothness of the ORIGINAL total incidence over the ORIGINAL characteristic-
zero field yields actual nonempty dense good parameters for its actual projection.
No generic-fibre smoothness or good-open premise is supplied. -/
theorem projectiveGoodOpen_specification {k : Type u} [Field k] [CharZero k]
    (j : X ⟶ DeJongAlterations.projectiveSpace k m) [IsClosedImmersion j]
    [Smooth (projectiveToSource j ≫ j ≫ DeJongAlterations.projectiveSpaceStructure k m)] :
    genericPoint (Spec (.of (parameterRing k m))) ∈ projectiveGoodOpen j ∧
      Nonempty (projectiveGoodOpen j) ∧
      Dense (projectiveGoodOpen j : Set (Spec (.of (parameterRing k m)))) ∧
      (projectiveToParameters j) ⁻¹ᵁ projectiveGoodOpen j ≤
        (projectiveToParameters j).smoothLocus ∧
      Smooth ((projectiveToParameters j) ∣_ projectiveGoodOpen j) := by
  let : IsProper (projectiveToParameters j) := projectiveToParameters_proper j
  let : LocallyOfFinitePresentation (projectiveToParameters j) :=
    projectiveToParameters_locallyOfFinitePresentation j
  exact NadelBertiniGenericOpen.goodOpen_specification_of_smooth
    (Spec.map (CommRingCat.ofHom (algebraMap k (parameterRing k m))))
    (projectiveToParameters j)
    (projectiveToSource j ≫ j ≫ DeJongAlterations.projectiveSpaceStructure k m)

end EnvelopeProperty.Vanishing.NadelBertiniGenericIncidence
