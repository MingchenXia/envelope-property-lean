import EnvelopeProperty.AlgGeom.Canonical.LineSectionRatios

/-! # Exact original regular-function image in the same rational line coefficients -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
namespace EnvelopeProperty.CanonicalGeometry
universe u
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}

/-- EVERY original section map from the structure module is multiplication
by the SAME original restricted top-section value at one. -/
theorem originalUnitSection_apply {L : X.Modules} (δ : Scheme.Modules.unitObj X ⟶ L)
    (U : X.Opens) (a : Γ(X, U)) :
    δ.val.app (.op U) a = a • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) := by
  let i := (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op
  have h := PresheafOfModules.naturality_apply δ.val i (show Γ(X, ⊤) from 1)
  change δ.val.app (.op U) (X.presheaf.map i (show Γ(X, ⊤) from 1)) =
    L.presheaf.map i (δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1)) at h
  rw [map_one] at h
  calc
    _ = δ.val.app (.op U) (a • (1 : Γ(X, U))) := by rw [smul_eq_mul, mul_one]
    _ = a • δ.val.app (.op U) (show Γ(X, U) from 1) :=
      (δ.val.app (.op U)).hom.map_smul a (show Γ(X, U) from 1)
    _ = _ := congrArg (fun z => a • z) h

variable [IsIntegral X]

/-- The true normalized coefficient of EVERY original function times the
SAME original nonzero section is its SAME actual function-field germ. -/
theorem sectionRatio_unitSection_apply (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (δ : Scheme.Modules.unitObj X ⟶ L)
    (hd : δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1) ≠ 0)
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    sectionRatio L hL _ hd U (δ.val.app (.op U) a) = X.germToFunctionField U a := by
  let d := δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1)
  let R := sectionRatio L hL d hd U
  calc
    R (δ.val.app (.op U) a) = R (a • L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op d) :=
      congrArg R (originalUnitSection_apply δ U a)
    _ = X.germToFunctionField U a • R (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op d) :=
      R.map_smulₛₗ a _
    _ = X.germToFunctionField U a • (1 : X.functionField) :=
      congrArg (fun z => X.germToFunctionField U a • z) (sectionRatio_generator L hL d hd U)
    _ = _ := by rw [smul_eq_mul, mul_one]

/-- Exact normalized rational equality detects the ENTIRE original
function-multiple image, for EVERY original section and function. -/
theorem sectionRatio_eq_germ_iff (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (δ : Scheme.Modules.unitObj X ⟶ L)
    (hd : δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1) ≠ 0)
    (U : X.Opens) [Nonempty U] (s : Γ(L, U)) (a : Γ(X, U)) :
    sectionRatio L hL _ hd U s = X.germToFunctionField U a ↔ δ.val.app (.op U) a = s := by
  rw [← sectionRatio_unitSection_apply L hL δ hd U a]
  constructor
  · intro h
    exact ((sectionRatio_injective L hL _ hd U) h).symm
  · intro h
    exact congrArg (sectionRatio L hL _ hd U) h.symm

/-- Regularity of the SAME actual rational coefficient is exactly membership
in the WHOLE original function-multiple image; no regularity certificate is assumed. -/
theorem sectionRatio_mem_regular_iff (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (δ : Scheme.Modules.unitObj X ⟶ L)
    (hd : δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1) ≠ 0)
    (U : X.Opens) [Nonempty U] (s : Γ(L, U)) :
    sectionRatio L hL _ hd U s ∈ Set.range (X.germToFunctionField U) ↔
      ∃ a : Γ(X, U), δ.val.app (.op U) a = s := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (sectionRatio_eq_germ_iff L hL δ hd U s a).mp ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, ((sectionRatio_eq_germ_iff L hL δ hd U s a).mpr ha).symm⟩

/-- Multiplication by the SAME nonzero actual section is faithful on EVERY
nonempty original open, derived from the genuine entire rational coefficient. -/
theorem unitSection_app_injective (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (δ : Scheme.Modules.unitObj X ⟶ L)
    (hd : δ.val.app (.op ⊤) (show Γ(X, ⊤) from 1) ≠ 0)
    (U : X.Opens) [Nonempty U] : Function.Injective (δ.val.app (.op U)) := by
  intro a b hab
  apply X.germToFunctionField_injective U
  exact (sectionRatio_unitSection_apply L hL δ hd U a).symm.trans
    ((congrArg (sectionRatio L hL _ hd U) hab).trans
      (sectionRatio_unitSection_apply L hL δ hd U b))

end EnvelopeProperty.CanonicalGeometry
