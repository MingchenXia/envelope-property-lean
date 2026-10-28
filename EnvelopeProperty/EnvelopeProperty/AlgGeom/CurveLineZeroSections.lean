import EnvelopeProperty.AlgGeom.CurveLineSectionPositivity

/-! # TRUE original line degree detects the ACTUAL zero scheme of a nonzero section -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.CurveLineZeroSections
open CurveLineDegrees SchemeCoherentEulerIndex FiniteClosedIdealLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The SAME original nonzero section's line degree is the actual field
dimension of its SAME entire original zero scheme. -/
theorem degree_eq_zeroScheme_finrank {X : Scheme.{u}} [IsIntegral X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    degree q L = (Module.finrank k (fieldSections
      ((LineSectionZeroIdeal.zeroIdeal L hL s).subschemeι ≫ q)
      (unitObj (LineSectionZeroIdeal.zeroIdeal L hL s).subscheme)) : ℤ) := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let I := LineSectionZeroIdeal.zeroIdeal L hL s
  let hI := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs
  have hd := degree_dual q hq hdim L hL
  have he := degree_eq_of_iso q (IntegralLineImageModules.zeroSectionDualIso L hL s hs)
  have hχ := CurveCartierIdealDegrees.normalizedEulerCharacteristic_toModules q hq hdim I hI
  change degree q I.toModules = -(Module.finrank k
    (fieldSections (I.subschemeι ≫ q) (unitObj I.subscheme)) : ℤ) at hχ
  change degree q (dualObj L) = degree q I.toModules at he
  change degree q L = (Module.finrank k
    (fieldSections (I.subschemeι ≫ q) (unitObj I.subscheme)) : ℤ)
  omega

/-- A nonempty ACTUAL original zero scheme makes the SAME original
nonzero line section's true projective-curve degree strictly positive. -/
theorem degree_pos_of_nonempty_zeroScheme {X : Scheme.{u}} [IsIntegral X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (hs : s ≠ 0)
    (hzero : Nonempty (LineSectionZeroIdeal.zeroIdeal L hL s).subscheme) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    0 < degree q L := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  let I := LineSectionZeroIdeal.zeroIdeal L hL s
  let : Nonempty I.subscheme := hzero
  let : Nonempty (⊤ : I.subscheme.Opens) := ⟨⟨Classical.choice hzero, trivial⟩⟩
  let := structureSectionsAlgebra (I.subschemeι ≫ q)
  let : Module.Finite k Γ(I.subscheme, ⊤) := structureSections_finite I.subschemeι q hq
  rw [degree_eq_zeroScheme_finrank q hq hdim L hL s hs,
    (structureFieldSectionsIso (I.subschemeι ≫ q)).toLinearEquiv.finrank_eq]
  exact_mod_cast (Module.finrank_pos (R := k) (M := Γ(I.subscheme, ⊤)))

/-- The entire original unit ideal is the actual structure line, via its
SAME whole original ideal inclusion. -/
def topIdealModuleIso (X : Scheme.{u}) :
    (⊤ : X.IdealSheafData).toModules ≅ unitObj X := by
  let α := (⊤ : X.IdealSheafData).toModulesInclusion
  have hα : IsIso α := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine ⟨fun a b h => Subtype.ext h, fun s => ?_⟩
    refine ⟨⟨s, ?_⟩, rfl⟩
    intro V _hVU
    simp
  let := hα
  exact asIso α

/-- Empty actual zero support of a nonzero ORIGINAL section derives a
WHOLE original trivialization, with no supplied line-isomorphism datum. -/
def trivializationOfZeroIdealTop {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L) (hs : s ≠ 0)
    (htop : LineSectionZeroIdeal.zeroIdeal L hL s = ⊤) : L ≅ unitObj X := by
  let e : dualObj L ≅ unitObj X :=
    IntegralLineImageModules.zeroSectionDualIso L hL s hs ≪≫
      eqToIso (congrArg (fun I : X.IdealSheafData => I.toModules) htop) ≪≫ topIdealModuleIso X
  exact (ρ_ L).symm ≪≫
    (Iso.refl L ⊗ᵢ ((ModularCurves.monoidalUnitObjIso X) ≪≫ e.symm)) ≪≫
      hL.monoidalEvaluationIso ≪≫ ModularCurves.monoidalUnitObjIso X

/-- Zero TRUE original curve degree forces the SAME nonzero section's
ACTUAL zero ideal to be the unit ideal. -/
theorem zeroIdeal_eq_top_of_degree_eq_zero {X : Scheme.{u}} [IsIntegral X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    (hL : IsInvertible L) (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    degree q L = 0 → LineSectionZeroIdeal.zeroIdeal L hL s = ⊤ := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  intro hd
  let I := LineSectionZeroIdeal.zeroIdeal L hL s
  have hempty : ¬ Nonempty I.subscheme := by
    intro hzero
    have hp := degree_pos_of_nonempty_zeroScheme q hq hdim L hL s hs hzero
    omega
  apply (Scheme.IdealSheafData.support_eq_bot_iff (I := I)).mp
  ext x
  constructor
  · intro hx
    exact (hempty ⟨⟨x, hx⟩⟩).elim
  · intro hx
    exact hx.elim

/-- A SAME genuinely globally generated line has zero true original curve
degree EXACTLY when that SAME entire original line is trivial. -/
theorem degree_eq_zero_iff_trivial_of_generatingSections {X : Scheme.{u}} [IsIntegral X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    (hL : IsInvertible L) (G : L.GeneratingSections) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    degree q L = 0 ↔ Nonempty (L ≅ unitObj X) := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  constructor
  · intro hd
    obtain ⟨i, hi⟩ := CurveLineSectionPositivity.exists_generatorHom_ne_zero hL G
      (genericPoint X)
    let s := SchemeGeneratingSectionsUnit.generatorHom G i
    exact ⟨trivializationOfZeroIdealTop L hL s hi
      (zeroIdeal_eq_top_of_degree_eq_zero q hq hdim L hL s hi hd)⟩
  · rintro ⟨e⟩
    exact (degree_eq_of_iso q e).trans (degree_unit q)

/-- A genuinely globally generated nontrivial original line has strictly
positive TRUE intrinsic degree on the SAME original integral projective curve. -/
theorem degree_pos_of_generatingSections_of_nontrivial {X : Scheme.{u}} [IsIntegral X]
    {k : Type u} [Field k] (q : X ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    (hL : IsInvertible L) (G : L.GeneratingSections) (hnot : ¬ Nonempty (L ≅ unitObj X)) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
    0 < degree q L := by
  let : IsProper q := hq.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have hn := CurveLineSectionPositivity.degree_nonneg_of_generatingSections q hq hdim L hL G
  have hz := degree_eq_zero_iff_trivial_of_generatingSections q hq hdim L hL G
  by_contra hp
  exact hnot (hz.mp (le_antisymm (le_of_not_gt hp) hn))

end EnvelopeProperty.CurveLineZeroSections
