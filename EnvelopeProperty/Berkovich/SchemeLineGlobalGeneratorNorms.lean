import EnvelopeProperty.AlgGeom.SchemeGeneratingSectionsUnit
import EnvelopeProperty.Berkovich.SchemeLineFibreSectionNorms

/-! # Actual proper-model norms of original global generating sections -/
open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
open SchemeGeneratingSectionsUnit
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- Genuine original global generation supplies an ACTUAL original generator
whose TRUE generic-fiber section has model norm exactly one. No finite-family,
metric, center-frame or generation comparison certificate is an input. -/
theorem exists_modelLineNorm_generatorHom_eq_one {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (G : M.GeneratingSections) :
    ∃ i : G.I, modelLineNorm hb y hM (fibreSection y (generatorHom G i)) = 1 := by
  let e := Classical.choice (exists_centerLineUnitIso hb y hM)
  let H := (ClosedProjectiveGlobalGeneration.pullback_generatingSections (centerLift hb y) G).ofEpi e.hom
  obtain ⟨i, hi⟩ := exists_isUnit_coefficient H
  let α := generatorHom G i
  let u := Scheme.Modules.pullbackUnitIso (centerLift hb y)
  have hc : generatorHom H i = u.inv ≫
      (Scheme.Modules.pullback (centerLift hb y)).map α ≫ e.hom := by
    rw [generatorHom_ofEpi, generatorHom_pullback]
    exact Category.assoc _ _ _
  have hr : ((generatorHom H i).val.app (op ⊤)).hom
      (1 : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤)) =
      centerHomCoefficient hb y α u e :=
    congrArg (fun q => (q.val.app (op ⊤)).hom
      (1 : Γ(Spec (CommRingCat.of (CenterRing y)), ⊤))) hc
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (CenterRing y))).hom.hom
      (centerHomCoefficient hb y α u e)) :=
    Eq.mp (congrArg (fun r => IsUnit ((Scheme.ΓSpecIso
      (CommRingCat.of (CenterRing y))).hom.hom r)) hr) hi
  refine ⟨i, ?_⟩
  rw [modelLineNorm_fibreSection, modelHomNorm_eq_frames hb y
    (Scheme.Modules.isInvertible_unit (X := X)) hM _ u e]
  exact (Valuation.valuationSubring.integers y.1.residueVal).one_of_isUnit hu

/-- The supremum of the TRUE original model norms of the SAME original
whole global generating sections is EXACTLY one, including arbitrary families. -/
theorem iSup_modelLineNorm_generatorHom_eq_one {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (G : M.GeneratingSections) :
    (⨆ i : G.I, (modelLineNorm hb y hM (fibreSection y (generatorHom G i)) : ℝ≥0∞)) = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    rw [modelLineNorm_fibreSection]
    exact_mod_cast (modelHomNorm_le_one hb y
      (Scheme.Modules.isInvertible_unit (X := X)) hM (generatorHom G i))
  · obtain ⟨i, hi⟩ := exists_modelLineNorm_generatorHom_eq_one hb y hM G
    have h := le_iSup (fun j : G.I =>
      (modelLineNorm hb y hM (fibreSection y (generatorHom G j)) : ℝ≥0∞)) i
    simpa only [hi, ENNReal.coe_one] using h

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
