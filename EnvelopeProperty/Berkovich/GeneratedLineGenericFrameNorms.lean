import EnvelopeProperty.Berkovich.SchemeLineGlobalGeneratorNorms

/-! # Genuine generated model norms in arbitrary original generic frames -/

open scoped NNReal ENNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleFrameCoefficients
variable {Y : Scheme.{u}} {M : Y.Modules}

/-- The genuine unit section in any actual whole line frame. -/
def unitSection (e : M ≅ Scheme.Modules.unitObj Y) : Γ(M, ⊤) :=
  ((e.inv.val.app (op ⊤)).hom) (1 : Γ(Y, ⊤))

/-- The original section's actual coefficient in the given whole frame. -/
def coefficient (e : M ≅ Scheme.Modules.unitObj Y) (s : Γ(M, ⊤)) : Γ(Y, ⊤) :=
  ((e.hom.val.app (op ⊤)).hom) s

/-- Whole inverse and linearity give every actual section, not just basis elements. -/
theorem eq_coefficient_smul_unitSection (e : M ≅ Scheme.Modules.unitObj Y)
    (s : Γ(M, ⊤)) : s = coefficient e s • unitSection e := by
  let F : Γ(Y, ⊤) →ₗ[Γ(Y, ⊤)] Γ(M, ⊤) := (e.inv.val.app (op ⊤)).hom
  have h : F (coefficient e s) = coefficient e s • F (1 : Γ(Y, ⊤)) := by
    simpa only [smul_eq_mul, mul_one] using F.map_smul (coefficient e s) (1 : Γ(Y, ⊤))
  have hi := congrArg (fun q : M ⟶ M => (q.val.app (op ⊤)).hom s) e.hom_inv_id
  exact hi.symm.trans h

/-- The original inverse-frame section has actual coefficient one. -/
theorem coefficient_unitSection (e : M ≅ Scheme.Modules.unitObj Y) :
    coefficient e (unitSection e) = 1 :=
  congrArg (fun q : Scheme.Modules.unitObj Y ⟶ Scheme.Modules.unitObj Y =>
    (q.val.app (op ⊤)).hom (1 : Γ(Y, ⊤))) e.inv_hom_id

end EnvelopeProperty.SchemeModuleFrameCoefficients

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

open SchemeModuleFrameCoefficients SchemeGeneratingSectionsUnit

/-- Native residue-field coefficient of the WHOLE original generic section. -/
def genericFrameCoefficient {M : X.Modules}
    (e : genericLineModule y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point))))
    (s : Γ(genericLineModule y M, ⊤)) : X.residueField y.1.point :=
  (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
    (coefficient e s)

/-- An arbitrary actual generic frame computes every true original model norm
up to its own derived original unit-section norm. -/
theorem modelLineNorm_eq_genericFrameCoefficient_mul {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M)
    (e : genericLineModule y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point))))
    (s : Γ(genericLineModule y M, ⊤)) :
    modelLineNorm hb y hM s =
      y.1.residueVal (genericFrameCoefficient y e s) *
        modelLineNorm hb y hM (unitSection e) := by
  calc
    _ = modelLineNorm hb y hM (coefficient e s • unitSection e) :=
      congrArg (modelLineNorm hb y hM) (eq_coefficient_smul_unitSection e s)
    _ = _ := modelLineNorm_smul hb y hM (coefficient e s) (unitSection e)

/-- Every actual generic frame has a genuinely nonzero unit-section norm. -/
theorem modelLineNorm_genericFrameUnit_ne_zero {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M)
    (e : genericLineModule y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point)))) :
    modelLineNorm hb y hM (unitSection e) ≠ 0 := by
  intro hn
  obtain ⟨s, hs⟩ := exists_modelLineNorm_eq_one hb y hM
  have h := modelLineNorm_eq_genericFrameCoefficient_mul hb y hM e s
  rw [hs, hn, mul_zero] at h
  exact one_ne_zero h

/-- Actual generation internally supplies an original index attaining the
WHOLE generic coefficient maximum and determining the true unit norm. -/
theorem exists_genericFrameCoefficient_max_and_unitNorm {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (G : M.GeneratingSections)
    (e : genericLineModule y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point)))) :
    ∃ i : G.I,
      (∀ j : G.I,
        y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G j))) ≤
          y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G i)))) ∧
      modelLineNorm hb y hM (unitSection e) =
        (y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G i))))⁻¹ := by
  obtain ⟨i, hi⟩ := exists_modelLineNorm_generatorHom_eq_one hb y hM G
  have hci :
      y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G i))) *
        modelLineNorm hb y hM (unitSection e) = 1 :=
    (modelLineNorm_eq_genericFrameCoefficient_mul hb y hM e
      (fibreSection y (generatorHom G i))).symm.trans hi
  refine ⟨i, ?_, eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hci)⟩
  intro j
  have hj : modelLineNorm hb y hM (fibreSection y (generatorHom G j)) ≤ 1 := by
    rw [modelLineNorm_fibreSection]
    exact modelHomNorm_le_one hb y (Scheme.Modules.isInvertible_unit (X := X))
      hM (generatorHom G j)
  have hmul :
      y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G j))) *
          modelLineNorm hb y hM (unitSection e) ≤
        y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G i))) *
          modelLineNorm hb y hM (unitSection e) := by
    rw [hci, ← modelLineNorm_eq_genericFrameCoefficient_mul hb y hM e]
    exact hj
  apply (mul_le_mul_iff_left₀
    (pos_iff_ne_zero.mpr (modelLineNorm_genericFrameUnit_ne_zero hb y hM e))).mp
  simpa only [mul_comm] using hmul

/-- The WHOLE actual original model norm is its original generic coefficient
divided by an internally attained original generator maximum, in ANY frame.
For finite G this is the true finite-coordinate metric formula. -/
theorem exists_genericFrameCoefficient_max_and_modelNorm {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (G : M.GeneratingSections)
    (e : genericLineModule y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point)))) :
    ∃ i : G.I,
      (∀ j : G.I,
        y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G j))) ≤
          y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G i)))) ∧
      ∀ s : Γ(genericLineModule y M, ⊤), modelLineNorm hb y hM s =
        y.1.residueVal (genericFrameCoefficient y e s) /
          y.1.residueVal (genericFrameCoefficient y e (fibreSection y (generatorHom G i))) := by
  obtain ⟨i, hi, hn⟩ := exists_genericFrameCoefficient_max_and_unitNorm hb y hM G e
  refine ⟨i, hi, fun s => ?_⟩
  rw [modelLineNorm_eq_genericFrameCoefficient_mul hb y hM e s, hn, div_eq_mul_inv]

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
