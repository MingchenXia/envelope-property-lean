/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.LocalSchemeLineTriviality
import EnvelopeProperty.Berkovich.SchemeCenter

/-! # Actual line fibers at genuine proper valuative centers -/

open scoped NNReal
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
variable [IsProper f] (hb : ∀ r, v r ≤ 1) (y : RelativeSchemeValuedPoint v f)

/-- The actual ORIGINAL residue-field generic line module sheaf. -/
def genericLineModule (M : X.Modules) : (Spec (CommRingCat.of (X.residueField y.1.point))).Modules :=
  (Scheme.Modules.pullback (X.fromSpecResidueField y.1.point)).obj M

/-- The actual ORIGINAL model line module sheaf over the genuine
residue-field valuation ring produced by properness. -/
def centerLineModule (M : X.Modules) : (Spec (CommRingCat.of (CenterRing y))).Modules :=
  (Scheme.Modules.pullback (centerLift hb y)).obj M

/-- The actual genuine generic morphism of the ORIGINAL valuation ring. -/
def centerGenericMap : Spec (CommRingCat.of (X.residueField y.1.point)) ⟶
    Spec (CommRingCat.of (CenterRing y)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (CenterRing y) (X.residueField y.1.point)))

/-- The ORIGINAL valuative triangle and true native pullback composition
identify the actual valuative line's generic restriction with the original fiber. -/
def centerLineGenericIso (M : X.Modules) :
    (Scheme.Modules.pullback (centerGenericMap y)).obj (centerLineModule hb y M) ≅
      genericLineModule y M :=
  (Scheme.Modules.pullbackComp (centerGenericMap y) (centerLift hb y)).app M ≪≫
    (Scheme.Modules.pullbackCongr (centerLift_generic hb y)).app M

/-- Original cover-local invertibility supplies an ACTUAL entire
valuative frame, with no hypothetical model lattice or frame as input. -/
theorem exists_centerLineUnitIso {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) :
    Nonempty (centerLineModule hb y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (CenterRing y)))) :=
  (hM.pullback (centerLift hb y)).nonempty_iso_unit_on_localSpec

/-- The actual center frame induces a frame on the SAME original generic
line using the genuine native comparisons and actual structure unit. -/
def centerFrameGenericIso {M : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    genericLineModule y M ≅ Scheme.Modules.unitObj
      (Spec (CommRingCat.of (X.residueField y.1.point))) :=
  (centerLineGenericIso hb y M).symm ≪≫
    (Scheme.Modules.pullback (centerGenericMap y)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (centerGenericMap y)

/-- ORIGINAL residue-field coefficient of a section of the actual generic
line in an actual original valuative frame. -/
def centerFrameCoefficient {M : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (s : Γ(genericLineModule y M, ⊤)) : X.residueField y.1.point :=
  (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom
    (((centerFrameGenericIso hb y e).hom.val.app (op ⊤)).hom s)

/-- Actual original valued frame norm on the WHOLE original generic-line
section module, constructed by the original residue-field valuation. -/
def centerFrameLineNorm {M : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (s : Γ(genericLineModule y M, ⊤)) : ℝ≥0 :=
  y.1.residueVal (centerFrameCoefficient hb y e s)

/-- The actual frame norm vanishes at the zero ORIGINAL generic section. -/
theorem centerFrameLineNorm_zero {M : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y)))) :
    centerFrameLineNorm hb y e 0 = 0 := by
  simp only [centerFrameLineNorm, centerFrameCoefficient, map_zero]

/-- Original addition on the actual generic line satisfies its genuine
nonarchimedean model-frame norm inequality. -/
theorem centerFrameLineNorm_add_le_max {M : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (s t : Γ(genericLineModule y M, ⊤)) :
    centerFrameLineNorm hb y e (s + t) ≤
      max (centerFrameLineNorm hb y e s) (centerFrameLineNorm hb y e t) := by
  unfold centerFrameLineNorm centerFrameCoefficient
  rw [map_add, map_add]
  exact y.1.residueVal.map_add _ _

/-- Vanishing of the genuine frame norm detects the zero section of
this SAME ORIGINAL generic line module. -/
theorem centerFrameLineNorm_eq_zero_iff {M : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (s : Γ(genericLineModule y M, ⊤)) :
    centerFrameLineNorm hb y e s = 0 ↔ s = 0 := by
  constructor
  · intro hs
    have hc : centerFrameCoefficient hb y e s = 0 := y.1.residueVal.zero_iff.mp hs
    have : IsIso ((centerFrameGenericIso hb y e).hom.val.app (op ⊤)) :=
      inferInstanceAs (IsIso ((SheafOfModules.evaluation _ (op ⊤)).map
        (centerFrameGenericIso hb y e).hom))
    apply (ConcreteCategory.bijective_of_isIso
      ((centerFrameGenericIso hb y e).hom.val.app (op ⊤))).1
    have hΓ : Function.Injective
        (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom :=
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom).1
    apply hΓ
    simpa only [centerFrameCoefficient, map_zero] using hc
  · rintro rfl
    exact centerFrameLineNorm_zero hb y e

/-- Actual scalar multiplication in the ORIGINAL generic-line section
module scales by the actual original residue-field scalar valuation. -/
theorem centerFrameLineNorm_smul {M : X.Modules}
    (e : centerLineModule hb y M ≅ Scheme.Modules.unitObj (Spec (CommRingCat.of (CenterRing y))))
    (r : Γ(Spec (CommRingCat.of (X.residueField y.1.point)), ⊤))
    (s : Γ(genericLineModule y M, ⊤)) :
    centerFrameLineNorm hb y e (r • s) =
      y.1.residueVal ((Scheme.ΓSpecIso (CommRingCat.of (X.residueField y.1.point))).hom.hom r) *
        centerFrameLineNorm hb y e s := by
  unfold centerFrameLineNorm centerFrameCoefficient
  rw [map_smul, smul_eq_mul, map_mul, map_mul]

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
