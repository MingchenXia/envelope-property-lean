import EnvelopeProperty.AlgGeom.ClosedFibreComplexPoints
import EnvelopeProperty.AlgGeom.FlatSectionKernel
import EnvelopeProperty.ComplexGeometry.Germs.SchemeAffineNativeFormal
import EnvelopeProperty.Alterations.StableModification.Cohomology.PullbackQcoh

/-! # Original native fibres index the actual formal closed-fibre germs -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace EnvelopeProperty.Char0.NativeFormalClosedFibrePoints

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexSchemes HolomorphicGerms
open FlatSectionKernel

variable {R : Type} [CommRing R]
  (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  [IsSeparated f] [QuasiCompact f] (x : SchemeComplexPoint f)

/-- Actual constant-coefficient evaluation recovers the SAME original base point. -/
theorem residueMap_comp :
    Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ))) ≫
      Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)) = x.val := by
  rw [← Spec.map_comp]
  have he : (CommRingCat.ofHom (schemeAffineNativeFormal f n x)) ≫
      CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ)) =
        Spec.preimage x.val := by
    ext a
    exact schemeAffineNativeFormal_constantCoeff f n x a
  rw [he, Spec.map_preimage]

variable {Y : Scheme} (g : Y ⟶ Spec (.of R))

/-- The literal pullback along the actual original affine Taylor map. -/
abbrev formalBaseChange : Scheme :=
  pullback g (Spec.map (CommRingCat.ofHom (schemeAffineNativeFormal f n x)))

/-- The SAME actual formal-base projection. -/
abbrev formalStructureMap : formalBaseChange f n x g ⟶ Spec (.of (MvPowerSeries (Fin n) ℂ)) :=
  pullback.snd _ _

/-- An actual original fibre point lifts using precisely the actual residue map. -/
def pointLift (p : SchemeComplexPoint (g ≫ f))
    (hp : schemeComplexPointMap (g ≫ f) f g rfl p = x) :
    Spec (.of ℂ) ⟶ formalBaseChange f n x g :=
  pullback.lift p.val
    (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ))))
    ((congrArg Subtype.val hp).trans (residueMap_comp f n x).symm)

/-- The whole original fibre point is the first projection of its canonical lift. -/
@[simp] theorem pointLift_fst (p : SchemeComplexPoint (g ≫ f))
    (hp : schemeComplexPointMap (g ≫ f) f g rfl p = x) :
    pointLift f n x g p hp ≫ pullback.fst _ _ = p.val :=
  pullback.lift_fst _ _ _

/-- The second projection is the literal constant-coefficient residue map. -/
@[simp] theorem pointLift_snd (p : SchemeComplexPoint (g ≫ f))
    (hp : schemeComplexPointMap (g ≫ f) f g rfl p = x) :
    pointLift f n x g p hp ≫ formalStructureMap f n x g =
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ))) :=
  pullback.lift_snd _ _ _

/-- EVERY actual residue-compatible field point is a lift of an original native fibre point. -/
theorem exists_pointLift_of_over_residue
    (a : Spec (.of ℂ) ⟶ formalBaseChange f n x g)
    (ha : a ≫ formalStructureMap f n x g =
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ)))) :
    ∃ (p : SchemeComplexPoint (g ≫ f))
      (hp : schemeComplexPointMap (g ≫ f) f g rfl p = x), a = pointLift f n x g p hp := by
  have hb : (a ≫ pullback.fst _ _) ≫ g = x.val := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, residueMap_comp]
  let p : SchemeComplexPoint (g ≫ f) := ⟨a ≫ pullback.fst _ _, by
    rw [← Category.assoc, hb]
    exact x.property⟩
  have hp : schemeComplexPointMap (g ≫ f) f g rfl p = x := Subtype.ext hb
  refine ⟨p, hp, ?_⟩
  apply pullback.hom_ext
  · rw [pointLift_fst]
  · rw [pointLift_snd]
    exact ha

variable [IsProper g]

/-- A WHOLE quasi-coherent section on the actual formal base change is detected
at the canonical lifts of ALL original complex points over the SAME base point. -/
theorem section_eq_zero_iff_originalFiber
    (M : (formalBaseChange f n x g).Modules) [M.IsQuasicoherent] (m : Γ(M, ⊤)) :
    m = 0 ↔ ∀ (p : SchemeComplexPoint (g ≫ f))
      (hp : schemeComplexPointMap (g ≫ f) f g rfl p = x),
        M.presheaf.germ ⊤ ((pointLift f n x g p hp) (IsLocalRing.closedPoint ℂ)) trivial m = 0 := by
  have hβ : Function.Surjective (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ)) := by
    intro c
    exact ⟨MvPowerSeries.C c, by simp⟩
  have htest := ClosedFibreComplexPoints.section_eq_zero_iff_residueFieldPoints
    (MvPowerSeries.constantCoeff (σ := Fin n) (R := ℂ)) hβ
      (formalStructureMap f n x g) M m
  constructor
  · rintro rfl p hp
    exact map_zero _
  · intro h
    apply htest.mpr
    intro a ha
    obtain ⟨p, hp, rfl⟩ := exists_pointLift_of_over_residue f n x g a ha
    exact h p hp

/-- ALL actual formal coefficients in the WHOLE original section-kernel extension
are detected on the SAME original native fibre, with actual Taylor flatness derived. -/
theorem mem_map_sectionKernel_iff_originalFiber
    (M : Y.Modules) [M.IsQuasicoherent]
    (m : AffineModuleFlatBaseChange.sections g M) (s : MvPowerSeries (Fin n) ℂ) :
    letI : Algebra R (MvPowerSeries (Fin n) ℂ) := (schemeAffineNativeFormal f n x).toAlgebra
    let N := (Scheme.Modules.pullback
      (FlatGlobalSections.firstProjection (S := MvPowerSeries (Fin n) ℂ) g)).obj M
    s ∈ (sectionKernel g M m).map (schemeAffineNativeFormal f n x) ↔
      ∀ (p : SchemeComplexPoint (g ≫ f))
        (hp : schemeComplexPointMap (g ≫ f) f g rfl p = x),
        N.presheaf.germ ⊤ ((pointLift f n x g p hp) (IsLocalRing.closedPoint ℂ)) trivial
          ((ProperBirationalSections.coefficientMap
            (FlatGlobalSections.structureMap (S := MvPowerSeries (Fin n) ℂ) g) s) •
            pulledSection (S := MvPowerSeries (Fin n) ℂ) g M m) = 0 := by
  let : Algebra R (MvPowerSeries (Fin n) ℂ) := (schemeAffineNativeFormal f n x).toAlgebra
  let : Module.Flat R (MvPowerSeries (Fin n) ℂ) := schemeAffineNativeFormal_flat f n x
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from g]; infer_instance⟩
  let N := (Scheme.Modules.pullback
    (FlatGlobalSections.firstProjection (S := MvPowerSeries (Fin n) ℂ) g)).obj M
  let : N.IsQuasicoherent := inferInstance
  change s ∈ (sectionKernel g M m).map (algebraMap R (MvPowerSeries (Fin n) ℂ)) ↔ _
  rw [map_sectionKernel_eq, mem_sectionKernel_iff]
  exact section_eq_zero_iff_originalFiber f n x g N _

end EnvelopeProperty.Char0.NativeFormalClosedFibrePoints
