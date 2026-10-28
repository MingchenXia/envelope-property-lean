import EnvelopeProperty.AlgGeom.SchemeTensorUnitSections
import ModularCurves.ForMathlib.ProjectiveFactorizationFiniteSections

/-! # One finite original global family generates the whole projective base ideal -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace EnvelopeProperty.ProjectiveLineBaseIdealGenerators
open Scheme.Modules InvertibleSheafBaseIdeal SchemeTensorUnitSections

private def coefficient {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (d : Γ(dualObj L, U)) (s : Γ(L, ⊤)) : Γ(X, U) :=
  ModularCurves.SheafOfModules.evalSection X.ringCatSheaf L U d
    (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)

private theorem coefficient_zero {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (d : Γ(dualObj L, U)) : coefficient L U d 0 = 0 := by
  dsimp only [coefficient, ModularCurves.SheafOfModules.evalSection_eq]
  simp only [map_zero]

private theorem coefficient_add {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)
    (d : Γ(dualObj L, U)) (s t : Γ(L, ⊤)) :
    coefficient L U d (s+t) = coefficient L U d s + coefficient L U d t := by
  dsimp only [coefficient]
  have h := map_add (L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s t
  exact (congrArg (ModularCurves.SheafOfModules.evalSection X.ringCatSheaf L U d) h).trans
    (ModularCurves.SheafOfModules.evalSection_add_right X.ringCatSheaf L U d _ _)

private theorem coefficient_base_smul {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) (U : X.Opens) (d : Γ(dualObj L, U))
    (a : Γ(S, ⊤)) (s : baseSections f L) :
    coefficient L U d (show Γ(L, ⊤) from a • s) =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (f.appTop.hom a) •
        coefficient L U d s := by
  let i := (homOfLE (le_top : U ≤ ⊤)).op
  have hb := baseSections_smul f L a s
  have hr := PresheafOfModules.map_smul L.val i (f.appTop.hom a) s
  dsimp only [coefficient]
  exact (congrArg (fun z => ModularCurves.SheafOfModules.evalSection
      X.ringCatSheaf L U d (L.presheaf.map i z)) hb).trans
    ((congrArg (ModularCurves.SheafOfModules.evalSection X.ringCatSheaf L U d) hr).trans
      (ModularCurves.SheafOfModules.evalSection_smul_right X.ringCatSheaf L U d _ _))

/-- A finite family is derived from the actual original projective geometry,
and generates the SAME whole ALL-global-section base ideal on every affine open. -/
theorem exists_finite_global_generators {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) :
    ∃ G : Finset Γ(L, ⊤), baseIdeal hL = ⨆ s ∈ G, sectionIdeal hL s := by
  classical
  let : L.IsQuasicoherent := hL.isQuasicoherent
  let : L.IsFinitePresentation := hL.isFinitePresentation
  let : Module.Finite Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (baseSections f L) := hf.baseSections_module_finite L
  obtain ⟨G, hG⟩ := Module.Finite.fg_top
    (R := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))) (M := baseSections f L)
  let J : X.IdealSheafData := ⨆ s ∈ G, sectionIdeal hL s
  let P : Submodule Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) (baseSections f L) :=
    { carrier := {s | ∀ (U : X.affineOpens) (d : Γ(dualObj L, U.1)),
        coefficient L U.1 d s ∈ J.ideal U}
      zero_mem' := by
        intro U d
        rw [coefficient_zero]
        exact (J.ideal U).zero_mem
      add_mem' := by
        intro s t hs ht U d
        rw [coefficient_add]
        exact (J.ideal U).add_mem (hs U d) (ht U d)
      smul_mem' := by
        intro a s hs U d
        rw [coefficient_base_smul]
        exact (J.ideal U).smul_mem _ (hs U d) }
  have hGP : (G : Set (baseSections f L)) ⊆ P := by
    intro s hs U d
    have hle : sectionIdeal hL s ≤ J :=
      le_iSup_of_le s (le_iSup_of_le hs le_rfl)
    have h := hle U ⟨d, rfl⟩
    exact Eq.mp (congrArg (fun z => z ∈ J.ideal U)
      (sectionEvaluation_apply L s U.1 d)) h
  have htop : (⊤ : Submodule Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
      (baseSections f L)) ≤ P := by
    rw [← hG]
    exact Submodule.span_le.mpr hGP
  refine ⟨G, le_antisymm ?_ ?_⟩
  · apply (baseIdeal_le_iff hL J).mpr
    intro s U a ha
    obtain ⟨d, rfl⟩ := ha
    have hs : (show baseSections f L from s) ∈ P := htop (Submodule.mem_top :
      (show baseSections f L from s) ∈ (⊤ : Submodule
        Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) (baseSections f L)))
    exact Eq.mpr (congrArg (fun z => z ∈ J.ideal U)
      (sectionEvaluation_apply L s U.1 d)) (hs U d)
  · exact iSup₂_le fun s _ => le_iSup (fun s => sectionIdeal hL s) s

end EnvelopeProperty.ProjectiveLineBaseIdealGenerators
