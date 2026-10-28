import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Entire original module maps detected by an actual open-immersion point cover

The stalk argument adapts AINT185's private proof in
ModularCurves.ForMathlib.SchemeModuleEpiCover, to arbitrary original open maps
and the actual native restriction/pullback comparison. That source is unchanged.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u v
namespace EnvelopeProperty.SchemeModuleOpenCoverDetection

/-- Every actual original point is covered, so ENTIRE original morphisms
are determined by their genuine native pullbacks to those original open maps.
No affine, quasicoherent, compactness or matching-family premise. -/
theorem hom_ext {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (j : (i : ι) → Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), j i y = x)
    {M N : X.Modules} {g h : M ⟶ N}
    (hgh : ∀ i, (Scheme.Modules.pullback (j i)).map g =
      (Scheme.Modules.pullback (j i)).map h) : g = h := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext s
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) V.unop
  intro x hx
  obtain ⟨i, y, hxy⟩ := hcover x
  let C := Scheme.Modules.restrictFunctorIsoPullback (j i)
  have hr : (Scheme.Modules.restrictFunctor (j i)).map g =
      (Scheme.Modules.restrictFunctor (j i)).map h := by
    apply (cancel_mono (C.hom.app N)).mp
    rw [C.hom.naturality g, C.hom.naturality h, hgh i]
  let e := Scheme.Modules.restrictStalkNatIso (j i) y
  let F := Scheme.Modules.restrictFunctor (j i) ⋙ Scheme.Modules.toPresheaf (Y i) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let G := Scheme.Modules.toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j i y)
  have hrestrictStalk : F.map g = F.map h :=
    congrArg (fun k : (Scheme.Modules.restrictFunctor (j i)).obj M ⟶
      (Scheme.Modules.restrictFunctor (j i)).obj N =>
        (Scheme.Modules.toPresheaf (Y i) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map k) hr
  have hstalk : G.map g = G.map h := by
    dsimp only [G]
    rw [← cancel_epi (e.hom.app M)]
    rw [← e.hom.naturality g, ← e.hom.naturality h]
    change F.map g ≫ e.hom.app N = F.map h ≫ e.hom.app N
    exact congrArg (fun k => k ≫ e.hom.app N) hrestrictStalk
  dsimp only [G, Scheme.Modules.toPresheaf, Scheme.Modules.toPresheafOfModules,
    Functor.comp_map] at hstalk
  rw [hxy] at hstalk
  have happly := ConcreteCategory.congr_hom hstalk (M.presheaf.germ V.unop x hx s)
  let gp := (Scheme.Modules.toPresheaf X).map g
  let hp := (Scheme.Modules.toPresheaf X).map h
  have hgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop x hx gp s
  have hhgerm := TopCat.Presheaf.stalkFunctor_map_germ_apply V.unop x hx hp s
  exact hgerm.symm.trans (happly.trans hhgerm)

/-- The SAME entire original module morphism vanishes exactly when every
actual original open-cover pullback vanishes. -/
theorem eq_zero_iff {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (j : (i : ι) → Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), j i y = x)
    {M N : X.Modules} (g : M ⟶ N) :
    g = 0 ↔ ∀ i, (Scheme.Modules.pullback (j i)).map g = 0 := by
  constructor
  · rintro rfl i
    exact (Scheme.Modules.pullback (j i)).map_zero _ _
  · intro h
    apply hom_ext Y j hcover
    intro i
    exact (h i).trans ((Scheme.Modules.pullback (j i)).map_zero M N).symm

end EnvelopeProperty.SchemeModuleOpenCoverDetection
