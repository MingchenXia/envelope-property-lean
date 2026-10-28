import EnvelopeProperty.Algebra.LeftExactHomologyComparison

/-! # Exact native preservation and composition of the SAME canonical comparison -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.LeftExactHomologyCoherence
open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
variable [Abelian C] [Abelian D] [Abelian E]
variable (S : ShortComplex C) (F : C ⥤ D)
variable [F.PreservesZeroMorphisms] [PreservesFiniteLimits F]

private instance mappedCyclesMono : Mono (F.map S.iCycles) :=
  mono_of_isLimit_fork (isLimitForkMapOfIsLimit' F S.iCycles_g S.cyclesIsKernel)

omit [PreservesFiniteLimits F] in
private theorem preserved_homologyπ [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.homologyData.left
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  have hπ := congrArg (fun k : (S.map F).cycles ⟶ F.obj h.H =>
    k ≫ F.map h.homologyIso.inv) (h.map F).homologyπ_comp_homologyIso_hom
  have hf : F.map h.π ≫ F.map h.homologyIso.inv =
      F.map h.cyclesIso.inv ≫ F.map S.homologyπ :=
    (F.map_comp h.π h.homologyIso.inv).symm.trans
      ((congrArg F.map h.π_comp_homologyIso_inv).trans
        (F.map_comp h.cyclesIso.inv S.homologyπ))
  exact (Category.assoc _ _ _).symm.trans
    (hπ.trans ((Category.assoc _ _ _).trans
      (congrArg (fun k : F.obj h.K ⟶ F.obj S.homology => (h.map F).cyclesIso.hom ≫ k) hf)))

/-- The SAME map agrees with genuine native homology preservation, not just an arbitrary iso. -/
theorem map_eq_mapHomologyIso [F.PreservesLeftHomologyOf S] :
    LeftExactHomologyComparison.map S F = (S.mapHomologyIso F).hom := by
  have hc : (LeftExactHomologyComparison.cyclesIso S F).hom = (S.mapCyclesIso F).hom := by
    apply (cancel_mono (F.map S.iCycles)).mp
    exact (LeftExactHomologyComparison.cyclesIso_hom_iCycles S F).trans
      (S.mapCyclesIso_hom_iCycles F).symm
  apply (cancel_epi (S.map F).homologyπ).mp
  rw [LeftExactHomologyComparison.homologyπ_map, preserved_homologyπ, hc]

variable (G : D ⥤ E) [G.PreservesZeroMorphisms] [PreservesFiniteLimits G]

private instance compositionPreservesFiniteLimits : PreservesFiniteLimits (F ⋙ G) :=
  comp_preservesFiniteLimits F G

private theorem cycles_comp :
    (LeftExactHomologyComparison.cyclesIso S (F ⋙ G)).hom =
      (LeftExactHomologyComparison.cyclesIso (S.map F) G).hom ≫
        G.map (LeftExactHomologyComparison.cyclesIso S F).hom := by
  apply (cancel_mono ((F ⋙ G).map S.iCycles)).mp
  rw [LeftExactHomologyComparison.cyclesIso_hom_iCycles]
  change ((S.map F).map G).iCycles =
    ((LeftExactHomologyComparison.cyclesIso (S.map F) G).hom ≫
      G.map (LeftExactHomologyComparison.cyclesIso S F).hom) ≫ G.map (F.map S.iCycles)
  rw [Category.assoc, ← G.map_comp, LeftExactHomologyComparison.cyclesIso_hom_iCycles,
    LeftExactHomologyComparison.cyclesIso_hom_iCycles]

/-- The complete canonical map of the actual composite is the composite of the SAME maps. -/
theorem map_comp :
    LeftExactHomologyComparison.map S (F ⋙ G) =
      LeftExactHomologyComparison.map (S.map F) G ≫
        G.map (LeftExactHomologyComparison.map S F) := by
  apply (cancel_epi (((S.map F).map G).homologyπ)).mp
  symm
  calc
    ((S.map F).map G).homologyπ ≫ (LeftExactHomologyComparison.map (S.map F) G ≫
        G.map (LeftExactHomologyComparison.map S F)) =
        (LeftExactHomologyComparison.cyclesIso (S.map F) G).hom ≫
          G.map ((S.map F).homologyπ ≫ LeftExactHomologyComparison.map S F) := by
      rw [← Category.assoc, LeftExactHomologyComparison.homologyπ_map,
        Category.assoc, ← G.map_comp]
    _ = (LeftExactHomologyComparison.cyclesIso (S.map F) G).hom ≫
        G.map ((LeftExactHomologyComparison.cyclesIso S F).hom ≫ F.map S.homologyπ) := by
      rw [LeftExactHomologyComparison.homologyπ_map]
    _ = (LeftExactHomologyComparison.cyclesIso S (F ⋙ G)).hom ≫ (F ⋙ G).map S.homologyπ := by
      rw [G.map_comp, ← Category.assoc, ← cycles_comp]
      rfl
    _ = ((S.map F).map G).homologyπ ≫ LeftExactHomologyComparison.map S (F ⋙ G) :=
      (LeftExactHomologyComparison.homologyπ_map S (F ⋙ G)).symm

end EnvelopeProperty.LeftExactHomologyCoherence
