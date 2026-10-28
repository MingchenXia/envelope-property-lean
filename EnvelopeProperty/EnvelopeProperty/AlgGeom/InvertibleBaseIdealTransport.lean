import EnvelopeProperty.AlgGeom.InvertibleSheafBaseIdealMultiplication

/-! # Whole base ideals are invariant under original line-sheaf isomorphisms -/

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory
noncomputable section
universe u

namespace EnvelopeProperty.InvertibleBaseIdealTransport
open Scheme.Modules ModularCurves InvertibleSheafBaseIdeal

/-- Precomposition by the actual original module map retains evaluation on
EVERY original open and EVERY original functional and section. -/
theorem evaluation_dualMap {X : Scheme.{u}} {L M : X.Modules}
    (f : L ⟶ M) (U : X.Opens) (d : Γ(dualObj M, U)) (s : Γ(L, U)) :
    SheafOfModules.evalSection X.ringCatSheaf L U
      ((dualMapObj f).val.app (.op U) d) s =
        SheafOfModules.evalSection X.ringCatSheaf M U d
          (f.val.app (.op U) s) := by
  change d.val.app (.op (Over.mk (𝟙 U)))
      (f.val.app (.op U) (L.val.map (𝟙 U).op s)) =
    d.val.app (.op (Over.mk (𝟙 U)))
      (M.val.map (𝟙 U).op (f.val.app (.op U) s))
  simp only [op_id, PresheafOfModules.map_id]
  rfl


/-- The SAME original global section and actual contravariant dual map
retain every evaluation coefficient. -/
theorem sectionEvaluation_map {X : Scheme.{u}} {L M : X.Modules}
    (f : L ⟶ M) (s : Γ(L, ⊤)) (U : X.Opens) (d : Γ(dualObj M, U)) :
    (sectionEvaluation M (f.val.app (.op ⊤) s)).val.app (.op U) d =
      (sectionEvaluation L s).val.app (.op U)
        ((dualMapObj f).val.app (.op U) d) := by
  have hM := SchemeTensorUnitSections.sectionEvaluation_apply M
    (f.val.app (.op ⊤) s) U d
  have hL := SchemeTensorUnitSections.sectionEvaluation_apply L s U
    ((dualMapObj f).val.app (.op U) d)
  have hE := evaluation_dualMap f U d (L.val.map (.op (homOfLE le_top)) s)
  have hN := congrArg (fun q => q.hom s)
    (f.val.naturality (.op (homOfLE (le_top : U ≤ ⊤))))
  change f.val.app (.op U) (L.val.map (.op (homOfLE le_top)) s) =
    M.val.map (.op (homOfLE (le_top : U ≤ ⊤))) (f.val.app (.op ⊤) s) at hN
  exact hM.trans ((congrArg
    (SheafOfModules.evalSection X.ringCatSheaf M U d) hN.symm).trans
      (hE.symm.trans hL.symm))


private theorem baseIdeal_le_of_retract {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) (f : L ⟶ M) (g : M ⟶ L)
    (hfg : f ≫ g = 𝟙 L) : baseIdeal hL ≤ baseIdeal hM := by
  intro U
  rw [baseIdeal_ideal hL U]
  refine iSup_le fun s => ?_
  rintro a ⟨d, rfl⟩
  let t : Γ(M, ⊤) := f.val.app (.op ⊤) s
  let e : Γ(dualObj M, U.1) := (dualMapObj g).val.app (.op U.1) d
  have ht : g.val.app (.op ⊤) t = s := by
    have h := congrArg (fun q : L ⟶ L => q.val.app (.op ⊤) s) hfg
    exact h
  have hE := sectionEvaluation_map g t U.1 d
  have hS := congrArg (fun z : Γ(L, ⊤) =>
    (sectionEvaluation L z).val.app (.op U.1) d) ht
  have hC : (sectionEvaluation M t).val.app (.op U.1) e =
      (sectionEvaluation L s).val.app (.op U.1) d := hE.symm.trans hS
  have hm := evaluation_mem_baseIdeal hM U t e
  exact Eq.mp (congrArg (fun z : Γ(X, U.1) => z ∈ (baseIdeal hM).ideal U) hC) hm

/-- The WHOLE original base ideal is invariant under EVERY actual original
line-sheaf isomorphism, retaining ALL global and local sections. -/
theorem baseIdeal_eq_of_iso {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) (e : L ≅ M) :
    baseIdeal hL = baseIdeal hM :=
  le_antisymm
    (baseIdeal_le_of_retract hL hM e.hom e.inv e.hom_inv_id)
    (baseIdeal_le_of_retract hM hL e.inv e.hom e.inv_hom_id)

end EnvelopeProperty.InvertibleBaseIdealTransport
