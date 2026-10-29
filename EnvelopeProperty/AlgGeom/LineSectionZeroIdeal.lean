/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.AlgGeom.QuasicoherentImageIdeal
import ModularCurves.Picard.Dual
import ModularCurves.Picard.InvertibleSheafLocallyFree
import Hironaka.Scheme.IdealSheaf.Defs
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace EnvelopeProperty.LineSectionZeroIdeal
variable {X : Scheme.{u}} (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
  (s : Scheme.Modules.unitObj X ⟶ L)

private theorem evaluation_app (U : X.Opens) (α : Γ(Scheme.Modules.dualObj L, U)) :
    (Scheme.Modules.dualMapObj s ≫ (Scheme.Modules.dualUnitObjIso (X := X)).hom).val.app
        (op U) α =
      α.val.app (op (Over.mk (𝟙 U))) (s.val.app (op U) (1 : Γ(X, U))) := rfl

/-- The genuine zero ideal of the same original section of an invertible module. -/
def zeroIdeal : X.IdealSheafData := by
  let : (Scheme.Modules.dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  exact QuasicoherentImageIdeal.imageIdeal (Scheme.Modules.dualObj L)
    (Scheme.Modules.dualMapObj s ≫ (Scheme.Modules.dualUnitObjIso (X := X)).hom)

/-- On an actual original affine frame the same zero ideal is the actual coefficient ideal. -/
theorem zeroIdeal_ideal_of_frame (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    (zeroIdeal L hL s).ideal U =
      Ideal.span ({e.hom.val.app (op (Over.mk (𝟙 U.1)))
        (s.val.app (op U.1) (1 : Γ(X, U)))} : Set Γ(X, U)) := by
  let c : Γ(X, U) := e.hom.val.app (op (Over.mk (𝟙 U.1))) (s.val.app (op U.1) (1 : Γ(X, U)))
  change (((Scheme.Modules.dualMapObj s ≫
    (Scheme.Modules.dualUnitObjIso (X := X)).hom).val.app (op U.1)).hom.range : Ideal Γ(X, U)) =
      Ideal.span {c}
  apply le_antisymm
  · rintro a ⟨α, rfl⟩
    rw [evaluation_app]
    have he := congrArg (fun f => f.val.app (op (Over.mk (𝟙 U.1)))
      (s.val.app (op U.1) (1 : Γ(X, U)))) e.hom_inv_id
    have ht : s.val.app (op U.1) (1 : Γ(X, U)) =
        c • e.inv.val.app (op (Over.mk (𝟙 U.1))) (1 : Γ(X, U)) := by
      calc
        _ = e.inv.val.app (op (Over.mk (𝟙 U.1))) c := he.symm
        _ = _ := by simpa only [smul_eq_mul, mul_one] using
          (e.inv.val.app (op (Over.mk (𝟙 U.1)))).hom.map_smul c (1 : Γ(X, U))
    rw [ht, map_smul]
    change c * (show Γ(X, U) from α.val.app (op (Over.mk (𝟙 U.1)))
      (e.inv.val.app (op (Over.mk (𝟙 U.1))) (1 : Γ(X, U)))) ∈
        Ideal.span ({c} : Set Γ(X, U))
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  · apply Ideal.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact ⟨e.hom, evaluation_app L s U.1 e.hom⟩

include hL in
private theorem exists_affine_frame (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) := by
  obtain ⟨ι, V, hV, e⟩ := hL
  have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let E := Scheme.Modules.overTrivializationOfRestrictIso L (V i)
    (Scheme.Modules.restrictIsoOfPullbackIso L (V i) (e i).some)
  obtain ⟨W, hWa, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hi
  exact ⟨⟨W, hWa⟩, hxW,
    ⟨ModularCurves.SheafOfModules.restrictOverTrivialization X.ringCatSheaf L (V i) E
      (Over.mk (homOfLE hWV))⟩⟩

include hL in
private theorem coefficient_ne_zero [IsIntegral X] (hs : s ≠ 0)
    (U : X.Opens) [Nonempty U]
    (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (e.hom.val.app (op (Over.mk (𝟙 U)))
      (s.val.app (op U) (1 : Γ(X, U))) : Γ(X, U)) ≠ 0 := by
  intro hc
  apply hs
  let t := L.unitHomEquiv s
  have htres {A B : X.Opens} (i : A ⟶ B) :
      L.val.map i.op (t.val (op B)) = t.val (op A) := t.property i.op
  have hUne : (U : Set X).Nonempty := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    exact ⟨u.1, u.2⟩
  have hU : t.val (op U) = 0 := by
    have he := congrArg (fun f => f.val.app (op (Over.mk (𝟙 U))) (t.val (op U)))
      e.hom_inv_id
    change e.inv.val.app (op (Over.mk (𝟙 U)))
      (e.hom.val.app (op (Over.mk (𝟙 U))) (t.val (op U))) = t.val (op U) at he
    change e.hom.val.app (op (Over.mk (𝟙 U))) (t.val (op U)) = 0 at hc
    rw [hc, map_zero] at he
    exact he.symm
  obtain ⟨ι, V, hV, eV⟩ := hL
  have htop : t.val (op ⊤) = 0 := by
    apply TopCat.Presheaf.IsSheaf.section_ext (F := L.val.presheaf) L.isSheaf
    intro x _hx
    have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    let E := Scheme.Modules.overTrivializationOfRestrictIso L (V i)
      (Scheme.Modules.restrictIsoOfPullbackIso L (V i) (eV i).some)
    let W := U ⊓ V i
    have hWne : (W : Set X).Nonempty :=
      nonempty_preirreducible_inter U.isOpen (V i).isOpen
        hUne ⟨x, hi⟩
    let : Nonempty W := hWne.to_subtype
    have hW : t.val (op W) = 0 := by
      rw [← htres (homOfLE (show W ≤ U from inf_le_left)), hU, map_zero]
    let j : W ⟶ V i := homOfLE inf_le_right
    let c : Γ(X, V i) := E.hom.val.app (op (Over.mk (𝟙 (V i)))) (t.val (op (V i)))
    have hres : X.presheaf.map j.op c = 0 := by
      have hn := PresheafOfModules.naturality_apply E.hom.val
        (Over.homMk j : Over.mk j ⟶ Over.mk (𝟙 (V i))).op (t.val (op (V i)))
      change E.hom.val.app (op (Over.mk j))
        (L.val.map j.op (t.val (op (V i)))) = X.presheaf.map j.op c at hn
      rw [htres j, hW, map_zero] at hn
      exact hn.symm
    have hcV : c = 0 := (map_injective_of_isIntegral X j) (by simpa using hres)
    have hVec : t.val (op (V i)) = 0 := by
      have he := congrArg (fun f => f.val.app (op (Over.mk (𝟙 (V i))))
        (t.val (op (V i)))) E.hom_inv_id
      change E.inv.val.app (op (Over.mk (𝟙 (V i)))) c = t.val (op (V i)) at he
      rw [hcV, map_zero] at he
      exact he.symm
    refine ⟨V i, le_top, hi, ?_⟩
    change L.val.map (homOfLE le_top).op (t.val (op ⊤)) =
      L.val.map (homOfLE le_top).op (0 : Γ(L, ⊤))
    rw [htres, hVec, map_zero]
  apply (SheafOfModules.unitHomEquiv L).injective
  apply PresheafOfModules.sections_ext
  intro Q
  change t.val Q = 0
  rw [← htres (homOfLE (show Q.unop ≤ ⊤ from le_top)), htop, map_zero]

/-- A nonzero original line section on an integral scheme gives its actual effective Cartier ideal. -/
theorem zeroIdeal_isInvertible_of_ne_zero [IsIntegral X] (hs : s ≠ 0) :
    (zeroIdeal L hL s).IsInvertible := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := exists_affine_frame L hL x
  let : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  let c : Γ(X, U) := e.hom.val.app (op (Over.mk (𝟙 U.1)))
    (s.val.app (op U.1) (1 : Γ(X, U)))
  exact ⟨U, hx, c, mem_nonZeroDivisors_of_ne_zero (coefficient_ne_zero L hL s hs U.1 e),
    zeroIdeal_ideal_of_frame L hL s U e⟩

end EnvelopeProperty.LineSectionZeroIdeal
