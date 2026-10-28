import EnvelopeProperty.AlgGeom.InvertibleBaseIdealTransport
import EnvelopeProperty.AlgGeom.LineSectionZeroIdeal
import EnvelopeProperty.AlgGeom.ProjectiveLineBaseIdealGenerators

/-! # The whole base ideal uses the actual original section coefficients -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.InvertibleBaseIdealFrameCoefficients
open Scheme.Modules ModularCurves InvertibleSheafBaseIdeal

/-- The entire original contraction is the actual dual of the SAME original
structure-sheaf section map, with no supplied comparison. -/
theorem sectionEvaluation_eq_dual {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤)) :
    sectionEvaluation L s =
      dualMapObj (SchemeModuleGlobalSections.sectionHom L s) ≫
        (dualUnitObjIso (X := X)).hom := by
  apply SheafOfModules.hom_ext
  ext U d
  have h := SchemeTensorUnitSections.sectionEvaluation_apply L s U.unop d
  refine h.trans ?_
  change d.val.app (.op (Over.mk (𝟙 U.unop)))
      (L.val.map (𝟙 U.unop).op
        (L.val.map (.op (homOfLE (le_top : U.unop ≤ ⊤))) s)) =
    d.val.app (.op (Over.mk (𝟙 U.unop)))
      ((SchemeModuleGlobalSections.sectionHom L s).val.app U (1 : Γ(X, U.unop)))
  simp only [op_id, PresheafOfModules.map_id]
  have hs : (SchemeModuleGlobalSections.sectionHom L s).val.app U
      (1 : Γ(X, U.unop)) =
    L.presheaf.map (.op (homOfLE (le_top : U.unop ≤ ⊤))) s := by
    change (1 : Γ(X, U.unop)) •
      (show Γ(L, U.unop) from L.presheaf.map (.op (homOfLE le_top)) s) = _
    exact one_smul _ _
  exact congrArg (fun z : Γ(L, U.unop) =>
    d.val.app (.op (Over.mk (𝟙 U.unop))) z) hs.symm


/-- The WHOLE original section ideal equals the actual canonical zero ideal
of the SAME original section map. -/
theorem sectionIdeal_eq_zeroIdeal {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (s : Γ(L, ⊤)) :
    sectionIdeal hL s = LineSectionZeroIdeal.zeroIdeal L hL
      (SchemeModuleGlobalSections.sectionHom L s) := by
  let : (dualObj L).IsQuasicoherent := hL.dual.isQuasicoherent
  exact congrArg (QuasicoherentImageIdeal.imageIdeal (dualObj L))
    (sectionEvaluation_eq_dual L s)

/-- The actual coefficient of the SAME original global section in the given
original frame, using its genuine structure-sheaf section map. -/
def frameCoefficient {X : Scheme.{u}} (L : X.Modules) (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (s : Γ(L, ⊤)) : Γ(X, U) :=
  e.hom.val.app (.op (Over.mk (𝟙 U.1)))
    ((SchemeModuleGlobalSections.sectionHom L s).val.app (.op U.1) (1 : Γ(X, U)))

/-- Each actual original section ideal is the principal ideal of its actual
coefficient, on every original affine frame. -/
theorem sectionIdeal_ideal_of_frame {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (s : Γ(L, ⊤)) :
    (sectionIdeal hL s).ideal U = Ideal.span ({frameCoefficient L U e s} : Set Γ(X, U)) := by
  have h := congrArg (fun I : X.IdealSheafData => I.ideal U)
    (sectionIdeal_eq_zeroIdeal hL s)
  exact h.trans (LineSectionZeroIdeal.zeroIdeal_ideal_of_frame L hL
    (SchemeModuleGlobalSections.sectionHom L s) U e)

/-- The entire actual original base ideal uses the coefficients of ALL
original global sections in each original affine frame. -/
theorem baseIdeal_ideal_of_frame {X : Scheme.{u}} {L : X.Modules}
    (hL : IsInvertible L) (U : X.affineOpens)
    (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)) :
    (baseIdeal hL).ideal U =
      ⨆ s : Γ(L, ⊤), Ideal.span ({frameCoefficient L U e s} : Set Γ(X, U)) := by
  rw [baseIdeal, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  exact iSup_congr fun s => sectionIdeal_ideal_of_frame hL U e s

private theorem iSup_span_image {R : Type u} [CommRing R] {S : Type u}
    (G : Finset S) (c : S → R) :
    (⨆ s ∈ G, Ideal.span ({c s} : Set R)) = Ideal.span (c '' (G : Set S)) := by
  classical
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun hs => Ideal.span_le.mpr ?_
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact Ideal.subset_span ⟨s, hs, rfl⟩
  · apply Ideal.span_le.mpr
    intro a ha
    obtain ⟨s, hs, rfl⟩ := ha
    exact Ideal.mem_iSup_of_mem (R := R) s
      (Ideal.mem_iSup_of_mem (R := R) hs (Ideal.mem_span_singleton_self (c s)))

private theorem ideal_iSup_finset {X : Scheme.{u}} {S : Type u}
    (G : Finset S) (J : S → X.IdealSheafData) (U : X.affineOpens) :
    (⨆ s ∈ G, J s).ideal U = ⨆ s ∈ G, (J s).ideal U := by
  classical
  rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
  refine iSup_congr fun s => ?_
  by_cases hs : s ∈ G <;> simp [hs]

/-- One finite family is derived from the original projective geometry BEFORE
choosing any affine open or frame; its actual coefficients generate the WHOLE
original base ideal on EVERY such frame. -/
theorem exists_finite_global_frame_coefficients {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (hf : IsProjectiveFactorization f) (L : X.Modules) (hL : IsInvertible L) :
    ∃ G : Finset Γ(L, ⊤), ∀ (U : X.affineOpens)
      (e : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1)),
      (baseIdeal hL).ideal U =
        Ideal.span (frameCoefficient L U e '' (G : Set Γ(L, ⊤))) := by
  classical
  obtain ⟨G, hG⟩ := ProjectiveLineBaseIdealGenerators.exists_finite_global_generators
    f hf L hL
  refine ⟨G, fun U e => ?_⟩
  have hcoeff : (fun s : Γ(L, ⊤) => (sectionIdeal hL s).ideal U) =
      (fun s : Γ(L, ⊤) => Ideal.span ({frameCoefficient L U e s} : Set Γ(X, U))) :=
    funext (sectionIdeal_ideal_of_frame hL U e)
  have hi := congrArg (fun c : Γ(L, ⊤) → Ideal Γ(X, U) => ⨆ s ∈ G, c s) hcoeff
  exact (congrArg (fun I : X.IdealSheafData => I.ideal U) hG).trans
    ((ideal_iSup_finset G (sectionIdeal hL) U).trans
      (hi.trans (iSup_span_image G (frameCoefficient L U e))))


end EnvelopeProperty.InvertibleBaseIdealFrameCoefficients
