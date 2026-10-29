import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorEquivalence
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.EllipticCurve.PoleSheaf

/-! # Genuine tensoring by an original line preserves quasicoherence -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeInvertibleTensorQuasicoherent
attribute [local instance] Scheme.Modules.monoidalCategory

/-- An actual original local line frame gives the actual whole restricted
module-tensor comparison with the SAME original restricted module. -/
def restrictTensorIsoOfFrame {X : Scheme.{u}} (M L : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ unitObj U.toScheme) :
    (M ⊗ L).restrict U.ι ≅ M.restrict U.ι :=
  ModularCurves.restrictMonoidalTensorIso U.ι M L ≪≫
    (Iso.refl (M.restrict U.ι) ⊗ᵢ e) ≪≫
    (Iso.refl (M.restrict U.ι) ⊗ᵢ (ModularCurves.monoidalUnitObjIso U.toScheme).symm) ≪≫
    ρ_ (M.restrict U.ι)

theorem exists_affine_trivializing_cover {X : Scheme.{u}} (L : X.Modules)
    (hL : IsInvertible L) :
    ∃ (ι : Type u) (U : ι → X.affineOpens), IsOpenCover (fun i => (U i).1) ∧
      ∀ i, Nonempty (L.restrict (U i).1.ι ≅ unitObj (U i).1.toScheme) := by
  classical
  obtain ⟨ι, V, hV, e⟩ := hL
  let I := Σ i : ι, { W : X.affineOpens // W.1 ≤ V i }
  let U : I → X.affineOpens := fun i => i.2.1
  refine ⟨I, U, ?_, ?_⟩
  · change (⨆ i : I, (U i).1) = ⊤
    apply le_antisymm le_top
    intro x _hx
    have hx : x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨W, hWa, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hi
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨W,hWa⟩, hWV⟩⟩, hxW⟩
  · intro i
    exact ⟨restrictOpenTrivialization i.2.2
      (restrictIsoOfPullbackIso L (V i.1) (e i.1).some)⟩

/-- The original quasicoherent module tensored by any original invertible
module remains genuinely quasicoherent. The actual affine trivializing cover
and local whole-module tensor comparisons are DERIVED internally from invertibility. -/
theorem isQuasicoherent_tensorRight {X : Scheme.{u}} (M L : X.Modules)
    [M.IsQuasicoherent] (hL : IsInvertible L) : (M ⊗ L).IsQuasicoherent := by
  obtain ⟨ι, U, hU, e⟩ := exists_affine_trivializing_cover L hL
  have hlocal (i : ι) : ((M ⊗ L).over (U i).1).IsQuasicoherent := by
    let : (M.restrict (U i).1.ι).IsQuasicoherent := inferInstance
    let : ((M ⊗ L).restrict (U i).1.ι).IsQuasicoherent :=
      (isQuasicoherent (U i).1.toScheme).prop_of_iso
        (restrictTensorIsoOfFrame M L (U i).1 (e i).some).symm inferInstance
    exact isQuasicoherent_over_of_restrict_of_isAffineOpen (M ⊗ L) (U i).1
  have hcover : (Opens.grothendieckTopology X).CoversTop (fun i => (U i).1) := by
    rw [Opens.coversTop_iff]
    exact hU
  exact @SheafOfModules.IsQuasicoherent.of_coversTop
    _ _ _ _ _ _ _ _ (M ⊗ L : X.Modules) _ (fun i => (U i).1) hcover hlocal

end EnvelopeProperty.SchemeInvertibleTensorQuasicoherent
