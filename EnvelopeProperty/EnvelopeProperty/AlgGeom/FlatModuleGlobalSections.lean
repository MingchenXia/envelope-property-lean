import EnvelopeProperty.AlgGeom.SchemeModuleFlatBaseChangeAffineOpen
import ModularCurves.ForMathlib.FiniteAffineOpenCover
import ModularCurves.ForMathlib.SheafCechCochains

/-! # Whole original quasicoherent module sections under actual flat base change -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.FlatModuleGlobalSections

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- Genuine compactness, separatedness and flatness make the actual entire
canonical section comparison invertible, without a Cech matching premise. -/
theorem isIso_comparison [Module.Flat R S] [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app (op ⊤)) := by
  obtain ⟨ι, hι, U, hcover, hU⟩ := X.exists_finite_affine_openCover
  let : Finite ι := hι
  let : ∀ i : Fin 1 → ι,
      IsIso ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (⊤ ⊓ ∏ᶜ fun k : Fin 1 => U (i k)))) := fun i =>
    SchemeModuleFlatBaseChangeAffineOpen.isIso_comparison p M _
      (by simpa only [top_inf_eq] using IsAffineOpen.cechIntersection U hU 0 i)
  let : ∀ i : Fin 2 → ι,
      IsIso ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app
        (op (⊤ ⊓ ∏ᶜ fun k : Fin 2 => U (i k)))) := fun i =>
    SchemeModuleFlatBaseChangeAffineOpen.isIso_comparison p M _
      (by simpa only [top_inf_eq] using IsAffineOpen.cechIntersection U hU 1 i)
  exact FiniteCechFlatBaseChange.isIso_component
    (SchemeScalarModulePresheaf.sheaf p M)
    (SchemeModuleFlatBaseChangeMap.targetSheaf (S := S) p M)
    (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M) U hcover ⊤

private def targetTopIso (M : X.Modules) :
    (SchemeModuleFlatBaseChangeMap.targetSheaf (S := S) p M).obj.obj (op ⊤) ≅
      AffineModuleFlatBaseChange.sections (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M) :=
  (SchemeScalarModulePresheaf.sheaf (FlatGlobalSections.structureMap (S := S) p)
    ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)).obj.mapIso
      (eqToIso (show (⊤ : (FlatGlobalSections.baseChange (S := S) p).Opens) =
        (FlatGlobalSections.firstProjection (S := S) p) ⁻¹ᵁ ⊤ by simp)).op ≪≫
    SchemeScalarModulePresheaf.topSectionsIso (FlatGlobalSections.structureMap (S := S) p)
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M)

/-- The literal whole original global-section scalar-extension morphism,
constructed from the actual canonical unit comparison and original top transports. -/
def globalComparison (M : X.Modules) :
    (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).obj
        (AffineModuleFlatBaseChange.sections p M) ⟶
      AffineModuleFlatBaseChange.sections (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M) :=
  (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).map
      (SchemeScalarModulePresheaf.topSectionsIso p M).inv ≫
    (SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app (op ⊤) ≫
      (targetTopIso (S := S) p M).hom

private theorem composite_tmul {A A' : ModuleCat.{u} R} {B C : ModuleCat.{u} S}
    (r : A ⟶ A')
    (c : (FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).obj A' ⟶ B)
    (t : B ⟶ C) (v : A' → B)
    (hc : ∀ (s : S) (m : A'), c (s ⊗ₜ[R] m) = s • v m) (s : S) (m : A) :
    ((FiniteCechFlatBaseChange.tensorFunctor (R := R) (S := S)).map r ≫ c ≫ t)
      (s ⊗ₜ[R] m) = s • t (v (r m)) := by
  change t (c (s ⊗ₜ[R] r m)) = _
  rw [hc, t.hom.map_smul]

private theorem targetTopIso_unit (M : X.Modules)
    (m : AffineModuleFlatBaseChange.sections p M) :
    (targetTopIso (S := S) p M).hom
      (SchemeModuleFlatBaseChangeMap.unitMap (S := S) p M ⊤
        ((SchemeScalarModulePresheaf.topSectionsIso p M).inv m)) =
      Scheme.Modules.affinePullbackUnitTop
        (FlatGlobalSections.firstProjection (S := S) p) M m := rfl

/-- Every original pure tensor is sent to its literal original coefficient
multiplied by the actual original pullback-adjunction-unit section. -/
theorem globalComparison_tmul (M : X.Modules)
    (s : S) (m : AffineModuleFlatBaseChange.sections p M) :
    globalComparison (S := S) p M (s ⊗ₜ[R] m) =
      (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := S) p) s) •
      Scheme.Modules.affinePullbackUnitTop
        (FlatGlobalSections.firstProjection (S := S) p) M m := by
  have h := composite_tmul (SchemeScalarModulePresheaf.topSectionsIso p M).inv
    ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app (op ⊤))
    (targetTopIso (S := S) p M).hom
    (fun m => SchemeModuleFlatBaseChangeMap.unitMap (S := S) p M ⊤ m)
    (fun s m => SchemeModuleFlatBaseChangeMap.comparison_tmul (S := S) p M ⊤ s m) s m
  rw [targetTopIso_unit] at h
  exact h

/-- Whole original quasicoherent global sections genuinely commute with
actual flat scalar base change on a compact separated scheme. -/
def tensorEquiv [Module.Flat R S] [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] :
    S ⊗[R] AffineModuleFlatBaseChange.sections p M ≃ₗ[S]
      AffineModuleFlatBaseChange.sections (FlatGlobalSections.structureMap (S := S) p)
        ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := S) p)).obj M) := by
  let : IsIso ((SchemeModuleFlatBaseChangeMap.comparison (S := S) p M).app (op ⊤)) :=
    isIso_comparison p M
  let : IsIso (globalComparison (S := S) p M) := by
    dsimp only [globalComparison]
    infer_instance
  exact (asIso (globalComparison (S := S) p M)).toLinearEquiv

/-- ALL pure tensors in the genuine whole global-section equivalence retain
the actual original coefficient map and original pullback unit. -/
theorem tensorEquiv_tmul [Module.Flat R S] [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent]
    (s : S) (m : AffineModuleFlatBaseChange.sections p M) :
    tensorEquiv (S := S) p M (s ⊗ₜ[R] m) =
      (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := S) p) s) •
      Scheme.Modules.affinePullbackUnitTop
        (FlatGlobalSections.firstProjection (S := S) p) M m :=
  globalComparison_tmul p M s m

end EnvelopeProperty.FlatModuleGlobalSections
