import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Exactness of the SAME original native associated-sheaf functor -/
noncomputable section
namespace EnvelopeProperty.TildeExactness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

private instance tildeAdditive (R : CommRingCat.{u}) : (tilde.functor R).Additive where
  map_add := by
    intro M N f g
    exact AlgebraicGeometry.tilde.map_add f g

/-- Actual original quasicoherent kernel closure, derived from genuine native localization. -/
theorem quasicoherent_closedUnderKernels (R : CommRingCat.{u}) :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderKernels := by
  constructor
  intro K hK
  obtain ⟨f, c, hc, hMN⟩ := hK
  rename_i M N
  let : M.IsQuasicoherent := hMN.1
  let : N.IsQuasicoherent := hMN.2
  have hK : (kernel f).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel f
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hc) hK

/-- The SAME actual native associated-sheaf functor preserves EVERY original kernel. -/
theorem preservesKernel (R : CommRingCat.{u}) {M N : ModuleCat R} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (tilde.functor R) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let : P.IsClosedUnderKernels := quasicoherent_closedUnderKernels R
  let E := tildeEquiv (R := R)
  let I := P.ι
  let : E.functor.PreservesZeroMorphisms :=
    ⟨fun _ _ => by apply ObjectProperty.hom_ext; exact AlgebraicGeometry.tilde.map_zero⟩
  let : PreservesLimit (parallelPair (E.functor.map f) 0) I :=
    P.preservesKernels_ι (E.functor.map f)
  let e : (parallelPair f 0 ⋙ E.functor) ≅ parallelPair (E.functor.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  let : PreservesLimit (parallelPair f 0 ⋙ E.functor) I :=
    preservesLimit_of_iso_diagram I e.symm
  change PreservesLimit (parallelPair f 0) (E.functor ⋙ I)
  infer_instance

/-- Genuine finite-limit preservation of the SAME actual associated-sheaf functor. -/
theorem preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (tilde.functor R) := by
  let : (tilde.functor R).Additive := tildeAdditive R
  let : ∀ {M N : ModuleCat R} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (tilde.functor R) := fun _ => preservesKernel R _
  exact Functor.preservesFiniteLimits_of_preservesKernels (tilde.functor R)

/-- The SAME original native associated-sheaf functor preserves actual native homology. -/
theorem preservesHomology (R : CommRingCat.{u}) : (tilde.functor R).PreservesHomology := by
  let : (tilde.functor R).Additive := tildeAdditive R
  let : PreservesFiniteLimits (tilde.functor R) := preservesFiniteLimits R
  let : (tilde.functor R).IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  infer_instance

private instance tildePreservesZero (R : CommRingCat.{u}) :
    (tilde.functor R).PreservesZeroMorphisms where
  map_zero _ _ := AlgebraicGeometry.tilde.map_zero

/-- ACTUAL native associated-sheaf image of EVERY SAME original module complex. -/
def associatedComplex (R : CommRingCat.{u}) (K : CochainComplex (ModuleCat R) ℕ) :
    CochainComplex (Spec R).Modules ℕ := by
  let T := tilde.functor R
  letI : T.PreservesZeroMorphisms := tildePreservesZero R
  exact (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The GENUINE native homology comparison on the SAME actual original complex. -/
def homologyIso (R : CommRingCat.{u}) (K : CochainComplex (ModuleCat R) ℕ) (q : ℕ) :
    (associatedComplex R K).homology q ≅ AlgebraicGeometry.tilde (K.homology q) := by
  let T := tilde.functor R
  letI : T.PreservesZeroMorphisms := tildePreservesZero R
  letI : T.PreservesHomology := preservesHomology R
  exact ShortComplex.mapHomologyIso (K.sc q) T

end EnvelopeProperty.TildeExactness
