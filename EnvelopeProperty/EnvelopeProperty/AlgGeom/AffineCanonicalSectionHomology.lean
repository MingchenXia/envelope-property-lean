import EnvelopeProperty.Algebra.LeftExactHomologyComparison
import EnvelopeProperty.AlgGeom.AffineQuasicoherentComplexHomology
import Mathlib.CategoryTheory.Abelian.Exact

/-! # The SAME canonical native homology map is an actual affine QC isomorphism -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace EnvelopeProperty.AffineCanonicalSectionHomology
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
variable (R : CommRingCat.{u})
private abbrev gamma : (Spec R).Modules ⥤ ModuleCat R := moduleSpecΓFunctor
local notation "G" => gamma R

private instance gammaAdditive : (G).Additive where
  map_add := by intro M N α β; rfl

private instance gammaPreservesZero : (G).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private instance gammaPreservesFiniteLimits : PreservesFiniteLimits G := by
  let : (G).IsRightAdjoint := (tilde.adjunction (R := R)).isRightAdjoint
  infer_instance

private theorem cycles_isQuasicoherent (S : ShortComplex (Spec R).Modules)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.cycles.IsQuasicoherent := by
  have h : (kernel S.g).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel S.g
  exact (Scheme.Modules.isQuasicoherent (Spec R)).prop_of_iso S.cyclesIsoKernel.symm h

private theorem homology_isQuasicoherent (S : ShortComplex (Spec R).Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.homology.IsQuasicoherent := by
  let : S.cycles.IsQuasicoherent := cycles_isQuasicoherent R S
  have h : (cokernel S.toCycles).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_cokernel S.toCycles
  exact (Scheme.Modules.isQuasicoherent (Spec R)).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.toCycles)
      S.homologyIsCokernel) h

private def leftData (S : ShortComplex (Spec R).Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map G).LeftHomologyData := by
  let : S.cycles.IsQuasicoherent := cycles_isQuasicoherent R S
  let : S.homology.IsQuasicoherent := homology_isQuasicoherent R S
  let : (kernel S.homologyπ).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_kernel S.homologyπ
  let k := kernel.lift S.homologyπ S.toCycles S.toCycles_comp_homologyπ
  have hx : (ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel
  let : Epi k := hx.epi_kernelLift
  let : Epi ((G).map k) := Scheme.Modules.moduleSpecΓ_epi_of_epi k
  let : Epi ((G).map S.homologyπ) := Scheme.Modules.moduleSpecΓ_epi_of_epi S.homologyπ
  have hz : (G).map S.toCycles ≫ (G).map S.homologyπ = 0 := by
    rw [← (G).map_comp, ShortComplex.toCycles_comp_homologyπ, (G).map_zero]
  let T : ShortComplex (ModuleCat R) := ShortComplex.mk ((G).map S.toCycles) ((G).map S.homologyπ) hz
  have hk : kernel.lift T.g T.f T.zero =
      (G).map k ≫ (PreservesKernel.iso G S.homologyπ).hom := by
    apply (cancel_mono (kernel.ι T.g)).mp
    rw [kernel.lift_ι]
    change (G).map S.toCycles =
      ((G).map k ≫ (PreservesKernel.iso G S.homologyπ).hom) ≫ kernel.ι ((G).map S.homologyπ)
    rw [Category.assoc, PreservesKernel.iso_hom, kernelComparison_comp_ι, ← (G).map_comp]
    exact (congrArg (G).map (kernel.lift_ι S.homologyπ S.toCycles
      S.toCycles_comp_homologyπ)).symm
  have hT : T.Exact := T.exact_iff_epi_kernel_lift.mpr (hk ▸ inferInstance)
  have wi : (G).map S.iCycles ≫ (S.map G).g = 0 := by
    change (G).map S.iCycles ≫ (G).map S.g = 0
    rw [← (G).map_comp, ShortComplex.iCycles_g, (G).map_zero]
  let hi := isLimitForkMapOfIsLimit' G S.iCycles_g S.cyclesIsKernel
  let f' := hi.lift (KernelFork.ofι (S.map G).f (S.map G).zero)
  have hf : f' = (G).map S.toCycles := by
    apply Fork.IsLimit.hom_ext hi
    dsimp only [f']
    rw [Fork.IsLimit.lift_ι]
    change (G).map S.f = (G).map S.toCycles ≫ (G).map S.iCycles
    rw [← (G).map_comp, ShortComplex.toCycles_i]
  have wπ : f' ≫ (G).map S.homologyπ = 0 := by rw [hf]; exact hz
  have hπ : IsColimit (CokernelCofork.ofπ ((G).map S.homologyπ) wπ) := by
    let e : parallelPair f' 0 ≅ parallelPair ((G).map S.toCycles) 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf) (by simp)
    refine IsColimit.precomposeInvEquiv e _
      (IsColimit.ofIsoColimit hT.gIsCokernel ?_)
    exact Cofork.ext (Iso.refl _) (by simp [e, T])
  exact
    { K := (G).obj S.cycles
      H := (G).obj S.homology
      i := (G).map S.iCycles
      π := (G).map S.homologyπ
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }

/-- The SAME canonical map is invertible from actual affine QC geometry, not an exact-H0 input. -/
theorem comparison_isIso (S : ShortComplex (Spec R).Modules)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    IsIso (LeftExactHomologyComparison.map S G) := by
  let h := leftData R S
  have hc : (LeftExactHomologyComparison.cyclesIso S G).hom = h.cyclesIso.hom := by
    apply (cancel_mono ((G).map S.iCycles)).mp
    exact (LeftExactHomologyComparison.cyclesIso_hom_iCycles S G).trans
      h.cyclesIso_hom_comp_i.symm
  have hm : LeftExactHomologyComparison.map S G = h.homologyIso.hom := by
    apply (cancel_epi (S.map G).homologyπ).mp
    rw [LeftExactHomologyComparison.homologyπ_map, hc]
    exact h.homologyπ_comp_homologyIso_hom.symm
  rw [hm]
  infer_instance

variable (K : CochainComplex (Spec R).Modules ℕ) [∀ q, (K.X q).IsQuasicoherent]

/-- Native homology of original affine sections is sections of the SAME original homology. -/
def homologyIso (q : ℕ) :
    (AffineQuasicoherentComplexHomology.sectionComplex R K).homology q ≅ (G).obj (K.homology q) := by
  let : (K.sc q).X₁.IsQuasicoherent := (inferInstance : ∀ j, (K.X j).IsQuasicoherent) _
  let : (K.sc q).X₂.IsQuasicoherent := (inferInstance : ∀ j, (K.X j).IsQuasicoherent) _
  let : (K.sc q).X₃.IsQuasicoherent := (inferInstance : ∀ j, (K.X j).IsQuasicoherent) _
  let : IsIso (LeftExactHomologyComparison.map (K.sc q) G) := comparison_isIso R (K.sc q)
  exact asIso (LeftExactHomologyComparison.map (K.sc q) G)

/-- The entire forward map is EXACTLY the original canonical comparison. -/
theorem homologyIso_hom (q : ℕ) :
    (homologyIso R K q).hom = LeftExactHomologyComparison.map (K.sc q) G := rfl

/-- Every native cycle class retains the actual original evaluated homology projection. -/
theorem homologyIso_cycle (q : ℕ) :
    ((AffineQuasicoherentComplexHomology.sectionComplex R K).sc q).homologyπ ≫
        (homologyIso R K q).hom =
      (LeftExactHomologyComparison.cyclesIso (K.sc q) G).hom ≫ (G).map (K.sc q).homologyπ :=
  LeftExactHomologyComparison.homologyπ_map (K.sc q) G

end EnvelopeProperty.AffineCanonicalSectionHomology
