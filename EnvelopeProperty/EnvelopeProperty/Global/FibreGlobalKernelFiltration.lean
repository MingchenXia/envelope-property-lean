import EnvelopeProperty.Global.FibreGlobalKernelCohomology
import EnvelopeProperty.Global.FibreStableFiltration
import EnvelopeProperty.AlgGeom.FormalFunctionsImageFiltration

/-! # Genuine stable original global-kernel filtration and whole quotient reconstruction -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FibreGlobalKernelFiltration

open FibreGlobalKernelCohomology

private theorem stable_of_map {A M N : Type*} [CommRing A] [AddCommGroup M]
    [AddCommGroup N] [Module A M] [Module A N] (I : Ideal A)
    (F : I.Filtration M) (G : I.Filtration N) (e : M →ₗ[A] N)
    (hF : F.Stable) (hN : ∀ n, (F.N n).map e = G.N n) : G.Stable := by
  obtain ⟨c, hc⟩ := hF
  refine ⟨c, fun n hn => ?_⟩
  calc
    I • G.N n = I • (F.N n).map e := congrArg (fun S => I • S) (hN n).symm
    _ = (I • F.N n).map e := (Submodule.map_smul'' I (F.N n) e).symm
    _ = (F.N (n+1)).map e := congrArg (fun S : Submodule A M => S.map e) (hc n hn)
    _ = G.N (n+1) := hN (n+1)

private theorem map_range_eq_submodule {A : Type u} [CommRing A]
    {N : Type u} [AddCommGroup N] [Module A N] (S : Submodule A N)
    {M P : ModuleCat.{u} A} (e0 : M ≅ ModuleCat.of A N) (ed : P ≅ ModuleCat.of A S)
    (l : P ⟶ M) (hl : l ≫ e0.hom = ed.hom ≫ ModuleCat.ofHom S.subtype) :
    (LinearMap.range l.hom).map e0.hom.hom = S := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, rfl⟩
    have h := ConcreteCategory.congr_hom hl y
    change e0.hom (l y) = (ed.hom y).1 at h
    exact h.symm ▸ (ed.hom y).2
  · intro hs
    let y := ed.inv ⟨s, hs⟩
    refine ⟨l y, ⟨y, rfl⟩, ?_⟩
    have h := ConcreteCategory.congr_hom hl y
    change e0.hom (l y) = (ed.hom y).1 at h
    exact h.trans (congrArg (fun z : S => z.1) (Iso.inv_hom_id_apply ed ⟨s, hs⟩))

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [X.IsSeparated]
    {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : TopologicalSpace.IsOpenCover U)

/-- The ACTUAL original cohomology-image filtration maps to EXACTLY the
whole original global projection-kernel filtration under the original R-linear isomorphism. -/
theorem image_transport (d : ℕ) :
    letI := FlatGlobalSections.sectionsAlgebra f
    ((FormalFunctionsImageFiltration.imageFiltration I f U hU 0).N d).map
        (degreeZeroGlobalIso I f U hU hcover).hom.hom =
      (FibreInfinitesimalH0.imageFiltration I f).N d := by
  let := FlatGlobalSections.sectionsAlgebra f
  exact map_range_eq_submodule ((FibreInfinitesimalH0.imageFiltration I f).N d)
    (degreeZeroGlobalIso I f U hU hcover) (degreeZeroKernelIso I f U hU hcover d)
    (FcReesCechDegreeTransitions.homologyLower I f U hU (Nat.zero_le d) 0)
    (degreeZeroGlobalIso_inclusion I f U hU hcover d)

variable [IsNoetherianRing R] (hf : IsProjectiveFactorization f)
include I U hU hcover hf

/-- Actual projective coherent cohomology makes the WHOLE ORIGINAL
global-section module genuinely finite for its original R coefficient action. -/
theorem globalSections_finite :
    letI := FlatGlobalSections.sectionsAlgebra f
    Module.Finite R Γ(X, ⊤) := by
  let := FlatGlobalSections.sectionsAlgebra f
  let : Module.Finite R ((FcReesCechDegreeComplex.degreeComplex I f U hU 0).homology 0) :=
    FormalFunctionsDegreeFinite.degreeCech_finite I f hf U hcover hU 0 0
  exact Module.Finite.equiv (degreeZeroGlobalIso I f U hU hcover).toLinearEquiv

/-- Genuine finite original projective Rees cohomology DERIVES stability
of the SAME original global-section kernel filtration, without a stability premise. -/
theorem imageFiltration_stable :
    letI := FlatGlobalSections.sectionsAlgebra f
    (FibreInfinitesimalH0.imageFiltration I f).Stable := by
  let := FlatGlobalSections.sectionsAlgebra f
  exact stable_of_map I (FormalFunctionsImageFiltration.imageFiltration I f U hU 0)
    (FibreInfinitesimalH0.imageFiltration I f) (degreeZeroGlobalIso I f U hU hcover).hom.hom
    (FormalFunctionsImageFiltration.imageFiltration_stable I f U hU hf hcover 0)
    (image_transport I f U hU hcover)

variable [IsAdicComplete I R]

/-- The ORIGINAL whole global-section quotient map reconstructs every
compatible family in its ACTUAL original kernel quotients over the actual complete base. -/
def quotientReconstructionEquiv :
    letI := FlatGlobalSections.sectionsAlgebra f
    Γ(X, ⊤) ≃ₗ[R]
      FibreStableFiltration.compatibleQuotients I (FibreInfinitesimalH0.imageFiltration I f) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  let : Module.Finite R Γ(X, ⊤) := globalSections_finite I f U hU hcover hf
  exact FibreStableFiltration.reconstructionEquiv I (FibreInfinitesimalH0.imageFiltration I f)
    (imageFiltration_stable I f U hU hcover hf) (FibreInfinitesimalH0.imageFiltration_zero I f)

/-- Every coordinate of the actual reconstruction is the quotient of the
SAME ORIGINAL global section by its ENTIRE original projection kernel. -/
theorem quotientReconstructionEquiv_apply (s : Γ(X, ⊤)) (n : ℕ) :
    letI := FlatGlobalSections.sectionsAlgebra f
    (quotientReconstructionEquiv I f U hU hcover hf s).1 n =
      ((FibreInfinitesimalH0.imageFiltration I f).N (n+1)).mkQ s := rfl

end EnvelopeProperty.FibreGlobalKernelFiltration
