import EnvelopeProperty.Global.FibreIdealPowerCechMaps
import EnvelopeProperty.Global.FibreInfinitesimalH0Cech

/-! # Original global-section kernel filtration in genuine degree-zero Rees cohomology -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FibreGlobalKernelCohomology

open FcReesCechIdealPowerSections

private theorem inverse_square {C : Type*} [Category C]
    {A B E F : C} (a : A ⟶ B) (b : E ⟶ F) (e : A ≅ E) (g : B ≅ F)
    (h : a ≫ g.hom = e.hom ≫ b) : b ≫ g.inv = e.inv ≫ a := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

private theorem map_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E G : C} (a : A ⟶ B) (b : B ⟶ G) (c : A ⟶ E) (d : E ⟶ G)
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

private theorem compose_squares {C : Type*} [Category C]
    {A B E F P Q : C} (a : A ⟶ B) (b : A ⟶ E) (c : B ⟶ F) (d : E ⟶ F)
    (e : E ⟶ P) (g : F ⟶ Q) (v : P ⟶ Q)
    (h₁ : a ≫ c = b ≫ d) (h₂ : d ≫ g = e ≫ v) :
    a ≫ (c ≫ g) = (b ≫ e) ≫ v := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

private def zeroInverse :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ FibreIdealPowers.powerModule I f 0 where
  val := PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := fun s => ⟨s, by
            intro U hUW
            rw [FibreIdealPowers.extendedPower_ideal, pow_zero]
            simp⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality {U V} h := by
        ext s
        apply Subtype.ext
        rfl }
    (by
      intro W a s
      apply Subtype.ext
      rfl)

/-- The actual original zeroth-power module is the ENTIRE original
structure module, with its original actual inclusion as the isomorphism. -/
def powerZeroIso : FibreIdealPowers.powerModule I f 0 ≅ SheafOfModules.unit X.ringCatSheaf where
  hom := (FibreIdealPowers.extendedPower I f 0).toModulesInclusion
  inv := zeroInverse I f
  hom_inv_id := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    rfl
  inv_hom_id := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    rfl

/-- Whole original ideal-power global sections identify over the SAME
original R action with the actual original global projection kernel. -/
def globalKernelSectionsIso (d : ℕ) :
    letI := FlatGlobalSections.sectionsAlgebra f
    (ModuleCat.restrictScalars (baseScalar (R := R))).obj
        (baseSections f (FibreIdealPowers.powerModule I f d)) ≅
      ModuleCat.of R ((FibreInfinitesimalH0.imageFiltration I f).N d) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  let M := (ModuleCat.restrictScalars (baseScalar (R := R))).obj
    (baseSections f (FibreIdealPowers.powerModule I f d))
  let : Module Γ(X, ⊤) M := ((FibreIdealPowers.powerModule I f d).val.obj (op ⊤)).isModule
  let e := FibreInfinitesimalH0.sectionsEquivKernel I f d
  let eR : M ≃ₗ[R] (FibreInfinitesimalH0.imageFiltration I f).N d :=
    { e.toAddEquiv with
      map_smul' := by
        intro r s
        change e ((f.appLE ⊤ ⊤ (by simp) (baseScalar (R := R) r)) • s) = r • e s
        have hc : f.appLE ⊤ ⊤ (by simp) (baseScalar (R := R) r) =
            ProperBirationalSections.coefficientMap f r := by
          change (f.appTop ≫ X.presheaf.map (𝟙 (op (⊤ : X.Opens))))
            (baseScalar (R := R) r) = _
          rw [CategoryTheory.Functor.map_id, Category.comp_id]
          rfl
        rw [hc]
        refine (e.map_smul (ProperBirationalSections.coefficientMap f r) s).trans ?_
        apply Subtype.ext
        rfl }
  exact eR.toModuleIso

/-- Every value of the genuine whole global kernel comparison is exactly
its unchanged ORIGINAL underlying global function. -/
theorem globalKernelSectionsIso_apply (d : ℕ)
    (s : (ModuleCat.restrictScalars (baseScalar (R := R))).obj
      (baseSections f (FibreIdealPowers.powerModule I f d))) :
    letI := FlatGlobalSections.sectionsAlgebra f
    ((globalKernelSectionsIso I f d).hom s : Γ(X, ⊤)) = (show Γ(X, ⊤) from s.1) := rfl


/-- EVERY higher-to-lower original global kernel inclusion, keeping the
same entire original global function and its original R action. -/
def kernelInclusion {n m : ℕ} (h : n ≤ m) :
    letI := FlatGlobalSections.sectionsAlgebra f
    ModuleCat.of R ((FibreInfinitesimalH0.imageFiltration I f).N m) ⟶
      ModuleCat.of R ((FibreInfinitesimalH0.imageFiltration I f).N n) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  exact ModuleCat.ofHom (Submodule.inclusion
    ((FibreInfinitesimalH0.imageFiltration I f).antitone h))

/-- The actual whole original global-section kernel comparisons retain
EVERY actual higher-to-lower ideal-power global-section inclusion. -/
theorem globalKernelSectionsIso_naturality {n m : ℕ} (h : n ≤ m) :
    letI := FlatGlobalSections.sectionsAlgebra f
    (ModuleCat.restrictScalars (baseScalar (R := R))).map
        (baseSectionsMap f (FibreIdealPowerTransitions.inclusion I f h)) ≫
        (globalKernelSectionsIso I f n).hom =
      (globalKernelSectionsIso I f m).hom ≫ kernelInclusion I f h := by
  let := FlatGlobalSections.sectionsAlgebra f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  rfl

/-- The actual zeroth global kernel is the WHOLE original global-section
module, preserving its actual original coefficients and every original function. -/
def kernelZeroIso :
    letI := FlatGlobalSections.sectionsAlgebra f
    ModuleCat.of R ((FibreInfinitesimalH0.imageFiltration I f).N 0) ≅
      ModuleCat.of R Γ(X, ⊤) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  let e : (FibreInfinitesimalH0.imageFiltration I f).N 0 ≃ₗ[R] Γ(X, ⊤) :=
    { toFun := fun s => s.1
      invFun := fun s => ⟨s, by rw [FibreInfinitesimalH0.imageFiltration_zero]; trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.toModuleIso

variable [X.IsSeparated] {ι : Type u} [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : TopologicalSpace.IsOpenCover U)

/-- The literal original degree-zero Rees cohomology is canonically the
SAME whole original global-section kernel, over the SAME original R coefficients. -/
def degreeZeroKernelIso (d : ℕ) :
    letI := FlatGlobalSections.sectionsAlgebra f
    (FcReesCechDegreeComplex.degreeComplex I f U hU d).homology 0 ≅
      ModuleCat.of R ((FibreInfinitesimalH0.imageFiltration I f).N d) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  exact (homologyIso I f U hU d 0).symm ≪≫
    (ModuleCat.restrictScalars (baseScalar (R := R))).mapIso
      (FibreInfinitesimalH0Cech.globalSectionsIso f U hcover
        (FibreIdealPowers.powerModule I f d)).symm ≪≫ globalKernelSectionsIso I f d


/-- The genuine literal degree-zero cohomology transition is the actual
whole ORIGINAL global-kernel inclusion under the SAME original R-linear isomorphisms. -/
theorem degreeZeroKernelIso_inclusion {n m : ℕ} (h : n ≤ m) :
    letI := FlatGlobalSections.sectionsAlgebra f
    FcReesCechDegreeTransitions.homologyLower I f U hU h 0 ≫
        (degreeZeroKernelIso I f U hU hcover n).hom =
      (degreeZeroKernelIso I f U hU hcover m).hom ≫ kernelInclusion I f h := by
  let := FlatGlobalSections.sectionsAlgebra f
  let F := ModuleCat.restrictScalars (baseScalar (R := R))
  have hd := inverse_square _ _ (homologyIso I f U hU m 0) (homologyIso I f U hU n 0)
    (FibreIdealPowerCechMaps.inclusion_homology I f U hU h 0)
  have hg := inverse_square _ _
    (FibreInfinitesimalH0Cech.globalSectionsIso f U hcover (FibreIdealPowers.powerModule I f m))
    (FibreInfinitesimalH0Cech.globalSectionsIso f U hcover (FibreIdealPowers.powerModule I f n))
    (FibreInfinitesimalH0Cech.globalSectionsIso_naturality f U hcover
      (FibreIdealPowerTransitions.inclusion I f h)).symm
  have hfg := map_square F _ _ _ _ hg
  have hcore := compose_squares _ _ _ _ _ _ _ hfg
    (globalKernelSectionsIso_naturality I f h)
  exact compose_squares _ _ _ _ _ _ _ hd hcore


/-- The actual original zeroth Rees-degree H0 is the WHOLE
original global-section module with its genuine original R coefficient action. -/
def degreeZeroGlobalIso :
    letI := FlatGlobalSections.sectionsAlgebra f
    (FcReesCechDegreeComplex.degreeComplex I f U hU 0).homology 0 ≅
      ModuleCat.of R Γ(X, ⊤) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  exact degreeZeroKernelIso I f U hU hcover 0 ≪≫ kernelZeroIso I f

/-- Every original ideal-power cohomology image in degree-zero H0 is
EXACTLY its whole ORIGINAL global-section kernel inclusion. -/
theorem degreeZeroGlobalIso_inclusion (d : ℕ) :
    letI := FlatGlobalSections.sectionsAlgebra f
    FcReesCechDegreeTransitions.homologyLower I f U hU (Nat.zero_le d) 0 ≫
        (degreeZeroGlobalIso I f U hU hcover).hom =
      (degreeZeroKernelIso I f U hU hcover d).hom ≫
        ModuleCat.ofHom ((FibreInfinitesimalH0.imageFiltration I f).N d).subtype := by
  let := FlatGlobalSections.sectionsAlgebra f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := ConcreteCategory.congr_hom
    (degreeZeroKernelIso_inclusion I f U hU hcover (Nat.zero_le d)) x
  exact congrArg (fun s : (FibreInfinitesimalH0.imageFiltration I f).N 0 =>
    (show Γ(X, ⊤) from s.1)) h

end EnvelopeProperty.FibreGlobalKernelCohomology
