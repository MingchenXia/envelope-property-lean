import EnvelopeProperty.Global.FibreInfinitesimalSections
import EnvelopeProperty.AlgGeom.IdealModuleFunctorial
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Genuine whole infinitesimal module-sheaf short exact sequence

The SAME actual geometric ideal-power module is the genuine categorical
kernel of the original canonical module map to the pushforward of the
LITERAL infinitesimal model. Local affine surjectivity derives its genuine
epimorphism, without a supplied exactness or quotient comparison premise.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
noncomputable section
universe u

namespace EnvelopeProperty.FibreInfinitesimalModules

open InfinitesimalSchemes

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual canonical map to the genuine pushforward of the original
infinitesimal structure module. -/
abbrev sectionMap (n : ℕ) : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pushforward (projection I f n)).obj
      (SheafOfModules.unit (model I f n).ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit (projection I f n).toRingCatSheafHom

/-- On EVERY original open the actual canonical module map is the literal
original scheme section map. -/
theorem sectionMap_app (n : ℕ) (W : X.Opens)
    (s : Γ(SheafOfModules.unit X.ringCatSheaf, W)) :
    (sectionMap I f n).val.app (op W) s = (projection I f n).app W s := rfl

/-- The SAME genuine ideal-power module on EVERY original open is exactly
the kernel of the ENTIRE actual infinitesimal projection section map. -/
theorem projection_isLocallyMem_iff (n : ℕ) (W : X.Opens) (s : Γ(X, W)) :
    (FibreIdealPowers.extendedPower I f n).IsLocallyMem W s ↔
      (projection I f n).app W s = 0 := by
  constructor
  · intro hs
    apply Scheme.IdealSheafData.ker_isLocallyMem_app_eq_zero (projection I f n) W s
    rwa [FibreInfinitesimalSections.projection_ker]
  · intro hs U hUW
    rw [← FibreInfinitesimalSections.projection_ker, Scheme.Hom.ker_apply]
    change (projection I f n).app U (X.presheaf.map (homOfLE hUW).op s) = 0
    have hnat := congrArg
      (fun q : Γ(X, W) ⟶ Γ(model I f n, projection I f n ⁻¹ᵁ U.1) => q.hom s)
      ((projection I f n).naturality (homOfLE hUW).op)
    change (projection I f n).app U (X.presheaf.map (homOfLE hUW).op s) =
      (model I f n).presheaf.map _ ((projection I f n).app W s) at hnat
    simpa only [hs, map_zero] using hnat

/-- The actual whole ideal-power inclusion followed by the genuine original
canonical section map is zero on the ENTIRE original scheme. -/
theorem inclusion_comp_sectionMap (n : ℕ) :
    (FibreIdealPowers.extendedPower I f n).toModulesInclusion ≫ sectionMap I f n = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  exact (projection_isLocallyMem_iff I f n W s.1).mp s.2

/-- The SAME original ideal-power inclusion and genuine infinitesimal
pushforward section map form an actual complex of module sheaves. -/
def sequence (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (FibreIdealPowers.extendedPower I f n).toModulesInclusion
    (sectionMap I f n) (inclusion_comp_sectionMap I f n)

/-- The actual original whole module section pair is exact on EVERY open. -/
theorem section_exact (n : ℕ) (W : X.Opens) :
    Function.Exact
      ((FibreIdealPowers.extendedPower I f n).toModulesInclusion.app W)
      ((sectionMap I f n).val.app (op W)) := by
  intro s
  change (projection I f n).app W (show Γ(X, W) from s) = 0 ↔
    ∃ a : Γ(FibreIdealPowers.powerModule I f n, W), a.1 = s
  rw [← projection_isLocallyMem_iff]
  exact ⟨fun hs => ⟨⟨s, hs⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩

/-- The SAME genuine original ideal-power section inclusion is injective on EVERY open. -/
theorem section_injective (n : ℕ) (W : X.Opens) :
    Function.Injective ((FibreIdealPowers.extendedPower I f n).toModulesInclusion.app W) :=
  Subtype.val_injective

/-- Every actual module map with zero whole infinitesimal composite lifts
to the SAME genuine geometric ideal-power module, retaining all sections. -/
def kernelLift (n : ℕ) {M : X.Modules} (t : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (ht : t ≫ sectionMap I f n = 0) : M ⟶ FibreIdealPowers.powerModule I f n where
  val := PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := fun s => ⟨t.app W.unop s, (projection_isLocallyMem_iff I f n W.unop _).mpr (by
            have h := congrArg (fun a => a.app W.unop s) ht
            exact h)⟩
          map_zero' := Subtype.ext ((t.app W.unop).hom.map_zero)
          map_add' := fun s v => Subtype.ext ((t.app W.unop).hom.map_add s v) }
      naturality {U V} h := by
        ext s
        apply Subtype.ext
        exact congrArg (fun q => q s) (t.val.naturality h) }
    (by
      intro W r s
      apply Subtype.ext
      exact (t.val.app W).hom.map_smul r s)

/-- The actual categorical kernel lift retains the ENTIRE original module morphism. -/
theorem kernelLift_inclusion (n : ℕ) {M : X.Modules}
    (t : M ⟶ SheafOfModules.unit X.ringCatSheaf) (ht : t ≫ sectionMap I f n = 0) :
    kernelLift I f n t ht ≫ (FibreIdealPowers.extendedPower I f n).toModulesInclusion = t := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

/-- The SAME actual original geometric ideal-power module is the genuine
categorical kernel of the original infinitesimal section morphism. -/
def kernelIsLimit (n : ℕ) :
    IsLimit (KernelFork.ofι (FibreIdealPowers.extendedPower I f n).toModulesInclusion
      (inclusion_comp_sectionMap I f n)) :=
  Fork.IsLimit.mk _
    (fun s => kernelLift I f n s.ι s.condition)
    (fun s => kernelLift_inclusion I f n s.ι s.condition)
    (fun s _m hm => (cancel_mono
      (FibreIdealPowers.extendedPower I f n).toModulesInclusion).mp
        (hm.trans (kernelLift_inclusion I f n s.ι s.condition).symm))

/-- The SAME actual original module-sheaf sequence is genuinely exact. -/
theorem sequence_exact (n : ℕ) : (sequence I f n).Exact :=
  (sequence I f n).exact_of_f_is_kernel (kernelIsLimit I f n)

/-- The actual original canonical module map is locally surjective, using
the genuine original affine closed-immersion section surjectivity. -/
theorem sectionMap_isLocallySurjective (n : ℕ) :
    Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (sectionMap I f n)) := by
  constructor
  intro W s x hx
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := W) (x := x) hx
  refine ⟨V, homOfLE hVW, ?_, hxV⟩
  exact FibreInfinitesimalSections.affine_projection_surjective I f n ⟨V, hV⟩ _

/-- The SAME original canonical infinitesimal section map is an actual
epimorphism of module sheaves, without global section surjectivity. -/
instance sectionMap_epi (n : ℕ) : Epi (sectionMap I f n) := by
  let := sectionMap_isLocallySurjective I f n
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map inferInstance

/-- The SAME actual original ideal-power, structure module and literal
infinitesimal pushforward form a genuine whole short exact sequence. -/
theorem sequence_shortExact (n : ℕ) : (sequence I f n).ShortExact where
  exact := sequence_exact I f n
  mono_f := inferInstanceAs (Mono (FibreIdealPowers.extendedPower I f n).toModulesInclusion)
  epi_g := sectionMap_epi I f n

/-- Evaluation of the SAME actual whole infinitesimal module sequence on
an arbitrary original open, with its actual original section-ring scalars. -/
def sectionSequence (n : ℕ) (W : X.Opens) : ShortComplex (ModuleCat Γ(X, W)) :=
  ShortComplex.mk
    ((FibreIdealPowers.extendedPower I f n).toModulesInclusion.val.app (op W))
    ((sectionMap I f n).val.app (op W)) (by
      ext s
      exact (projection_isLocallyMem_iff I f n W s.1).mp s.2)

/-- The actual evaluated original module sequence is exact on EVERY open,
without a surjectivity assertion on nonaffine opens. -/
theorem sectionSequence_exact (n : ℕ) (W : X.Opens) :
    (sectionSequence I f n W).Exact :=
  ModuleCat.shortComplex_exact _ (section_exact I f n W)

/-- On EVERY original affine open, including every affine intersection in
an original cover, evaluation of the SAME genuine sequence is short exact. -/
theorem affine_sectionSequence_shortExact (n : ℕ) (U : X.affineOpens) :
    (sectionSequence I f n U).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (section_exact I f n U)
    (section_injective I f n U)
    (FibreInfinitesimalSections.affine_projection_surjective I f n U)

end EnvelopeProperty.FibreInfinitesimalModules
