import EnvelopeProperty.Global.FibreInfinitesimalModules
import EnvelopeProperty.FlatGlobalSections
import Mathlib.RingTheory.Filtration

/-!
# Genuine global-H0 image kernels and all original infinitesimal quotients

The whole original ideal-power global-section image is the actual kernel
of the literal infinitesimal projection. Its genuine original coefficient
module structure gives an I-filtration. Quotient maps retain every
original representative and every actual whole order transition.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
namespace EnvelopeProperty.FibreInfinitesimalH0

open InfinitesimalSchemes
variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The actual entire global section kernel of the original order-n projection. -/
def sectionKernel (n : ℕ) : Ideal Γ(X, ⊤) :=
  RingHom.ker (projection I f n).appTop.hom

/-- Membership in the actual global kernel is exactly being a whole
section of the SAME actual original geometric ideal power. -/
theorem mem_sectionKernel_iff (n : ℕ) (s : Γ(X, ⊤)) :
    s ∈ sectionKernel I f n ↔ (FibreIdealPowers.extendedPower I f n).IsLocallyMem ⊤ s :=
  (FibreInfinitesimalModules.projection_isLocallyMem_iff I f n ⊤ s).symm

/-- The global kernel is exactly the ENTIRE actual original ideal-power
section image, with its original subtype inclusion. -/
theorem mem_sectionKernel_iff_exists (n : ℕ) (s : Γ(X, ⊤)) :
    s ∈ sectionKernel I f n ↔
      ∃ a : Γ(FibreIdealPowers.powerModule I f n, ⊤),
        (FibreIdealPowers.extendedPower I f n).toModulesInclusion.app ⊤ a = s :=
  FibreInfinitesimalModules.section_exact I f n ⊤ s

/-- The global kernel is the ENTIRE actual linear image of the original
global ideal-power module inclusion, with the whole section-ring action. -/
theorem sectionKernel_eq_range (n : ℕ) :
    (sectionKernel I f n : Submodule Γ(X, ⊤) Γ(X, ⊤)) =
      LinearMap.range
        ((FibreIdealPowers.extendedPower I f n).toModulesInclusion.val.app (op ⊤)).hom := by
  ext s
  exact mem_sectionKernel_iff_exists I f n s

/-- The ENTIRE original global ideal-power module is the actual original
projection kernel, preserving its original section-ring scalar action. -/
def sectionsEquivKernel (n : ℕ) :
    Γ(FibreIdealPowers.powerModule I f n, ⊤) ≃ₗ[Γ(X, ⊤)] sectionKernel I f n where
  toFun s := ⟨s.1, (mem_sectionKernel_iff I f n s.1).mpr s.2⟩
  invFun s := ⟨s.1, (mem_sectionKernel_iff I f n s.1).mp s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The whole actual original kernel equivalence retains EVERY original
global section, including all its nilpotent directions. -/
theorem sectionsEquivKernel_apply (n : ℕ)
    (s : Γ(FibreIdealPowers.powerModule I f n, ⊤)) :
    (sectionsEquivKernel I f n s).1 = s.1 := rfl

/-- The entire original transition preserves every original projection section. -/
theorem transition_projection_sections {n m : ℕ} (h : n ≤ m) :
    (transition I f h).appTop.hom.comp (projection I f m).appTop.hom =
      (projection I f n).appTop.hom := by
  have hh := congrArg (fun q => q.appTop) (transition_projection I f h)
  rw [Scheme.Hom.comp_appTop] at hh
  ext s
  exact congrArg (fun q : Γ(X, ⊤) ⟶ Γ(model I f n, ⊤) => q s) hh

/-- The original global projection kernels decrease at every original order. -/
theorem sectionKernel_antitone : Antitone (sectionKernel I f) := by
  intro n m h s hs
  change (projection I f n).appTop s = 0
  rw [← RingHom.congr_fun (transition_projection_sections I f h) s]
  change (transition I f h).appTop ((projection I f m).appTop s) = 0
  rw [hs, map_zero]

/-- At order zero the ACTUAL original global kernel is the whole original ring. -/
theorem sectionKernel_zero : sectionKernel I f 0 = ⊤ := by
  apply top_unique
  intro s _
  rw [mem_sectionKernel_iff]
  intro U hU
  rw [FibreIdealPowers.extendedPower_ideal, pow_zero]
  simp

/-- Restricting EVERY original global coefficient gives its original
coefficient section on the ENTIRE original open. -/
theorem coefficient_restriction (U : X.Opens) (r : R) :
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (ProperBirationalSections.coefficientMap f r) = sectionsHom f U r := by
  rfl

/-- Multiplication by every actual original ideal coefficient advances the
ENTIRE original global kernel by one genuine geometric power. -/
theorem coefficient_mul_mem_sectionKernel (n : ℕ) {r : R} (hr : r ∈ I)
    {s : Γ(X, ⊤)} (hs : s ∈ sectionKernel I f n) :
    ProperBirationalSections.coefficientMap f r * s ∈ sectionKernel I f (n+1) := by
  rw [mem_sectionKernel_iff] at hs ⊢
  intro U hU
  rw [FibreIdealPowers.extendedPower_ideal, pow_succ']
  rw [map_mul, coefficient_restriction]
  apply Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hr)
  simpa only [FibreIdealPowers.extendedPower_ideal] using hs U hU

/-- The SAME actual original global-section image kernels form a genuine
I-filtration with the original coefficient-induced R-module action. -/
def imageFiltration :
    letI := FlatGlobalSections.sectionsAlgebra f
    I.Filtration Γ(X, ⊤) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  exact
    { N n := (sectionKernel I f n).restrictScalars R
      mono n := sectionKernel_antitone I f (Nat.le_succ n)
      smul_le n := Submodule.smul_le.mpr (fun r hr s hs =>
        coefficient_mul_mem_sectionKernel I f n hr hs) }

/-- Membership in the genuine original image filtration is exactly whole
vanishing under the LITERAL original infinitesimal projection section map. -/
theorem mem_imageFiltration (n : ℕ) (s : Γ(X, ⊤)) :
    letI := FlatGlobalSections.sectionsAlgebra f
    s ∈ (imageFiltration I f).N n ↔ (projection I f n).appTop s = 0 := Iff.rfl

/-- The genuine original image filtration starts at the WHOLE original
global-section module, including nilpotents and arbitrary original schemes. -/
theorem imageFiltration_zero :
    letI := FlatGlobalSections.sectionsAlgebra f
    (imageFiltration I f).N 0 = ⊤ := by
  let := FlatGlobalSections.sectionsAlgebra f
  change (sectionKernel I f 0).restrictScalars R = ⊤
  rw [sectionKernel_zero]
  rfl

/-- The actual original whole projection descends to its true entire kernel quotient. -/
def quotientInclusion (n : ℕ) :
    Γ(X, ⊤) ⧸ sectionKernel I f n →+* Γ(model I f n, ⊤) :=
  Ideal.Quotient.lift _ (projection I f n).appTop.hom (fun _ hs => hs)

/-- Every actual quotient representative is its literal original projection section. -/
theorem quotientInclusion_mk (n : ℕ) (s : Γ(X, ⊤)) :
    quotientInclusion I f n (Ideal.Quotient.mk (sectionKernel I f n) s) =
      (projection I f n).appTop s := rfl

/-- The whole original infinitesimal projection retains the ENTIRE genuine
original R-coefficient map on global sections. -/
theorem projection_coefficient (n : ℕ) :
    (projection I f n).appTop.hom.comp (ProperBirationalSections.coefficientMap f) =
      ProperBirationalSections.coefficientMap (projection I f n ≫ f) := by
  ext r
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫
    (projection I f n).appTop) r = _
  rw [← Scheme.Hom.comp_appTop]
  rfl

/-- The actual entire global-section quotient inclusion is linear for
the SAME original coefficient action, expressed as an actual R-algebra map. -/
def quotientInclusionAlgHom (n : ℕ) :
    letI := FlatGlobalSections.sectionsAlgebra f
    letI := FlatGlobalSections.sectionsAlgebra (projection I f n ≫ f)
    Γ(X, ⊤) ⧸ sectionKernel I f n →ₐ[R] Γ(model I f n, ⊤) := by
  letI := FlatGlobalSections.sectionsAlgebra f
  letI := FlatGlobalSections.sectionsAlgebra (projection I f n ≫ f)
  exact
    { quotientInclusion I f n with
      commutes' r := RingHom.congr_fun (projection_coefficient I f n) r }

/-- The actual global-section quotient inclusion is injective, without
claiming a nonaffine projection section map is surjective. -/
theorem quotientInclusion_injective (n : ℕ) :
    Function.Injective (quotientInclusion I f n) := by
  intro a b hab
  induction a using Quotient.inductionOn' with
  | _ a =>
    induction b using Quotient.inductionOn' with
    | _ b =>
      apply Ideal.Quotient.eq.mpr
      change (projection I f n).appTop (a-b) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hab

/-- The actual quotient factor of the decreasing ORIGINAL global-section kernel ideals. -/
def quotientTransition {n m : ℕ} (h : n ≤ m) :
    Γ(X, ⊤) ⧸ sectionKernel I f m →+* Γ(X, ⊤) ⧸ sectionKernel I f n :=
  Ideal.Quotient.factor (sectionKernel_antitone I f h)

/-- Every genuine original whole section transition is the canonical quotient
factor under the SAME original global-section quotient inclusions. -/
theorem quotientInclusion_transition {n m : ℕ} (h : n ≤ m)
    (s : Γ(X, ⊤) ⧸ sectionKernel I f m) :
    (transition I f h).appTop (quotientInclusion I f m s) =
      quotientInclusion I f n (quotientTransition I f h s) := by
  induction s using Quotient.inductionOn' with
  | _ s => exact RingHom.congr_fun (transition_projection_sections I f h) s

end EnvelopeProperty.FibreInfinitesimalH0
