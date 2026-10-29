import ModularCurves.ForMathlib.ProjectiveFactorizationFiniteSections
import ModularCurves.ForMathlib.ProjectiveFactorizationCechHOne
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Actual coherent field cohomology and intrinsic Euler index

The normalized index is the cohomological definition of degree on proper
curves. No tensor additivity, local-order formula or nefness is asserted here.
-/
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules TopCat TopCat.Sheaf
noncomputable section
universe u
namespace EnvelopeProperty.SchemeCoherentEulerIndex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- The canonical actual scalar identification of the original field. -/
abbrev baseScalar : k →+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The original global sections retaining the original base-field action. -/
def fieldSections (f : C ⟶ Spec (.of k)) (M : C.Modules) : ModuleCat k :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).obj (baseSections f M)

/-- The whole actual base-linear Cech homology retaining original field scalars. -/
def fieldCech (f : C ⟶ Spec (.of k)) (M : C.Modules)
    {ι : Type u} (U : ι → C.Opens) (n : ℕ) : ModuleCat k :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).obj ((baseCechComplex f M U).homology n)

private theorem restrict_field_finite (N : ModuleCat Γ(Spec (.of k), ⊤))
    [Module.Finite Γ(Spec (.of k), ⊤) N] :
    Module.Finite k ((ModuleCat.restrictScalars (baseScalar (k := k))).obj N) := by
  let G := Γ(Spec (.of k), ⊤)
  let M := (ModuleCat.restrictScalars (baseScalar (k := k))).obj N
  let : Module G M := N.isModule
  let : Module.Finite G M := inferInstanceAs (Module.Finite G N)
  let : Algebra k G := (baseScalar (k := k)).toAlgebra
  let : IsScalarTower k G M := ⟨fun a b x => by
    change (baseScalar a * b) • x = baseScalar a • (b • x)
    exact mul_smul _ _ _⟩
  let : Module.Finite k G := Module.Finite.of_surjective (Algebra.linearMap k G)
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact Module.Finite.trans (R := k) G M

/-- Genuine projective coherent finiteness for the original field-linear sections. -/
theorem fieldSections_finite (f : C ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (M : C.Modules) [M.IsQuasicoherent] [M.IsFiniteType] : Module.Finite k (fieldSections f M) := by
  let : Module.Finite Γ(Spec (.of k), ⊤) (baseSections f M) := hf.baseSections_module_finite M
  exact restrict_field_finite (baseSections f M)

/-- Genuine projective coherent finiteness of every positive actual field Cech group. -/
theorem fieldCech_succ_finite (f : C ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (M : C.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    {ι : Type u} [Finite ι] (U : ι → C.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) (n : ℕ) : Module.Finite k (fieldCech f M U (n+1)) := by
  let : Module.Finite Γ(Spec (.of k), ⊤) ((baseCechComplex f M U).homology (n+1)) :=
    hf.baseModuleCech_homology_succ_module_finite_of_affine_openCover M U hU hUa n
  exact restrict_field_finite ((baseCechComplex f M U).homology (n+1))

/-- The original module isomorphism induces the original field-linear section isomorphism. -/
def fieldSectionsIso (f : C ⟶ Spec (.of k)) {M N : C.Modules} (e : M ≅ N) :
    fieldSections f M ≅ fieldSections f N :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).mapIso (baseSectionsMapIso f e)

/-- Original module isomorphisms act on the whole original field Cech cohomology. -/
def fieldCechIso (f : C ⟶ Spec (.of k)) {M N : C.Modules} (e : M ≅ N)
    {ι : Type u} (U : ι → C.Opens) (n : ℕ) : fieldCech f M U n ≅ fieldCech f N U n :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).mapIso
    (HomologicalComplex.homologyMapIso ((baseCechComplexFunctor f U).mapIso e) n)

/-- Whole field-linear Cech cohomology is independent of the actual finite affine cover. -/
def fieldCechCoverIso [C.IsSeparated] (f : C ⟶ Spec (.of k))
    (M : C.Modules) [M.IsQuasicoherent]
    {ι κ : Type u} [Finite ι] [Finite κ]
    (U : ι → C.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (V : κ → C.Opens) (hV : IsOpenCover V) (hVa : ∀ i, IsAffineOpen (V i)) (n : ℕ) :
    fieldCech f M U (n+1) ≅ fieldCech f M V (n+1) := by
  apply (ModuleCat.restrictScalars (baseScalar (k := k))).mapIso
  exact (moduleCechTwoCoverHomologySuccIso (baseModuleTopSheaf f M) U V hU hV n
    (fun q p _ hp => by
      cases p with
      | zero => omega
      | succ p =>
          simpa only [Nat.succ_eq_add_one] using
            baseModuleCechTerm_cech_exactAt_succ_of_affine_openCover
              f M U hUa V hV hVa q p)
    (fun q p _ hp => by
      cases p with
      | zero => omega
      | succ p =>
          simpa only [Nat.succ_eq_add_one] using
            baseModuleCechTerm_cech_exactAt_succ_of_affine_openCover
              f M U hUa V hV hVa q p)
    (fun p q _ _ i => moduleCechShortComplexApp_exact_of_affine_openCover_succ
      f M U hU hUa (∏ᶜ fun j : Fin (p+1) => V (i j))
      (IsAffineOpen.cechIntersection V hVa p i) (q-1))
    (fun p q _ _ i => moduleCechShortComplexApp_exact_of_affine_openCover_succ
      f M U hU hUa (∏ᶜ fun j : Fin (p+1) => V (i j))
      (IsAffineOpen.cechIntersection V hVa p i) (q-1))).symm

/-- A true finite affine cover chosen from the original scheme's actual affine cover. -/
def finiteAffineCover (C : Scheme.{u}) [CompactSpace C] : C.OpenCover := C.affineCover.finiteSubcover

/-- The actual opens of that same finite affine cover. -/
def finiteAffineOpens (C : Scheme.{u}) [CompactSpace C] : (finiteAffineCover C).I₀ → C.Opens :=
  fun i => ((finiteAffineCover C).f i).opensRange

instance finiteAffineCover_finite (C : Scheme.{u}) [CompactSpace C] : Finite (finiteAffineCover C).I₀ :=
  inferInstanceAs (Finite C.affineCover.finiteSubcover.I₀)

theorem finiteAffineOpens_cover (C : Scheme.{u}) [CompactSpace C] : IsOpenCover (finiteAffineOpens C) :=
  (finiteAffineCover C).isOpenCover_opensRange

theorem finiteAffineOpens_isAffine (C : Scheme.{u}) [CompactSpace C]
    (i : (finiteAffineCover C).I₀) : IsAffineOpen (finiteAffineOpens C i) := by
  let : IsAffine ((finiteAffineCover C).X i) := by
    dsimp only [finiteAffineCover, Scheme.OpenCover.finiteSubcover]
    infer_instance
  exact isAffineOpen_opensRange ((finiteAffineCover C).f i)

/-- The actual whole original first cohomology, with the unchanged original field action. -/
def fieldHOne [CompactSpace C] (f : C ⟶ Spec (.of k)) (M : C.Modules) : ModuleCat k :=
  fieldCech f M (finiteAffineOpens C) 1

/-- The actual coherent Euler index from original global sections and original H¹. -/
def eulerIndex [CompactSpace C] (f : C ⟶ Spec (.of k)) (M : C.Modules) : ℤ :=
  (Module.finrank k (fieldSections f M) : ℤ) - Module.finrank k (fieldHOne f M)

/-- The normalized cohomological degree expression, applied to the SAME original line. -/
def normalizedEulerIndex [CompactSpace C] (f : C ⟶ Spec (.of k)) (M : C.Modules) : ℤ :=
  eulerIndex f M - eulerIndex f (unitObj C)

/-- Genuine whole original H¹ is finite dimensional, derived from actual projective geometry. -/
theorem fieldHOne_finite [CompactSpace C] (f : C ⟶ Spec (.of k))
    (hf : IsProjectiveFactorization f) (M : C.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : Module.Finite k (fieldHOne f M) :=
  fieldCech_succ_finite f hf M (finiteAffineOpens C)
    (finiteAffineOpens_cover C) (finiteAffineOpens_isAffine C) 0

/-- The actual first cohomology is the whole original sheaf H¹, not a new certificate. -/
def fieldHOneSheafIso [CompactSpace C] (f : C ⟶ Spec (.of k))
    (M : C.Modules) [M.IsQuasicoherent] :
    AddCommGrpCat.of (fieldHOne f M) ≅
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology C) 1).obj M.sheaf :=
  baseCechHomologyOneIso_of_affine_openCover f M (finiteAffineOpens C)
    (finiteAffineOpens_cover C) (finiteAffineOpens_isAffine C)

/-- The actual H¹ dimension agrees with every original finite affine cover. -/
theorem fieldHOne_finrank_eq [CompactSpace C] [C.IsSeparated]
    (f : C ⟶ Spec (.of k)) (M : C.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → C.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) :
    Module.finrank k (fieldHOne f M) = Module.finrank k (fieldCech f M U 1) :=
  (fieldCechCoverIso f M (finiteAffineOpens C)
    (finiteAffineOpens_cover C) (finiteAffineOpens_isAffine C) U hU hUa 0).toLinearEquiv.finrank_eq

/-- Every original line/module isomorphism preserves the actual coherent Euler index. -/
theorem eulerIndex_eq_of_iso [CompactSpace C] (f : C ⟶ Spec (.of k))
    {M N : C.Modules} (e : M ≅ N) : eulerIndex f M = eulerIndex f N := by
  unfold eulerIndex fieldHOne
  rw [(fieldSectionsIso f e).toLinearEquiv.finrank_eq,
    (fieldCechIso f e (finiteAffineOpens C) 1).toLinearEquiv.finrank_eq]

/-- The normalized original index is preserved by actual whole module isomorphisms. -/
theorem normalizedEulerIndex_eq_of_iso [CompactSpace C] (f : C ⟶ Spec (.of k))
    {M N : C.Modules} (e : M ≅ N) :
    normalizedEulerIndex f M = normalizedEulerIndex f N := by
  unfold normalizedEulerIndex
  rw [eulerIndex_eq_of_iso f e]

/-- The actual structure line has zero normalized Euler index. -/
@[simp] theorem normalizedEulerIndex_unit [CompactSpace C] (f : C ⟶ Spec (.of k)) :
    normalizedEulerIndex f (unitObj C) = 0 := sub_self _

/-- The index can be computed on any actual finite affine cover of the original scheme. -/
theorem eulerIndex_eq_on_cover [CompactSpace C] [C.IsSeparated]
    (f : C ⟶ Spec (.of k)) (M : C.Modules) [M.IsQuasicoherent]
    {ι : Type u} [Finite ι] (U : ι → C.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) :
    eulerIndex f M = (Module.finrank k (fieldSections f M) : ℤ) -
      Module.finrank k (fieldCech f M U 1) := by
  unfold eulerIndex
  rw [fieldHOne_finrank_eq f M U hU hUa]

end EnvelopeProperty.SchemeCoherentEulerIndex
