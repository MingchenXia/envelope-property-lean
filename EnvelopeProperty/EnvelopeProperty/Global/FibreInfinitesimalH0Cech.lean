import EnvelopeProperty.Global.FibreInfinitesimalCech
import EnvelopeProperty.Global.FibreInfinitesimalH0
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechZero

/-! # Canonical original global H0 and the original infinitesimal Cech maps -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FibreInfinitesimalH0Cech

private theorem comp_projection {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (z : B ⟶ E) (w : A ⟶ E) (hb : b ≫ c = z) (ha : a ≫ z = w) :
    (a ≫ b) ≫ c = w := by
  rw [Category.assoc, hb, ha]

private theorem augmentation_projection_square {C : Type*} [Category C]
    {S T A B E F : C} (m : S ⟶ T) (a : S ⟶ A) (b : T ⟶ B) (c : A ⟶ B)
    (p : A ⟶ E) (q : B ⟶ F) (k : E ⟶ F) (r : S ⟶ E) (s : T ⟶ F)
    (ha : a ≫ p = r) (hb : b ≫ q = s) (hc : c ≫ q = p ≫ k)
    (hm : m ≫ s = r ≫ k) : (m ≫ b) ≫ q = (a ≫ c) ≫ q := by
  rw [Category.assoc, hb, Category.assoc, hc, ← Category.assoc, ha, hm]

private theorem homology_lift_square {C : Type*} [Category C]
    {S T H J A B : C} (e : S ⟶ H) (g : T ⟶ J) (m : S ⟶ T) (h : H ⟶ J)
    (i : H ⟶ A) (j : J ⟶ B) (t : A ⟶ B) (a : S ⟶ A) (b : T ⟶ B)
    (he : e ≫ i = a) (hg : g ≫ j = b) (hh : h ≫ j = i ≫ t)
    (hm : m ≫ b = a ≫ t) : (e ≫ h) ≫ j = (m ≫ g) ≫ j := by
  rw [Category.assoc, hh, ← Category.assoc, he, Category.assoc, hg, hm]

private theorem exact_iso_transport {A : Type u} [CommRing A]
    {M N H J P : ModuleCat.{u} A} (eM : M ≅ H) (eN : N ≅ J)
    (b : M ⟶ N) (g : H ⟶ J) (δ : J ⟶ P)
    (h : eM.hom ≫ g = b ≫ eN.hom) (hex : Function.Exact g δ) :
    Function.Exact b (eN.hom ≫ δ) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hex (eN.hom x)).mp hx
    refine ⟨eM.inv y, ?_⟩
    apply (ModuleCat.mono_iff_injective eN.hom).mp inferInstance
    have he := ConcreteCategory.congr_hom h (eM.inv y)
    change g (eM.hom (eM.inv y)) = eN.hom (b (eM.inv y)) at he
    rw [Iso.inv_hom_id_apply] at he
    exact he.symm.trans hy
  · rintro ⟨y, rfl⟩
    have he := ConcreteCategory.congr_hom h y
    change g (eM.hom y) = eN.hom (b y) at he
    change δ (eN.hom (b y)) = 0
    rw [← he]
    exact (hex (g (eM.hom y))).mpr ⟨eM.hom y, rfl⟩

private def kernelHomologyZeroIso {A : Type u} [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) :
    ModuleCat.of A (LinearMap.ker (C.d 0 1).hom) ≅ C.homology 0 :=
  (C.sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
    (C.cyclesIsoSc' 0 0 1 CochainComplex.prev_nat_zero (by simp)).symm ≪≫ C.isoHomologyπ₀

private def h0Inclusion {A : Type u} [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) : C.homology 0 ⟶ C.X 0 :=
  C.isoHomologyπ₀.inv ≫ C.iCycles 0

private instance h0Inclusion_mono {A : Type u} [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) : Mono (h0Inclusion C) := by
  dsimp [h0Inclusion]
  infer_instance

private theorem kernelHomologyZeroIso_inclusion {A : Type u} [CommRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℕ) :
    (kernelHomologyZeroIso C).hom ≫ h0Inclusion C =
      ModuleCat.ofHom (LinearMap.ker (C.d 0 1).hom).subtype := by
  change ((C.sc' 0 0 1).moduleCatCyclesIso.inv ≫
      (C.cyclesIsoSc' 0 0 1 CochainComplex.prev_nat_zero (by simp)).inv ≫
        C.isoHomologyπ₀.hom) ≫ (C.isoHomologyπ₀.inv ≫ C.iCycles 0) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc,
    HomologicalComplex.cyclesIsoSc'_inv_iCycles]
  exact (C.sc' 0 0 1).moduleCatCyclesIso_inv_iCycles

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : IsOpenCover U)

/-- The WHOLE original global sections of any original module sheaf identify
canonically with actual degree-zero ordered Cech cohomology of its original cover. -/
def globalSectionsIso (M : X.Modules) :
    baseSections f M ≅ (orderedBaseCechComplex f M U).homology 0 :=
  baseSectionsIsoKernelOrderedBaseCechDifferential f M U hU ≪≫
    kernelHomologyZeroIso (orderedBaseCechComplex f M U)

private def orderedAugmentation (M : X.Modules) :
    baseSections f M ⟶ (orderedBaseCechComplex f M U).X 0 :=
  baseCechAugmentation f M U ≫ baseCechToOrderedF f M U 0

private theorem globalSectionsIso_augmentation (M : X.Modules) :
    (globalSectionsIso f U hU M).hom ≫ h0Inclusion (orderedBaseCechComplex f M U) =
      orderedAugmentation f U M := by
  rw [globalSectionsIso, Iso.trans_hom, Category.assoc, kernelHomologyZeroIso_inclusion]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact baseSectionsIsoKernelOrderedBaseCechDifferential_hom_coe f M U hU s

private theorem orderedAugmentation_projection (M : X.Modules) (i : OrderedCechIndex ι 0) :
    orderedAugmentation f U M ≫
        Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor f M U 0 j.1) i =
      (baseModulePresheaf f M).map
        (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i.1 k)) ≤ ⊤ from le_top)).op := by
  exact comp_projection _ _ _ _ _
    (baseCechToOrderedF_comp_π f M U 0 i) (baseCechAugmentation_comp_π f M U i.1)

private theorem cechMap_projection {M N : X.Modules} (t : M ⟶ N)
    (i : OrderedCechIndex ι 0) :
    ((orderedBaseCechComplexFunctor f U).map t).f 0 ≫
        Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor f N U 0 j.1) i =
      Pi.π (fun j : OrderedCechIndex ι 0 => baseCechFactor f M U 0 j.1) i ≫
        ((baseModulePresheafFunctor f).map t).app
          (op (∏ᶜ fun k : Fin 1 => U (i.1 k))) :=
  Pi.map_π (fun j : OrderedCechIndex ι 0 =>
    ((baseModulePresheafFunctor f).map t).app
      (op (∏ᶜ fun k : Fin 1 => U (j.1 k)))) i

private theorem orderedAugmentation_naturality {M N : X.Modules} (t : M ⟶ N) :
    baseSectionsMap f t ≫ orderedAugmentation f U N =
      orderedAugmentation f U M ≫ ((orderedBaseCechComplexFunctor f U).map t).f 0 := by
  apply Pi.hom_ext
  intro i
  change OrderedCechIndex ι 0 at i
  exact augmentation_projection_square _ _ _ _ _ _ _ _ _
    (orderedAugmentation_projection f U M i) (orderedAugmentation_projection f U N i)
    (cechMap_projection f U t i)
    (((baseModulePresheafFunctor f).map t).naturality
      (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i.1 k)) ≤ ⊤ from le_top)).op).symm

private theorem h0Inclusion_naturality {A : Type u} [CommRing A]
    {C D : CochainComplex (ModuleCat.{u} A) ℕ} (t : C ⟶ D) :
    HomologicalComplex.homologyMap t 0 ≫ h0Inclusion D =
      h0Inclusion C ≫ t.f 0 := by
  rw [h0Inclusion, ← Category.assoc, CochainComplex.isoHomologyπ₀_inv_naturality,
    Category.assoc, HomologicalComplex.cyclesMap_i]
  rfl

/-- The SAME original global-section/cohomology equivalence intertwines
EVERY actual original module-sheaf morphism with its genuine cohomology map. -/
theorem globalSectionsIso_naturality {M N : X.Modules} (t : M ⟶ N) :
    (globalSectionsIso f U hU M).hom ≫
        HomologicalComplex.homologyMap ((orderedBaseCechComplexFunctor f U).map t) 0 =
      baseSectionsMap f t ≫ (globalSectionsIso f U hU N).hom := by
  apply (cancel_mono (h0Inclusion (orderedBaseCechComplex f N U))).mp
  exact homology_lift_square _ _ _ _ _ _ _ _ _
    (globalSectionsIso_augmentation f U hU M) (globalSectionsIso_augmentation f U hU N)
    (h0Inclusion_naturality ((orderedBaseCechComplexFunctor f U).map t))
    (orderedAugmentation_naturality f U t)

variable (I : Ideal R) [X.IsSeparated] (hUa : ∀ i, IsAffineOpen (U i))

/-- The genuine cohomology obstruction of EVERY actual original whole
infinitesimal global section, using the SAME original cover and coefficients. -/
def sectionBoundary (d : ℕ) :
    baseSections f ((Scheme.Modules.pushforward (InfinitesimalSchemes.projection I f d)).obj
        (SheafOfModules.unit (InfinitesimalSchemes.model I f d).ringCatSheaf)) ⟶
      (orderedBaseCechComplex f (FibreIdealPowers.powerModule I f d) U).homology 1 :=
  (globalSectionsIso f U hU _).hom ≫
    FibreInfinitesimalCech.connecting I f U hUa d 0

/-- The actual original whole global-section projection and the genuine
cohomology obstruction form an exact pair, with no assumed section lift. -/
theorem sectionBoundary_exact (d : ℕ) :
    Function.Exact (baseSectionsMap f (FibreInfinitesimalModules.sectionMap I f d))
      (sectionBoundary f U hU I hUa d) :=
  exact_iso_transport (globalSectionsIso f U hU _) (globalSectionsIso f U hU _)
    (baseSectionsMap f (FibreInfinitesimalModules.sectionMap I f d))
    (HomologicalComplex.homologyMap (FibreInfinitesimalCech.complexSequence I f U d).g 0)
    (FibreInfinitesimalCech.connecting I f U hUa d 0)
    (globalSectionsIso_naturality f U hU (FibreInfinitesimalModules.sectionMap I f d))
    (FibreInfinitesimalCech.homology_exact_right I f U hUa d 0)

/-- A whole ORIGINAL infinitesimal section has zero actual obstruction
exactly when it lifts to a whole ORIGINAL global section under the LITERAL projection. -/
theorem sectionBoundary_eq_zero_iff (d : ℕ)
    (s : Γ(InfinitesimalSchemes.model I f d, ⊤)) :
    sectionBoundary f U hU I hUa d s = 0 ↔
      ∃ t : Γ(X, ⊤), (InfinitesimalSchemes.projection I f d).appTop t = s :=
  sectionBoundary_exact f U hU I hUa d s

end EnvelopeProperty.FibreInfinitesimalH0Cech
