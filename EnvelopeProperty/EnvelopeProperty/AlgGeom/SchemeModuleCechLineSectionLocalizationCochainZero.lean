import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationCochains
import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationSectionZero

/-! # Eventual zero-clearing on the SAME native finite Cech tuples

Actual normalized-zero original cochains are killed by actual original
finite section transitions. The finite affine family and ordinary original
line frames are geometric inputs, supplied internally by the cochain-lift
cover producer in the eventual global-to-open consumer.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModuleCechLineSectionLocalization
open CanonicalGeometry SchemeLineSectionEvaluation
attribute [local instance] Scheme.Modules.monoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The native whole Cech map of the SAME actual original finite transition. -/
def twistCechMap {X : Scheme.{u}} (F L : X.Modules) (s : unitObj X ⟶ L)
    {I : Type u} (U : I → X.Opens) (m a : ℕ) :
    (baseCechComplexFunctor (𝟙 X) U).obj (F ⊗ bundleTensorPower L m) ⟶
      (baseCechComplexFunctor (𝟙 X) U).obj (F ⊗ bundleTensorPower L (m + a)) :=
  (baseCechComplexFunctor (𝟙 X) U).map (twistIterate F L s m a)

private theorem zero_native_cochain_map_value {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) {I : Type u} (U : I → X.Opens) (n : ℕ)
    (x : (baseCechComplex (𝟙 X) M U).X n) (i : Fin (n + 1) → I) :
    (baseCechXIsoPi (𝟙 X) N U n).hom
      (((baseCechComplexFunctor (𝟙 X) U).map f).f n x) i =
      f.app (∏ᶜ fun k : Fin (n + 1) => U (i k))
        ((baseCechXIsoPi (𝟙 X) M U n).hom x i) := by
  rw [show (baseCechXIsoPi (𝟙 X) N U n).hom
      (((baseCechComplexFunctor (𝟙 X) U).map f).f n x) i =
      Limits.Pi.π (fun j : Fin (n + 1) → I => baseCechFactor (𝟙 X) N U n j) i
        (((baseCechComplexFunctor (𝟙 X) U).map f).f n x) from
    ModuleCat.piIsoPi_hom_ker_subtype_apply _ i _]
  rw [show (baseCechXIsoPi (𝟙 X) M U n).hom x i =
      Limits.Pi.π (fun j : Fin (n + 1) → I => baseCechFactor (𝟙 X) M U n j) i x from
    ModuleCat.piIsoPi_hom_ker_subtype_apply _ i _]
  exact ConcreteCategory.congr_hom
    (Limits.Pi.map_π (fun j : Fin (n + 1) → I =>
      ((baseModulePresheafFunctor (𝟙 X)).map f).app
        (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i) x

/-- Every normalized-zero ORIGINAL native Cech cochain is killed by EVERY
sufficiently long SAME original section transition. Actual tuple frames,
original affine section zero-clearing and the common finite bound are all
assembled internally, with no annihilator or differential certificate. -/
theorem finite_normalized_cochain_zero {X : Scheme.{u}} [X.IsSeparated]
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I] (U : I → X.Opens)
    (hUa : ∀ i, IsAffineOpen (U i))
    (he : ∀ i, Nonempty ((pullback (U i).ι).obj L ≅ unitObj (U i).toScheme))
    (n m : ℕ) (y : ((baseCechComplexFunctor (𝟙 X) U).obj (F ⊗ bundleTensorPower L m)).X n)
    (hy : ((normalizedCechMap L hL s F U m).f n).hom y = 0) :
    ∃ A : ℕ, ∀ a : ℕ, A ≤ a →
      ((twistCechMap F L s U m a).f n).hom y = 0 := by
  classical
  let G := (pushforward (sectionOpen L hL s).ι).obj
    ((pullback (sectionOpen L hL s).ι).obj F)
  let M := F ⊗ bundleTensorPower L m
  let C (i : Fin (n + 1) → I) : X.Opens := ∏ᶜ fun k : Fin (n + 1) => U (i k)
  have hC (i : Fin (n + 1) → I) : IsAffineOpen (C i) :=
    IsAffineOpen.cechIntersection U hUa n i
  have eC (i : Fin (n + 1) → I) :
      Nonempty ((pullback (C i).ι).obj L ≅ unitObj (C i).toScheme) := by
    let hi : C i ≤ U (i 0) := leOfHom (Limits.Pi.π (fun k : Fin (n + 1) => U (i k)) 0)
    exact ⟨frameViaFactor (X.homOfLE hi) (U (i 0)).ι (C i).ι
      (X.homOfLE_ι hi) (he (i 0)).some⟩
  have hzero (i : Fin (n + 1) → I) :
      (normalizedPushforwardMap L hL s F m).app (C i)
        ((baseCechXIsoPi (𝟙 X) M U n).hom y i) = 0 := by
    have hh := congrArg (fun z => (baseCechXIsoPi (𝟙 X) G U n).hom z i) hy
    have h0 := congrFun (baseCechXIsoPi (𝟙 X) G U n).hom.hom.map_zero i
    exact (zero_native_cochain_map_value (normalizedPushforwardMap L hL s F m) U n y i).symm.trans
      (hh.trans h0)
  have ha (i : Fin (n + 1) → I) := affineOpen_eventual_zero_clearing L hL s F
    ⟨C i, hC i⟩ (eC i).some m ((baseCechXIsoPi (𝟙 X) M U n).hom y i) (hzero i)
  choose A hA using ha
  let := Fintype.ofFinite (Fin (n + 1) → I)
  refine ⟨Finset.univ.sup A, fun a ha => ?_⟩
  let M' := F ⊗ bundleTensorPower L (m + a)
  apply (ConcreteCategory.bijective_of_isIso (baseCechXIsoPi (𝟙 X) M' U n).hom).1
  rw [map_zero]
  funext i
  exact (zero_native_cochain_map_value (twistIterate F L s m a) U n y i).trans
    (hA i a ((Finset.le_sup (Finset.mem_univ i)).trans ha))

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
