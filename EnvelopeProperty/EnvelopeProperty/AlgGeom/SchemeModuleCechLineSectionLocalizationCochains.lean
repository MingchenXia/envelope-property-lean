import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationSections
import ModularCurves.ForMathlib.SchemeModuleBaseCechFlat

/-! # Native finite Cech cochain denominators for the original line section

Original invertibility and compactness choose the actual finite affine
line-frame cover internally. On every native finite tuple intersection,
actual normalized restriction lifts in every sufficiently large SAME
original twist. A finite maximum gives one exponent for the whole native
Cech cochain, not an abstract graded-localization or matching certificate.
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

/-- The native Cech map induced by the SAME actual whole normalized
restriction. Its source and target are the original native complexes. -/
def normalizedCechMap {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (F : X.Modules) {I : Type u} (U : I → X.Opens) (m : ℕ) :
    (baseCechComplexFunctor (𝟙 X) U).obj (F ⊗ bundleTensorPower L m) ⟶
      (baseCechComplexFunctor (𝟙 X) U).obj ((pushforward (sectionOpen L hL s).ι).obj
        ((pullback (sectionOpen L hL s).ι).obj F)) :=
  (baseCechComplexFunctor (𝟙 X) U).map (normalizedPushforwardMap L hL s F m)

private theorem native_cochain_map_value {X : Scheme.{u}} {M N : X.Modules}
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

/-- The genuine internally chosen finite affine cover lifts EVERY original
native Cech cochain of actual normalized restriction in EVERY sufficiently
large SAME original tensor twist. No chosen cover, local frame, cochain
matching, localization or bound certificate is an input. -/
theorem exists_finite_normalized_cochain_lift {X : Scheme.{u}} [CompactSpace X]
    [X.IsSeparated] (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.Opens), IsOpenCover U ∧
      (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty ((pullback (U i).ι).obj L ≅ unitObj (U i).toScheme)) ∧
      ∀ (n : ℕ) (x : ((baseCechComplexFunctor (𝟙 X) U).obj
        ((pushforward (sectionOpen L hL s).ι).obj
          ((pullback (sectionOpen L hL s).ι).obj F))).X n),
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
          ∃ y : ((baseCechComplexFunctor (𝟙 X) U).obj (F ⊗ bundleTensorPower L m)).X n,
            ((normalizedCechMap L hL s F U m).f n).hom y = x := by
  classical
  obtain ⟨I, hI, U₀, hU, he⟩ := exists_finite_affine_frame_cover L hL
  let : Finite I := hI
  let U : I → X.Opens := fun i => (U₀ i).1
  refine ⟨I, hI, U, hU, fun i => (U₀ i).2, he, fun n x => ?_⟩
  let G := (pushforward (sectionOpen L hL s).ι).obj
    ((pullback (sectionOpen L hL s).ι).obj F)
  let C (i : Fin (n + 1) → I) : X.Opens := ∏ᶜ fun k : Fin (n + 1) => U (i k)
  have hC (i : Fin (n + 1) → I) : IsAffineOpen (C i) :=
    IsAffineOpen.cechIntersection U (fun i => (U₀ i).2) n i
  have eC (i : Fin (n + 1) → I) :
      Nonempty ((pullback (C i).ι).obj L ≅ unitObj (C i).toScheme) := by
    let hi : C i ≤ U (i 0) := leOfHom (Limits.Pi.π (fun k : Fin (n + 1) => U (i k)) 0)
    exact ⟨frameViaFactor (X.homOfLE hi) (U (i 0)).ι (C i).ι
      (X.homOfLE_ι hi) (he (i 0)).some⟩
  have hl (i : Fin (n + 1) → I) :=
    affineOpen_eventual_normalized_lift L hL s F ⟨C i, hC i⟩ (eC i).some
      ((baseCechXIsoPi (𝟙 X) G U n).hom x i)
  choose N hN using hl
  let := Fintype.ofFinite (Fin (n + 1) → I)
  refine ⟨Finset.univ.sup N, fun m hm => ?_⟩
  have hNm (i : Fin (n + 1) → I) : N i ≤ m :=
    (Finset.le_sup (Finset.mem_univ i)).trans hm
  choose y hy using fun i => hN i m (hNm i)
  let M := F ⊗ bundleTensorPower L m
  let y' := (baseCechXIsoPi (𝟙 X) M U n).inv y
  refine ⟨y', ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (baseCechXIsoPi (𝟙 X) G U n).hom).1
  funext i
  refine (native_cochain_map_value (normalizedPushforwardMap L hL s F m) U n y' i).trans ?_
  have hv : (baseCechXIsoPi (𝟙 X) M U n).hom y' = y :=
    ConcreteCategory.congr_hom (Iso.inv_hom_id (baseCechXIsoPi (𝟙 X) M U n)) y
  exact (congrArg ((normalizedPushforwardMap L hL s F m).app (C i))
    (congrFun hv i)).trans (hy i)

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
