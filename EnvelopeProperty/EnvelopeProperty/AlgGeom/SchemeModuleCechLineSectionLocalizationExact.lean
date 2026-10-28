import EnvelopeProperty.AlgGeom.SchemeModuleCechLineSectionLocalizationCochainZero
import EnvelopeProperty.AlgGeom.SchemeModuleCechNativeCohomology

/-! # Actual eventual original twist vanishing makes normalized Cech exact

Lift an actual target cocycle in a sufficiently large original twist, clear
its actual differential by an actual original section transition, and use
that SAME source twist's actual global higher cohomology vanishing to
produce an actual boundary. No localization or exactness certificate is an
incoming substitute for the original geometry.
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

private theorem native_normalized_transition {X : Scheme.{u}}
    (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L) (F : X.Modules)
    {I : Type u} (U : I → X.Opens) (m a : ℕ) :
    twistCechMap F L s U m a ≫ normalizedCechMap L hL s F U (m + a) =
      normalizedCechMap L hL s F U m := by
  change (baseCechComplexFunctor (𝟙 X) U).map (twistIterate F L s m a) ≫
      (baseCechComplexFunctor (𝟙 X) U).map (normalizedPushforwardMap L hL s F (m + a)) =
    (baseCechComplexFunctor (𝟙 X) U).map (normalizedPushforwardMap L hL s F m)
  rw [← Functor.map_comp, normalizedPushforwardMap_transition]

/-- Eventual global vanishing of the SAME original twists in any chosen
positive degree proves actual normalized native Cech exactness. The finite
affine cover and geometric original line frames are produced internally;
all tuple lifting, differential clearing and source boundaries are actual. -/
theorem exists_finite_normalized_cech_exactAt {X : Scheme.{u}} [CompactSpace X]
    [X.IsSeparated] (L : X.Modules) (hL : IsInvertible L) (s : unitObj X ⟶ L)
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ)
    (hH : ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H (F ⊗ bundleTensorPower L m).sheaf (q + 1))) :
    ∃ (I : Type u) (_ : Finite I) (U : I → X.Opens), IsOpenCover U ∧
      (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty ((pullback (U i).ι).obj L ≅ unitObj (U i).toScheme)) ∧
      ((baseCechComplexFunctor (𝟙 X) U).obj
        ((pushforward (sectionOpen L hL s).ι).obj
          ((pullback (sectionOpen L hL s).ι).obj F))).ExactAt (q + 1) := by
  classical
  obtain ⟨N₀, hH₀⟩ := hH
  obtain ⟨I, hI, U, hU, hUa, he, hLift⟩ := exists_finite_normalized_cochain_lift L hL s F
  let : Finite I := hI
  refine ⟨I, hI, U, hU, hUa, he, ?_⟩
  let G := (pushforward (sectionOpen L hL s).ι).obj
    ((pullback (sectionOpen L hL s).ι).obj F)
  let D := (baseCechComplexFunctor (𝟙 X) U).obj G
  apply (HomologicalComplex.exactAt_iff' D q (q + 1) (q + 2)
    (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q + 1))).mpr
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (D.d q (q + 1)).hom (D.d (q + 1) (q + 2)).hom
  intro x
  constructor
  · intro hx
    obtain ⟨N, hN⟩ := hLift (q + 1) x
    let m := max N₀ N
    obtain ⟨y, hy⟩ := hN m (Nat.le_max_right _ _)
    let C := (baseCechComplexFunctor (𝟙 X) U).obj (F ⊗ bundleTensorPower L m)
    let dy := (C.d (q + 1) (q + 2)).hom y
    have hα := congrArg (fun φ => φ.hom y) ((normalizedCechMap L hL s F U m).comm (q + 1) (q + 2))
    change (D.d (q + 1) (q + 2)).hom (((normalizedCechMap L hL s F U m).f (q + 1)).hom y) =
      ((normalizedCechMap L hL s F U m).f (q + 2)).hom dy at hα
    rw [hy, hx] at hα
    obtain ⟨A, hA⟩ := finite_normalized_cochain_zero L hL s F U hUa he (q + 2) m dy hα.symm
    let M' := F ⊗ bundleTensorPower L (m + A)
    let C' := (baseCechComplexFunctor (𝟙 X) U).obj M'
    let y' := ((twistCechMap F L s U m A).f (q + 1)).hom y
    have hT := congrArg (fun φ => φ.hom y) ((twistCechMap F L s U m A).comm (q + 1) (q + 2))
    change (C'.d (q + 1) (q + 2)).hom y' =
      ((twistCechMap F L s U m A).f (q + 2)).hom dy at hT
    have hy' : (C'.d (q + 1) (q + 2)).hom y' = 0 := hT.trans (hA A le_rfl)
    let : M'.IsQuasicoherent := SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight F _
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (m + A))
    have hm : N₀ ≤ m + A := (Nat.le_max_left N₀ N).trans (Nat.le_add_right m A)
    have hn : ((cechComplexFunctor U).obj M'.sheaf.obj).ExactAt (q + 1) :=
      cechComplex_exactAt_succ_of_affine_openCover M' U hU hUa q (hH₀ (m + A) hm)
    have hs : C'.ExactAt (q + 1) :=
      (baseCechComplex_exactAt_iff (𝟙 X) M' U (q + 1)).mpr hn
    have hsc := (HomologicalComplex.exactAt_iff' C' q (q + 1) (q + 2)
      (CochainComplex.prev_nat_succ q) (CochainComplex.next ℕ (q + 1))).mp hs
    have hf : Function.Exact (C'.d q (q + 1)).hom (C'.d (q + 1) (q + 2)).hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hsc
    obtain ⟨z, hz⟩ := (hf y').mp hy'
    let z' := ((normalizedCechMap L hL s F U (m + A)).f q).hom z
    refine ⟨z', ?_⟩
    have hb := congrArg (fun φ => φ.hom z)
      ((normalizedCechMap L hL s F U (m + A)).comm q (q + 1))
    change (D.d q (q + 1)).hom z' =
      ((normalizedCechMap L hL s F U (m + A)).f (q + 1)).hom ((C'.d q (q + 1)).hom z) at hb
    rw [hz] at hb
    have ht := congrArg (fun φ => (φ.f (q + 1)).hom y)
      (native_normalized_transition L hL s F U m A)
    change ((normalizedCechMap L hL s F U (m + A)).f (q + 1)).hom y' =
      ((normalizedCechMap L hL s F U m).f (q + 1)).hom y at ht
    exact hb.trans (ht.trans hy)
  · rintro ⟨z, rfl⟩
    exact congrArg (fun φ => φ.hom z) (D.d_comp_d q (q + 1) (q + 2))

end EnvelopeProperty.SchemeModuleCechLineSectionLocalization
