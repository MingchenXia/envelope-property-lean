import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionEulerPolynomialCoefficients
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionPolynomialDifferences

/-! Actual original module-list mixed Euler differences. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules TopologicalSpace
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion
open SchemeCoherentEulerCharacteristic
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]

def mixedEulerDifference (f : X ⟶ Spec (.of k)) : List X.Modules → X.Modules → ℤ
  | [], M => eulerCharacteristic f M
  | L :: ls, M => mixedEulerDifference f ls (M ⊗ L) - mixedEulerDifference f ls M

variable (f : X ⟶ Spec (.of k))

theorem mixedEulerDifference_eq_of_iso (ls : List X.Modules) {M N : X.Modules}
    (e : M ≅ N) : mixedEulerDifference f ls M = mixedEulerDifference f ls N := by
  induction ls generalizing M N with
  | nil => exact eulerCharacteristic_eq_of_iso f e
  | cons L ls ih =>
    change mixedEulerDifference f ls (M ⊗ L) - mixedEulerDifference f ls M =
      mixedEulerDifference f ls (N ⊗ L) - mixedEulerDifference f ls N
    rw [ih (e ⊗ᵢ Iso.refl L), ih e]

theorem mixedEulerDifference_eq_zero_of_isZero (ls : List X.Modules) :
    (∀ L ∈ ls, IsInvertible L) → ∀ (M : X.Modules), IsZero M →
      mixedEulerDifference f ls M = 0 := by
  induction ls with
  | nil => intro _ M hM; exact eulerCharacteristic_eq_zero_of_isZero f M hM
  | cons L ls ih =>
    intro hls M hM
    let hL : IsInvertible L := hls L (by simp)
    have ht : ∀ K ∈ ls, IsInvertible K := fun K hK => hls K (by simp [hK])
    let : (tensorRight L).IsEquivalence :=
      SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
    have hz : IsZero (M ⊗ L) := (tensorRight L).map_isZero hM
    change mixedEulerDifference f ls (M ⊗ L) - mixedEulerDifference f ls M = 0
    rw [ih ht (M ⊗ L) hz, ih ht M hM, sub_self]

theorem mixedEulerDifference_add [X.IsSeparated] [IsProjective f] (ls : List X.Modules) :
    ∀ (_ : ∀ L ∈ ls, IsInvertible L) (S : ShortComplex X.Modules)
      [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
      [S.X₁.IsFiniteType] [S.X₂.IsFiniteType] [S.X₃.IsFiniteType], S.ShortExact →
      mixedEulerDifference f ls S.X₂ =
        mixedEulerDifference f ls S.X₁ + mixedEulerDifference f ls S.X₃ := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  induction ls with
  | nil =>
    intro _ S _ _ _ _ _ _ hS
    exact eulerCharacteristic_add f hf S hS
  | cons L ls ih =>
    intro hls S _ _ _ _ _ _ hS
    let hL : IsInvertible L := hls L (by simp)
    have ht : ∀ K ∈ ls, IsInvertible K := fun K hK => hls K (by simp [hK])
    let : (S.X₁ ⊗ L).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₁ L hL
    let : (S.X₂ ⊗ L).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₂ L hL
    let : (S.X₃ ⊗ L).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight S.X₃ L hL
    let : (S.X₁ ⊗ L).IsFiniteType :=
      SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight S.X₁ L hL
    let : (S.X₂ ⊗ L).IsFiniteType :=
      SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight S.X₂ L hL
    let : (S.X₃ ⊗ L).IsFiniteType :=
      SchemeInvertibleTensorFiniteType.isFiniteType_tensorRight S.X₃ L hL
    let : (tensorRight L).IsEquivalence :=
      SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
    let SP := S.map (tensorRight L)
    have hSP : SP.ShortExact :=
      SchemeInvertibleTensorEquivalence.tensorRight_shortExact L hL S hS
    let : SP.X₁.IsQuasicoherent := by change (S.X₁ ⊗ L).IsQuasicoherent; infer_instance
    let : SP.X₂.IsQuasicoherent := by change (S.X₂ ⊗ L).IsQuasicoherent; infer_instance
    let : SP.X₃.IsQuasicoherent := by change (S.X₃ ⊗ L).IsQuasicoherent; infer_instance
    let : SP.X₁.IsFiniteType := by change (S.X₁ ⊗ L).IsFiniteType; infer_instance
    let : SP.X₂.IsFiniteType := by change (S.X₂ ⊗ L).IsFiniteType; infer_instance
    let : SP.X₃.IsFiniteType := by change (S.X₃ ⊗ L).IsFiniteType; infer_instance
    have h₁ := ih ht S hS
    have h₂ := ih ht SP hSP
    change mixedEulerDifference f ls (S.X₂ ⊗ L) =
      mixedEulerDifference f ls (S.X₁ ⊗ L) + mixedEulerDifference f ls (S.X₃ ⊗ L) at h₂
    change mixedEulerDifference f ls (S.X₂ ⊗ L) - mixedEulerDifference f ls S.X₂ =
      (mixedEulerDifference f ls (S.X₁ ⊗ L) - mixedEulerDifference f ls S.X₁) +
      (mixedEulerDifference f ls (S.X₃ ⊗ L) - mixedEulerDifference f ls S.X₃)
    rw [h₁, h₂]
    ring

theorem mixedEulerDifference_swap (L M : X.Modules) (ls : List X.Modules) (F : X.Modules) :
    mixedEulerDifference f (L :: M :: ls) F = mixedEulerDifference f (M :: L :: ls) F := by
  let e : (F ⊗ L) ⊗ M ≅ (F ⊗ M) ⊗ L :=
    α_ F L M ≪≫ (Iso.refl F ⊗ᵢ β_ L M) ≪≫ (α_ F M L).symm
  have h := mixedEulerDifference_eq_of_iso f ls e
  change (mixedEulerDifference f ls ((F ⊗ L) ⊗ M) - mixedEulerDifference f ls (F ⊗ L)) -
      (mixedEulerDifference f ls (F ⊗ M) - mixedEulerDifference f ls F) =
    (mixedEulerDifference f ls ((F ⊗ M) ⊗ L) - mixedEulerDifference f ls (F ⊗ M)) -
      (mixedEulerDifference f ls (F ⊗ L) - mixedEulerDifference f ls F)
  rw [h]
  ring

theorem mixedEulerDifference_pushforward {Y : Scheme.{u}} [CompactSpace Y]
    [X.IsSeparated] [Y.IsSeparated] (i : Y ⟶ X) [IsAffineHom i] (ls : List X.Modules) :
    (∀ L ∈ ls, IsInvertible L) → ∀ (N : Y.Modules) [N.IsQuasicoherent],
      mixedEulerDifference f ls ((Scheme.Modules.pushforward i).obj N) =
        mixedEulerDifference (i ≫ f) (ls.map (Scheme.Modules.pullback i).obj) N := by
  induction ls with
  | nil =>
    intro _ N _
    exact (SchemeCoherentEulerAffine.eulerCharacteristic_pushforward i f N).symm
  | cons L ls ih =>
    intro hls N _
    let hL : IsInvertible L := hls L (by simp)
    have ht : ∀ K ∈ ls, IsInvertible K := fun K hK => hls K (by simp [hK])
    let K := (Scheme.Modules.pullback i).obj L
    let hK : IsInvertible K := hL.pullback i
    let : (N ⊗ K).IsQuasicoherent :=
      SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight N K hK
    let e : (Scheme.Modules.pushforward i).obj N ⊗ L ≅
        (Scheme.Modules.pushforward i).obj (N ⊗ K) :=
      SchemeLineProjectionFormula.lineProjectionFormulaObj i L hL N
    change mixedEulerDifference f ls ((Scheme.Modules.pushforward i).obj N ⊗ L) -
        mixedEulerDifference f ls ((Scheme.Modules.pushforward i).obj N) =
      mixedEulerDifference (i ≫ f) (ls.map (Scheme.Modules.pullback i).obj) (N ⊗ K) -
        mixedEulerDifference (i ≫ f) (ls.map (Scheme.Modules.pullback i).obj) N
    rw [mixedEulerDifference_eq_of_iso f ls e, ih ht (N ⊗ K), ih ht N]

theorem mixedEulerDifference_cartierDifference [X.IsSeparated] [IsIntegral X] [IsProjective f]
    (L B : X.Modules) (hL : IsInvertible L) (hB : IsInvertible B)
    (a : unitObj X ⟶ L ⊗ B) (ha : a ≠ 0) (b : unitObj X ⟶ B) (hb : b ≠ 0) :
    let hA := (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
    let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
    let J := LineSectionZeroIdeal.zeroIdeal B hB b
    letI : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
    letI : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
    ∀ (ls : List X.Modules), (∀ K ∈ ls, IsInvertible K) → ∀ (T : X.Modules), IsInvertible T →
      mixedEulerDifference f (L :: ls) T =
        mixedEulerDifference (I.subschemeι ≫ f) (ls.map (Scheme.Modules.pullback I.subschemeι).obj)
            ((Scheme.Modules.pullback I.subschemeι).obj (T ⊗ L)) -
          mixedEulerDifference (J.subschemeι ≫ f) (ls.map (Scheme.Modules.pullback J.subschemeι).obj)
            ((Scheme.Modules.pullback J.subschemeι).obj T) := by
  let hf := ProjectiveFactorizationRingIso.of_isProjective f
  let hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
  let J := LineSectionZeroIdeal.zeroIdeal B hB b
  let i := I.subschemeι
  let j := J.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  let : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace j
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let : Fi.Monoidal := Scheme.Modules.pullbackMonoidal i
  let : Fj.Monoidal := Scheme.Modules.pullbackMonoidal j
  change ∀ (ls : List X.Modules), (∀ K ∈ ls, IsInvertible K) → ∀ (T : X.Modules), IsInvertible T →
    mixedEulerDifference f (L :: ls) T =
      mixedEulerDifference (i ≫ f) (ls.map Fi.obj) (Fi.obj (T ⊗ L)) -
        mixedEulerDifference (j ≫ f) (ls.map Fj.obj) (Fj.obj T)
  intro ls
  induction ls with
  | nil =>
    intro _ T hT
    have h := eulerCharacteristic_cartierDifference f hf L B T hL hB hT a ha b hb
    change eulerCharacteristic f (L ⊗ T) - eulerCharacteristic f T =
      eulerCharacteristic (i ≫ f) (Fi.obj (L ⊗ T)) -
        eulerCharacteristic (j ≫ f) (Fj.obj T) at h
    let e : L ⊗ T ≅ T ⊗ L := β_ L T
    rw [eulerCharacteristic_eq_of_iso f e,
      eulerCharacteristic_eq_of_iso (i ≫ f) (Fi.mapIso e)] at h
    exact h
  | cons K ls ih =>
    intro hls T hT
    let hK : IsInvertible K := hls K (by simp)
    have ht : ∀ M ∈ ls, IsInvertible M := fun M hM => hls M (by simp [hM])
    let hTK : IsInvertible (T ⊗ K) :=
      (hT.tensorObj hK).of_iso (ModularCurves.monoidalTensorObjIso T K)
    have h₁ := ih ht (T ⊗ K) hTK
    have h₂ := ih ht T hT
    let e : (T ⊗ K) ⊗ L ≅ (T ⊗ L) ⊗ K :=
      α_ T K L ≪≫ (Iso.refl T ⊗ᵢ β_ K L) ≪≫ (α_ T L K).symm
    let eI : Fi.obj ((T ⊗ K) ⊗ L) ≅ Fi.obj (T ⊗ L) ⊗ Fi.obj K :=
      Fi.mapIso e ≪≫ (Functor.Monoidal.μIso Fi (T ⊗ L) K).symm
    let eJ : Fj.obj (T ⊗ K) ≅ Fj.obj T ⊗ Fj.obj K :=
      (Functor.Monoidal.μIso Fj T K).symm
    rw [mixedEulerDifference_eq_of_iso (i ≫ f) (ls.map Fi.obj) eI,
      mixedEulerDifference_eq_of_iso (j ≫ f) (ls.map Fj.obj) eJ] at h₁
    rw [mixedEulerDifference_swap f L K ls T]
    change mixedEulerDifference f (L :: ls) (T ⊗ K) - mixedEulerDifference f (L :: ls) T =
      (mixedEulerDifference (i ≫ f) (ls.map Fi.obj) (Fi.obj (T ⊗ L) ⊗ Fi.obj K) -
          mixedEulerDifference (i ≫ f) (ls.map Fi.obj) (Fi.obj (T ⊗ L))) -
        (mixedEulerDifference (j ≫ f) (ls.map Fj.obj) (Fj.obj T ⊗ Fj.obj K) -
          mixedEulerDifference (j ≫ f) (ls.map Fj.obj) (Fj.obj T))
    rw [h₁, h₂]
    ring

private theorem isProjective_closedComp_mixed {Z Y W : Scheme.{u}}
    (i : Z ⟶ Y) [IsClosedImmersion i] (p : Y ⟶ W) [IsProjective p] :
    IsProjective (i ≫ p) := by
  constructor
  obtain ⟨E, hE, hEF, j, hj, hjp⟩ := IsProjective.exists_isClosedImmersion (f := p)
  let : IsClosedImmersion j := hj
  refine ⟨E, hE, hEF, i ≫ j, inferInstance, ?_⟩
  exact (Category.assoc i j E.projectiveBundleπ).trans
    (congrArg (fun q => i ≫ q) hjp)

private theorem integralMixedEuler_zero
    {k : Type u} [Field k] {Z : Scheme.{u}} [IsIntegral Z]
    [CompactSpace Z] [Z.IsSeparated]
    (p : Z ⟶ Spec (.of k)) [IsProjective p] (hdim : topologicalKrullDim Z ≤ 0)
    (ls : List Z.Modules) (hlen : ls.length = 1) (hls : ∀ L ∈ ls, IsInvertible L)
    (T : Z.Modules) (hT : IsInvertible T) : mixedEulerDifference p ls T = 0 := by
  cases ls with
  | nil => simp at hlen
  | cons L ls =>
    cases ls with
    | nil =>
      let hL : IsInvertible L := hls L (by simp)
      let hp := ProjectiveFactorizationRingIso.of_isProjective p
      have h : eulerCharacteristic p (T ⊗ L) = eulerCharacteristic p T :=
        (eulerCharacteristic_eq_of_iso p (β_ T L)).trans
          (eulerCharacteristic_tensor_eq_of_dimension_le_zero p hp hdim L T hL hT)
      exact sub_eq_zero.mpr h
    | cons M ls => simp only [List.length_cons] at hlen; omega

private theorem coherentMixedEuler_of_integralLines
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Z : Scheme.{u}} [IsIntegral Z] [CompactSpace Z] [Z.IsSeparated]
      (p : Z ⟶ Spec (.of k)) [IsProjective p] (_ : topologicalKrullDim Z ≤ d)
      (ls : List Z.Modules) (_ : ls.length = d + 1) (_ : ∀ L ∈ ls, IsInvertible L)
      (T : Z.Modules) (_ : IsInvertible T), mixedEulerDifference p ls T = 0)
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (hdim : topologicalKrullDim X ≤ d)
    (ls : List X.Modules) (hlen : ls.length = d + 1) (hls : ∀ L ∈ ls, IsInvertible L)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    mixedEulerDifference f ls F = 0 := by
  obtain ⟨n, hfil⟩ := exists_finite_coherent_primeFiltration f F
  induction hfil with
  | zero M hM => exact mixedEulerDifference_eq_zero_of_isZero f ls hls M hM
  | iso e _ ih => exact (mixedEulerDifference_eq_of_iso f ls e).symm.trans ih
  | extension S hS hQ₁ hQ₂ hQ₃ hF₁ hF₂ hF₃ eta T hT e _ ih =>
    let : S.X₁.IsQuasicoherent := hQ₁
    let : S.X₂.IsQuasicoherent := hQ₂
    let : S.X₃.IsQuasicoherent := hQ₃
    let : S.X₁.IsFiniteType := hF₁
    let : S.X₂.IsFiniteType := hF₂
    let : S.X₃.IsFiniteType := hF₃
    let I := Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : Closeds X)
    let Z := I.subscheme
    let i : Z ⟶ X := I.subschemeι
    let : IsIntegral Z := SchemePointClosureIntegral.isIntegral_pointClosure eta
    let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
    let : Z.IsSeparated := ⟨by
      have h : IsSeparated (i ≫ terminal.from X) := inferInstance
      simpa only [terminal.comp_from] using h⟩
    let : IsProjective (i ≫ f) := isProjective_closedComp_mixed i f
    have hdimZ : topologicalKrullDim Z ≤ d :=
      IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom i d hdim
    let Fi := Scheme.Modules.pullback i
    have hInv : ∀ K ∈ ls.map Fi.obj, IsInvertible K := by
      intro K hK
      obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hK
      exact (hls L hL).pullback i
    have hz := H (i ≫ f) hdimZ (ls.map Fi.obj) (by simpa using hlen) hInv T hT
    let : T.IsQuasicoherent := hT.isQuasicoherent
    have h₃ : mixedEulerDifference f ls S.X₃ = 0 :=
      (mixedEulerDifference_eq_of_iso f ls e).trans
        ((mixedEulerDifference_pushforward f i ls hls T).trans hz)
    have h := mixedEulerDifference_add f ls hls S hS
    rw [ih, h₃, add_zero] at h
    exact h

private theorem integralMixedEuler_succ
    {k : Type u} [Field k] (d : ℕ)
    (H : ∀ {Z : Scheme.{u}} [CompactSpace Z] [Z.IsSeparated]
      (p : Z ⟶ Spec (.of k)) [IsProjective p] (_ : topologicalKrullDim Z ≤ d)
      (ls : List Z.Modules) (_ : ls.length = d + 1) (_ : ∀ L ∈ ls, IsInvertible L)
      (F : Z.Modules) [F.IsQuasicoherent] [F.IsFiniteType], mixedEulerDifference p ls F = 0)
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (lines : List X.Modules) (hlen : lines.length = (d + 1) + 1)
    (hlines : ∀ L ∈ lines, IsInvertible L) (T : X.Modules) (hT : IsInvertible T) :
    mixedEulerDifference f lines T = 0 := by
  cases lines with
  | nil => simp at hlen
  | cons L ls =>
    have hlen' : ls.length = d + 1 := by simpa using hlen
    let hL : IsInvertible L := hlines L (by simp)
    have hls : ∀ K ∈ ls, IsInvertible K := fun K hK => hlines K (by simp [hK])
    let hf := ProjectiveFactorizationRingIso.of_isProjective f
    obtain ⟨B, hB, a, b, ha, hb, _⟩ :=
      exists_eulerCharacteristic_powerCartierDifference f hf L hL
    let hA : IsInvertible (L ⊗ B) :=
      (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
    let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
    let J := LineSectionZeroIdeal.zeroIdeal B hB b
    let i := I.subschemeι
    let j := J.subschemeι
    let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace i
    let : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace j
    let : I.subscheme.IsSeparated := ⟨by
      have h : IsSeparated (i ≫ terminal.from X) := inferInstance
      simpa only [terminal.comp_from] using h⟩
    let : J.subscheme.IsSeparated := ⟨by
      have h : IsSeparated (j ≫ terminal.from X) := inferInstance
      simpa only [terminal.comp_from] using h⟩
    let : IsProjective (i ≫ f) := isProjective_closedComp_mixed i f
    let : IsProjective (j ≫ f) := isProjective_closedComp_mixed j f
    have hdimI : topologicalKrullDim I.subscheme ≤ d :=
      sectionZero_dimension_drop d hdim (L ⊗ B) hA a ha
    have hdimJ : topologicalKrullDim J.subscheme ≤ d :=
      sectionZero_dimension_drop d hdim B hB b hb
    let Fi := Scheme.Modules.pullback i
    let Fj := Scheme.Modules.pullback j
    let TI := Fi.obj (T ⊗ L)
    let TJ := Fj.obj T
    let hTL : IsInvertible (T ⊗ L) :=
      (hT.tensorObj hL).of_iso (ModularCurves.monoidalTensorObjIso T L)
    let hTI : IsInvertible TI := hTL.pullback i
    let hTJ : IsInvertible TJ := hT.pullback j
    let : TI.IsQuasicoherent := hTI.isQuasicoherent
    let : TJ.IsQuasicoherent := hTJ.isQuasicoherent
    let : TI.IsFinitePresentation := hTI.isFinitePresentation
    let : TJ.IsFinitePresentation := hTJ.isFinitePresentation
    let : TI.IsFiniteType :=
      SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := I.subscheme.ringCatSheaf) TI
    let : TJ.IsFiniteType :=
      SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := J.subscheme.ringCatSheaf) TJ
    have hInvI : ∀ K ∈ ls.map Fi.obj, IsInvertible K := by
      intro K hK
      obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hK
      exact (hls M hM).pullback i
    have hInvJ : ∀ K ∈ ls.map Fj.obj, IsInvertible K := by
      intro K hK
      obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hK
      exact (hls M hM).pullback j
    have hI := H (i ≫ f) hdimI (ls.map Fi.obj) (by simpa using hlen') hInvI TI
    have hJ := H (j ≫ f) hdimJ (ls.map Fj.obj) (by simpa using hlen') hInvJ TJ
    have h := mixedEulerDifference_cartierDifference f L B hL hB a ha b hb ls hls T hT
    change mixedEulerDifference f (L :: ls) T =
      mixedEulerDifference (i ≫ f) (ls.map Fi.obj) TI -
        mixedEulerDifference (j ≫ f) (ls.map Fj.obj) TJ at h
    rw [hI, hJ, sub_self] at h
    exact h

/-- Actual mixed Euler differences vanish beyond the genuine original ambient dimension. -/
theorem mixedEulerDifference_eq_zero_of_dimension_le
    {k : Type u} [Field k] (d : ℕ)
    {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [IsProjective f] (hdim : topologicalKrullDim X ≤ d)
    (ls : List X.Modules) (hlen : ls.length = d + 1) (hls : ∀ L ∈ ls, IsInvertible L)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : mixedEulerDifference f ls F = 0 := by
  have all : ∀ d : ℕ, ∀ {Y : Scheme.{u}} [CompactSpace Y] [Y.IsSeparated]
      (g : Y ⟶ Spec (.of k)) [IsProjective g] (_ : topologicalKrullDim Y ≤ d)
      (lines : List Y.Modules) (_ : lines.length = d + 1) (_ : ∀ L ∈ lines, IsInvertible L)
      (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType], mixedEulerDifference g lines M = 0 := by
    intro d
    induction d with
    | zero =>
      intro Y _ _ g _ hdimY lines hlenY hlines M _ _
      refine coherentMixedEuler_of_integralLines 0 ?_ g hdimY lines hlenY hlines M
      intro Z _ _ _ p _ hdimZ lines hlenZ hlines T hT
      exact integralMixedEuler_zero p hdimZ lines hlenZ hlines T hT
    | succ d ih =>
      intro Y _ _ g _ hdimY lines hlenY hlines M _ _
      refine coherentMixedEuler_of_integralLines (d + 1) ?_ g hdimY lines hlenY hlines M
      intro Z _ _ _ p _ hdimZ lines hlenZ hlines T hT
      exact integralMixedEuler_succ d ih p hdimZ lines hlenZ hlines T hT
  exact all d f hdim ls hlen hls F

private theorem mixedEulerDifference_tensor_identity (L M : X.Modules)
    (ls : List X.Modules) (F : X.Modules) :
    mixedEulerDifference f ((L ⊗ M) :: ls) F =
      mixedEulerDifference f (L :: ls) F + mixedEulerDifference f (M :: ls) F +
        mixedEulerDifference f (L :: M :: ls) F := by
  have h := mixedEulerDifference_eq_of_iso f ls (α_ F L M).symm
  change mixedEulerDifference f ls (F ⊗ (L ⊗ M)) - mixedEulerDifference f ls F =
    (mixedEulerDifference f ls (F ⊗ L) - mixedEulerDifference f ls F) +
      (mixedEulerDifference f ls (F ⊗ M) - mixedEulerDifference f ls F) +
      ((mixedEulerDifference f ls ((F ⊗ L) ⊗ M) - mixedEulerDifference f ls (F ⊗ L)) -
        (mixedEulerDifference f ls (F ⊗ M) - mixedEulerDifference f ls F))
  rw [h]
  ring

/-- The actual dimension-vanishing theorem removes the genuine extra mixed term. -/
theorem mixedEulerDifference_tensor_add [X.IsSeparated] [IsProjective f]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (L M : X.Modules) (hL : IsInvertible L) (hM : IsInvertible M)
    (ls : List X.Modules) (hlen : ls.length + 1 = d) (hls : ∀ K ∈ ls, IsInvertible K)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    mixedEulerDifference f ((L ⊗ M) :: ls) F =
      mixedEulerDifference f (L :: ls) F + mixedEulerDifference f (M :: ls) F := by
  have hInv : ∀ K ∈ L :: M :: ls, IsInvertible K := by
    intro K hK
    simp only [List.mem_cons] at hK
    rcases hK with rfl | rfl | hK
    · exact hL
    · exact hM
    · exact hls K hK
  have hz := mixedEulerDifference_eq_zero_of_dimension_le d f hdim (L :: M :: ls)
    (by simp only [List.length_cons]; omega) hInv F
  rw [mixedEulerDifference_tensor_identity f L M ls F, hz, add_zero]

private theorem iteratedPolynomialForwardDifference_succ_outer (d : ℕ) (p : Polynomial ℚ) :
    iteratedPolynomialForwardDifference (d + 1) p =
      polynomialForwardDifference (iteratedPolynomialForwardDifference d p) := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih => exact ih (polynomialForwardDifference p)

private theorem iteratedEulerPolynomial_eval [X.IsSeparated] [IsProjective f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) (d : ℕ) : ∀ n : ℕ,
    (iteratedPolynomialForwardDifference d (eulerPolynomial f F L hL)).eval (n : ℚ) =
      (mixedEulerDifference f (List.replicate d L)
        (F ⊗ CanonicalGeometry.bundleTensorPower L n) : ℚ) := by
  induction d with
  | zero => intro n; exact eulerPolynomial_eval f F L hL n
  | succ d ih =>
    intro n
    rw [iteratedPolynomialForwardDifference_succ_outer, polynomialForwardDifference_eval]
    rw [show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by simp only [Nat.cast_add, Nat.cast_one], ih (n + 1), ih n]
    let P := CanonicalGeometry.bundleTensorPower L n
    let e : (F ⊗ P) ⊗ L ≅ F ⊗ CanonicalGeometry.bundleTensorPower L (n + 1) :=
      α_ F P L ≪≫ (Iso.refl F ⊗ᵢ ModularCurves.monoidalTensorObjIso P L)
    have he := mixedEulerDifference_eq_of_iso f (List.replicate d L) e
    change (mixedEulerDifference f (List.replicate d L)
          (F ⊗ CanonicalGeometry.bundleTensorPower L (n + 1)) : ℚ) -
        (mixedEulerDifference f (List.replicate d L) (F ⊗ P) : ℚ) =
      ((mixedEulerDifference f (List.replicate d L) ((F ⊗ P) ⊗ L) -
        mixedEulerDifference f (List.replicate d L) (F ⊗ P) : ℤ) : ℚ)
    rw [Int.cast_sub, he]

/-- Actual repeated original line differences compute the original Euler coefficient. -/
theorem mixedEulerDifference_replicate_eq_factorial_mul_coeff [X.IsSeparated] [IsProjective f]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : X.Modules) (hL : IsInvertible L) :
    (mixedEulerDifference f (List.replicate d L) F : ℚ) =
      (d.factorial : ℚ) * (eulerPolynomial f F L hL).coeff d := by
  have h := iteratedEulerPolynomial_eval f F L hL d 0
  have hp := eulerPolynomial_natDegree_le f F L hL d hdim
  rw [iteratedPolynomialForwardDifference_eq_C_factorial_mul_coeff d _ hp,
    Polynomial.eval_C] at h
  let e : F ⊗ CanonicalGeometry.bundleTensorPower L 0 ≅ F :=
    (Iso.refl F ⊗ᵢ (ModularCurves.monoidalUnitObjIso X).symm) ≪≫ ρ_ F
  rw [mixedEulerDifference_eq_of_iso f (List.replicate d L) e] at h
  exact h.symm

/-- The actual top mixed value is independent of the original invertible coefficient. -/
theorem mixedEulerDifference_eq_unit_of_dimension_le [X.IsSeparated] [IsProjective f]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d) (ls : List X.Modules)
    (hlen : ls.length = d) (hls : ∀ K ∈ ls, IsInvertible K)
    (T : X.Modules) (hT : IsInvertible T) :
    mixedEulerDifference f ls T = mixedEulerDifference f ls (unitObj X) := by
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj X).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  let : (unitObj X).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (R := X.ringCatSheaf) (unitObj X)
  have hInv : ∀ K ∈ T :: ls, IsInvertible K := by
    intro K hK
    rcases List.mem_cons.mp hK with rfl | hK
    · exact hT
    · exact hls K hK
  have hz := mixedEulerDifference_eq_zero_of_dimension_le d f hdim (T :: ls)
    (by simp only [List.length_cons, hlen]) hInv (unitObj X)
  change mixedEulerDifference f ls (unitObj X ⊗ T) -
    mixedEulerDifference f ls (unitObj X) = 0 at hz
  let e : unitObj X ⊗ T ≅ T :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl T) ≪≫ λ_ T
  rw [mixedEulerDifference_eq_of_iso f ls e] at hz
  exact sub_eq_zero.mp hz

#check @mixedEulerDifference_replicate_eq_factorial_mul_coeff
#print axioms mixedEulerDifference_replicate_eq_factorial_mul_coeff
#check @mixedEulerDifference_eq_unit_of_dimension_le
#print axioms mixedEulerDifference_eq_unit_of_dimension_le
#check @mixedEulerDifference_tensor_add
#print axioms mixedEulerDifference_tensor_add
#check @integralMixedEuler_succ
#print axioms integralMixedEuler_succ
#check @mixedEulerDifference_eq_zero_of_dimension_le
#print axioms mixedEulerDifference_eq_zero_of_dimension_le
#check @integralMixedEuler_zero
#print axioms integralMixedEuler_zero
#check @coherentMixedEuler_of_integralLines
#print axioms coherentMixedEuler_of_integralLines
#check @mixedEulerDifference_cartierDifference
#print axioms mixedEulerDifference_cartierDifference
#check @mixedEulerDifference_pushforward
#print axioms mixedEulerDifference_pushforward
#check @mixedEulerDifference_eq_of_iso
#print axioms mixedEulerDifference_eq_of_iso
#check @mixedEulerDifference_eq_zero_of_isZero
#print axioms mixedEulerDifference_eq_zero_of_isZero
#check @mixedEulerDifference_add
#print axioms mixedEulerDifference_add
#check @mixedEulerDifference_swap
#print axioms mixedEulerDifference_swap
end EnvelopeProperty.SeshadriAmplenessCriterion
