import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCutCohomology
import Mathlib.Order.OrderIsoNat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # The same actual fixed-section H1 maps stabilize

Original projective coherent finiteness and the actual single-cut epimorphisms
are consumed directly. The original maps, original powers and literal cut are
preserved; no stabilization or cohomology-matching certificate is supplied.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Modules
universe u v w
namespace EnvelopeProperty.SeshadriAmplenessCriterionSingleCutStability
open CanonicalGeometry SchemeCoherentEulerIndex SchemeCoherentEulerExact
open SeshadriAmplenessCriterionCutCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nat_fixedStep_stabilizes (d : ℕ → ℕ) (r : ℕ) (hr : 0 < r)
    (N₀ : ℕ) (hstep : ∀ n, N₀ ≤ n → d (n + r) ≤ d n) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∀ n : ℕ, N ≤ n → d (n + r) = d n := by
  classical
  have hanti (i : Fin r) : Antitone (fun t : ℕ => d (N₀ + i.val + r * t)) := by
    apply antitone_nat_of_succ_le
    intro t
    have hn : N₀ ≤ N₀ + i.val + r * t := by omega
    simpa only [Nat.mul_succ, Nat.add_assoc] using hstep (N₀ + i.val + r * t) hn
  have hres (i : Fin r) := WellFoundedLT.antitone_chain_condition (hanti i)
  choose K hK using hres
  let N := Finset.univ.sup (fun i : Fin r => N₀ + i.val + r * K i)
  have hbound (i : Fin r) : N₀ + i.val + r * K i ≤ N :=
    Finset.le_sup (f := fun j : Fin r => N₀ + j.val + r * K j) (Finset.mem_univ i)
  have hN : N₀ ≤ N := by
    have hh := hbound (⟨0, hr⟩ : Fin r)
    omega
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := hN.trans hn
  let i : Fin r := ⟨(n - N₀) % r, Nat.mod_lt _ hr⟩
  let t := (n - N₀) / r
  have hrep : N₀ + i.val + r * t = n := by
    dsimp only [i, t]
    have h := Nat.mod_add_div (n - N₀) r
    omega
  have hprod : r * K i ≤ r * t := by
    have hh := (hbound i).trans hn
    omega
  have hk : K i ≤ t := by
    by_contra hkt
    have ht : t + 1 ≤ K i := by omega
    have hm := Nat.mul_le_mul_left r ht
    rw [Nat.mul_succ] at hm
    omega
  have h₀ := hK i t hk
  have h₁ := hK i (t + 1) (hk.trans (Nat.le_succ t))
  have heq := h₁.symm.trans h₀
  change d (N₀ + i.val + r * (t + 1)) = d (N₀ + i.val + r * t) at heq
  have hrep₁ : N₀ + i.val + r * (t + 1) = n + r := by
    rw [Nat.mul_succ]
    omega
  simpa only [hrep₁, hrep] using heq

private theorem finiteType_of_invertible {X : Scheme.{u}} (M : X.Modules)
    (hM : IsInvertible M) : M.IsFiniteType := by
  let : M.IsFinitePresentation := hM.isFinitePresentation
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
  constructor
  intro i
  exact (hq.isFinite_presentation i).isFiniteType_generators

/-- Genuine projective finiteness and ampleness only on the SAME actual cut
internally make the SAME fixed-section H1 multiplication maps eventually
isomorphisms. No ambient-X ampleness, dimension-stability, vanishing or map
comparison certificate occurs among the inputs. -/
theorem exists_singleCut_powerHOne_isIso_of_ample {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ) (hr : 0 < r)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r) hA s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsIso (HomologicalComplex.homologyMap
      ((fieldComplexFunctor f U).map (powerSectionSequence L hL r s hs n).f) 1) := by
  dsimp only
  intro hI
  obtain ⟨N₀, hN₀⟩ := exists_singleCut_powerHOne_epi_of_ample f U hU hUa L hL r s hs hI
  let V : ℕ → ModuleCat.{u} k := fun n =>
    ((fieldComplexFunctor f U).obj (bundleTensorPower L n)).homology 1
  let v (n : ℕ) : V n ⟶ V (n + r) := HomologicalComplex.homologyMap
    ((fieldComplexFunctor f U).map (powerSectionSequence L hL r s hs n).f) 1
  have hfinite (n : ℕ) : Module.Finite k (V n) := by
    let M := bundleTensorPower L n
    have hM := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
    let : M.IsQuasicoherent := hM.isQuasicoherent
    let : M.IsFiniteType := finiteType_of_invertible M hM
    let : Module.Finite k (fieldCech f M U 1) :=
      SchemeCoherentEulerCharacteristic.fieldCech_finite f hf M U hU hUa 1
    exact Module.Finite.equiv (fieldComplexHomologyIso f M U 1).symm.toLinearEquiv
  have hstep (n : ℕ) (hn : N₀ ≤ n) :
      Module.finrank k (V (n + r)) ≤ Module.finrank k (V n) := by
    let : Module.Finite k (V n) := hfinite n
    have hepi : Epi (v n) := hN₀ n hn
    exact LinearMap.finrank_le_finrank_of_surjective (f := (v n).hom)
      ((ModuleCat.epi_iff_surjective (v n)).mp hepi)
  obtain ⟨N, hN, hdim⟩ := nat_fixedStep_stabilizes
    (fun n => Module.finrank k (V n)) r hr N₀ hstep
  refine ⟨N, fun n hn => ?_⟩
  change IsIso (v n)
  let : Module.Finite k (V n) := hfinite n
  let : Module.Finite k (V (n + r)) := hfinite (n + r)
  have hepi : Epi (v n) := hN₀ n (hN.trans hn)
  have hsurj := (ModuleCat.epi_iff_surjective (v n)).mp hepi
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdim n hn).symm).mpr hsurj
  have : Mono (v n) := (ModuleCat.mono_iff_injective (v n)).mpr hinj
  have : Epi (v n) := hepi
  exact isIso_of_mono_of_epi _

private theorem baseCechAugmentation_naturality {X T : Scheme.{u}}
    (f : X ⟶ T) {M N : X.Modules} (v : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) :
    baseSectionsMap f v ≫ baseCechAugmentation f N U =
      baseCechAugmentation f M U ≫ ((baseCechComplexFunctor f U).map v).f 0 := by
  let φ : baseModulePresheaf f M ⟶ baseModulePresheaf f N :=
    (baseModulePresheafFunctor f).map v
  change baseSectionsMap f v ≫ baseCechAugmentation f N U =
    baseCechAugmentation f M U ≫ Limits.Pi.map
      (fun j : Fin 1 → ι => φ.app (.op (∏ᶜ fun k : Fin 1 => U (j k))))
  refine Limits.Pi.hom_ext
    (f := fun j : Fin 1 → ι => (baseModulePresheaf f N).obj (.op (∏ᶜ fun k : Fin 1 => U (j k))))
    _ _ (fun i => ?_)
  calc
    (baseSectionsMap f v ≫ baseCechAugmentation f N U) ≫
        Limits.Pi.π (fun j : Fin 1 → ι => (baseModulePresheaf f N).obj (.op (∏ᶜ fun k : Fin 1 => U (j k)))) i =
      baseSectionsMap f v ≫ (baseModulePresheaf f N).map
        (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op := by
      rw [Category.assoc, baseCechAugmentation_comp_π]
    _ = (baseModulePresheaf f M).map
        (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op ≫
          φ.app (.op (∏ᶜ fun k : Fin 1 => U (i k))) :=
      (φ.naturality (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤ ⊤ from le_top)).op).symm
    _ = (baseCechAugmentation f M U ≫ Limits.Pi.map
        (fun j : Fin 1 → ι => φ.app (.op (∏ᶜ fun k : Fin 1 => U (j k))))) ≫
          Limits.Pi.π (fun j : Fin 1 → ι => (baseModulePresheaf f N).obj (.op (∏ᶜ fun k : Fin 1 => U (j k)))) i := by
      have hp := Limits.Pi.map_π
        (f := fun j : Fin 1 → ι => (baseModulePresheaf f M).obj
          (.op (∏ᶜ fun k : Fin 1 => U (j k))))
        (g := fun j : Fin 1 → ι => (baseModulePresheaf f N).obj
          (.op (∏ᶜ fun k : Fin 1 => U (j k))))
        (fun j : Fin 1 → ι => φ.app (.op (∏ᶜ fun k : Fin 1 => U (j k)))) i
      have ha := baseCechAugmentation_comp_π f M U i
      calc
        _ = (baseCechAugmentation f M U ≫
            Limits.Pi.π (fun j : Fin 1 → ι => (baseModulePresheaf f M).obj
              (.op (∏ᶜ fun k : Fin 1 => U (j k)))) i) ≫
                φ.app (.op (∏ᶜ fun k : Fin 1 => U (i k))) :=
          congrArg (fun z => z ≫ φ.app (.op (∏ᶜ fun k : Fin 1 => U (i k)))) ha.symm
        _ = baseCechAugmentation f M U ≫
            (Limits.Pi.π (fun j : Fin 1 → ι => (baseModulePresheaf f M).obj
              (.op (∏ᶜ fun k : Fin 1 => U (j k)))) i ≫
                φ.app (.op (∏ᶜ fun k : Fin 1 => U (i k)))) := Category.assoc _ _ _
        _ = _ := by
          exact (congrArg (fun z => baseCechAugmentation f M U ≫ z) hp.symm).trans
            (Category.assoc _ _ _).symm

private def baseSectionsHZeroIso {X T : Scheme.{u}}
    (f : X ⟶ T) (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (hU : IsOpenCover U) :
    baseSections f M ≅ ((baseCechComplexFunctor f U).obj M).homology 0 := by
  let C := (baseCechComplexFunctor f U).obj M
  let a := baseCechAugmentation f M U
  have hz : a ≫ C.d 0 1 = 0 := baseCechAugmentation_comp_d f M U
  let l := C.liftCycles a 1 (by simp) hz
  have hl : IsIso l := (CochainComplex.isIso_liftCycles_iff C a hz).mpr
    ⟨baseCechAugmentedShortComplex_exact f M U hU, baseCechAugmentation_mono f M U hU⟩
  have := hl
  exact asIso l ≪≫ CochainComplex.isoHomologyπ₀ C

private theorem baseSectionsHZeroIso_naturality {X T : Scheme.{u}}
    (f : X ⟶ T) {M N : X.Modules} (v : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    baseSectionsMap f v ≫ (baseSectionsHZeroIso f N U hU).hom =
      (baseSectionsHZeroIso f M U hU).hom ≫
        HomologicalComplex.homologyMap ((baseCechComplexFunctor f U).map v) 0 := by
  let CM := (baseCechComplexFunctor f U).obj M
  let CN := (baseCechComplexFunctor f U).obj N
  let φ : CM ⟶ CN := (baseCechComplexFunctor f U).map v
  let aM := baseCechAugmentation f M U
  let aN := baseCechAugmentation f N U
  let lM := CM.liftCycles aM 1 (by simp) (baseCechAugmentation_comp_d f M U)
  let lN := CN.liftCycles aN 1 (by simp) (baseCechAugmentation_comp_d f N U)
  change baseSectionsMap f v ≫ (lN ≫ CN.homologyπ 0) =
    (lM ≫ CM.homologyπ 0) ≫ HomologicalComplex.homologyMap φ 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  suffices h : baseSectionsMap f v ≫ lN = lM ≫ HomologicalComplex.cyclesMap φ 0 by
    simpa only [Category.assoc] using congrArg (fun w => w ≫ CN.homologyπ 0) h
  rw [← cancel_mono (CN.iCycles 0)]
  have hm : lM ≫ CM.iCycles 0 = aM :=
    CM.liftCycles_i aM 1 (by simp) (baseCechAugmentation_comp_d f M U)
  have hn : lN ≫ CN.iCycles 0 = aN :=
    CN.liftCycles_i aN 1 (by simp) (baseCechAugmentation_comp_d f N U)
  have hc : HomologicalComplex.cyclesMap φ 0 ≫ CN.iCycles 0 = CM.iCycles 0 ≫ φ.f 0 :=
    HomologicalComplex.cyclesMap_i φ 0
  calc
    (baseSectionsMap f v ≫ lN) ≫ CN.iCycles 0 = baseSectionsMap f v ≫ aN := by
      rw [Category.assoc, hn]
    _ = aM ≫ φ.f 0 := baseCechAugmentation_naturality f v U
    _ = (lM ≫ CM.iCycles 0) ≫ φ.f 0 := by rw [hm]
    _ = (lM ≫ HomologicalComplex.cyclesMap φ 0) ≫ CN.iCycles 0 := by
      simp only [Category.assoc, hc]

private def fieldSectionsHZeroIso {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    fieldSections f M ≅ ((fieldComplexFunctor f U).obj M).homology 0 :=
  (ModuleCat.restrictScalars (baseScalar (k := k))).mapIso
      (baseSectionsHZeroIso f M U hU) ≪≫
    (fieldComplexHomologyIso f M U 0).symm

private theorem fieldSectionsHZeroIso_naturality {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {M N : X.Modules} (v : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U) :
    (ModuleCat.restrictScalars (baseScalar (k := k))).map (baseSectionsMap f v) ≫
        (fieldSectionsHZeroIso f N U hU).hom =
      (fieldSectionsHZeroIso f M U hU).hom ≫
        HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map v) 0 := by
  let F := ModuleCat.restrictScalars (baseScalar (k := k))
  let φ := (baseCechComplexFunctor f U).map v
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    (φ := (HomologicalComplex.shortComplexFunctor _ _ 0).map φ) (F := F)
  change F.map (baseSectionsMap f v) ≫
      (F.map (baseSectionsHZeroIso f N U hU).hom ≫
        (fieldComplexHomologyIso f N U 0).inv) =
    (F.map (baseSectionsHZeroIso f M U hU).hom ≫
        (fieldComplexHomologyIso f M U 0).inv) ≫
      HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map v) 0
  calc
    _ = F.map (baseSectionsMap f v ≫ (baseSectionsHZeroIso f N U hU).hom) ≫
        (fieldComplexHomologyIso f N U 0).inv := by rw [F.map_comp, Category.assoc]
    _ = F.map ((baseSectionsHZeroIso f M U hU).hom ≫
          HomologicalComplex.homologyMap φ 0) ≫
        (fieldComplexHomologyIso f N U 0).inv := by
      rw [baseSectionsHZeroIso_naturality]
    _ = F.map (baseSectionsHZeroIso f M U hU).hom ≫
        ((fieldComplexHomologyIso f M U 0).inv ≫
          HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map v) 0) := by
      rw [F.map_comp, Category.assoc]
      exact congrArg (fun z => F.map (baseSectionsHZeroIso f M U hU).hom ≫ z) hn
    _ = _ := by rw [Category.assoc]

/-- For the SAME original short exact sequence, a monic actual first-cohomology
map internally gives surjectivity of the original global-section quotient map. -/
theorem sections_surjective_of_hOne_mono {k : Type u} [Field k]
    {X : Scheme.{u}} [X.IsSeparated] (f : X ⟶ Spec (.of k))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hm : Mono (HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map S.f) 1)) :
    Function.Surjective (S.g.app (⊤ : X.Opens)) := by
  let T := S.map (fieldComplexFunctor f U)
  have hT : T.ShortExact :=
    (hS.map_baseCechComplexFunctor_of_affine_openCover f U hUa).map_of_exact
      ((ModuleCat.restrictScalars (baseScalar (k := k))).mapHomologicalComplex (.up ℕ))
  have : Mono (HomologicalComplex.homologyMap T.f 1) := hm
  have hδ : hT.δ 0 1 rfl = 0 := by
    rw [← cancel_mono (HomologicalComplex.homologyMap T.f 1)]
    simpa only [zero_comp] using hT.δ_comp 0 1 rfl
  have : Epi (HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map S.g) 0) :=
    (hT.homology_exact₃ 0 1 rfl).epi_f hδ
  let F := ModuleCat.restrictScalars (baseScalar (k := k))
  have hn := fieldSectionsHZeroIso_naturality f S.g U hU
  have hep : Epi (F.map (baseSectionsMap f S.g) ≫
      (fieldSectionsHZeroIso f S.X₃ U hU).hom) := by
    rw [hn]
    infer_instance
  have : Epi (F.map (baseSectionsMap f S.g)) :=
    (epi_comp_iff_of_isIso _ (fieldSectionsHZeroIso f S.X₃ U hU).hom).mp hep
  exact (ModuleCat.epi_iff_surjective (F.map (baseSectionsMap f S.g))).mp inferInstance

private theorem conjugate_tensor_quotient_unit_factorization
    {C D : Type v} [Category.{w} C] [Category.{w} D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (E : C ≌ C) (E' : D ≌ D)
    (α : F ⋙ E'.inverse ≅ E.inverse ⋙ F)
    (A U : C) (V : D)
    (e : E.inverse.obj A ≅ U) (b : E.functor.obj U ≅ A)
    (t : E'.functor.obj V ≅ F.obj A)
    (q : U ⟶ G.obj V) [IsIso ((adj.homEquiv U V).symm q)] :
    ∃ τ : F.obj A ≅ F.obj A,
      b.inv ≫ E.functor.map q ≫
          (conjugateIsoEquiv (E.symm.toAdjunction.comp adj)
            (adj.comp E'.symm.toAdjunction) α).hom.app V ≫ G.map t.hom =
        adj.unit.app A ≫ G.map τ.hom := by
  let g : F.obj (E.inverse.obj A) ≅ V :=
    F.mapIso e ≪≫ asIso ((adj.homEquiv U V).symm q)
  let ξ : A ≅ E.functor.obj U :=
    asIso (E.symm.toAdjunction.unit.app A) ≪≫ E.functor.mapIso e
  let a : A ≅ A := b.symm ≪≫ ξ.symm
  let σ : F.obj A ≅ E'.functor.obj V :=
    asIso (E'.symm.toAdjunction.unit.app (F.obj A)) ≪≫ E'.functor.mapIso (α.app A ≪≫ g)
  let τ := F.mapIso a ≪≫ σ ≪≫ t
  let PF := conjugateIsoEquiv (E.symm.toAdjunction.comp adj)
    (adj.comp E'.symm.toAdjunction) α
  have hg : adj.homEquiv (E.inverse.obj A) V g.hom = e.hom ≫ q := by
    change adj.homEquiv (E.inverse.obj A) V
      (F.map e.hom ≫ (adj.homEquiv U V).symm q) = _
    rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
  have hgu : adj.unit.app (E.inverse.obj A) ≫ G.map g.hom = e.hom ≫ q := hg
  have hξ : (E.symm.toAdjunction.comp adj).unit.app A ≫
      E.functor.map (G.map g.hom) = ξ.hom ≫ E.functor.map q := by
    rw [Adjunction.comp_unit_app]
    change (E.symm.toAdjunction.unit.app A ≫ E.functor.map (adj.unit.app (E.inverse.obj A))) ≫
      E.functor.map (G.map g.hom) =
      (E.symm.toAdjunction.unit.app A ≫ E.functor.map e.hom) ≫ E.functor.map q
    rw [Category.assoc, ← E.functor.map_comp, hgu, E.functor.map_comp, Category.assoc]
  have hu := unit_conjugateEquiv (E.symm.toAdjunction.comp adj)
    (adj.comp E'.symm.toAdjunction) α.hom A
  have hs : ξ.hom ≫ E.functor.map q ≫ PF.hom.app V =
      adj.unit.app A ≫ G.map σ.hom := by
    calc
      _ = ((E.symm.toAdjunction.comp adj).unit.app A ≫
            E.functor.map (G.map g.hom)) ≫ PF.hom.app V := by rw [hξ, Category.assoc]
      _ = (E.symm.toAdjunction.comp adj).unit.app A ≫
          (PF.hom.app (F.obj (E.inverse.obj A)) ≫ G.map (E'.functor.map g.hom)) := by
        rw [Category.assoc]
        congr 1
        exact PF.hom.naturality g.hom
      _ = ((adj.comp E'.symm.toAdjunction).unit.app A ≫
          G.map (E'.functor.map (α.hom.app A))) ≫ G.map (E'.functor.map g.hom) := by
        rw [← Category.assoc]
        exact congrArg (fun z => z ≫ G.map (E'.functor.map g.hom)) hu
      _ = _ := by
        rw [Adjunction.comp_unit_app]
        dsimp only [σ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
        simp only [asIso_hom, Functor.map_comp, Category.assoc]
  refine ⟨τ, ?_⟩
  have haξ : a.hom ≫ ξ.hom = b.inv := by
    dsimp only [a, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = a.hom ≫ (ξ.hom ≫ E.functor.map q ≫ PF.hom.app V) ≫ G.map t.hom := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ E.functor.map q ≫ PF.hom.app V ≫ G.map t.hom) haξ.symm
    _ = a.hom ≫ (adj.unit.app A ≫ G.map σ.hom) ≫ G.map t.hom := by rw [hs]
    _ = (adj.unit.app A ≫ G.map (F.map a.hom)) ≫ G.map σ.hom ≫ G.map t.hom := by
      have ha : a.hom ≫ adj.unit.app A = adj.unit.app A ≫ G.map (F.map a.hom) :=
        adj.unit.naturality a.hom
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ G.map σ.hom ≫ G.map t.hom) ha
    _ = _ := by
      dsimp only [τ, Iso.trans_hom, Functor.mapIso_hom]
      simp only [Functor.map_comp, Category.assoc]

open CategoryTheory.MonoidalCategory
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem lineProjectionFormula_quotient_unit_factorization
    {X D : Scheme.{u}} (g : D ⟶ X) (W : X.Modules) (hW : IsInvertible W) :
    let F := Scheme.Modules.pullback g
    let G := Scheme.Modules.pushforward g
    let b : unitObj X ⊗ W ≅ W :=
      ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl W) ≪≫ λ_ W
    let t : unitObj D ⊗ F.obj W ≅ F.obj W :=
      ((ModularCurves.monoidalUnitObjIso D).symm ⊗ᵢ Iso.refl (F.obj W)) ≪≫ λ_ (F.obj W)
    ∃ τ : F.obj W ≅ F.obj W,
      b.inv ≫ (tensorRight W).map (FiniteClosedIdealEuler.quotientMap g) ≫
          (SchemeLineProjectionFormula.lineProjectionFormulaObj g W hW (unitObj D)).hom ≫
          G.map t.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app W ≫ G.map τ.hom := by
  let F := Scheme.Modules.pullback g
  let G := Scheme.Modules.pushforward g
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let : F.Monoidal := Scheme.Modules.pullbackMonoidal g
  let E := SchemeInvertibleTensorEquivalence.rightTensorEquivalence W (dualObj W)
    hW.monoidalEvaluationIso
  let E' := SchemeInvertibleTensorEquivalence.rightTensorEquivalence
    (F.obj W) (F.obj (dualObj W))
    (Functor.Monoidal.μIso F W (dualObj W) ≪≫ F.mapIso hW.monoidalEvaluationIso ≪≫
      (Functor.Monoidal.εIso F).symm)
  let α : F ⋙ E'.inverse ≅ E.inverse ⋙ F :=
    Functor.Monoidal.commTensorRight F (dualObj W)
  let e : E.inverse.obj W ≅ unitObj X :=
    hW.monoidalEvaluationIso ≪≫ ModularCurves.monoidalUnitObjIso X
  let b : E.functor.obj (unitObj X) ≅ W :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl W) ≪≫ λ_ W
  let t : E'.functor.obj (unitObj D) ≅ F.obj W :=
    ((ModularCurves.monoidalUnitObjIso D).symm ⊗ᵢ Iso.refl (F.obj W)) ≪≫ λ_ (F.obj W)
  have : IsIso ((adj.homEquiv (unitObj X) (unitObj D)).symm
      (FiniteClosedIdealEuler.quotientMap g)) := by
    change IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
    infer_instance
  exact conjugate_tensor_quotient_unit_factorization F G adj E E' α W (unitObj X)
    (unitObj D) e b t (FiniteClosedIdealEuler.quotientMap g)

private theorem sectionCutSequence_standardUnit_factorization
    {X : Scheme.{u}} [IsIntegral X]
    (A M : X.Modules) (hA : IsInvertible A) (hM : IsInvertible M)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
    ∃ τ : (Scheme.Modules.pullback g).obj (A ⊗ M) ≅
          (Scheme.Modules.pullback g).obj (A ⊗ M),
      (sectionCutSequence A M hA hM s hs).g =
        (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (A ⊗ M) ≫
          (Scheme.Modules.pushforward g).map τ.hom := by
  let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
  let W := A ⊗ M
  have hW : IsInvertible W := (hA.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso A M)
  exact lineProjectionFormula_quotient_unit_factorization g W hW

private theorem powerSectionSequence_standardUnit_factorization
    {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) (n : ℕ) :
    let g := (LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s).subschemeι
    ∃ τ : (Scheme.Modules.pullback g).obj (bundleTensorPower L (n + r)) ≅
          (Scheme.Modules.pullback g).obj (bundleTensorPower L (n + r)),
      (powerSectionSequence L hL r s hs n).g =
        (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (bundleTensorPower L (n + r)) ≫
          (Scheme.Modules.pushforward g).map τ.hom := by
  let A := bundleTensorPower L r
  let M := bundleTensorPower L n
  let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  let hM := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
  let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
  let F := Scheme.Modules.pullback g
  let G := Scheme.Modules.pushforward g
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  let e : A ⊗ M ≅ bundleTensorPower L (n + r) :=
    β_ A M ≪≫ TensorPowerBaseIdealGrading.tensorPowerAddIso L n r
  obtain ⟨τ, hτ⟩ := sectionCutSequence_standardUnit_factorization A M hA hM s hs
  refine ⟨(F.mapIso e).symm ≪≫ τ ≪≫ F.mapIso e, ?_⟩
  change e.inv ≫ (sectionCutSequence A M hA hM s hs).g ≫ G.map (F.map e.hom) = _
  rw [hτ]
  have he : e.inv ≫ adj.unit.app (A ⊗ M) =
      adj.unit.app (bundleTensorPower L (n + r)) ≫ G.map (F.map e.inv) :=
    adj.unit.naturality e.inv
  calc
    _ = (e.inv ≫ adj.unit.app (A ⊗ M)) ≫ G.map τ.hom ≫ G.map (F.map e.hom) := by
      simp only [Category.assoc]
      rfl
    _ = (adj.unit.app (bundleTensorPower L (n + r)) ≫ G.map (F.map e.inv)) ≫
        G.map τ.hom ≫ G.map (F.map e.hom) := by rw [he]
    _ = _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      rfl

/-- Genuine native ampleness on the SAME literal fixed-section cut, together
with original projectivity, internally makes the STANDARD actual adjunction-unit
restriction on original power sections eventually surjective. The transported
quotient comparison and its target automorphism are proved inside this theorem's
producer chain; no matching, stabilization or lifting certificate is supplied. -/
theorem exists_singleCut_powerSections_surjective_of_ample {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ) (hr : 0 < r)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r) hA s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app
        (bundleTensorPower L (n + r))).app (⊤ : X.Opens)) := by
  dsimp only
  intro hI
  obtain ⟨N, hN⟩ := exists_singleCut_powerHOne_isIso_of_ample
    f hf U hU hUa L hL r hr s hs hI
  refine ⟨N, fun n hn => ?_⟩
  let g := (LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s).subschemeι
  let F := Scheme.Modules.pullback g
  let G := Scheme.Modules.pushforward g
  let P := bundleTensorPower L (n + r)
  let S := powerSectionSequence L hL r s hs n
  have hM := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
  have hP := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (n + r)
  let : S.X₁.IsQuasicoherent := by change (bundleTensorPower L n).IsQuasicoherent; exact hM.isQuasicoherent
  let : S.X₂.IsQuasicoherent := by change P.IsQuasicoherent; exact hP.isQuasicoherent
  let : (F.obj P).IsQuasicoherent := (hP.pullback g).isQuasicoherent
  let : S.X₃.IsQuasicoherent := by
    change (G.obj (F.obj P)).IsQuasicoherent
    exact isQuasicoherent_pushforward_of_isAffineHom g
  have : IsIso (HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map S.f) 1) := hN n hn
  have hsurj := sections_surjective_of_hOne_mono f U hU hUa S
    (powerSectionSequence_shortExact L hL r s hs n) inferInstance
  obtain ⟨τ, hτ⟩ := powerSectionSequence_standardUnit_factorization L hL r s hs n
  let eΓ := (SheafOfModules.evaluation X.ringCatSheaf (.op (⊤ : X.Opens))).mapIso (G.mapIso τ)
  intro z
  obtain ⟨x, hx⟩ := hsurj (eΓ.hom z)
  refine ⟨x, eΓ.toLinearEquiv.injective ?_⟩
  change ((G.map τ.hom).app (⊤ : X.Opens))
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app P).app (⊤ : X.Opens) x) =
    eΓ.hom z
  exact (congrArg (fun v => v.app (⊤ : X.Opens) x) hτ).symm.trans hx

#print axioms exists_singleCut_powerSections_surjective_of_ample
#print axioms lineProjectionFormula_quotient_unit_factorization
#print axioms sectionCutSequence_standardUnit_factorization
#print axioms powerSectionSequence_standardUnit_factorization
#print axioms conjugate_tensor_quotient_unit_factorization
#print axioms fieldSectionsHZeroIso_naturality
#print axioms sections_surjective_of_hOne_mono
#print axioms baseSectionsHZeroIso_naturality
#print axioms nat_fixedStep_stabilizes
#print axioms exists_singleCut_powerHOne_isIso_of_ample
end EnvelopeProperty.SeshadriAmplenessCriterionSingleCutStability
