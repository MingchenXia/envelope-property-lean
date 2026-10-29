import EnvelopeProperty.AlgGeom.SchemeQuasicoherentAffineEffacement
import EnvelopeProperty.AlgGeom.SchemeModuleCohomologyCoefficients
import ModularCurves.ForMathlib.SchemeModuleBaseCechExact
import ModularCurves.ForMathlib.SheafCohomologyExactSequencePort
import EnvelopeProperty.AlgGeom.SchemeModuleCechOneNaturality
import ModularCurves.ForMathlib.SchemeModuleBaseCechZero
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Actual affine-effacement connecting maps and ordinary native cohomology comparison -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u

namespace EnvelopeProperty.SchemeModuleCechNativeCohomology

variable {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)

private def sequenceMap {M N : X.Modules} (f : M ⟶ N) :
    SchemeQuasicoherentAffineEffacement.sequence U M ⟶ SchemeQuasicoherentAffineEffacement.sequence U N where
  τ₁ := f
  τ₂ := SchemeQuasicoherentAffineEffacement.EMap U f
  τ₃ := SchemeQuasicoherentAffineEffacement.quotientMap U f
  comm₁₂ := SchemeQuasicoherentAffineEffacement.augmentation_naturality U f
  comm₂₃ := (SchemeQuasicoherentAffineEffacement.π_naturality U f).symm

/-- The actual native connecting map for the SAME canonical effacement sequence. -/
def nativeConnecting (hU : IsOpenCover U) (M : X.Modules) (q : ℕ) :
    CategoryTheory.Sheaf.H.{u} (SchemeQuasicoherentAffineEffacement.quotient U M).sheaf (q + 1) →+
      CategoryTheory.Sheaf.H.{u} M.sheaf (q + 2) :=
  CategoryTheory.Sheaf.H.δ (SchemeQuasicoherentAffineEffacement.sheafSequence_shortExact U hU M) (q + 1) (q + 2) rfl

/-- The whole native connecting square comes from the actual original effacement maps. -/
theorem nativeConnecting_naturality (hU : IsOpenCover U) {M N : X.Modules}
    (f : M ⟶ N) (q : ℕ) :
    (nativeConnecting U hU N q).comp
        (CategoryTheory.Sheaf.H.map.{u}
          ((Scheme.Modules.toSheaf X).map (SchemeQuasicoherentAffineEffacement.quotientMap U f)) (q + 1)) =
      (CategoryTheory.Sheaf.H.map.{u} ((Scheme.Modules.toSheaf X).map f) (q + 2)).comp
        (nativeConnecting U hU M q) := by
  ext x
  exact CategoryTheory.Sheaf.H.δ_naturality
    (n₀ := q + 1) (n₁ := q + 2) (h := rfl)
    (h₁ := SchemeQuasicoherentAffineEffacement.sheafSequence_shortExact U hU M)
    (h₂ := SchemeQuasicoherentAffineEffacement.sheafSequence_shortExact U hU N)
    (f := (Scheme.Modules.toSheaf X).mapShortComplex.map (sequenceMap U f)) (x := x)

/-- Bijectivity is produced internally from the actual middle object's native acyclicity. -/
theorem nativeConnecting_bijective [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Function.Bijective (nativeConnecting U hU M q) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{u} (SchemeQuasicoherentAffineEffacement.E U M).sheaf (q + 1)) :=
    SchemeQuasicoherentAffineEffacement.E_subsingleton_H U hU hUa M q
  let : Subsingleton (CategoryTheory.Sheaf.H.{u} (SchemeQuasicoherentAffineEffacement.E U M).sheaf (q + 2)) :=
    SchemeQuasicoherentAffineEffacement.E_subsingleton_H U hU hUa M (q + 1)
  constructor
  · intro x y hxy
    have hz : nativeConnecting U hU M q (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := CategoryTheory.Sheaf.H.longSequence_exact₃
      (SchemeQuasicoherentAffineEffacement.sheafSequence_shortExact U hU M) (x - y) rfl hz
    have hz0 : z = 0 :=
      (SchemeQuasicoherentAffineEffacement.E_subsingleton_H U hU hUa M q).elim z 0
    have hsub : x - y = 0 := by
      rw [hz0, map_zero] at hz
      exact hz.symm
    exact sub_eq_zero.mp hsub
  · intro y
    have hy : CategoryTheory.Sheaf.H.map.{u}
        ((Scheme.Modules.toSheaf X).map (SchemeQuasicoherentAffineEffacement.augmentation U M)) (q + 2) y = 0 :=
      Subsingleton.elim _ _
    exact CategoryTheory.Sheaf.H.longSequence_exact₁
      (SchemeQuasicoherentAffineEffacement.sheafSequence_shortExact U hU M) y hy rfl

/-- The genuine native positive-degree connecting equivalence on the original modules. -/
def nativeConnectingEquiv [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    CategoryTheory.Sheaf.H.{u} (SchemeQuasicoherentAffineEffacement.quotient U M).sheaf (q + 1) ≃+
      CategoryTheory.Sheaf.H.{u} M.sheaf (q + 2) :=
  AddEquiv.ofBijective (nativeConnecting U hU M q)
    (nativeConnecting_bijective U hU hUa M q)

/-- The native additive Cech complex, functorial in the original module. -/
abbrev cechFunctor : X.Modules ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  Scheme.Modules.toSheaf X ⋙ TopCat.Sheaf.forget AddCommGrpCat X ⋙ cechComplexFunctor U

instance cechFunctor_preservesZeroMorphisms : (cechFunctor U).PreservesZeroMorphisms where
  map_zero M N := by
    apply HomologicalComplex.hom_ext
    intro n
    change Limits.Pi.map (fun i : Fin (n + 1) → I =>
      (((Scheme.Modules.toSheaf X).map (0 : M ⟶ N)).hom.app
        (op (∏ᶜ fun k : Fin (n + 1) => U (i k))))) = 0
    apply Pi.hom_ext
    intro i
    rw [Pi.map_π, Limits.zero_comp]
    change Pi.π _ i ≫ 0 = 0
    exact Limits.comp_zero

private theorem baseForget_projection {S : Scheme.{u}} (p : X ⟶ S)
    (M : X.Modules) (n : ℕ) (i : Fin (n + 1) → I) :
    (baseCechComplexForgetIso p M U).hom.f n ≫
        Pi.π (fun j : Fin (n + 1) → I =>
          M.sheaf.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i =
      (baseModuleForget S).map (Pi.π (fun j : Fin (n + 1) → I =>
        (baseModulePresheaf p M).obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i) := by
  ext x
  exact baseCechXForgetIso_hom_apply p M U n x i

private theorem baseForget_naturality {S : Scheme.{u}} (p : X ⟶ S)
    {M N : X.Modules} (f : M ⟶ N) :
    ((baseModuleForget S).mapHomologicalComplex (.up ℕ)).map
        ((baseCechComplexFunctor p U).map f) ≫ (baseCechComplexForgetIso p N U).hom =
      (baseCechComplexForgetIso p M U).hom ≫ (cechFunctor U).map f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply Pi.hom_ext
  intro i
  change Fin (n + 1) → I at i
  change (baseModuleForget S).map (((baseCechComplexFunctor p U).map f).f n) ≫
      (baseCechComplexForgetIso p N U).hom.f n ≫
        Pi.π (fun j : Fin (n + 1) → I =>
          N.sheaf.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i =
    (baseCechComplexForgetIso p M U).hom.f n ≫
      (Limits.Pi.map (fun j : Fin (n + 1) → I =>
        ((Scheme.Modules.toSheaf X).map f).hom.app
          (op (∏ᶜ fun k : Fin (n + 1) => U (j k))))) ≫
        Pi.π (fun j : Fin (n + 1) → I =>
          N.sheaf.obj.obj (op (∏ᶜ fun k : Fin (n + 1) => U (j k)))) i
  erw [baseForget_projection, Pi.map_π, ← Category.assoc, baseForget_projection,
    ← Functor.map_comp]
  change (baseModuleForget S).map
      ((Limits.Pi.map (fun j : Fin (n + 1) → I =>
        ((baseModulePresheafFunctor p).map f).app
          (op (∏ᶜ fun k : Fin (n + 1) => U (j k))))) ≫ Pi.π _ i) = _
  rw [Pi.map_π, Functor.map_comp]
  rfl

/-- The actual canonical sequence remains short exact as native additive Cech complexes. -/
theorem cechSequence_shortExact [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] :
    ((SchemeQuasicoherentAffineEffacement.sequence U M).map (cechFunctor U)).ShortExact := by
  let : (SchemeQuasicoherentAffineEffacement.E U M).IsQuasicoherent :=
    SchemeQuasicoherentAffineEffacement.E_isQuasicoherent U hUa M
  let : (SchemeQuasicoherentAffineEffacement.quotient U M).IsQuasicoherent :=
    SchemeQuasicoherentAffineEffacement.quotient_isQuasicoherent U hUa M
  let : (SchemeQuasicoherentAffineEffacement.sequence U M).X₁.IsQuasicoherent := ‹M.IsQuasicoherent›
  let : (SchemeQuasicoherentAffineEffacement.sequence U M).X₂.IsQuasicoherent :=
    SchemeQuasicoherentAffineEffacement.E_isQuasicoherent U hUa M
  let : (SchemeQuasicoherentAffineEffacement.sequence U M).X₃.IsQuasicoherent :=
    SchemeQuasicoherentAffineEffacement.quotient_isQuasicoherent U hUa M
  let hB := (SchemeQuasicoherentAffineEffacement.sequence_shortExact U hU M).map_baseCechComplexFunctor_of_affine_openCover (𝟙 X) U hUa
  let hA := hB.map_of_exact ((baseModuleForget X).mapHomologicalComplex (.up ℕ))
  let e : (((SchemeQuasicoherentAffineEffacement.sequence U M).map
      (baseCechComplexFunctor (𝟙 X) U)).map
        ((baseModuleForget X).mapHomologicalComplex (.up ℕ))) ≅
      ((SchemeQuasicoherentAffineEffacement.sequence U M).map (cechFunctor U)) :=
    ShortComplex.isoMk (baseCechComplexForgetIso (𝟙 X) M U)
      (baseCechComplexForgetIso (𝟙 X) (SchemeQuasicoherentAffineEffacement.E U M) U)
      (baseCechComplexForgetIso (𝟙 X) (SchemeQuasicoherentAffineEffacement.quotient U M) U)
      (baseForget_naturality U (𝟙 X) (SchemeQuasicoherentAffineEffacement.augmentation U M)).symm
      (baseForget_naturality U (𝟙 X) (SchemeQuasicoherentAffineEffacement.π U M)).symm
  exact ShortComplex.shortExact_of_iso e hA

/-- The actual middle Cech homology vanishes, from its independently proved native acyclicity. -/
theorem E_cech_isZero [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    IsZero (((cechFunctor U).obj (SchemeQuasicoherentAffineEffacement.E U M)).homology (q + 1)) := by
  let : (SchemeQuasicoherentAffineEffacement.E U M).IsQuasicoherent :=
    SchemeQuasicoherentAffineEffacement.E_isQuasicoherent U hUa M
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (cechComplex_exactAt_succ_of_affine_openCover
      (SchemeQuasicoherentAffineEffacement.E U M) U hU hUa q
      (SchemeQuasicoherentAffineEffacement.E_subsingleton_H U hU hUa M q))

/-- The genuine Cech connecting map of the SAME actual canonical effacement. -/
def cechConnecting [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    ((cechFunctor U).obj (SchemeQuasicoherentAffineEffacement.quotient U M)).homology (q + 1) ⟶
      ((cechFunctor U).obj M).homology (q + 2) :=
  (cechSequence_shortExact U hU hUa M).δ (q + 1) (q + 2) rfl

/-- Internal middle-object acyclicity makes the actual Cech connecting map an isomorphism. -/
def cechConnectingIso [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    ((cechFunctor U).obj (SchemeQuasicoherentAffineEffacement.quotient U M)).homology (q + 1) ≅
      ((cechFunctor U).obj M).homology (q + 2) :=
  (cechSequence_shortExact U hU hUa M).δIso (q + 1) (q + 2) rfl
    (E_cech_isZero U hU hUa M q) (E_cech_isZero U hU hUa M (q + 1))

/-- The whole Cech connecting square is the native LES naturality square. -/
theorem cechConnecting_naturality [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (q : ℕ) :
    cechConnecting U hU hUa M q ≫ HomologicalComplex.homologyMap ((cechFunctor U).map f) (q + 2) =
      HomologicalComplex.homologyMap
        ((cechFunctor U).map (SchemeQuasicoherentAffineEffacement.quotientMap U f)) (q + 1) ≫
          cechConnecting U hU hUa N q :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((cechFunctor U).mapShortComplex.map (sequenceMap U f))
    (cechSequence_shortExact U hU hUa M) (cechSequence_shortExact U hU hUa N)
    (q + 1) (q + 2) rfl

private theorem inverseSquare {C : Type*} [Category* C] {A B D E : C}
    (v : A ⟶ B) (w : D ⟶ E) [IsIso v] [IsIso w]
    (f : A ⟶ D) (g : B ⟶ E) (h : f ≫ w = v ≫ g) :
    inv v ≫ f = g ≫ inv w := by
  apply (cancel_mono w).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- The native positive connecting equivalence as an actual additive-group isomorphism. -/
def nativeConnectingIso [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u}
      (SchemeQuasicoherentAffineEffacement.quotient U M).sheaf (q + 1)) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} M.sheaf (q + 2)) :=
  AddEquiv.toAddCommGrpIso
    (X := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u}
      (SchemeQuasicoherentAffineEffacement.quotient U M).sheaf (q + 1)))
    (Y := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} M.sheaf (q + 2)))
    (nativeConnectingEquiv U hU hUa M q)

/-- All positive native additive Cech homology groups compute genuine small sheaf cohomology. -/
def positiveComparison [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) :
    (q : ℕ) → (M : X.Modules) → [M.IsQuasicoherent] →
      ((cechFunctor U).obj M).homology (q + 1) ≅
        AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} M.sheaf (q + 1))
  | 0, M, _ => cechHomologyOneIso_of_affine_openCover M U hU hUa
  | q + 1, M, _ => by
      let : (SchemeQuasicoherentAffineEffacement.quotient U M).IsQuasicoherent :=
        SchemeQuasicoherentAffineEffacement.quotient_isQuasicoherent U hUa M
      exact (cechConnectingIso U hU hUa M q).symm ≪≫
        positiveComparison hU hUa q (SchemeQuasicoherentAffineEffacement.quotient U M) ≪≫
          nativeConnectingIso U hU hUa M q

/-- The all-positive comparison commutes with the entire maps induced by every original map. -/
theorem positiveComparison_naturality [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (q : ℕ)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    HomologicalComplex.homologyMap ((cechFunctor U).map f) (q + 1) ≫
        (positiveComparison U hU hUa q N).hom =
      (positiveComparison U hU hUa q M).hom ≫
        AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map.{u} ((Scheme.Modules.toSheaf X).map f) (q + 1)) := by
  induction q generalizing M N with
  | zero => exact SchemeModuleCechOneNaturality.affineHOneIso_naturality f U hU hUa
  | succ q ih =>
      let : (SchemeQuasicoherentAffineEffacement.quotient U M).IsQuasicoherent :=
        SchemeQuasicoherentAffineEffacement.quotient_isQuasicoherent U hUa M
      let : (SchemeQuasicoherentAffineEffacement.quotient U N).IsQuasicoherent :=
        SchemeQuasicoherentAffineEffacement.quotient_isQuasicoherent U hUa N
      let cM := cechConnectingIso U hU hUa M q
      let cN := cechConnectingIso U hU hUa N q
      let pM := positiveComparison U hU hUa q (SchemeQuasicoherentAffineEffacement.quotient U M)
      let pN := positiveComparison U hU hUa q (SchemeQuasicoherentAffineEffacement.quotient U N)
      let nM := nativeConnectingIso U hU hUa M q
      let nN := nativeConnectingIso U hU hUa N q
      let a := HomologicalComplex.homologyMap ((cechFunctor U).map f) (q + 2)
      let b := HomologicalComplex.homologyMap
        ((cechFunctor U).map (SchemeQuasicoherentAffineEffacement.quotientMap U f)) (q + 1)
      let d := AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map.{u}
        ((Scheme.Modules.toSheaf X).map (SchemeQuasicoherentAffineEffacement.quotientMap U f)) (q + 1))
      let e := AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map.{u}
        ((Scheme.Modules.toSheaf X).map f) (q + 2))
      have hc : b ≫ cN.hom = cM.hom ≫ a :=
        (cechConnecting_naturality U hU hUa f q).symm
      have hi : cM.inv ≫ b = a ≫ cN.inv := by
        have hM : inv cM.hom = cM.inv := IsIso.inv_eq_of_hom_inv_id cM.hom_inv_id
        have hN : inv cN.hom = cN.inv := IsIso.inv_eq_of_hom_inv_id cN.hom_inv_id
        simpa only [hM, hN] using inverseSquare cM.hom cN.hom b a hc
      have hp : b ≫ pN.hom = pM.hom ≫ d :=
        ih (SchemeQuasicoherentAffineEffacement.quotientMap U f)
      have hn : d ≫ nN.hom = nM.hom ≫ e := by
        ext x
        exact DFunLike.congr_fun (nativeConnecting_naturality U hU f q) x
      change a ≫ (cN.inv ≫ pN.hom ≫ nN.hom) =
        (cM.inv ≫ pM.hom ≫ nM.hom) ≫ e
      calc
        _ = cM.inv ≫ (b ≫ pN.hom) ≫ nN.hom := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ pN.hom ≫ nN.hom) hi.symm
        _ = cM.inv ≫ (pM.hom ≫ d) ≫ nN.hom := by rw [hp]
        _ = cM.inv ≫ pM.hom ≫ (nM.hom ≫ e) := by
          simpa only [Category.assoc] using
            congrArg (fun k => cM.inv ≫ pM.hom ≫ k) hn
        _ = _ := by simp only [Category.assoc]

private def zeroCyclesIso (hU : IsOpenCover U) (M : X.Modules) :
    (TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).obj M.sheaf ≅
      ((cechFunctor U).obj M).cycles 0 := by
  let : Mono (TopCat.Sheaf.cechGlobalSectionsNativeShortComplex U M.sheaf).f :=
    TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U M.sheaf hU
  exact IsLimit.conePointUniqueUpToIso
    (TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U M.sheaf hU).fIsKernel
    (((cechFunctor U).obj M).cyclesIsKernel 0 1 (by simp))

private theorem zeroCyclesIso_hom_iCycles (hU : IsOpenCover U) (M : X.Modules) :
    (zeroCyclesIso U hU M).hom ≫ ((cechFunctor U).obj M).iCycles 0 =
      TopCat.Sheaf.cechGlobalSectionsAugmentation M.sheaf U := by
  let : Mono (TopCat.Sheaf.cechGlobalSectionsNativeShortComplex U M.sheaf).f :=
    TopCat.Sheaf.cechGlobalSectionsAugmentation_mono U M.sheaf hU
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (TopCat.Sheaf.cechGlobalSectionsNativeShortComplex_exact U M.sheaf hU).fIsKernel
    (((cechFunctor U).obj M).cyclesIsKernel 0 1 (by simp)) WalkingParallelPair.zero

private theorem zeroCyclesIso_naturality (hU : IsOpenCover U)
    {M N : X.Modules} (f : M ⟶ N) :
    (TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).map ((Scheme.Modules.toSheaf X).map f) ≫
        (zeroCyclesIso U hU N).hom =
      (zeroCyclesIso U hU M).hom ≫ HomologicalComplex.cyclesMap ((cechFunctor U).map f) 0 := by
  apply (cancel_mono (((cechFunctor U).obj N).iCycles 0)).mp
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    zeroCyclesIso_hom_iCycles]
  rw [← Category.assoc, zeroCyclesIso_hom_iCycles]
  exact (TopCat.Sheaf.cechGlobalSectionsAugmentation_naturality (F := M.sheaf)
    (U := U) ((Scheme.Modules.toSheaf X).map f)).symm

private def zeroHomologyIso (hU : IsOpenCover U) (M : X.Modules) :
    (TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).obj M.sheaf ≅
      ((cechFunctor U).obj M).homology 0 :=
  zeroCyclesIso U hU M ≪≫ ((cechFunctor U).obj M).isoHomologyπ₀

private theorem zeroHomologyIso_naturality (hU : IsOpenCover U)
    {M N : X.Modules} (f : M ⟶ N) :
    (TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).map ((Scheme.Modules.toSheaf X).map f) ≫
        (zeroHomologyIso U hU N).hom =
      (zeroHomologyIso U hU M).hom ≫ HomologicalComplex.homologyMap ((cechFunctor U).map f) 0 := by
  change _ ≫ ((zeroCyclesIso U hU N).hom ≫ ((cechFunctor U).obj N).homologyπ 0) =
    ((zeroCyclesIso U hU M).hom ≫ ((cechFunctor U).obj M).homologyπ 0) ≫ _
  rw [← Category.assoc, zeroCyclesIso_naturality, Category.assoc,
    ← HomologicalComplex.homologyπ_naturality, ← Category.assoc]

private def sectionsNativeZeroIso (M : X.Modules) :
    (TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).obj M.sheaf ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} M.sheaf 0) :=
  (CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} isTerminalTop).app M.sheaf ≪≫
      (AddEquiv.toAddCommGrpIso
        (X := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} M.sheaf 0))
        (Y := M.sheaf.obj.obj (op ⊤))
        (CategoryTheory.Sheaf.H.equiv₀ M.sheaf isTerminalTop)).symm

private theorem sectionsNativeZeroIso_naturality {M N : X.Modules} (f : M ⟶ N) :
    (TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).map ((Scheme.Modules.toSheaf X).map f) ≫
        (sectionsNativeZeroIso N).hom =
      (sectionsNativeZeroIso M).hom ≫
        AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map.{u} ((Scheme.Modules.toSheaf X).map f) 0) := by
  let g := (Scheme.Modules.toSheaf X).map f
  let e := CategoryTheory.Sheaf.ΓNatIsoSheafSections (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} isTerminalTop
  ext x
  have he := ConcreteCategory.congr_hom (e.hom.naturality g) x
  change (e.app N.sheaf).hom
      ((TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).map g x) =
    g.hom.app (op ⊤) ((e.app M.sheaf).hom x) at he
  change (CategoryTheory.Sheaf.H.equiv₀ N.sheaf isTerminalTop).symm
      ((e.app N.sheaf).hom
        ((TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).map g x)) =
    CategoryTheory.Sheaf.H.map.{u} g 0
      ((CategoryTheory.Sheaf.H.equiv₀ M.sheaf isTerminalTop).symm ((e.app M.sheaf).hom x))
  rw [he]
  exact (CategoryTheory.Sheaf.H.equiv₀_symm_naturality (f := g) isTerminalTop _).symm

/-- The actual degree-zero Cech homology computes genuine small native cohomology. -/
def zeroComparison (hU : IsOpenCover U) (M : X.Modules) :
    ((cechFunctor U).obj M).homology 0 ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} M.sheaf 0) :=
  (zeroHomologyIso U hU M).symm ≪≫ sectionsNativeZeroIso M

/-- The degree-zero comparison retains the entire original module map. -/
theorem zeroComparison_naturality (hU : IsOpenCover U)
    {M N : X.Modules} (f : M ⟶ N) :
    HomologicalComplex.homologyMap ((cechFunctor U).map f) 0 ≫ (zeroComparison U hU N).hom =
      (zeroComparison U hU M).hom ≫
        AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map.{u} ((Scheme.Modules.toSheaf X).map f) 0) := by
  let g := (TopCat.Sheaf.globalSectionsFunctor (TopCat.of X)).map ((Scheme.Modules.toSheaf X).map f)
  let c := HomologicalComplex.homologyMap ((cechFunctor U).map f) 0
  let n := AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map.{u} ((Scheme.Modules.toSheaf X).map f) 0)
  let eM := zeroHomologyIso U hU M
  let eN := zeroHomologyIso U hU N
  have hi : eM.inv ≫ g = c ≫ eN.inv := by
    have hM : inv eM.hom = eM.inv := IsIso.inv_eq_of_hom_inv_id eM.hom_inv_id
    have hN : inv eN.hom = eN.inv := IsIso.inv_eq_of_hom_inv_id eN.hom_inv_id
    simpa only [hM, hN] using inverseSquare eM.hom eN.hom g c (zeroHomologyIso_naturality U hU f)
  change c ≫ (eN.inv ≫ (sectionsNativeZeroIso N).hom) =
    (eM.inv ≫ (sectionsNativeZeroIso M).hom) ≫ n
  rw [← Category.assoc, ← hi, Category.assoc, sectionsNativeZeroIso_naturality,
    ← Category.assoc]

/-- Genuine native additive Cech cohomology comparison in every degree. -/
def comparison [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    ((cechFunctor U).obj M).homology q ≅ AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u} M.sheaf q) :=
  match q with
  | 0 => zeroComparison U hU M
  | q + 1 => positiveComparison U hU hUa q M

/-- The all-degree comparison retains the whole original cohomology map. -/
theorem comparison_naturality [X.IsSeparated] [Finite I]
    (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i)) (q : ℕ)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    HomologicalComplex.homologyMap ((cechFunctor U).map f) q ≫ (comparison U hU hUa q N).hom =
      (comparison U hU hUa q M).hom ≫
        AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map.{u} ((Scheme.Modules.toSheaf X).map f) q) := by
  cases q with
  | zero => exact zeroComparison_naturality U hU f
  | succ q => exact positiveComparison_naturality U hU hUa q f

end EnvelopeProperty.SchemeModuleCechNativeCohomology
