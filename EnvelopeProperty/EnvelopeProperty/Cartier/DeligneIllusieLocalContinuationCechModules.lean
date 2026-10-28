import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # The genuine structure-sheaf-linear Cech complex of an actual scheme module -/
noncomputable section
namespace EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechModules
open CategoryTheory Category Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
universe u
variable {X : Scheme.{u}}

private abbrev cut (U W : X.Opens) : X.Opens := U.ι ''ᵁ (U.ι ⁻¹ᵁ W)
private theorem cut_le (U W : X.Opens) : cut U W ≤ W := U.ι.image_preimage_le W
private theorem cut_mono {U V : X.Opens} (h : U ≤ V) (W : X.Opens) : cut U W ≤ cut V W := by
  simpa only [cut, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    using inf_le_inf_right W h

private abbrev cutRestriction (U : X.Opens) {W Z : X.Opensᵒᵖ} (f : W ⟶ Z) :
    op (cut U W.unop) ⟶ op (cut U Z.unop) :=
  U.ι.opensFunctor.op.map ((Opens.map U.ι.base).op.map f)

/-- The EXISTING actual scheme-module restriction and pushforward, retaining O_X actions. -/
def factor (M : X.Modules) (U : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward U.ι).obj (M.restrict U.ι)

private theorem factor_smul (M : X.Modules) (U W : X.Opens) (r : Γ(X, W))
    (m : Γ(factor M U, W)) :
    (r • m : Γ(factor M U, W)) =
      (show Γ(M, cut U W) from
        X.presheaf.map (homOfLE (cut_le U W)).op r • (show Γ(M, cut U W) from m)) := by
  change (U.ι.appIso (U.ι ⁻¹ᵁ W)).inv ((U.ι.app W).hom r) •
      (show Γ(M, cut U W) from m) = _
  exact congrArg (fun s : Γ(X, cut U W) => s • (show Γ(M, cut U W) from m))
    (ConcreteCategory.congr_hom (U.ι.app_appIso_inv W) r)

private def factorSectionMap (M : X.Modules) {U V : X.Opens} (h : U ≤ V) (W : X.Opens) :
    (factor M V).val.obj (op W) →ₗ[X.ringCatSheaf.obj.obj (op W)]
      (factor M U).val.obj (op W) := by
  refine
    { toFun := fun m => M.presheaf.map (homOfLE (cut_mono h W)).op m
      map_add' := map_add _
      map_smul' := ?_ }
  intro r m
  let r₀ : Γ(X, W) := r
  let m₀ : Γ(factor M V, W) := m
  let ρ : Γ(M, cut V W) →+ Γ(M, cut U W) :=
    (M.presheaf.map (homOfLE (cut_mono h W)).op).hom
  have hr : X.presheaf.map (homOfLE (cut_mono h W)).op
      (X.presheaf.map (homOfLE (cut_le V W)).op r₀) =
    X.presheaf.map (homOfLE (cut_le U W)).op r₀ := by
    rw [← Functor.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (X.presheaf.congr_map (Subsingleton.elim _ _)) r₀
  have hleft := congrArg
    (fun z : Γ(factor M V, W) => ρ (show Γ(M, cut V W) from z))
    (factor_smul M V W r₀ m₀)
  have hmid : ρ (X.presheaf.map (homOfLE (cut_le V W)).op r₀ •
        (show Γ(M, cut V W) from m₀)) =
      X.presheaf.map (homOfLE (cut_le U W)).op r₀ •
        ρ (show Γ(M, cut V W) from m₀) := by
    exact (Scheme.Modules.map_smul M (homOfLE (cut_mono h W))
      (X.presheaf.map (homOfLE (cut_le V W)).op r₀)
      (show Γ(M, cut V W) from m₀)).trans
        (congrArg (fun z : Γ(X, cut U W) =>
          z • ρ (show Γ(M, cut V W) from m₀)) hr)
  have hright := factor_smul M U W r₀
    (show Γ(factor M U, W) from ρ (show Γ(M, cut V W) from m₀))
  exact hleft.trans (hmid.trans hright.symm)

private theorem factorSectionMap_apply (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (W : X.Opens) (m : Γ(factor M V, W)) :
    factorSectionMap M h W m =
      M.presheaf.map (homOfLE (cut_mono h W)).op (show Γ(M, cut V W) from m) := rfl

/-- Actual original section restriction constructs a genuine O_X-linear factor map. -/
def factorMap (M : X.Modules) {U V : X.Opens} (h : U ≤ V) : factor M V ⟶ factor M U := by
  refine ⟨
    { app := fun W =>
        ModuleCat.ofHom (X := (factor M V).val.obj W) (Y := (factor M U).val.obj W)
          (factorSectionMap M h W.unop)
      naturality := ?_ }⟩
  intro W Z f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change factorSectionMap M h Z.unop ((factor M V).presheaf.map f m) =
    (factor M U).presheaf.map f (factorSectionMap M h W.unop m)
  let m₀ : Γ(factor M V, W.unop) := m
  have hleft := factorSectionMap_apply M h Z.unop ((factor M V).presheaf.map f m₀)
  have hright := congrArg
    (fun z : Γ(factor M U, W.unop) => (factor M U).presheaf.map f z)
    (factorSectionMap_apply M h W.unop m₀)
  have hmid : M.presheaf.map (homOfLE (cut_mono h Z.unop)).op
        (show Γ(M, cut V Z.unop) from (factor M V).presheaf.map f m₀) =
      (factor M U).presheaf.map f
        (show Γ(factor M U, W.unop) from
          M.presheaf.map (homOfLE (cut_mono h W.unop)).op (show Γ(M, cut V W.unop) from m₀)) := by
    change M.presheaf.map (homOfLE (cut_mono h Z.unop)).op
        (M.presheaf.map (cutRestriction V f) (show Γ(M, cut V W.unop) from m₀)) =
      M.presheaf.map (cutRestriction U f)
        (M.presheaf.map (homOfLE (cut_mono h W.unop)).op
          (show Γ(M, cut V W.unop) from m₀))
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (M.presheaf.congr_map (Subsingleton.elim _ _)) (show Γ(M, cut V W.unop) from m₀)
  exact hleft.trans (hmid.trans hright.symm)

/-- EVERY native component is EXACTLY the SAME original M restriction between the actual cut opens. -/
theorem factorMap_app (M : X.Modules) {U V : X.Opens} (h : U ≤ V) (W : X.Opens) :
    (factorMap M h).app W = M.presheaf.map (homOfLE (cut_mono h W)).op := rfl

/-- Genuine factor restriction preserves the actual identity morphism. -/
theorem factorMap_id (M : X.Modules) (U : X.Opens) : factorMap M (le_refl U) = 𝟙 (factor M U) := by
  apply Scheme.Modules.hom_ext
  intro W
  rw [factorMap_app, Scheme.Modules.Hom.id_app]
  rw [show (homOfLE (cut_mono (le_refl U) W)).op = 𝟙 (op (cut U W)) from Subsingleton.elim _ _]
  exact M.presheaf.map_id _

/-- Genuine factor restrictions compose by the SAME original section restrictions. -/
theorem factorMap_comp (M : X.Modules) {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    factorMap M hVW ≫ factorMap M hUV = factorMap M (hUV.trans hVW) := by
  apply Scheme.Modules.hom_ext
  intro Z
  apply ConcreteCategory.hom_ext
  intro m
  change M.presheaf.map (homOfLE (cut_mono hUV Z)).op
      (M.presheaf.map (homOfLE (cut_mono hVW Z)).op (show Γ(M, cut W Z) from m)) =
    M.presheaf.map (homOfLE (cut_mono (hUV.trans hVW) Z)).op (show Γ(M, cut W Z) from m)
  rw [← Functor.map_comp_apply]
  exact ConcreteCategory.congr_hom
    (M.presheaf.congr_map (Subsingleton.elim _ _)) (show Γ(M, cut W Z) from m)

/-- The genuine original factors form an actual presheaf with values in X.Modules itself. -/
def factorPresheaf (M : X.Modules) : X.Opensᵒᵖ ⥤ X.Modules where
  obj U := factor M U.unop
  map f := factorMap M (leOfHom f.unop)
  map_id U := factorMap_id M U.unop
  map_comp f g := (factorMap_comp M (leOfHom g.unop) (leOfHom f.unop)).symm

variable (M : X.Modules) {ι : Type u} (U : ι → X.Opens)

/-- The EXISTING native Cech functor evaluated in the ORIGINAL ringed-module category. -/
def complex : CochainComplex X.Modules ℕ := (cechComplexFunctor U).obj (factorPresheaf M)

/-- Native degree q is the ACTUAL product of original pushforward-restriction factors. -/
theorem complex_X (q : ℕ) : (complex M U).X q =
    ∏ᶜ (fun i : Fin (q+1) → ι => factor M (∏ᶜ fun k : Fin (q+1) => U (i k))) := rfl

private theorem tuple_le (q : ℕ) (k : Fin (q+2)) (i : Fin (q+2) → ι) :
    (∏ᶜ fun a : Fin (q+2) => U (i a)) ≤
      ∏ᶜ fun a : Fin (q+1) => U ((i ∘ (SimplexCategory.δ k).toOrderHom.toFun) a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i)

/-- Each original Cech coface projects to the deleted tuple and uses ACTUAL factor restriction. -/
def coface (q : ℕ) (k : Fin (q+2)) : (complex M U).X q ⟶ (complex M U).X (q+1) :=
  Pi.lift (fun i : Fin (q+2) → ι =>
    Pi.π (fun j : Fin (q+1) → ι => factor M (∏ᶜ fun a : Fin (q+1) => U (j a)))
        (i ∘ (SimplexCategory.δ k).toOrderHom.toFun) ≫
      factorMap M (tuple_le U q k i))

private theorem nativeCoface_eq (q : ℕ) (k : Fin (q+2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj (factorPresheaf M)).δ k = coface M U q k := by
  rw [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map, FormalCoproduct.cech_map]
  rfl

/-- The ENTIRE native differential is the alternating sum of the actual original cofaces. -/
theorem complex_d (q : ℕ) : (complex M U).d q (q+1) =
    ∑ k : Fin (q+2), (-1 : ℤ)^(k : ℕ) • coface M U q k := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj (factorPresheaf M)).d q (q+1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  refine (CochainComplex.of_d _ _ q).trans ?_
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  exact Finset.sum_congr rfl (fun k _ =>
    congrArg (fun f => (-1 : ℤ)^(k : ℕ) • f) (nativeCoface_eq M U q k))

end EnvelopeProperty.Cartier.DeligneIllusieLocalContinuationCechModules
