import EnvelopeProperty.Cartier.DeligneIllusieCechCupProduct

/-! # Ordered products in the original all-tuple sheaf Čech complex

Prefix and suffix tuples share their joining vertex.  All maps use the
published original restriction--pushforward factors and original exterior
products; no multiplication on a replacement Čech model is supplied.
-/

noncomputable section
universe u
namespace EnvelopeProperty.DI.CechAlexanderWhitneyProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieCechCupProduct

/-- The prefix of the original ordered Alexander--Whitney tuple. -/
def tuplePrefix (j j' : ℕ) : Fin (j+1) → Fin (j+j'+1) :=
  fun a => ⟨a.val, by omega⟩

/-- The suffix starts at the last vertex of the prefix. -/
def tupleSuffix (j j' : ℕ) : Fin (j'+1) → Fin (j+j'+1) :=
  fun a => ⟨j+a.val, by omega⟩

variable {Z : Scheme.{u}} {ι : Type u} (U : ι → Z.Opens)

/-- The full original intersection lies in its actual prefix intersection. -/
theorem tupleOpen_le_prefix (j j' : ℕ) (i : Fin (j+j'+1) → ι) :
    (∏ᶜ fun a : Fin (j+j'+1) => U (i a)) ≤
      ∏ᶜ fun a : Fin (j+1) => U ((i ∘ tuplePrefix j j') a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower (tuplePrefix j j')).φ i)

/-- The full original intersection lies in its actual suffix intersection. -/
theorem tupleOpen_le_suffix (j j' : ℕ) (i : Fin (j+j'+1) → ι) :
    (∏ᶜ fun a : Fin (j+j'+1) => U (i a)) ≤
      ∏ᶜ fun a : Fin (j'+1) => U ((i ∘ tupleSuffix j j') a) :=
  leOfHom (((FormalCoproduct.mk _ U).mapPower (tupleSuffix j j')).φ i)

/-- The original cut open used by the published restriction--pushforward factor. -/
abbrev factorCut (V W : Z.Opens) : Z.Opens := V.ι ''ᵁ (V.ι ⁻¹ᵁ W)

private theorem factorCut_le (V W : Z.Opens) : factorCut V W ≤ W :=
  V.ι.image_preimage_le W

private theorem factorSection_smul (M : Z.Modules) (V W : Z.Opens) (c : Γ(Z,W))
    (s : Γ(factor M V,W)) :
    (c • s : Γ(factor M V,W)) =
      (show Γ(M,factorCut V W) from
        Z.presheaf.map (homOfLE (factorCut_le V W)).op c •
          (show Γ(M,factorCut V W) from s)) := by
  change (V.ι.appIso (V.ι ⁻¹ᵁ W)).inv ((V.ι.app W).hom c) •
      (show Γ(M,factorCut V W) from s) = _
  exact congrArg (fun a : Γ(Z,factorCut V W) => a •
    (show Γ(M,factorCut V W) from s))
    (ConcreteCategory.congr_hom (V.ι.app_appIso_inv W) c)

set_option backward.isDefEq.respectTransparency false in
local instance factorOriginalSectionModule (M : Z.Modules) (W : Z.Opens) :
    Module Γ(Z,W) Γ(M,W) := (M.val.obj (op W)).isModule

private def factorValue (M N P : Z.Modules)
    (μ : ∀ C : Z.Opens, Γ(M,C) →ₗ[Γ(Z,C)] Γ(N,C) →ₗ[Γ(Z,C)] Γ(P,C))
    (V W : Z.Opens) (a : Γ(factor M V,W)) (b : Γ(factor N V,W)) :
    Γ(factor P V,W) := μ (factorCut V W) a b

private theorem factorValue_smul_left (M N P : Z.Modules)
    (μ : ∀ C : Z.Opens, Γ(M,C) →ₗ[Γ(Z,C)] Γ(N,C) →ₗ[Γ(Z,C)] Γ(P,C))
    (V W : Z.Opens) (c : Γ(Z,W)) (a : Γ(factor M V,W)) (b : Γ(factor N V,W)) :
    factorValue M N P μ V W (c • a) b = c • factorValue M N P μ V W a b := by
  let C := factorCut V W
  let ρ := Z.presheaf.map (homOfLE (factorCut_le V W)).op
  have hl : μ C (c • a : Γ(factor M V,W)) b =
      μ C (ρ c • (show Γ(M,C) from a)) b :=
    congrArg (fun t : Γ(M,C) => μ C t b) (factorSection_smul M V W c a)
  have hr := factorSection_smul P V W c
    (show Γ(factor P V,W) from μ C a b)
  exact hl.trans ((LinearMap.congr_fun
    (map_smul (μ C) (ρ c) (show Γ(M,C) from a))
    (show Γ(N,C) from b)).trans hr.symm)

private theorem factorValue_smul_right (M N P : Z.Modules)
    (μ : ∀ C : Z.Opens, Γ(M,C) →ₗ[Γ(Z,C)] Γ(N,C) →ₗ[Γ(Z,C)] Γ(P,C))
    (V W : Z.Opens) (c : Γ(Z,W)) (a : Γ(factor M V,W)) (b : Γ(factor N V,W)) :
    factorValue M N P μ V W a (c • b) = c • factorValue M N P μ V W a b := by
  let C := factorCut V W
  let ρ := Z.presheaf.map (homOfLE (factorCut_le V W)).op
  have hl : μ C a (c • b : Γ(factor N V,W)) =
      μ C a (ρ c • (show Γ(N,C) from b)) :=
    congrArg (fun t : Γ(N,C) => μ C a t) (factorSection_smul N V W c b)
  have hr := factorSection_smul P V W c
    (show Γ(factor P V,W) from μ C a b)
  exact hl.trans ((map_smul (μ C a) (ρ c)
    (show Γ(N,C) from b)).trans hr.symm)

private def factorSectionPairing (M N P : Z.Modules)
    (μ : ∀ C : Z.Opens, Γ(M,C) →ₗ[Γ(Z,C)] Γ(N,C) →ₗ[Γ(Z,C)] Γ(P,C))
    (V W : Z.Opens) :
    Γ(factor M V,W) →ₗ[Γ(Z,W)]
      Γ(factor N V,W) →ₗ[Γ(Z,W)] Γ(factor P V,W) :=
  LinearMap.mk₂ Γ(Z,W) (factorValue M N P μ V W)
    (fun a b c => LinearMap.congr_fun (map_add (μ (factorCut V W)) a b) c)
    (factorValue_smul_left M N P μ V W)
    (fun a b c => map_add (μ (factorCut V W) a) b c)
    (factorValue_smul_right M N P μ V W)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
local notation "Y" => Cartier.SchemeRelativeFrobenius.twist p f
local notation "E" q => Cartier.SchemeRelativeFrobeniusDeRham.formModule f p q

/-- The actual whole exterior product on a SAME original Čech factor.  The
ambient scalar acts by the actual restriction to its cut open. -/
def factorWedge (q r : ℕ) (V W : (Y).Opens) :
    Γ(factor (E q) V,W) →ₗ[Γ(Y,W)]
      Γ(factor (E r) V,W) →ₗ[Γ(Y,W)] Γ(factor (E (r+q)) V,W) :=
  factorSectionPairing (E q) (E r) (E (r+q)) (formWedge f p q r) V W

/-- Every pair of original factor sections retains its literal original wedge. -/
theorem factorWedge_apply (q r : ℕ) (V W : (Y).Opens)
    (a : Γ(factor (E q) V,W)) (b : Γ(factor (E r) V,W)) :
    factorWedge f p q r V W a b = formWedge f p q r (factorCut V W) a b := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The factor pairing commutes with every original ambient-open restriction. -/
theorem factorWedge_restrict (q r : ℕ) (V : (Y).Opens) {W Z : (Y).Opens}
    (i : W ⟶ Z) (a : Γ(factor (E q) V,Z)) (b : Γ(factor (E r) V,Z)) :
    (factor (E (r+q)) V).val.map i.op (factorWedge f p q r V Z a b) =
      factorWedge f p q r V W ((factor (E q) V).val.map i.op a)
        ((factor (E r) V).val.map i.op b) := by
  exact formWedge_restrict f p q r
    (V.ι.opensFunctor.map ((Opens.map V.ι.base).map i)) a b

set_option backward.isDefEq.respectTransparency false in
local instance nativePresheafModule (P : (Y).PresheafOfModules) (W : (Y).Opensᵒᵖ) :
    Module ((Y).presheaf.obj W) (P.obj W) := (P.obj W).isModule

local instance nativeRing (W : (Y).Opensᵒᵖ) : CommRing ((Y).ringCatSheaf.obj.obj W) :=
  inferInstanceAs (CommRing ((Y).presheaf.obj W))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire original factor pairing is a genuine morphism out of the
original tensor presheaf. -/
def factorWedgePresheaf (q r : ℕ) (V : (Y).Opens) :
    CanonicalGeometry.bundleTensorPresheaf (factor (E q) V) (factor (E r) V) ⟶
      (factor (E (r+q)) V).val where
  app W := ModuleCat.ofHom
    (X := (CanonicalGeometry.bundleTensorPresheaf (factor (E q) V) (factor (E r) V)).obj W)
    («Y» := (factor (E (r+q)) V).val.obj W)
    (TensorProduct.lift (factorWedge f p q r V W.unop))
  naturality {W Z} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    exact (factorWedge_restrict f p q r V i.unop a b).symm

/-- Every original raw tensor keeps the original whole-section factor product. -/
theorem factorWedgePresheaf_tmul (q r : ℕ) (V W : (Y).Opens)
    (a : Γ(factor (E q) V,W)) (b : Γ(factor (E r) V,W)) :
    (factorWedgePresheaf f p q r V).app (op W) (a ⊗ₜ[Γ(Y,W)] b) =
      factorWedge f p q r V W a b := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual sheafification adjunction extends the original factor pairing
after two original module maps, without supplying a map on the tensor sheaf. -/
def factorWedgeAlong (q r : ℕ) (V : (Y).Opens) {A B : (Y).Modules}
    (a : A ⟶ factor (E q) V) (b : B ⟶ factor (E r) V) :
    CanonicalGeometry.bundleTensor A B ⟶ factor (E (r+q)) V :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (Y).ringCatSheaf.obj)).homEquiv
    (CanonicalGeometry.bundleTensorPresheaf A B) (factor (E (r+q)) V)).symm
    ((a.val ⊗ₘ b.val) ≫ factorWedgePresheaf f p q r V)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual factor tensor map retains EVERY pair of original whole sections. -/
theorem factorWedgeAlong_tensorSection (q r : ℕ) (V W : (Y).Opens)
    {A B : (Y).Modules} (a : A ⟶ factor (E q) V) (b : B ⟶ factor (E r) V)
    (x : Γ(A,W)) (y : Γ(B,W)) :
    (factorWedgeAlong f p q r V a b).val.app (op W)
        (CanonicalGeometry.tensorSection A B W x y) =
      factorWedge f p q r V W (a.val.app (op W) x) (b.val.app (op W) y) := by
  have h := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Y).ringCatSheaf.obj)).homEquiv
    (CanonicalGeometry.bundleTensorPresheaf A B) (factor (E (r+q)) V)).apply_symm_apply
      ((a.val ⊗ₘ b.val) ≫ factorWedgePresheaf f p q r V)
  have h' := congrArg (fun z => z.app (op W) (x ⊗ₜ[Γ(Y,W)] y)) h
  change (factorWedgeAlong f p q r V a b).val.app (op W)
      (CanonicalGeometry.tensorSection A B W x y) =
    (factorWedgePresheaf f p q r V).app (op W)
      ((a.val ⊗ₘ b.val).app (op W) (x ⊗ₜ[Γ(Y,W)] y)) at h'
  have ht : (a.val ⊗ₘ b.val).app (op W) (x ⊗ₜ[Γ(Y,W)] y) =
      (a.val.app (op W) x) ⊗ₜ[Γ(Y,W)] (b.val.app (op W) y) := rfl
  rw [ht] at h'
  exact h'

end EnvelopeProperty.DI.CechAlexanderWhitneyProduct
