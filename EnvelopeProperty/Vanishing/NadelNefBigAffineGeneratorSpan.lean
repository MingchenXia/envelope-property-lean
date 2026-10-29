import EnvelopeProperty.Vanishing.NadelNefBigGlobalFrames
import Mathlib.LinearAlgebra.Quotient.Defs

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigAffineGeneratorSpan
open SchemeGeneratingSectionsUnit

private theorem map_inverse_counit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {H : D ⥤ C} (a : F ⊣ H) (M : D) {N : C}
    [IsIso (a.counit.app M)] (q : H.obj M ⟶ N) :
    H.map (inv (a.counit.app M) ≫ F.map q) = q ≫ a.unit.app N := by
  have hc : H.map (inv (a.counit.app M)) ≫ H.map (a.counit.app M) = 𝟙 _ := by
    rw [← H.map_comp, IsIso.inv_hom_id, H.map_id]
  have ht : H.map (inv (a.counit.app M)) = a.unit.app (H.obj M) :=
    (cancel_mono (H.map (a.counit.app M))).mp (hc.trans (a.right_triangle_components M).symm)
  exact (H.map_comp _ _).trans ((congrArg (fun t => t ≫ H.map (F.map q)) ht).trans
    (a.unit.naturality q).symm)

private theorem unit_hom_ext_top {X : Scheme.{u}} {M : X.Modules}
    {a b : unitObj X ⟶ M}
    (h : a.val.app (op ⊤) (1 : Γ(X, ⊤)) = b.val.app (op ⊤) (1 : Γ(X, ⊤))) : a = b := by
  apply SheafOfModules.hom_ext
  ext U
  let i := (homOfLE (le_top : U.unop ≤ (⊤ : X.Opens))).op
  have ha := PresheafOfModules.naturality_apply a.val i (1 : Γ(X, ⊤))
  have hb := PresheafOfModules.naturality_apply b.val i (1 : Γ(X, ⊤))
  change a.val.app U (X.presheaf.map i (1 : Γ(X, ⊤))) =
    M.presheaf.map i (a.val.app (op ⊤) (1 : Γ(X, ⊤))) at ha
  change b.val.app U (X.presheaf.map i (1 : Γ(X, ⊤))) =
    M.presheaf.map i (b.val.app (op ⊤) (1 : Γ(X, ⊤))) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (fun t => M.presheaf.map i t) h).trans hb.symm)

private theorem triple_comp_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) : a ≫ b ≫ (0 : D ⟶ E) = 0 := by
  rw [comp_zero, comp_zero]

private theorem hom_zero_of_generators {X : Scheme.{u}} {M N : X.Modules}
    (G : M.GeneratingSections) (q : M ⟶ N) (h : ∀ i, generatorHom G i ≫ q = 0) : q = 0 := by
  apply G.epi.left_cancellation
  apply Sigma.hom_ext
  intro i
  change (SheafOfModules.ιFree i ≫ G.π) ≫ q = _
  exact (h i).trans (triple_comp_zero (SheafOfModules.ιFree i) G.π).symm


def generatorValue {A : CommRingCat.{u}} (M : (Spec (.of A)).Modules)
    (G : M.GeneratingSections) (i : G.I) :
    (moduleSpecΓFunctor (R := A)).obj M :=
  (generatorHom G i).val.app (op ⊤) (1 : Γ(Spec (.of A), ⊤))

private opaque mapFromGlobalsData {A : CommRingCat.{u}}
    (M : (Spec (.of A)).Modules) [M.IsQuasicoherent] {N : ModuleCat A}
    (q : (moduleSpecΓFunctor (R := A)).obj M ⟶ N) :
    { r : M ⟶ (tilde.functor (A)).obj N //
      (moduleSpecΓFunctor (R := A)).map r =
        q ≫ (tilde.adjunction (R := A)).unit.app N ∧
      (tilde.adjunction (R := A)).counit.app M ≫ r =
        (tilde.functor (A)).map q } := by
  let F := tilde.functor (A)
  let c : F.obj ((moduleSpecΓFunctor (R := A)).obj M) ⟶ M :=
    (tilde.adjunction (R := A)).counit.app M
  let : IsIso c := inferInstanceAs (IsIso M.fromTildeΓ)
  refine ⟨inv c ≫ F.map q, map_inverse_counit
    (tilde.adjunction (R := A)) M q, ?_⟩
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

theorem linearMap_eq_zero_of_generatorValues {A : CommRingCat.{u}}
    (M : (Spec (.of A)).Modules) [M.IsQuasicoherent] (G : M.GeneratingSections)
    {N : ModuleCat A} (q : (moduleSpecΓFunctor (R := A)).obj M ⟶ N)
    (hq : ∀ i, q.hom (generatorValue M G i) = 0) : q = 0 := by
  let F := tilde.functor (A)
  let c := (tilde.adjunction (R := A)).counit.app M
  let d := mapFromGlobalsData M q
  let r := d.val
  have hΓ : (moduleSpecΓFunctor (R := A)).map r =
      q ≫ (tilde.adjunction (R := A)).unit.app N := d.property.1
  have hr : r = 0 := by
    apply hom_zero_of_generators G r
    intro i
    apply unit_hom_ext_top
    have h := ConcreteCategory.congr_hom hΓ (generatorValue M G i)
    change r.val.app (op ⊤) (generatorValue M G i) =
      ((tilde.adjunction (R := A)).unit.app N).hom
        (q.hom (generatorValue M G i)) at h
    rw [hq i, map_zero] at h
    exact h
  have hfac : c ≫ r = F.map q := d.property.2
  have hFq : F.map q = 0 := hfac.symm.trans ((congrArg (fun t => c ≫ t) hr).trans comp_zero)
  exact F.map_injective (hFq.trans (F.map_zero _ _).symm)

/-- Actual original basis values span the entire original affine global module. -/
theorem span_generatorValues_eq_top {A : CommRingCat.{u}}
    (M : (Spec (.of A)).Modules) [M.IsQuasicoherent] (G : M.GeneratingSections) :
    Submodule.span A (Set.range (generatorValue M G)) = ⊤ := by
  let V : ModuleCat A := (moduleSpecΓFunctor (R := A)).obj M
  let S := Submodule.span A (Set.range (generatorValue M G))
  let N : ModuleCat A := ModuleCat.of A (V ⧸ S)
  let q : V ⟶ N := by
    change ModuleCat.of A V ⟶ ModuleCat.of A (V ⧸ S)
    exact ModuleCat.ofHom S.mkQ
  have hq : q = 0 := linearMap_eq_zero_of_generatorValues M G q (fun i =>
    (Submodule.Quotient.mk_eq_zero S).mpr (Submodule.subset_span ⟨i, rfl⟩))
  apply top_unique
  intro x _hx
  have hz : q.hom x = 0 := ConcreteCategory.congr_hom hq x
  exact (Submodule.Quotient.mk_eq_zero S).mp hz
end EnvelopeProperty.Vanishing.NadelNefBigAffineGeneratorSpan
