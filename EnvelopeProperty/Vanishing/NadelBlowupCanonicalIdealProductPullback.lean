import EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductFrame
import EnvelopeProperty.Vanishing.NadelBlowupCanonicalSquareTensor

/-! # Whole actual ideal-product multiplication under genuine original open pullback -/

open AlgebraicGeometry CategoryTheory
open Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductPullback
open NadelBlowupCanonicalIdealProductFrame NadelBlowupCanonicalSquareTensor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem three_squares {C : Type*} [Category C] {S T U V W Q Z : C}
    (a : S ⟶ T) (b : T ⟶ U) (c : U ⟶ V) (d : V ⟶ W)
    (e : T ⟶ Q) (i : Q ⟶ V) (g : Q ⟶ Z) (u : Z ⟶ W) (f : S ⟶ Q) (z : S ⟶ Z)
    (h₁ : b ≫ c = e ≫ i) (h₂ : i ≫ d = g ≫ u) (h₃ : a ≫ e = f) (h₄ : z = f ≫ g) :
    (a ≫ b) ≫ (c ≫ d) = z ≫ u := by
  calc
    _ = a ≫ (b ≫ c) ≫ d := by simp only [Category.assoc]
    _ = a ≫ (e ≫ i) ≫ d := by rw [h₁]
    _ = (a ≫ e) ≫ (i ≫ d) := by simp only [Category.assoc]
    _ = f ≫ (g ≫ u) := by rw [h₂, h₃]
    _ = z ≫ u := by rw [h₄, Category.assoc]

private theorem ideal_eq_inclusion {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.toModules h)).hom ≫ J.toModulesInclusion =
      I.toModulesInclusion := by
  subst J
  exact Category.id_comp _

private theorem transfer_factor {C : Type*} [Category C] {S T K L W V : C}
    (a : S ≅ T) (b : K ≅ L) (u : W ≅ V) (i : K ⟶ W) (j : L ⟶ V)
    (δ : S ⟶ W) (D : T ⟶ V) (hT : a.hom ≫ D = δ ≫ u.hom)
    (hB : b.hom ≫ j = i ≫ u.hom)
    (hC : ∃ c : T ≅ L, c.hom ≫ j = D) : ∃ e : S ≅ K, e.hom ≫ i = δ := by
  obtain ⟨c, hc⟩ := hC
  refine ⟨a ≪≫ c ≪≫ b.symm, ?_⟩
  apply (cancel_mono u.hom).mp
  have hb : b.inv ≫ i ≫ u.hom = j := by
    rw [← hB, b.inv_hom_id_assoc]
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hb, hc] using hT

variable {X Y : Scheme.{u}} (q : Y ⟶ X) [IsOpenImmersion q] (I J : X.IdealSheafData)

/-- The actual original tensor of geometric ideals retains both genuine
whole ideal-module comparisons under the original open immersion. -/
def tensorOpenPullbackIso :
    (pullback q).obj (Scheme.Modules.tensorObj I.toModules J.toModules) ≅
      Scheme.Modules.tensorObj (I.comap q).toModules (J.comap q).toModules :=
  SchemeTensorIdealPullback.idealTensorOpenPullbackIso q I.toModules J ≪≫
    tensorObjCongr (I.openPullbackModuleIso q) (Iso.refl _)

/-- This SAME tensor comparison preserves the ENTIRE actual original
multiplication inclusion and the SAME original pullback unit. -/
theorem tensorOpenPullbackIso_inclusion :
    (tensorOpenPullbackIso q I J).hom ≫ multiplicationIntoUnit (I.comap q) (J.comap q) =
      (pullback q).map (multiplicationIntoUnit I J) ≫ (pullbackUnitIso q).hom := by
  let F := pullback q
  let eR := SchemeTensorIdealPullback.idealTensorOpenPullbackIso q I.toModules J
  let eI := I.openPullbackModuleIso q
  exact three_squares eR.hom (tensorObjCongr eI (Iso.refl _)).hom
    (SchemeTensorObjMorphisms.tensorObjIdealMap _ _ (J.comap q).toModulesInclusion)
    (I.comap q).toModulesInclusion
    (SchemeTensorObjMorphisms.tensorObjIdealMap _ _ (J.comap q).toModulesInclusion)
    eI.hom (F.map I.toModulesInclusion) (pullbackUnitIso q).hom
    (F.map (SchemeTensorObjMorphisms.tensorObjIdealMap _ _ J.toModulesInclusion))
    (F.map (multiplicationIntoUnit I J))
    (tensorLeftIso_inclusion eI (J.comap q))
    (I.toModulesComapPullbackMap_inclusion q)
    (SchemeTensorIdealPullback.idealTensorOpenPullbackIso_inclusion q I.toModules J)
    (F.map_comp _ _)

/-- The SAME actual geometric product module retains its whole original
open pullback, using genuine geometric ideal-product comap equality. -/
def productOpenPullbackIso :
    (pullback q).obj (I * J).toModules ≅ ((I.comap q) * (J.comap q)).toModules :=
  (I * J).openPullbackModuleIso q ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.toModules (Scheme.IdealSheafData.comap_mul I J q))

/-- The actual product comparison retains its ENTIRE original inclusion. -/
theorem productOpenPullbackIso_inclusion :
    (productOpenPullbackIso q I J).hom ≫ ((I.comap q) * (J.comap q)).toModulesInclusion =
      (pullback q).map (I * J).toModulesInclusion ≫ (pullbackUnitIso q).hom := by
  simp only [productOpenPullbackIso, Iso.trans_hom, Category.assoc]
  rw [ideal_eq_inclusion (Scheme.IdealSheafData.comap_mul I J q)]
  exact (I * J).toModulesComapPullbackMap_inclusion q

/-- A genuine local product factor transports to the actual original
whole open pullbacks, preserving the actual multiplication equation.
The global geometric producer constructs this premise from actual generators. -/
theorem factor_pullback_of_local_factor
    (hc : ∃ c : Scheme.Modules.tensorObj (I.comap q).toModules (J.comap q).toModules ≅
        ((I.comap q) * (J.comap q)).toModules,
      c.hom ≫ ((I.comap q) * (J.comap q)).toModulesInclusion =
        multiplicationIntoUnit (I.comap q) (J.comap q)) :
    ∃ e : (pullback q).obj (Scheme.Modules.tensorObj I.toModules J.toModules) ≅
        (pullback q).obj (I * J).toModules,
      e.hom ≫ (pullback q).map (I * J).toModulesInclusion =
        (pullback q).map (multiplicationIntoUnit I J) :=
  transfer_factor (tensorOpenPullbackIso q I J) (productOpenPullbackIso q I J)
    (pullbackUnitIso q) _ _ _ _ (tensorOpenPullbackIso_inclusion q I J)
      (productOpenPullbackIso_inclusion q I J) hc

end EnvelopeProperty.Vanishing.NadelBlowupCanonicalIdealProductPullback
