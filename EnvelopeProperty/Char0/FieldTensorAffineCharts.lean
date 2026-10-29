import EnvelopeProperty.Char0.AffineFieldRoundedColon
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Actual literal changed-field affine charts of the original model

The actual original morphism manufactures the changed coefficient square,
the canonical chart map into the actual categorical model pullback,
its two literal projections, its cartesian chart square and coverage.
-/

set_option autoImplicit false

noncomputable section

namespace EnvelopeProperty.Char0.FieldTensorAffineCharts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {A B : CommRingCat.{u}} [Algebra k A] [Algebra k B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The literal tensor morphism supplies its actual cartesian spectrum square. -/
theorem morphism_isPullback (φ : A →ₐ[k] B) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id L L) φ).toRingHom))
      (Spec.map (CommRingCat.ofHom φ.toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom)) := by
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  let : Algebra (L ⊗[k] A) (L ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id L L) φ).toAlgebra
  let : IsScalarTower L (L ⊗[k] A) (L ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((Algebra.TensorProduct.map (AlgHom.id L L) φ).commutes r).symm
  let : Algebra A (L ⊗[k] B) :=
    ((algebraMap B (L ⊗[k] B)).comp φ.toRingHom).toAlgebra
  let : IsScalarTower A B (L ⊗[k] B) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (L ⊗[k] A) (L ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower k (L ⊗[k] A) (L ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply k L (L ⊗[k] A),
        ← IsScalarTower.algebraMap_apply L (L ⊗[k] A) (L ⊗[k] B),
        ← IsScalarTower.algebraMap_apply k L (L ⊗[k] B)]
  let : Algebra.IsPushout A B (L ⊗[k] A) (L ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k A L (L ⊗[k] A) (T := B) (T' := L ⊗[k] B)).mp
      TensorProduct.isPushout'
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout A B (L ⊗[k] A) (L ⊗[k] B))

variable {Y : Scheme.{u}} (g : Y ⟶ Spec A) (j : Spec B ⟶ Y)
  (φ : A →ₐ[k] B) (htriangle : j ≫ g = Spec.map (CommRingCat.ofHom φ.toRingHom))

/-- The actual literal new chart map into the actual categorical basechanged original model. -/
def chartMap : Spec (.of (L ⊗[k] B)) ⟶
    pullback g (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom)) :=
  (morphism_isPullback (L := L) φ).isoPullback.hom ≫
    pullback.map _ _ g _ j (𝟙 _) (𝟙 _) (by simpa using htriangle.symm) (by simp)

/-- The original model projection retains exactly the original coefficient map and original chart. -/
theorem chartMap_fst :
    chartMap (L := L) g j φ htriangle ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom) ≫ j := by
  simp only [chartMap, Category.assoc, pullback.lift_fst,
    IsPullback.isoPullback_hom_fst_assoc]

/-- The ENTIRE actual new-base action is precisely the literal coefficient tensor morphism. -/
theorem chartMap_snd :
    chartMap (L := L) g j φ htriangle ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id L L) φ).toRingHom) := by
  simp only [chartMap, Category.assoc, pullback.lift_snd, Category.comp_id,
    IsPullback.isoPullback_hom_snd]

/-- The actual new literal chart is the actual base change of the original chart. -/
theorem chart_isPullback :
    IsPullback (chartMap (L := L) g j φ htriangle)
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom))
      (pullback.fst _ _) j := by
  have hbig : IsPullback
      (chartMap (L := L) g j φ htriangle ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := B)).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom)) (j ≫ g) := by
    rw [chartMap_snd, htriangle]
    exact (morphism_isPullback (L := L) φ).flip
  exact hbig.of_right (chartMap_fst g j φ htriangle) (IsPullback.of_hasPullback _ _).flip

/-- Openness of the original chart manufactures openness of the actual new chart. -/
instance chartMap_isOpenImmersion [IsOpenImmersion j] :
    IsOpenImmersion (chartMap (L := L) g j φ htriangle) := by
  rw [← (chart_isPullback (L := L) g j φ htriangle).isoPullback_hom_fst]
  infer_instance

/-- The actual original cover manufactures coverage of ALL actual changed-model points by the literal tensor charts. -/
theorem chartMap_cover {ι : Type v} (B : ι → CommRingCat.{u}) [∀ i, Algebra k (B i)]
    (j : (i : ι) → Spec (B i) ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (φ : (i : ι) → A →ₐ[k] B i)
    (htriangle : ∀ i, j i ≫ g = Spec.map (CommRingCat.ofHom (φ i).toRingHom))
    (hcover : ∀ y : Y, ∃ i x, j i x = y) :
    ∀ y : (pullback g (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom)) : Scheme.{u}),
      ∃ i x, chartMap (L := L) g (j i) (φ i) (htriangle i) x = y := by
  let C : Y.Cover (Scheme.precoverage @IsOpenImmersion) :=
    Scheme.Cover.mkOfCovers ι (fun i => Spec (B i)) j hcover
  let pA := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := L) (B := A)).toRingHom)
  let C' : (pullback g pA).Cover (Scheme.precoverage @IsOpenImmersion) :=
    C.pullback₁ (pullback.fst g pA)
  intro y
  have hc : ∃ (i : ι) (x : (pullback (pullback.fst g pA) (j i) : Scheme.{u})),
      pullback.fst (pullback.fst g pA) (j i) x = y := Scheme.Cover.exists_eq C' y
  obtain ⟨i, x, hx⟩ := hc
  refine ⟨i, (chart_isPullback (L := L) g (j i) (φ i) (htriangle i)).isoPullback.inv x, ?_⟩
  have h := congrArg (fun t => t x)
    (chart_isPullback (L := L) g (j i) (φ i) (htriangle i)).isoPullback_inv_fst
  exact h.trans hx

end EnvelopeProperty.Char0.FieldTensorAffineCharts
