import EnvelopeProperty.Global.NativeTestConfigurationNefFSApproximationContinuationTensorComparisons
import EnvelopeProperty.AlgGeom.CartierPullbackTensorCoherence
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Tensor coherence of the unit-open and product line comparisons

For a test configuration `C`, a linearized line `(M, α, e)` determines the whole unit-open
comparison `C.unitOpenLineIso M L α e : v^* M ≅ w^* L` (nine factors: map congruences,
pullback compositions, the pulled linearization and the pulled fibre-one identification) and
the product comparison `C.productTotalLineIso`.  This file proves that, for the tensor data of
`…ContinuationTensorComparisons`,

* `unitOpenLineIso_tensor_comparisons`: the comparison of `M ⊗ H` is the tensor of the two
  comparisons, conjugated by the pullback tensorators;
* `productTotalLineIso_tensor_comparisons`: the same on `X × 𝔾ₘ`.

The proof composes nine (resp. four) commuting squares, each an instance of three elementary
facts: monoidal natural isomorphisms commute with inverse tensorators, inverse tensorators of
composites, and naturality of inverse tensorators.  This is the tensor half of the statement
"`φ_{𝓛 ⊗ 𝓗} = φ_𝓛 + φ_𝓗`" for PL functions of test configurations (FHX §2.3, BJ22 §2).
-/
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfigurationNefFSTensorCoherence

private theorem tensor_trans {D : Type*} [Category D] [MonoidalCategory D]
    {A B P Q E F : D} (a : A ≅ B) (b : P ≅ Q) (c : B ≅ E) (d : Q ≅ F) :
    (a ⊗ᵢ b) ≪≫ (c ⊗ᵢ d) = (a ≪≫ c) ⊗ᵢ (b ≪≫ d) := by
  apply Iso.ext
  exact tensorHom_comp_tensorHom _ _ _ _

/-- The tensor of two nine-fold composites (association pattern of the unit-open line
comparison) is the composite of the tensors. -/
private theorem tensorIso_nine {D : Type*} [Category D] [MonoidalCategory D]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ A₉ B₀ B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ B₉ : D}
    (d₀ : A₀ ≅ A₁) (d₁ : A₁ ≅ A₂) (d₂ : A₂ ≅ A₃) (d₃ : A₃ ≅ A₄) (d₄ : A₄ ≅ A₅)
    (d₅ : A₅ ≅ A₆) (d₆ : A₆ ≅ A₇) (d₇ : A₇ ≅ A₈) (d₈ : A₈ ≅ A₉)
    (e₀ : B₀ ≅ B₁) (e₁ : B₁ ≅ B₂) (e₂ : B₂ ≅ B₃) (e₃ : B₃ ≅ B₄) (e₄ : B₄ ≅ B₅)
    (e₅ : B₅ ≅ B₆) (e₆ : B₆ ≅ B₇) (e₇ : B₇ ≅ B₈) (e₈ : B₈ ≅ B₉) :
    (d₀ ≪≫ (d₁ ≪≫ d₂ ≪≫ d₃) ≪≫ d₄ ≪≫ d₅ ≪≫ d₆ ≪≫ d₇ ≪≫ d₈) ⊗ᵢ
        (e₀ ≪≫ (e₁ ≪≫ e₂ ≪≫ e₃) ≪≫ e₄ ≪≫ e₅ ≪≫ e₆ ≪≫ e₇ ≪≫ e₈) =
      (d₀ ⊗ᵢ e₀) ≪≫ ((d₁ ⊗ᵢ e₁) ≪≫ (d₂ ⊗ᵢ e₂) ≪≫ (d₃ ⊗ᵢ e₃)) ≪≫ (d₄ ⊗ᵢ e₄) ≪≫
        (d₅ ⊗ᵢ e₅) ≪≫ (d₆ ⊗ᵢ e₆) ≪≫ (d₇ ⊗ᵢ e₇) ≪≫ (d₈ ⊗ᵢ e₈) := by
  simp only [tensor_trans]

/-- The tensor of two four-fold composites is the composite of the tensors. -/
private theorem tensorIso_four {D : Type*} [Category D] [MonoidalCategory D]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    (d₀ : A₀ ≅ A₁) (d₁ : A₁ ≅ A₂) (d₂ : A₂ ≅ A₃) (d₃ : A₃ ≅ A₄)
    (e₀ : B₀ ≅ B₁) (e₁ : B₁ ≅ B₂) (e₂ : B₂ ≅ B₃) (e₃ : B₃ ≅ B₄) :
    (d₀ ≪≫ d₁ ≪≫ d₂ ≪≫ d₃) ⊗ᵢ (e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ e₃) =
      (d₀ ⊗ᵢ e₀) ≪≫ (d₁ ⊗ᵢ e₁) ≪≫ (d₂ ⊗ᵢ e₂) ≪≫ (d₃ ⊗ᵢ e₃) := by
  simp only [tensor_trans]

private theorem square_inverse {D : Type*} [Category D]
    {A B A' B' : D} (a : A ≅ B) (p : A ≅ A') (q : B ≅ B') (a' : A' ≅ B')
    (h : a ≪≫ q = p ≪≫ a') : a.symm ≪≫ p = q ≪≫ a'.symm := by
  have hh := congrArg (fun E => a.symm ≪≫ E ≪≫ a'.symm) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id, Iso.trans_refl]
    using hh.symm

private theorem mapped_conjugate_square {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) {A B A' B' : D} {P Q : E}
    (a : A ≅ A') (e : A' ≅ B') (b : B ≅ B') (p : F.obj A' ≅ P) (q : F.obj B' ≅ Q)
    (v : P ≅ Q) (h : F.mapIso e ≪≫ q = p ≪≫ v) :
    F.mapIso (a ≪≫ e ≪≫ b.symm) ≪≫ (F.mapIso b ≪≫ q) =
      (F.mapIso a ≪≫ p) ≪≫ v := by
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc]
  rw [h]

private theorem monoidal_iso_inverse_tensorator
    {D E : Type*} [Category D] [MonoidalCategory D]
    [Category E] [MonoidalCategory E]
    {F G : D ⥤ E} [F.Monoidal] [G.Monoidal] (e : F ≅ G)
    [e.hom.IsMonoidal] (M N : D) :
    e.app (M ⊗ N) ≪≫ (Functor.Monoidal.μIso G M N).symm =
      (Functor.Monoidal.μIso F M N).symm ≪≫ (e.app M ⊗ᵢ e.app N) := by
  apply Iso.ext
  apply (cancel_epi (Functor.Monoidal.μIso F M N).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.hom_inv_id_assoc]
  have h := NatTrans.IsMonoidal.tensor (τ := e.hom) M N
  simpa only [Functor.Monoidal.μIso_hom, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, Iso.app_hom, Functor.Monoidal.μIso_inv] using
    congrArg (fun f => f ≫ (Functor.Monoidal.μIso G M N).inv) h

private theorem inverse_tensorator_naturality
    {D E : Type*} [Category D] [MonoidalCategory D]
    [Category E] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] {A B P Q : D} (a : A ≅ B) (b : P ≅ Q) :
    F.mapIso (a ⊗ᵢ b) ≪≫ (Functor.Monoidal.μIso F B Q).symm =
      (Functor.Monoidal.μIso F A P).symm ≪≫ (F.mapIso a ⊗ᵢ F.mapIso b) := by
  apply Iso.ext
  exact (Functor.OplaxMonoidal.δ_natural F a.hom b.hom).symm

private theorem inverse_tensorator_comp
    {D E F : Type*} [Category D] [MonoidalCategory D]
    [Category E] [MonoidalCategory E] [Category F] [MonoidalCategory F]
    (G : D ⥤ E) (H : E ⥤ F) [G.Monoidal] [H.Monoidal] (M N : D) :
    (Functor.Monoidal.μIso (G ⋙ H) M N).symm =
      H.mapIso (Functor.Monoidal.μIso G M N).symm ≪≫
        (Functor.Monoidal.μIso H (G.obj M) (G.obj N)).symm := by
  apply Iso.ext
  exact Functor.OplaxMonoidal.comp_δ G H M N

noncomputable local instance nfTensorCoherenceModulesMonoidal (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y
noncomputable local instance nfTensorCoherencePullbackMonoidal {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (pullback f).Monoidal := pullbackMonoidal f

private theorem pullback_congr_square {Y Z : Scheme.{u}}
    {f g : Y ⟶ Z} (h : f = g) (M N : Z.Modules) :
    (pullbackCongr h).app (M ⊗ N) ≪≫ (Functor.Monoidal.μIso (pullback g) M N).symm =
      (Functor.Monoidal.μIso (pullback f) M N).symm ≪≫
        ((pullbackCongr h).app M ⊗ᵢ (pullbackCongr h).app N) := by
  have : (pullbackCongr h).hom.IsMonoidal := by
    subst g
    change NatTrans.IsMonoidal (𝟙 (pullback f))
    infer_instance
  exact monoidal_iso_inverse_tensorator (pullbackCongr h) M N

private theorem pullback_comp_square {Y Z W : Scheme.{u}}
    (f : Y ⟶ Z) (g : Z ⟶ W) (M N : W.Modules) :
    (pullbackComp f g).app (M ⊗ N) ≪≫
        (Functor.Monoidal.μIso (pullback (f ≫ g)) M N).symm =
      ((pullback f).mapIso (Functor.Monoidal.μIso (pullback g) M N).symm ≪≫
        (Functor.Monoidal.μIso (pullback f) ((pullback g).obj M) ((pullback g).obj N)).symm) ≪≫
          ((pullbackComp f g).app M ⊗ᵢ (pullbackComp f g).app N) := by
  have : (pullbackComp f g).hom.IsMonoidal := pullbackComp_hom_isMonoidal f g
  exact (monoidal_iso_inverse_tensorator (pullbackComp f g) M N).trans
    (congrArg (fun E => E ≪≫ ((pullbackComp f g).app M ⊗ᵢ (pullbackComp f g).app N))
      (inverse_tensorator_comp (pullback g) (pullback f) M N))

end EnvelopeProperty.NativeTestConfigurationNefFSTensorCoherence

namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open CanonicalGeometry
open NativeTestConfigurationNefFSTensorCoherence NativeTestConfigurationNefFSTensorComparisons
noncomputable local instance nfTensorCoherenceModulesMonoidal' (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y
noncomputable local instance nfTensorCoherencePullbackMonoidal' {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (pullback f).Monoidal := pullbackMonoidal f
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) (M H : C.total.Modules) (L K : X.left.Modules)
    (alpha : (pullback C.lineActionMap).obj M ≅ (pullback C.lineProjectionMap).obj M)
    (beta : (pullback C.lineActionMap).obj H ≅ (pullback C.lineProjectionMap).obj H)
    (e : (pullback C.fibreOneInclusion.left).obj M ≅ (pullback C.fibreOneIso.hom.left).obj L)
    (f : (pullback C.fibreOneInclusion.left).obj H ≅ (pullback C.fibreOneIso.hom.left).obj K)

/-- The actual tensor action and fibre-one comparisons give the whole tensor
of the original unit-open comparisons, with the actual pullback tensorators. -/
theorem unitOpenLineIso_tensor_comparisons :
    C.unitOpenLineIso (M ⊗ H) (L ⊗ K)
        (C.tensorLineActionComparison M H alpha beta)
        (C.tensorFibreOneComparison M H L K e f) =
      (Functor.Monoidal.μIso (pullback C.unitOpenInclusion.left) M H).symm ≪≫
        (C.unitOpenLineIso M L alpha e ⊗ᵢ C.unitOpenLineIso H K beta f) ≪≫
          Functor.Monoidal.μIso (pullback C.unitOpenOriginalProjection.left) L K := by
  let a := C.unitOpenActionLift.left
  let g := C.lineActionMap
  let h := C.lineProjectionMap
  let v := C.unitOpenInclusion.left
  let z := C.unitOpenFibreProjection.left
  let i := C.fibreOneInclusion.left
  let j := C.fibreOneIso.hom.left
  let w := C.unitOpenOriginalProjection.left
  let h0 := C.lineActionLift_action.symm
  let h4 := C.lineActionLift_projection
  let h8 := C.lineActionLift_original
  let d0 := (pullbackCongr h0).app M
  let e0 := (pullbackCongr h0).app H
  let D0 := (pullbackCongr h0).app (M ⊗ H)
  let d1 := ((pullbackComp a g).app M).symm
  let e1 := ((pullbackComp a g).app H).symm
  let D1 := ((pullbackComp a g).app (M ⊗ H)).symm
  let d2 := (pullback a).mapIso alpha
  let e2 := (pullback a).mapIso beta
  let D2 := (pullback a).mapIso (C.tensorLineActionComparison M H alpha beta)
  let d3 := (pullbackComp a h).app M
  let e3 := (pullbackComp a h).app H
  let D3 := (pullbackComp a h).app (M ⊗ H)
  let d4 := (pullbackCongr h4).app M
  let e4 := (pullbackCongr h4).app H
  let D4 := (pullbackCongr h4).app (M ⊗ H)
  let d5 := ((pullbackComp z i).app M).symm
  let e5 := ((pullbackComp z i).app H).symm
  let D5 := ((pullbackComp z i).app (M ⊗ H)).symm
  let d6 := (pullback z).mapIso e
  let e6 := (pullback z).mapIso f
  let D6 := (pullback z).mapIso (C.tensorFibreOneComparison M H L K e f)
  let d7 := (pullbackComp z j).app L
  let e7 := (pullbackComp z j).app K
  let D7 := (pullbackComp z j).app (L ⊗ K)
  let d8 := (pullbackCongr h8).app L
  let e8 := (pullbackCongr h8).app K
  let D8 := (pullbackCongr h8).app (L ⊗ K)
  let p0 := (Functor.Monoidal.μIso (pullback v) M H).symm
  let p1 := (Functor.Monoidal.μIso (pullback (a ≫ g)) M H).symm
  let p2 := (pullback a).mapIso (Functor.Monoidal.μIso (pullback g) M H).symm ≪≫
    (Functor.Monoidal.μIso (pullback a) ((pullback g).obj M) ((pullback g).obj H)).symm
  let p3 := (pullback a).mapIso (Functor.Monoidal.μIso (pullback h) M H).symm ≪≫
    (Functor.Monoidal.μIso (pullback a) ((pullback h).obj M) ((pullback h).obj H)).symm
  let p4 := (Functor.Monoidal.μIso (pullback (a ≫ h)) M H).symm
  let p5 := (Functor.Monoidal.μIso (pullback (z ≫ i)) M H).symm
  let p6 := (pullback z).mapIso (Functor.Monoidal.μIso (pullback i) M H).symm ≪≫
    (Functor.Monoidal.μIso (pullback z) ((pullback i).obj M) ((pullback i).obj H)).symm
  let p7 := (pullback z).mapIso (Functor.Monoidal.μIso (pullback j) L K).symm ≪≫
    (Functor.Monoidal.μIso (pullback z) ((pullback j).obj L) ((pullback j).obj K)).symm
  let p8 := (Functor.Monoidal.μIso (pullback (z ≫ j)) L K).symm
  let p9 := (Functor.Monoidal.μIso (pullback w) L K).symm
  have s0 : D0 ≪≫ p1 = p0 ≪≫ (d0 ⊗ᵢ e0) := pullback_congr_square h0 M H
  have s1 : D1 ≪≫ p2 = p1 ≪≫ (d1 ⊗ᵢ e1) :=
    square_inverse ((pullbackComp a g).app (M ⊗ H)) p2 p1
      ((pullbackComp a g).app M ⊗ᵢ (pullbackComp a g).app H) (pullback_comp_square a g M H)
  have s2 : D2 ≪≫ p3 = p2 ≪≫ (d2 ⊗ᵢ e2) :=
    mapped_conjugate_square (pullback a)
      (Functor.Monoidal.μIso (pullback g) M H).symm (alpha ⊗ᵢ beta)
      (Functor.Monoidal.μIso (pullback h) M H).symm
      (Functor.Monoidal.μIso (pullback a) ((pullback g).obj M) ((pullback g).obj H)).symm
      (Functor.Monoidal.μIso (pullback a) ((pullback h).obj M) ((pullback h).obj H)).symm
      ((pullback a).mapIso alpha ⊗ᵢ (pullback a).mapIso beta)
      (inverse_tensorator_naturality (pullback a) alpha beta)
  have s3 : D3 ≪≫ p4 = p3 ≪≫ (d3 ⊗ᵢ e3) := pullback_comp_square a h M H
  have s4 : D4 ≪≫ p5 = p4 ≪≫ (d4 ⊗ᵢ e4) := pullback_congr_square h4 M H
  have s5 : D5 ≪≫ p6 = p5 ≪≫ (d5 ⊗ᵢ e5) :=
    square_inverse ((pullbackComp z i).app (M ⊗ H)) p6 p5
      ((pullbackComp z i).app M ⊗ᵢ (pullbackComp z i).app H) (pullback_comp_square z i M H)
  have s6 : D6 ≪≫ p7 = p6 ≪≫ (d6 ⊗ᵢ e6) :=
    mapped_conjugate_square (pullback z)
      (Functor.Monoidal.μIso (pullback i) M H).symm (e ⊗ᵢ f)
      (Functor.Monoidal.μIso (pullback j) L K).symm
      (Functor.Monoidal.μIso (pullback z) ((pullback i).obj M) ((pullback i).obj H)).symm
      (Functor.Monoidal.μIso (pullback z) ((pullback j).obj L) ((pullback j).obj K)).symm
      ((pullback z).mapIso e ⊗ᵢ (pullback z).mapIso f)
      (inverse_tensorator_naturality (pullback z) e f)
  have s7 : D7 ≪≫ p8 = p7 ≪≫ (d7 ⊗ᵢ e7) := pullback_comp_square z j L K
  have s8 : D8 ≪≫ p9 = p8 ≪≫ (d8 ⊗ᵢ e8) := pullback_congr_square h8 L K
  have ht :
      C.unitOpenLineIso (M ⊗ H) (L ⊗ K)
          (C.tensorLineActionComparison M H alpha beta)
          (C.tensorFibreOneComparison M H L K e f) ≪≫ p9 =
        p0 ≪≫ (C.unitOpenLineIso M L alpha e ⊗ᵢ C.unitOpenLineIso H K beta f) := by
    change (D0 ≪≫ (D1 ≪≫ D2 ≪≫ D3) ≪≫ D4 ≪≫ D5 ≪≫ D6 ≪≫ D7 ≪≫ D8) ≪≫ p9 =
      p0 ≪≫ ((d0 ≪≫ (d1 ≪≫ d2 ≪≫ d3) ≪≫ d4 ≪≫ d5 ≪≫ d6 ≪≫ d7 ≪≫ d8) ⊗ᵢ
        (e0 ≪≫ (e1 ≪≫ e2 ≪≫ e3) ≪≫ e4 ≪≫ e5 ≪≫ e6 ≪≫ e7 ≪≫ e8))
    exact (isoSquare_nine s0 s1 s2 s3 s4 s5 s6 s7 s8).trans (congrArg (fun E => p0 ≪≫ E)
      (tensorIso_nine d0 d1 d2 d3 d4 d5 d6 d7 d8 e0 e1 e2 e3 e4 e5 e6 e7 e8).symm)
  exact (isoCancelRight_symm ht).trans (Iso.trans_assoc _ _ _)

/-- The actual original tensor action/fibre data give the tensor of the
two original whole product comparisons, without modifying either action. -/
theorem productTotalLineIso_tensor_comparisons :
    C.productTotalLineIso (M ⊗ H) (L ⊗ K)
        (C.tensorLineActionComparison M H alpha beta)
        (C.tensorFibreOneComparison M H L K e f) =
      (Functor.Monoidal.μIso (pullback C.productTotalMap) M H).symm ≪≫
        (C.productTotalLineIso M L alpha e ⊗ᵢ C.productTotalLineIso H K beta f) ≪≫
          Functor.Monoidal.μIso
              (pullback (fst X (ProjBerk.nativeMultiplicativeGroup k)).left) L K := by
  let a := C.unitOpenIso.inv.left
  let v := C.unitOpenInclusion.left
  let w := C.unitOpenOriginalProjection.left
  let q := (fst X (ProjBerk.nativeMultiplicativeGroup k)).left
  let U := C.unitOpenLineIso M L alpha e
  let V := C.unitOpenLineIso H K beta f
  let d0 := ((pullbackComp a v).app M).symm
  let e0 := ((pullbackComp a v).app H).symm
  let d1 := (pullback a).mapIso U
  let e1 := (pullback a).mapIso V
  let d2 := (pullbackComp a w).app L
  let e2 := (pullbackComp a w).app K
  let d3 := (pullbackCongr C.unitOpenIso_inv_originalProjection).app L
  let e3 := (pullbackCongr C.unitOpenIso_inv_originalProjection).app K
  let D0 := ((pullbackComp a v).app (M ⊗ H)).symm
  let D1 := (pullback a).mapIso (C.unitOpenLineIso (M ⊗ H) (L ⊗ K)
    (C.tensorLineActionComparison M H alpha beta) (C.tensorFibreOneComparison M H L K e f))
  let D2 := (pullbackComp a w).app (L ⊗ K)
  let D3 := (pullbackCongr C.unitOpenIso_inv_originalProjection).app (L ⊗ K)
  let p0 := (Functor.Monoidal.μIso (pullback C.productTotalMap) M H).symm
  let p1 := (pullback a).mapIso (Functor.Monoidal.μIso (pullback v) M H).symm ≪≫
    (Functor.Monoidal.μIso (pullback a) ((pullback v).obj M) ((pullback v).obj H)).symm
  let p2 := (pullback a).mapIso (Functor.Monoidal.μIso (pullback w) L K).symm ≪≫
    (Functor.Monoidal.μIso (pullback a) ((pullback w).obj L) ((pullback w).obj K)).symm
  let p3 := (Functor.Monoidal.μIso (pullback (a ≫ w)) L K).symm
  let p4 := (Functor.Monoidal.μIso (pullback q) L K).symm
  have s0 : D0 ≪≫ p1 = p0 ≪≫ (d0 ⊗ᵢ e0) :=
    square_inverse ((pullbackComp a v).app (M ⊗ H)) p1 p0
      ((pullbackComp a v).app M ⊗ᵢ (pullbackComp a v).app H) (pullback_comp_square a v M H)
  have s1 : D1 ≪≫ p2 = p1 ≪≫ (d1 ⊗ᵢ e1) := by
    dsimp only [D1]
    rw [C.unitOpenLineIso_tensor_comparisons M H L K alpha beta e f]
    exact mapped_conjugate_square (pullback a)
      (Functor.Monoidal.μIso (pullback v) M H).symm (U ⊗ᵢ V)
      (Functor.Monoidal.μIso (pullback w) L K).symm
      (Functor.Monoidal.μIso (pullback a) ((pullback v).obj M) ((pullback v).obj H)).symm
      (Functor.Monoidal.μIso (pullback a) ((pullback w).obj L) ((pullback w).obj K)).symm
      ((pullback a).mapIso U ⊗ᵢ (pullback a).mapIso V)
      (inverse_tensorator_naturality (pullback a) U V)
  have s2 : D2 ≪≫ p3 = p2 ≪≫ (d2 ⊗ᵢ e2) := pullback_comp_square a w L K
  have s3 : D3 ≪≫ p4 = p3 ≪≫ (d3 ⊗ᵢ e3) :=
    pullback_congr_square C.unitOpenIso_inv_originalProjection L K
  have ht :
      C.productTotalLineIso (M ⊗ H) (L ⊗ K)
          (C.tensorLineActionComparison M H alpha beta)
              (C.tensorFibreOneComparison M H L K e f) ≪≫ p4 =
        p0 ≪≫ (C.productTotalLineIso M L alpha e ⊗ᵢ C.productTotalLineIso H K beta f) := by
    change (D0 ≪≫ D1 ≪≫ D2 ≪≫ D3) ≪≫ p4 =
      p0 ≪≫ ((d0 ≪≫ d1 ≪≫ d2 ≪≫ d3) ⊗ᵢ (e0 ≪≫ e1 ≪≫ e2 ≪≫ e3))
    exact (isoSquare_four s0 s1 s2 s3).trans (congrArg (fun E => p0 ≪≫ E)
      (tensorIso_four d0 d1 d2 d3 e0 e1 e2 e3).symm)
  exact (isoCancelRight_symm ht).trans (Iso.trans_assoc _ _ _)

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration

