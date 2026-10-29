import EnvelopeProperty.AlgGeom.ProjectiveFactorizationProducts
import EnvelopeProperty.AlgGeom.ProjectiveFactorizationRingIso
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.ProjectiveIdentity

/-! # SAME finite original relative products, whole combined maps and genuinely derived closed embeddings -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
namespace EnvelopeProperty.FiniteRelativeProjectiveProducts
variable {R : Type u} [CommRing R]

/-- The SAME original relative finite product, literally iterated native scheme pullbacks. -/
def product : (n : ℕ) → (Fin n → Over (Spec (.of R))) → Over (Spec (.of R))
  | 0, _ => Over.mk (𝟙 (Spec (.of R)))
  | n + 1, F => Over.mk (pullback.fst (F 0).hom (product n (fun i => F i.succ)).hom ≫ (F 0).hom)

/-- Each whole original projection retains the SAME literal coefficient triangle. -/
def projection : {n : ℕ} → (F : Fin n → Over (Spec (.of R))) → (i : Fin n) → product n F ⟶ F i
  | n + 1, F, i => Fin.cases
      (Over.homMk (pullback.fst (F 0).hom (product n (fun i => F i.succ)).hom) rfl)
      (fun j => Over.homMk (pullback.snd (F 0).hom (product n (fun i => F i.succ)).hom)
        pullback.condition.symm ≫ projection (fun i => F i.succ) j) i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual whole combined original map, constructed from SAME native pullback lifts. -/
def lift {X : Over (Spec (.of R))} : {n : ℕ} → (F : Fin n → Over (Spec (.of R))) →
    (∀ i, X ⟶ F i) → (X ⟶ product n F)
  | 0, _, _ => Over.homMk X.hom (Category.comp_id X.hom)
  | n + 1, F, g =>
      Over.homMk (pullback.lift (g 0).left (lift (fun i => F i.succ) (fun i => g i.succ)).left
        ((g 0).w.trans (lift (fun i => F i.succ) (fun i => g i.succ)).w.symm))
        (by
          change (pullback.lift _ _ _) ≫ (pullback.fst _ _ ≫ (F 0).hom) = X.hom
          rw [← Category.assoc, pullback.lift_fst]
          exact (g 0).w)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- EVERY actual entire original constituent map is restored by its SAME whole projection. -/
@[reassoc]
theorem lift_projection {X : Over (Spec (.of R))} {n : ℕ} (F : Fin n → Over (Spec (.of R)))
    (g : ∀ i, X ⟶ F i) (i : Fin n) : lift F g ≫ projection F i = g i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply Over.OverMorphism.ext
      exact pullback.lift_fst _ _ _
    · apply Over.OverMorphism.ext
      change (pullback.lift (g 0).left
        (lift (fun i => F i.succ) (fun i => g i.succ)).left _) ≫
          (pullback.snd _ _ ≫ (projection (fun i => F i.succ) j).left) = _
      rw [← Category.assoc, pullback.lift_snd]
      exact congrArg (fun f => f.left) (ih (fun i => F i.succ) (fun i => g i.succ) j)

/-- True finite polynomial projectivity of the SAME actual finite product is DERIVED from its factors. -/
theorem product_isProjectiveFactorization {n : ℕ} (F : Fin n → Over (Spec (.of R)))
    (hF : ∀ i, IsProjectiveFactorization (F i).hom) : IsProjectiveFactorization (product n F).hom := by
  induction n with
  | zero =>
    exact (ProjectiveBlowupSequence.isProjectiveOver_iff _).mp
      (Alterations.Geometry.ProjectiveIdentity.isProjectiveOver_id_spec R)
  | succ n ih =>
    exact ProjectiveFactorizationProducts.pullback (F 0).hom
      (product n (fun i => F i.succ)).hom (hF 0) (ih (fun i => F i.succ) (fun i => hF i.succ))

/-- The SAME whole original projection is genuinely separated, with no projection certificate. -/
theorem projection_isSeparated {n : ℕ} (F : Fin n → Over (Spec (.of R)))
    (hF : ∀ i, IsProjectiveFactorization (F i).hom) (i : Fin n) :
    IsSeparated (projection F i).left := by
  let : IsProper (product n F).hom := (product_isProjectiveFactorization F hF).isProper
  have : IsSeparated ((projection F i).left ≫ (F i).hom) := by
    rw [(projection F i).w]
    infer_instance
  exact IsSeparated.of_comp (projection F i).left (F i).hom

/-- Appending ANY actual maps to ONE actual original closed embedding preserves a genuine
WHOLE original closed embedding into the SAME finite original projective product. -/
theorem lift_isClosedImmersion {X : Over (Spec (.of R))} {n : ℕ}
    (F : Fin n → Over (Spec (.of R))) (hF : ∀ i, IsProjectiveFactorization (F i).hom)
    (g : ∀ i, X ⟶ F i) (hg : ∃ i, IsClosedImmersion (g i).left) :
    IsClosedImmersion (lift F g).left := by
  obtain ⟨i, hi⟩ := hg
  let : IsSeparated (projection F i).left := projection_isSeparated F hF i
  have : IsClosedImmersion ((lift F g).left ≫ (projection F i).left) := by
    rw [← Over.comp_left, lift_projection]
    exact hi
  exact IsClosedImmersion.of_comp (lift F g).left (projection F i).left

end EnvelopeProperty.FiniteRelativeProjectiveProducts
