import Mathlib.AlgebraicGeometry.Normalization

/-! # The actual whole native affine relative-normalization spectrum

This exposes the genuine generic affine construction used privately by the
existing original cyclic normalization proof. Its rings are arbitrary; no
domain, reducedness or selected-component premise is introduced.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.Affine
def closureCongr {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra B D] (e : A ≃+* B) (q : C ≃+* D)
    (h : (algebraMap B D).comp e.toRingHom = q.toRingHom.comp (algebraMap A C)) :
    integralClosure A C ≃+* integralClosure B D where
  toFun z := ⟨q z, IsIntegral.map_of_comp_eq e.toRingHom q.toRingHom h z.property⟩
  invFun z := ⟨q.symm z, IsIntegral.map_of_comp_eq e.symm.toRingHom q.symm.toRingHom (by
    ext b
    apply q.injective
    change q (algebraMap A C (e.symm b)) = q (q.symm (algebraMap B D b))
    rw [q.apply_symm_apply]
    have hh := DFunLike.congr_fun h (e.symm b)
    change algebraMap B D (e (e.symm b)) = q (algebraMap A C (e.symm b)) at hh
    rw [e.apply_symm_apply] at hh
    exact hh.symm) z.property⟩
  left_inv z := Subtype.ext (q.symm_apply_apply z)
  right_inv z := Subtype.ext (q.apply_symm_apply z)
  map_mul' z w := Subtype.ext (q.map_mul z w)
  map_add' z w := Subtype.ext (q.map_add z w)

/-- The actual whole closure transport preserves EVERY original coefficient
through its actual original base-ring comparison. -/
theorem closureCongr_algebraMap {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra B D] (e : A ≃+* B) (q : C ≃+* D)
    (h : (algebraMap B D).comp e.toRingHom = q.toRingHom.comp (algebraMap A C)) (a : A) :
    closureCongr e q h (algebraMap A (integralClosure A C) a) =
      algebraMap B (integralClosure B D) (e a) := by
  apply Subtype.ext
  exact congrArg (fun f : A →+* D => f a) h.symm

variable (R Q : Type u) [CommRing R] [CommRing Q] [Algebra R Q]

abbrev genericSpecMap : Spec (.of Q) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R Q))

local instance genericSpecMap_quasiCompact : QuasiCompact (genericSpecMap R Q) := by
  unfold genericSpecMap
  infer_instance

local instance genericSpecMap_quasiSeparated : QuasiSeparated (genericSpecMap R Q) := by
  unfold genericSpecMap
  infer_instance

def gammaClosureEquiv :
    letI := ((genericSpecMap R Q).appTop).hom.toAlgebra
    integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of Q), ⊤) ≃+* integralClosure R Q := by
  let := ((genericSpecMap R Q).appTop).hom.toAlgebra
  apply closureCongr (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (.of Q)).commRingCatIsoToRingEquiv
  ext r
  exact (congrArg (fun k : Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of Q => k r)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R Q)))).symm

theorem gammaClosureEquiv_algebraMap (r : Γ(Spec (.of R), ⊤)) :
    letI := ((genericSpecMap R Q).appTop).hom.toAlgebra
    gammaClosureEquiv R Q (algebraMap Γ(Spec (.of R), ⊤)
      (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of Q), ⊤)) r) =
      algebraMap R (integralClosure R Q) ((Scheme.ΓSpecIso (.of R)).hom r) := by
  let := ((genericSpecMap R Q).appTop).hom.toAlgebra
  apply Subtype.ext
  exact congrArg (fun k : Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of Q => k r)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R Q)))

def normalizationSpectrumIso : Spec (.of (integralClosure R Q)) ≅
    (genericSpecMap R Q).normalization := by
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let j := (genericSpecMap R Q).normalizationOpenCover.f U
  have : IsOpenImmersion j := (genericSpecMap R Q).normalizationOpenCover.map_prop U
  have : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j (by
    exact ((genericSpecMap R Q).fromNormalization_preimage U).symm)
  exact Scheme.Spec.mapIso (gammaClosureEquiv R Q).toCommRingCatIso.op ≪≫ asIso j

theorem normalizationSpectrumIso_projection :
    (normalizationSpectrumIso R Q).hom ≫ (genericSpecMap R Q).fromNormalization =
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R Q))) := by
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let := ((genericSpecMap R Q).appTop).hom.toAlgebra
  change Spec.map (CommRingCat.ofHom (gammaClosureEquiv R Q).toRingHom) ≫
    ((genericSpecMap R Q).normalizationOpenCover.f U ≫ _) = _
  rw [(genericSpecMap R Q).ι_fromNormalization U]
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change gammaClosureEquiv R Q
    (algebraMap Γ(Spec (.of R), ⊤)
      (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of Q), ⊤)) ((Scheme.ΓSpecIso (.of R)).inv r)) = _
  rw [gammaClosureEquiv_algebraMap]
  exact congrArg (algebraMap R (integralClosure R Q))
    (congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of R => k r) (Scheme.ΓSpecIso (.of R)).inv_hom_id)

theorem normalizationSpectrumIso_generic :
    Spec.map (CommRingCat.ofHom (integralClosure R Q).val.toRingHom) ≫
        (normalizationSpectrumIso R Q).hom = (genericSpecMap R Q).toNormalization := by
  let U : (Spec (.of R)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  let := ((genericSpecMap R Q).appTop).hom.toAlgebra
  have : IsIso (⊤ : (Spec (.of Q)).Opens).ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have ht : (genericSpecMap R Q).toNormalization =
      (Spec (.of Q)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (integralClosure Γ(Spec (.of R), ⊤) Γ(Spec (.of Q), ⊤)).val.toRingHom) ≫
          (genericSpecMap R Q).normalizationOpenCover.f U := by
    apply (cancel_epi (⊤ : (Spec (.of Q)).Opens).ι).1
    simpa only [U, Scheme.Hom.preimage_top, Scheme.Opens.toSpecΓ_top, Category.assoc] using
      (genericSpecMap R Q).ι_toNormalization U
  rw [ht]
  change Spec.map (CommRingCat.ofHom (integralClosure R Q).val.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (gammaClosureEquiv R Q).toRingHom) ≫
        (genericSpecMap R Q).normalizationOpenCover.f U) =
    (Spec (.of Q)).isoSpec.hom ≫ _
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 1
end EnvelopeProperty.Vanishing.NadelGlobalNormalization.Affine
