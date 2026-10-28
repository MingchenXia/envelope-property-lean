import EnvelopeProperty.Vanishing.FrobeniusCohomologyHodge

/-! # Actual perfect-field Frobenius cohomology over any original affine base

Only projectivity over the supplied affine base is used to produce the native
finite affine cover. The original field structure and absolute differential
objects are retained, without properness over that field.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.RelativeFrobeniusCohomology
open Cartier CanonicalGeometry FrobeniusCohomology FrobeniusCohomologyDifferentials
open FrobeniusCohomologyHodge
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    {R : Type u} [CommRing R]

private theorem subsingleton_H_of_moduleIso {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (q : ℕ) (hN : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology Y) q).mapIso
    ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology Y) q).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N)) := hN
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

/-- The actual perfect-field twist pullback preserves and reflects positive
cohomology using the original projective map over any affine base. -/
theorem twistPullback_subsingleton_H_iff
    (g₀ : X ⟶ Spec (.of R)) (hg₀ : IsProjectiveFactorization g₀) (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((pullback (twistProjectionIso f p).hom).obj M).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  let e := twistProjectionIso f p
  let g := e.hom
  let N := (pullback g).obj M
  let : X.IsSeparated := ProjectiveAffineCover.separated g₀ hg₀
  let : (M.restrict g).IsQuasicoherent := inferInstance
  let : N.IsQuasicoherent :=
    (isQuasicoherent (SchemeRelativeFrobenius.twist p f)).prop_of_iso
      ((restrictFunctorIsoPullback g).app M) inferInstance
  let Q := (pushforward g).obj N
  obtain ⟨ι, hlin, hfin, U, hUa, hU⟩ := ProjectiveAffineCover.exists_affine_openCover g₀ hg₀
  let : LinearOrder ι := hlin
  let : Fintype ι := hfin
  have hpush : Subsingleton (CategoryTheory.Sheaf.H N.sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H Q.sheaf (q + 1)) :=
    AffinePushforwardCohomology.subsingleton_H_iff_pushforward g f N U hU hUa q
  have eu : M ≅ Q := twistPullbackUnitIso f p M
  exact hpush.trans ⟨fun h => subsingleton_H_of_moduleIso eu (q + 1) h,
    fun h => subsingleton_H_of_moduleIso eu.symm (q + 1) h⟩

/-- The entire original relative-Frobenius pushforward has the same positive
cohomology with actual projectivity over any affine base, with no properness over the field. -/
theorem relativePushforward_subsingleton_H_iff
    (g₀ : X ⟶ Spec (.of R)) (hg₀ : IsProjectiveFactorization g₀) (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((pushforward (SchemeRelativeFrobenius.map p f)).obj M).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  let π := (twistProjectionIso f p).hom
  let S := SchemeRelativeFrobenius.twist p f
  let : X.IsSeparated := ProjectiveAffineCover.separated g₀ hg₀
  let : S.IsSeparated := ⟨by rw [← Limits.terminal.comp_from π]; infer_instance⟩
  let : IsAffineHom (SchemeRelativeFrobenius.map p f) := relativeFrobenius_isAffineHom f p
  obtain ⟨ι, hlin, hfin, U, hUa, hU⟩ := ProjectiveAffineCover.exists_affine_openCover g₀ hg₀
  let : LinearOrder ι := hlin
  let : Fintype ι := hfin
  let s : S ⟶ Spec (.of k) :=
    Limits.pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
  exact (AffinePushforwardCohomology.subsingleton_H_iff_pushforward
    (SchemeRelativeFrobenius.map p f) s M (fun i => π ⁻¹ᵁ U i)
      (π.iSup_preimage_eq_top hU) (fun i => (hUa i).preimage π) q).symm

private theorem subsingleton_H_iff_moduleIso {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) ↔
      Subsingleton (CategoryTheory.Sheaf.H N.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology Y) q).mapIso
    ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e)
  constructor
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology Y) q).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology Y) q).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

/-- The same absolute Hodge tensor and all original line powers have the
native twist comparison under actual projectivity over the supplied affine base. -/
theorem twistHodge_subsingleton_H_iff
    (g₀ : X ⟶ Spec (.of R)) (n : ℕ) [SmoothOfRelativeDimension n f] (L : X.Modules)
    (hL : SchemeLineAmpleness.IsAmple g₀ L) (m i q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower ((pullback (twistProjectionIso f p).hom).obj L) m ⊗
        exteriorCotangentSheaf (twistStructure f p) i).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i).sheaf (q + 1)) := by
  let W := exteriorCotangentSheaf f i
  let A := bundleTensorPower L m
  let M := A ⊗ W
  let : W.IsQuasicoherent := SmoothExteriorFiniteType.isQuasicoherent f n i
  have hA : IsInvertible A :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hL.isInvertible m
  let : (W ⊗ A).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight W A hA
  let : M.IsQuasicoherent :=
    (isQuasicoherent X).prop_of_iso (β_ W A) inferInstance
  have hc := EnvelopeProperty.Vanishing.RelativeFrobeniusCohomology.twistPullback_subsingleton_H_iff f p g₀ hL.isProjectiveFactorization M q
  exact (subsingleton_H_iff_moduleIso (hodgeTwistTensorIso f p L m i) (q + 1)).symm.trans hc

end EnvelopeProperty.Vanishing.RelativeFrobeniusCohomology
