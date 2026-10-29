import EnvelopeProperty.Cartier.SchemeRelativeFrobenius
import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology
import EnvelopeProperty.Global.ProjectiveAffineCover

/-! # Positive cohomology under the actual perfect-field Frobenius twist

The first projection of the geometric Frobenius twist is a scheme isomorphism.
The actual pullback unit and ordered affine Cech comparison transport the
vanishing of whole original positive sheaf cohomology.  No cohomology comparison
or vanishing certificate is supplied as an input.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.FrobeniusCohomology

open Cartier

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- The actual first projection of the genuine Frobenius twist, as a scheme isomorphism. -/
def twistProjectionIso : SchemeRelativeFrobenius.twist p f ≅ X := by
  change Limits.pullback f (SchemeRelativeFrobenius.baseMap (k := k) p) ≅ X
  letI : IsIso (Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p)) :=
    SchemeRelativeFrobenius.twist_fst_isIso p f
  exact asIso (Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p))

/-- The actual pullback unit recovers the original module from its pullback
to the genuine Frobenius twist.  The isomorphism is derived from perfection. -/
def twistPullbackUnitIso (M : X.Modules) :
    M ≅ (pushforward (twistProjectionIso f p).hom).obj
      ((pullback (twistProjectionIso f p).hom).obj M) := by
  let e := twistProjectionIso f p
  let : (pullback e.hom).IsEquivalence := pullback_isEquivalence_of_iso e
  let : (pushforward e.hom).IsEquivalence :=
    (pullbackPushforwardAdjunction e.hom).isEquivalence_right_of_isEquivalence_left
  let : IsIso (pullbackPushforwardAdjunction e.hom).unit := by infer_instance
  exact asIso ((pullbackPushforwardAdjunction e.hom).unit.app M)

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

/-- All positive cohomology vanishing of the original quasicoherent module
is equivalent to that of its actual pullback to the perfect-field Frobenius
twist. The finite affine cover and separatedness are derived from projectivity. -/
theorem twistPullback_subsingleton_H_iff
    (hf : IsProjectiveFactorization f) (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((pullback (twistProjectionIso f p).hom).obj M).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  let e := twistProjectionIso f p
  let g := e.hom
  let N := (pullback g).obj M
  let : X.IsSeparated := ProjectiveAffineCover.separated f hf
  let : (M.restrict g).IsQuasicoherent := inferInstance
  let : N.IsQuasicoherent :=
    (isQuasicoherent (SchemeRelativeFrobenius.twist p f)).prop_of_iso
      ((restrictFunctorIsoPullback g).app M) inferInstance
  let Q := (pushforward g).obj N
  obtain ⟨ι, hlin, hfin, U, hUa, hU⟩ := ProjectiveAffineCover.exists_affine_openCover f hf
  let : LinearOrder ι := hlin
  let : Fintype ι := hfin
  have hpush : Subsingleton (CategoryTheory.Sheaf.H N.sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H Q.sheaf (q + 1)) :=
    AffinePushforwardCohomology.subsingleton_H_iff_pushforward g f N U hU hUa q
  have eu : M ≅ Q := twistPullbackUnitIso f p M
  exact hpush.trans ⟨fun h => subsingleton_H_of_moduleIso eu (q + 1) h,
    fun h => subsingleton_H_of_moduleIso eu.symm (q + 1) h⟩

/-- The actual relative Frobenius is affine over a perfect base, by its
factorization into the original absolute Frobenius and the inverse twist projection. -/
theorem relativeFrobenius_isAffineHom : IsAffineHom (SchemeRelativeFrobenius.map p f) := by
  let π := (twistProjectionIso f p).hom
  have he : SchemeRelativeFrobenius.map p f = SchemeFrobenius.map f p ≫ inv π := by
    apply (cancel_mono π).mp
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    change SchemeRelativeFrobenius.map p f ≫
      Limits.pullback.fst f (SchemeRelativeFrobenius.baseMap (k := k) p) =
        SchemeFrobenius.map f p
    exact SchemeRelativeFrobenius.map_fst p f
  let : IsAffineHom (SchemeFrobenius.map f p) := SchemeFrobenius.isAffineHom_map f p
  rw [he]
  infer_instance

/-- The actual relative-Frobenius pushforward preserves vanishing of every
positive original sheaf cohomology group.  The original projective cover,
affineness, and all Cech comparisons are produced internally. -/
theorem relativePushforward_subsingleton_H_iff
    (hf : IsProjectiveFactorization f) (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((pushforward (SchemeRelativeFrobenius.map p f)).obj M).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  let π := (twistProjectionIso f p).hom
  let S := SchemeRelativeFrobenius.twist p f
  let : X.IsSeparated := ProjectiveAffineCover.separated f hf
  let : S.IsSeparated := ⟨by rw [← Limits.terminal.comp_from π]; infer_instance⟩
  let : IsAffineHom (SchemeRelativeFrobenius.map p f) := relativeFrobenius_isAffineHom f p
  obtain ⟨ι, hlin, hfin, U, hUa, hU⟩ := ProjectiveAffineCover.exists_affine_openCover f hf
  let : LinearOrder ι := hlin
  let : Fintype ι := hfin
  let s : S ⟶ Spec (.of k) :=
    Limits.pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
  exact (AffinePushforwardCohomology.subsingleton_H_iff_pushforward
    (SchemeRelativeFrobenius.map p f) s M (fun i => π ⁻¹ᵁ U i)
      (π.iSup_preimage_eq_top hU) (fun i => (hUa i).preimage π) q).symm

end EnvelopeProperty.Vanishing.FrobeniusCohomology
