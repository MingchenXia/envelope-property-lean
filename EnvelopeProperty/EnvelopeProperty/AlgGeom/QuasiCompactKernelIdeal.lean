import EnvelopeProperty.AlgGeom.QuasiCompactSectionAnnihilation
import EnvelopeProperty.AlgGeom.ModuleKernelIdeal

/-! # The entire actual kernel ideal of an original quasi-compact pushforward map -/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g]
    (N : Y.Modules) [N.IsQuasicoherent]

/-- Genuine quasiCompactness and quasicoherence derive actual denominator
annihilation for the WHOLE original pushed section, without pushforwardQC. -/
theorem pushforwardSection_eq_zero_after_power (U : X.affineOpens)
    (r : Γ(X, U.1)) (m : Γ((pushforward g).obj N, U.1))
    (hm : ((pushforward g).obj N).presheaf.map
      (homOfLE (X.basicOpen_le r)).op m = 0) :
    ∃ n : ℕ, r ^ n • m = 0 := by
  have hmY : N.presheaf.map (homOfLE (Y.basicOpen_le (g.app U.1 r))).op m = 0 := by
    let hpre : g ⁻¹ᵁ X.basicOpen r ≤ g ⁻¹ᵁ U.1 := fun x hx ↦ X.basicOpen_le r hx
    change N.presheaf.map (homOfLE hpre).op m = 0 at hm
    have ht : ∀ (D : Y.Opens) (hD : D ≤ g ⁻¹ᵁ U.1),
        g ⁻¹ᵁ X.basicOpen r = D →
          N.presheaf.map (homOfLE hD).op m = 0 := by
      intro D hD he
      subst D
      exact hm
    exact ht _ (Y.basicOpen_le (g.app U.1 r)) (g.preimage_basicOpen r)
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isCompact
    N (g ⁻¹ᵁ U.1) (g.isCompact_preimage U.2.isCompact) (g.app U.1 r) m hmY
  refine ⟨n, ?_⟩
  change (g.app U.1 (r ^ n)) • (show Γ(N, g ⁻¹ᵁ U.1) from m) = 0
  exact (congrArg (fun a : Γ(Y, g ⁻¹ᵁ U.1) ↦ a • (show Γ(N, g ⁻¹ᵁ U.1) from m))
    (map_pow (g.app U.1).hom r n)).trans hn

private theorem kernelIdeal_localization_of_zero_power
    {R S L P : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization (Submonoid.powers r) S]
    [AddCommGroup L] [AddCommGroup P] [Module R L] [Module R P] [Module S P]
    (a : R →ₗ[R] L) (b : S →ₗ[S] P) (ρ : L →ₗ[R] P)
    (hsquare : ∀ x : R, ρ (a x) = b (algebraMap R S x))
    (hkill : ∀ m : L, ρ m = 0 → ∃ n : ℕ, r ^ n • m = 0) :
    Ideal.map (algebraMap R S) a.ker = b.ker := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change b (algebraMap R S x) = 0
    change a x = 0 at hx
    exact (hsquare x).symm.trans ((congrArg ρ hx).trans (map_zero ρ))
  · intro x hx
    obtain ⟨z, t, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers r) x
    change b (IsLocalization.mk' S z t) = 0 at hx
    have hρ : ρ (a z) = 0 := by
      rw [hsquare, ← IsLocalization.mk'_spec' S z t]
      change b ((algebraMap R S t) • IsLocalization.mk' S z t) = 0
      rw [b.map_smul, hx, smul_zero]
    obtain ⟨n, hn⟩ := hkill (a z) hρ
    apply (IsLocalization.mk'_mem_map_algebraMap_iff
      (Submonoid.powers r) S a.ker z t).mpr
    refine ⟨r ^ n, ⟨n, rfl⟩, ?_⟩
    change a ((r ^ n) • z) = 0
    rw [a.map_smul]
    exact hn

variable (α : unitObj X ⟶ (pushforward g).obj N)

/-- Actual quasiCompactness derives principal-open compatibility of the
ENTIRE original affine kernel, with NO whole pushforwardQC premise. -/
theorem map_unitMapPushforwardKernelIdeal_basicOpen
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    (unitMapKernelIdeal α U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      unitMapKernelIdeal α (X.affineBasicOpen r) := by
  let R := Γ(X, U.1)
  let S := Γ(X, X.basicOpen r)
  let M := (pushforward g).obj N
  let L := Γ(M, U.1)
  let P := Γ(M, X.basicOpen r)
  let h := X.basicOpen_le r
  let f : R →+* S := (X.presheaf.map (homOfLE h).op).hom
  let : Algebra R S := f.toAlgebra
  let : IsLocalization (Submonoid.powers r) S := U.2.isLocalization_basicOpen r
  let : Module R P := Module.compHom _ f
  let a : R →ₗ[R] L := (α.val.app (.op U.1)).hom
  let b : S →ₗ[S] P := (α.val.app (.op (X.basicOpen r))).hom
  let ρ : L →ₗ[R] P := M.resₗ h
  have hsquare : ∀ x : R, ρ (a x) = b (algebraMap R S x) := by
    intro x
    exact (PresheafOfModules.naturality_apply α.val (homOfLE h).op x).symm
  change Ideal.map (algebraMap R S) a.ker = b.ker
  exact kernelIdeal_localization_of_zero_power r a b ρ hsquare
    (fun m hm ↦ pushforwardSection_eq_zero_after_power g N U r m hm)

/-- The actual whole ideal sheaf with the ENTIRE original section kernels;
actual compact denominator clearing proves every compatibility internally. -/
def unitMapPushforwardKernelIdealSheaf : X.IdealSheafData where
  ideal U := unitMapKernelIdeal α U
  map_ideal_basicOpen U r := map_unitMapPushforwardKernelIdeal_basicOpen g N α U r

/-- Every component is precisely the ENTIRE original affine section-map kernel. -/
theorem unitMapPushforwardKernelIdealSheaf_ideal (U : X.affineOpens) :
    (unitMapPushforwardKernelIdealSheaf g N α).ideal U = unitMapKernelIdeal α U := rfl

/-- Membership is exactly vanishing under the SAME original whole pushed map. -/
theorem mem_unitMapPushforwardKernelIdealSheaf_ideal_iff
    (U : X.affineOpens) (a : Γ(X, U.1)) :
    a ∈ (unitMapPushforwardKernelIdealSheaf g N α).ideal U ↔
      α.val.app (.op U.1) a = 0 := Iff.rfl

end
end AlgebraicGeometry.Scheme.Modules
