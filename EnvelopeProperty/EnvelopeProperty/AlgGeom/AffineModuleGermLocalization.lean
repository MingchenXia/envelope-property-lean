import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.RingTheory.Localization.BaseChange

/-! # Actual affine quasi-coherent section germs and actual localization tensors -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
noncomputable section
universe u

namespace EnvelopeProperty.AffineModuleGermLocalization

variable {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]

/-- Actual affine quasi-coherent zero germs are precisely those killed by a genuine denominator. -/
theorem germ_eq_zero_iff_exists_annihilator (x : X) (m : Γ(M, ⊤)) :
    M.presheaf.germ ⊤ x trivial m = 0 ↔
      ∃ r : Γ(X, ⊤), x ∈ X.basicOpen r ∧ r • m = 0 := by
  constructor
  · intro h
    obtain ⟨W, hxW, i, j, he⟩ := M.presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial
      m 0 (by simpa only [map_zero] using h)
    have hW : M.presheaf.map i.op m = 0 := by simpa only [map_zero] using he
    obtain ⟨_, ⟨r, rfl⟩, hxr, hsub⟩ :=
      Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen X) hxW
    have hr : M.presheaf.map (X.basicOpen r).leTop.op m = 0 := by
      have hres := congrArg (M.presheaf.map (homOfLE hsub).op) hW
      rw [map_zero, ← M.presheaf.map_comp_apply] at hres
      exact hres
    obtain ⟨n, hn⟩ :=
      Scheme.Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffine
        M r m hr
    refine ⟨r ^ n, ?_, hn⟩
    apply (X.mem_basicOpen_top (r ^ n) x).mpr
    simpa only [map_pow] using (((X.mem_basicOpen_top r x).mp hxr).pow n)
  · rintro ⟨r, hxr, hrm⟩
    let : Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) M.val x
    have hmul := M.val.germ_smul (R := X.presheaf) x ⊤ trivial r m
    change M.presheaf.germ ⊤ x trivial (r • m) =
      X.presheaf.germ ⊤ x trivial r • M.presheaf.germ ⊤ x trivial m at hmul
    rw [hrm, map_zero] at hmul
    exact ((X.mem_basicOpen_top r x).mp hxr).smul_eq_zero.mp hmul.symm

variable {R : CommRingCat.{u}}

/-- The actual germ is zero exactly when the literal original section tensor is zero at its prime. -/
theorem germ_eq_zero_iff_localization_tensor (M : (Spec R).Modules) [M.IsQuasicoherent]
    (x : PrimeSpectrum R) (m : moduleSpecΓFunctor.obj M) :
    M.presheaf.germ ⊤ x trivial m = 0 ↔
      (1 : Localization.AtPrime x.asIdeal) ⊗ₜ[R] m = 0 := by
  have ht : (1 : Localization.AtPrime x.asIdeal) ⊗ₜ[R] m = 0 ↔
      ∃ r : x.asIdeal.primeCompl, (r : R) • m = 0 :=
    IsLocalizedModule.eq_zero_iff x.asIdeal.primeCompl
      (TensorProduct.mk R (Localization.AtPrime x.asIdeal) (moduleSpecΓFunctor.obj M) 1)
  rw [germ_eq_zero_iff_exists_annihilator, ht]
  constructor
  · rintro ⟨r, hxr, hrm⟩
    let b : R := (Scheme.ΓSpecIso R).hom r
    have hb : b ∉ x.asIdeal := (PrimeSpectrum.mem_basicOpen b x).mp
      (by simpa only [basicOpen_eq_of_affine'] using hxr)
    refine ⟨⟨b, hb⟩, ?_⟩
    change ((Scheme.ΓSpecIso R).inv.hom b) • (show Γ(M, ⊤) from m) = 0
    simpa only [b, Iso.hom_inv_id_apply] using hrm
  · rintro ⟨r, hrm⟩
    refine ⟨(Scheme.ΓSpecIso R).inv r, ?_, ?_⟩
    · rw [basicOpen_eq_of_affine]
      exact (PrimeSpectrum.mem_basicOpen (r : R) x).mpr r.property
    · exact hrm

end EnvelopeProperty.AffineModuleGermLocalization
