module

public import EnvelopeProperty.AlgGeom.SchemeModuleStalkLinearity
public import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-! # Actual associated points and socle elements in the original module stalk -/

@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open EnvelopeProperty.SchemeModuleStalkLinearity
universe u
namespace EnvelopeProperty.SchemeModuleAssociatedPoint

private theorem exists_affineSection_ne_zero {X : Scheme.{u}} (M : X.Modules)
    (hM : ¬ Limits.IsZero M) :
    ∃ U : X.affineOpens, ∃ t : Γ(M, U.1), t ≠ 0 := by
  classical
  by_contra h
  have hz (U : X.affineOpens) (t : Γ(M, U.1)) : t = 0 := by
    by_contra ht
    exact h ⟨U, t, ht⟩
  apply hM
  apply (Limits.IsZero.iff_id_eq_zero M).mpr
  apply Scheme.Modules.hom_ext
  intro W
  ext t
  change t = 0
  refine TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) W t 0 ?_
  intro x hx
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hzero : M.presheaf.map (homOfLE hVW).op t = 0 := hz ⟨V, hV⟩ _
  calc
    M.presheaf.germ W x hx t =
        M.presheaf.germ V x hxV (M.presheaf.map (homOfLE hVW).op t) :=
      (M.presheaf.germ_res_apply (homOfLE hVW) x hxV t).symm
    _ = 0 := by
      erw [hzero]
      exact (M.presheaf.germ V x hxV).hom.map_zero
    _ = M.presheaf.germ W x hx 0 := (M.presheaf.germ W x hx).hom.map_zero.symm

private theorem associatedSection_germ_socle {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (U : X.affineOpens) (eta : U.1) (t : Γ(M, U.1))
    (hann : (U.2.primeIdealOf eta).asIdeal =
      (⊥ : Submodule Γ(X, U.1) Γ(M, U.1)).colon {t}) :
    M.presheaf.germ U.1 eta eta.2 t ≠ 0 ∧
      ∀ r : X.presheaf.stalk eta,
        r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk eta) →
          r • M.presheaf.germ U.1 eta eta.2 t = 0 := by
  let p := (U.2.primeIdealOf eta).asIdeal
  let : p.IsPrime := (U.2.primeIdealOf eta).isPrime
  let := X.presheaf.algebra_section_stalk eta
  let : IsLocalization.AtPrime (X.presheaf.stalk eta) p :=
    U.2.isLocalization_stalk eta
  let g := M.presheaf.germ U.1 eta eta.2
  have hmax : p.map (X.presheaf.germ U.1 eta eta.2).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk eta) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p (X.presheaf.stalk eta)
  have hAnn : p.map (X.presheaf.germ U.1 eta eta.2).hom ≤
      (⊥ : Submodule (X.presheaf.stalk eta) (M.presheaf.stalk eta)).colon {g t} := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    have hrt : r • t = 0 := by
      have hr' : r ∈ (⊥ : Submodule Γ(X, U.1) Γ(M, U.1)).colon {t} := hann ▸ hr
      simpa [Submodule.mem_colon_singleton] using hr'
    have hk : X.presheaf.germ U.1 eta eta.2 r • g t = 0 :=
      (PresheafOfModules.germ_smul (R := X.presheaf) M.val eta U.1 eta.2 r t).symm.trans
        ((congrArg g hrt).trans g.hom.map_zero)
    change X.presheaf.germ U.1 eta eta.2 r ∈
      (⊥ : Submodule (X.presheaf.stalk eta) (M.presheaf.stalk eta)).colon {g t}
    simpa [Submodule.mem_colon_singleton] using hk
  constructor
  · intro hm
    have hg : M.presheaf.germ U.1 eta eta.2 t = M.presheaf.germ U.1 eta eta.2 0 :=
      hm.trans (M.presheaf.germ U.1 eta eta.2).hom.map_zero.symm
    obtain ⟨W, hetaW, i, j, hw⟩ := M.presheaf.germ_eq eta eta.2 eta.2 t 0 hg
    have hWzero : M.presheaf.map i.op t = 0 :=
      hw.trans (M.presheaf.map j.op).hom.map_zero
    obtain ⟨s, hsW, hetas⟩ := U.2.exists_basicOpen_le ⟨eta.1, hetaW⟩ eta.2
    have hres : M.presheaf.map (homOfLE (X.basicOpen_le s)).op t = 0 := by
      have he : (homOfLE (X.basicOpen_le s)).op = i.op ≫ (homOfLE hsW).op :=
        Subsingleton.elim _ _
      erw [he, M.presheaf.map_comp_apply, hWzero]
      exact (M.presheaf.map (homOfLE hsW).op).hom.map_zero
    obtain ⟨n, hn⟩ :=
      Scheme.Modules.exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isQuasicoherent_of_isAffineOpen
        M U s t hres
    have hpow : s ^ n ∈ p := by
      change s ^ n ∈ (U.2.primeIdealOf eta).asIdeal
      rw [hann]
      simpa [Submodule.mem_colon_singleton] using hn
    have hsp : s ∈ p := (U.2.primeIdealOf eta).isPrime.mem_of_pow_mem n hpow
    have hms : X.presheaf.germ U.1 eta eta.2 s ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk eta) :=
      hmax ▸ Ideal.mem_map_of_mem _ hsp
    have hnu : ¬ IsUnit (X.presheaf.germ U.1 eta eta.2 s) :=
      (IsLocalRing.mem_maximalIdeal _).mp hms
    exact hnu ((X.mem_basicOpen s eta eta.2).mp hetas)
  · intro r hr
    have hk := hAnn (hmax.symm ▸ hr)
    simpa [Submodule.mem_colon_singleton] using hk

/-- The actual nonzero coherent module internally supplies an original point
and a nonzero element of its SAME native stalk killed by the original maximal ideal. -/
theorem exists_nativeStalk_socle {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (hM : ¬ Limits.IsZero M) :
    ∃ eta : X, ∃ m : M.presheaf.stalk eta, m ≠ 0 ∧
      ∀ r : X.presheaf.stalk eta,
        r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk eta) → r • m = 0 := by
  obtain ⟨U, t, ht⟩ := exists_affineSection_ne_zero M hM
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  let : Nontrivial Γ(M, U.1) := ⟨t, 0, ht⟩
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty Γ(X, U.1) Γ(M, U.1)
  obtain ⟨hpPrime, a, ha⟩ := isAssociatedPrime_iff.mp hp
  let q : PrimeSpectrum Γ(X, U.1) := ⟨p, hpPrime⟩
  let eta : U.1 := U.2.isoSpec.inv q
  have he : U.2.primeIdealOf eta = q := by
    exact congrArg (fun f : Spec (CommRingCat.of Γ(X, U.1)) ⟶
      Spec (CommRingCat.of Γ(X, U.1)) => f q) U.2.isoSpec.inv_hom_id
  have hann : (U.2.primeIdealOf eta).asIdeal =
      (⊥ : Submodule Γ(X, U.1) Γ(M, U.1)).colon {a} :=
    (congrArg PrimeSpectrum.asIdeal he).trans ha
  exact ⟨eta.1, M.presheaf.germ U.1 eta eta.2 a, associatedSection_germ_socle M U eta a hann⟩

/-- The actual reduced closure of the same original point has original stalk
ideal contained in the SAME original maximal ideal. -/
theorem pointClosure_stalkIdeal_le_maximalIdeal {X : Scheme.{u}} (eta : X) :
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({eta} : Set X), isClosed_closure⟩ : TopologicalSpace.Closeds X)).stalkIdeal eta ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk eta) := by
  obtain ⟨U, heta⟩ : ∃ U : X.affineOpens, eta ∈ U.1 := by
    have hx : eta ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X, Opens.mem_iSup] at hx
    exact hx
  let Z : TopologicalSpace.Closeds X := ⟨closure ({eta} : Set X), isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let p := (U.2.primeIdealOf ⟨eta, heta⟩).asIdeal
  let : p.IsPrime := (U.2.primeIdealOf ⟨eta, heta⟩).isPrime
  let := X.presheaf.algebra_section_stalk ⟨eta, heta⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk eta) p :=
    U.2.isLocalization_stalk ⟨eta, heta⟩
  have hmax : p.map (X.presheaf.germ U.1 eta heta).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk eta) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p (X.presheaf.stalk eta)
  have hideal : I.ideal U ≤ p := by
    intro r hr
    have hr' : r ∈ PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X)) := by
      simpa only [I, Scheme.IdealSheafData.vanishingIdeal_ideal] using hr
    apply (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr' (U.2.primeIdealOf ⟨eta, heta⟩)
    change U.2.fromSpec (U.2.primeIdealOf ⟨eta, heta⟩) ∈ closure ({eta} : Set X)
    rw [U.2.fromSpec_primeIdealOf ⟨eta, heta⟩]
    exact subset_closure (Set.mem_singleton eta)
  change I.stalkIdeal eta ≤ _
  rw [I.stalkIdeal_eq_map_germ U heta]
  exact (Ideal.map_mono hideal).trans hmax.le

end EnvelopeProperty.SchemeModuleAssociatedPoint
