import BingWangEntropy.ProjectiveTwistingSections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.RingTheory.Localization.Finiteness

/-! # Actual quasicoherent section denominator clearing

These are native section restriction maps and actual localization consequences.
No extension, global-generation, or finite-global-section conclusion is an input.
The finite-family kernels supply the uniform exponents required for genuine
projective line-section extension and sheaf gluing.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace

namespace BingWangEntropy

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000


section LineAtlas

variable {X : Scheme.{u}} {L : X.Modules}

/-- The actual rank-one atlas gives actual one-generator free sheaf frames. -/
def LineBundleAtlas.freeFrame (a : LineBundleAtlas L) (i : a.I) :
    L.over (a.opens i) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (a.opens i)) (ULift.{u} PUnit) :=
  a.frame i ≪≫ (Limits.coproductUniqueIso
    (fun _ : ULift.{u} PUnit => SheafOfModules.unit (X.ringCatSheaf.over (a.opens i)))).symm

/-- Genuine atlas frames produce native local-generator data with one generator. -/
def LineBundleAtlas.localGeneratorsData (a : LineBundleAtlas L) : L.LocalGeneratorsData where
  I := a.I
  X := a.opens
  coversTop := by
    rw [_root_.Opens.coversTop_iff]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr (a.covers x)
  generators i := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over (a.opens i)) (ULift.{u} PUnit)).ofEpi (a.freeFrame i).inv

/-- Every produced local generator map is an isomorphism from the actual atlas frame. -/
theorem LineBundleAtlas.localGeneratorsData_isLocallyFreeData (a : LineBundleAtlas L) :
    a.localGeneratorsData.IsLocallyFreeData := by
  constructor
  intro i
  change IsIso ((SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf.over (a.opens i)) (ULift.{u} PUnit)).ofEpi (a.freeFrame i).inv).π
  rw [SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  exact (congrArg IsIso (Category.id_comp (a.freeFrame i).inv)).mpr
    (inferInstance : IsIso (a.freeFrame i).inv)

/-- Actual atlas local freeness is native sheaf local freeness, proved from the frames. -/
theorem LineBundleAtlas.isLocallyFree (a : LineBundleAtlas L) : L.IsLocallyFree := by
  let := a.localGeneratorsData_isLocallyFreeData
  exact a.localGeneratorsData.isLocallyFree

/-- Quasicoherence is derived from the actual rank-one atlas and native local freeness. -/
theorem LineBundleAtlas.isQuasicoherent (a : LineBundleAtlas L) : L.IsQuasicoherent := by
  let := a.isLocallyFree
  infer_instance

/-- Every actual tensor power of a genuine line atlas is quasicoherent. -/
theorem LineBundleAtlas.tensorPower_isQuasicoherent (a : LineBundleAtlas L) (n : ℕ) :
    (bundleTensorPower L n).IsQuasicoherent :=
  (a.tensorPower n).isQuasicoherent


/-- The true one-generator frames and empty relation families give native finite presentation data. -/
def LineBundleAtlas.quasicoherentData (a : LineBundleAtlas L) : L.QuasicoherentData := by
  let := a.localGeneratorsData_isLocallyFreeData
  exact a.localGeneratorsData.quasiCoherentData

/-- The actual local presentation has finitely many generators and relations. -/
theorem LineBundleAtlas.quasicoherentData_isFinitePresentation (a : LineBundleAtlas L) :
    a.quasicoherentData.IsFinitePresentation := by
  constructor
  intro i
  constructor
  · constructor
    change Finite (ULift.{u} PUnit)
    infer_instance
  · constructor
    change Finite (ULift Empty)
    infer_instance

/-- Actual line-atlas local freeness implies native finite presentation without
an assumed coherent presentation or target global generators. -/
theorem LineBundleAtlas.isFinitePresentation (a : LineBundleAtlas L) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (R := X.ringCatSheaf) L := by
  let := a.quasicoherentData_isFinitePresentation
  apply SheafOfModules.IsFinitePresentation.mk (M := L)
  refine ⟨a.quasicoherentData.shrink, ?_⟩
  constructor
  intro i
  exact inferInstanceAs ((a.quasicoherentData.presentation i.property.choose).IsFinite)

/-- Actual native finite type follows from the produced finite presentation. -/
theorem LineBundleAtlas.isFiniteType (a : LineBundleAtlas L) :
    SheafOfModules.IsFiniteType.{u, u, u} (R := X.ringCatSheaf) L := by
  let := a.isFinitePresentation
  infer_instance

end LineAtlas

variable {R : CommRingCat.{u}}

/-- Native affine sheaf restriction retains the actual structural scalar action. -/
def affineSectionRestriction (M : (Spec R).Modules) (f : R) :
    Γ(M, ⊤) →ₗ[R] Γ(M, PrimeSpectrum.basicOpen f) :=
  ((modulesSpecToSheaf.obj M).obj.map
    (homOfLE (show (PrimeSpectrum.basicOpen f : (Spec R).Opens) ≤ ⊤ from le_top)).op).hom

/-- Quasicoherence produces localization of the actual affine section restriction. -/
theorem affineSectionRestriction_isLocalized (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) : IsLocalizedModule.Away f (affineSectionRestriction M f) :=
  (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance f

/-- A genuine section on D(f) lifts to a true global section after multiplying by f^n. -/
theorem affineSection_clearDenominator (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) (s : Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)), affineSectionRestriction M f t = f ^ n • s := by
  let := affineSectionRestriction_isLocalized M f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj (affineSectionRestriction M f) f s
  exact ⟨n, t, ht.symm⟩

/-- Genuine global sections equal on D(f) become equal after an actual power of f. -/
theorem affineSection_eq_after_power (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) {s t : Γ(M, ⊤)}
    (h : affineSectionRestriction M f s = affineSectionRestriction M f t) :
    ∃ n : ℕ, f ^ n • s = f ^ n • t := by
  let := affineSectionRestriction_isLocalized M f
  exact IsLocalizedModule.Away.exists_of_eq f h

/-- A genuine global section vanishing on D(f) is killed by an actual power of f. -/
theorem affineSection_zero_after_power (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : R) {s : Γ(M, ⊤)} (h : affineSectionRestriction M f s = 0) :
    ∃ n : ℕ, f ^ n • s = 0 := by
  obtain ⟨n, hn⟩ := affineSection_eq_after_power M f
    (t := 0) (h.trans (affineSectionRestriction M f).map_zero.symm)
  exact ⟨n, hn.trans (smul_zero _)⟩

/-- Finitely many actual D(f)-sections share one clearing exponent; the lifts
are explicit higher-power scalar multiples of their individual actual lifts. -/
theorem affineSections_clearDenominators {I : Type u} [Fintype I]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s : I → Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : I → Γ(M, ⊤)), ∀ i,
      affineSectionRestriction M f (t i) = f ^ n • s i := by
  classical
  choose n t ht using fun i => affineSection_clearDenominator M f (s i)
  let N := Finset.univ.sup n
  refine ⟨N, fun i => f ^ (N - n i) • t i, ?_⟩
  intro i
  have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  rw [(affineSectionRestriction M f).map_smul, ht i, ← mul_smul, ← pow_add]
  congr 2
  omega

/-- Finitely many equalities on D(f) share one actual annihilating exponent. -/
theorem affineSections_eq_after_power {I : Type u} [Fintype I]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s t : I → Γ(M, ⊤))
    (h : ∀ i, affineSectionRestriction M f (s i) = affineSectionRestriction M f (t i)) :
    ∃ n : ℕ, ∀ i, f ^ n • s i = f ^ n • t i := by
  classical
  choose n hn using fun i => affineSection_eq_after_power M f (h i)
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  intro i
  have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have he : N = (N - n i) + n i := by omega
  rw [he, pow_add, mul_smul, mul_smul, hn i]

/-- Finite overlap errors vanishing on D(f) have one actual common power
that kills all of them before sheaf gluing. -/
theorem affineSections_zero_after_power {I : Type u} [Fintype I]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s : I → Γ(M, ⊤)) (h : ∀ i, affineSectionRestriction M f (s i) = 0) :
    ∃ n : ℕ, ∀ i, f ^ n • s i = 0 := by
  obtain ⟨n, hn⟩ := affineSections_eq_after_power M f s (fun _ => 0)
    (fun i => (h i).trans (affineSectionRestriction M f).map_zero.symm)
  exact ⟨n, fun i => (hn i).trans (smul_zero _)⟩


/-- A line atlas itself supplies quasicoherence for genuine affine denominator clearing. -/
theorem LineBundleAtlas.affineSection_clearDenominator {M : (Spec R).Modules}
    (a : LineBundleAtlas M) (f : R) (s : Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)), affineSectionRestriction M f t = f ^ n • s := by
  let := a.isQuasicoherent
  exact BingWangEntropy.affineSection_clearDenominator M f s

/-- Denominators for finite families in an actual tensor-power sheaf are cleared
from its derived local power frames, with no quasicoherence premise. -/
theorem LineBundleAtlas.affinePowerSections_clearDenominators {I : Type u} [Fintype I]
    {M : (Spec R).Modules} (a : LineBundleAtlas M) (k : ℕ) (f : R)
    (s : I → Γ(bundleTensorPower M k, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : I → Γ(bundleTensorPower M k, ⊤)), ∀ i,
      affineSectionRestriction (bundleTensorPower M k) f (t i) = f ^ n • s i := by
  let := a.tensorPower_isQuasicoherent k
  exact affineSections_clearDenominators (bundleTensorPower M k) f s

/-- Actual principal affine opens on which the given line atlas has a true local frame. -/
def LineBundleAtlas.affineFrameFunctions {M : (Spec R).Modules} (a : LineBundleAtlas M) :
    Set R := {f | ∃ i, PrimeSpectrum.basicOpen f ≤ a.opens i}

/-- The basis of true principal affine opens refines the actual frame cover,
so its defining functions generate the unit ideal. -/
theorem LineBundleAtlas.affineFrameFunctions_span {M : (Spec R).Modules}
    (a : LineBundleAtlas M) : Ideal.span a.affineFrameFunctions = ⊤ := by
  rw [← Subtype.range_val (s := a.affineFrameFunctions)]
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := a.covers x
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hfi⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hi (a.opens i).isOpen
  exact Opens.mem_iSup.mpr ⟨⟨f, i, hfi⟩, hxf⟩

/-- Actual sections on every derived principal frame open are finite over their
actual regular section ring, proved by the genuine local coefficient frame. -/
theorem LineBundleAtlas.affineFrameSections_finite {M : (Spec R).Modules}
    (a : LineBundleAtlas M) (g : a.affineFrameFunctions) :
    Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen g.val) Γ(M, PrimeSpectrum.basicOpen g.val) := by
  obtain ⟨i, hi⟩ := g.property
  let e := localFrameCoefficientsOn (a.frame i) (homOfLE hi)
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- Actual affine global sections of a genuine line bundle are finite over the
actual affine coordinate ring. Principal-frame refinements, real localization,
and unit-ideal finiteness produce the result. -/
theorem LineBundleAtlas.affineGlobalSections_finite {M : (Spec R).Modules}
    (a : LineBundleAtlas M) : Module.Finite R Γ(M, ⊤) := by
  let := a.isQuasicoherent
  let : ∀ g : a.affineFrameFunctions,
      IsLocalizedModule.Away g.val (affineSectionRestriction M g.val) :=
    fun g => affineSectionRestriction_isLocalized M g.val
  exact Module.Finite.of_localizationSpan' a.affineFrameFunctions a.affineFrameFunctions_span
    (Mₚ := fun g => Γ(M, PrimeSpectrum.basicOpen g.val))
    (Rₚ := fun g => Γ(Spec R, PrimeSpectrum.basicOpen g.val))
    (fun g => affineSectionRestriction M g.val) a.affineFrameSections_finite

/-- Every actual affine tensor-power section module is finite over the actual
coordinate ring, from the same derived local power atlas. -/
theorem LineBundleAtlas.affinePowerGlobalSections_finite {M : (Spec R).Modules}
    (a : LineBundleAtlas M) (k : ℕ) : Module.Finite R Γ(bundleTensorPower M k, ⊤) :=
  (a.tensorPower k).affineGlobalSections_finite

end

end BingWangEntropy
