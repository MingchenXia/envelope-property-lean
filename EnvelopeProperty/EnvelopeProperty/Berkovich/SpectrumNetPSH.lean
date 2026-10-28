import EnvelopeProperty.Berkovich.SchemeAffineLocalPSH
import EnvelopeProperty.Berkovich.SchemeLocalPSHAlgebra
import EnvelopeProperty.Berkovich.RelativeLocalPSHContinuity
import EnvelopeProperty.Berkovich.ExtensionLifts
import EnvelopeProperty.ERealDirectedLimits

/-! # Actual directed convex PL presentations on whole native affine spectra

These additional classes retain genuine nonempty directed index sets; the
original sequence-based local psh definitions remain unchanged.
-/

open scoped NNReal Topology Classical
open Topology Filter CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSpectrum
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {v : Valuation R ℝ≥0}
  {U V : Set (RelativeSpectrum v A)} {u w : RelativeSpectrum v A → EReal}

/-- Every actual original convex PL presentation has an open domain. -/
theorem IsConvexPLOn.isOpen (hu : IsConvexPLOn U u) : IsOpen U := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hW, hxW, hWU, _⟩ := hu x hx
  exact ⟨W, hWU, hW, hxW⟩

/-- Genuine original finite-coefficient expressions restrict to actual open subsets. -/
theorem IsConvexPLOn.mono (hu : IsConvexPLOn U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsConvexPLOn V u := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, n, a, s, hs, ha, hform⟩ := hu x (hVU hx)
  exact ⟨W ∩ V, hW.inter hV, ⟨hxW, hx⟩, Set.inter_subset_right,
    n, a, s, hs, (fun y hy => ha y hy.1), (fun y hy => hform y hy.1)⟩

/-- A genuine rational constant translates every original finite-coefficient expression. -/
theorem IsConvexPLOn.add_const (hu : IsConvexPLOn U u) (q : ℚ) :
    IsConvexPLOn U (fun y => u y + ((q : ℝ) : EReal)) := by
  have h := ((RelativeSchemeValuedPoint.IsConvexPLOn.of_affineSpectrum hu).add_const q).to_affineSpectrum
  simpa only [Set.preimage_preimage, Function.comp_def, Homeomorph.apply_symm_apply,
    Set.preimage_id'] using h

/-- A whole original convex PL net with its actual nonempty directed index and infimum. -/
def IsDecrConvexPLNetLimitOn (U : Set (RelativeSpectrum v A))
    (u : RelativeSpectrum v A → EReal) : Prop :=
  ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
    (a : J → RelativeSpectrum v A → EReal),
    (∀ j, IsConvexPLOn U (a j)) ∧
      (∀ y ∈ U, Antitone fun j => a j y) ∧ ∀ y ∈ U, u y = ⨅ j, a j y

/-- Genuine local directed presentations on the exact original analytic neighbourhoods. -/
def IsLocallyNetPSHOn (U : Set (RelativeSpectrum v A))
    (u : RelativeSpectrum v A → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (RelativeSpectrum v A), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    IsDecrConvexPLNetLimitOn W u

/-- One actual index witnesses openness of the original directed-presentation domain. -/
theorem IsDecrConvexPLNetLimitOn.isOpen (hu : IsDecrConvexPLNetLimitOn U u) : IsOpen U := by
  obtain ⟨J, hJ, hd, hn, a, ha, _⟩ := hu
  exact (ha (Classical.choice hn)).isOpen

/-- Entire actual directed presentations restrict to the same original open subset. -/
theorem IsDecrConvexPLNetLimitOn.mono (hu : IsDecrConvexPLNetLimitOn U u)
    (hV : IsOpen V) (hVU : V ⊆ U) : IsDecrConvexPLNetLimitOn V u := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, a, fun j => (ha j).mono hV hVU,
    fun y hy => hanti y (hVU hy), fun y hy => hlim y (hVU hy)⟩

/-- Domainwise equality changes only the actual pointwise-infimum identity. -/
theorem IsDecrConvexPLNetLimitOn.congr (hu : IsDecrConvexPLNetLimitOn U u)
    (heq : ∀ y ∈ U, u y = w y) : IsDecrConvexPLNetLimitOn U w := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, a, ha, hanti, fun y hy => (heq y hy).symm.trans (hlim y hy)⟩

/-- The actual directed presentation supplies its own original local neighbourhood. -/
theorem IsDecrConvexPLNetLimitOn.isLocallyNetPSHOn (hu : IsDecrConvexPLNetLimitOn U u) :
    IsLocallyNetPSHOn U u := fun _ hx => ⟨U, hu.isOpen, hx, subset_rfl, hu⟩

/-- A genuine finite term bounds the original whole infimum above. -/
theorem IsDecrConvexPLNetLimitOn.ne_top (hu : IsDecrConvexPLNetLimitOn U u)
    {x : RelativeSpectrum v A} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨J, hJ, hd, hn, a, ha, _, hlim⟩ := hu
  exact ne_top_of_le_ne_top ((ha (Classical.choice hn)).ne_top hx)
    ((hlim x hx).trans_le (iInf_le _ (Classical.choice hn)))

/-- One genuine continuous term below each threshold controls the entire original infimum. -/
theorem IsDecrConvexPLNetLimitOn.upperSemicontinuousOn
    (hu : IsDecrConvexPLNetLimitOn U u) : UpperSemicontinuousOn u U := by
  obtain ⟨J, hJ, hd, hn, a, ha, _, hlim⟩ := hu
  intro x hx c hc
  change u x < c at hc
  rw [hlim x hx] at hc
  obtain ⟨j, hj⟩ := iInf_lt_iff.1 hc
  have hev : ∀ᶠ y in 𝓝 x, a j y < c :=
    ((ha j).continuousAt hx).eventually (gt_mem_nhds hj)
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hev, self_mem_nhdsWithin]
    with y hy hyU
  rw [hlim y hyU]
  exact (iInf_le _ j).trans_lt hy

/-- Actual coefficient comaps retain the same original directed index, terms and infimum. -/
theorem IsDecrConvexPLNetLimitOn.comp_comap (hu : IsDecrConvexPLNetLimitOn U u)
    (φ : A →ₐ[R] B) : IsDecrConvexPLNetLimitOn (comap φ ⁻¹' U)
      (fun y => u (comap φ y)) := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, (fun j y => a j (comap φ y)),
    fun j => (ha j).comp_comap φ, fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- The unchanged original local neighbourhoods pull back through the actual coefficient map. -/
theorem IsLocallyNetPSHOn.comp_comap (hu : IsLocallyNetPSHOn U u) (φ : A →ₐ[R] B) :
    IsLocallyNetPSHOn (comap φ ⁻¹' U) (fun y => u (comap φ y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu (comap φ y) hy
  exact ⟨comap φ ⁻¹' W, hW.preimage (continuous_comap φ), hyW,
    Set.preimage_mono hWU, hloc.comp_comap φ⟩

/-- The same local function is finite above on its original local presentation domain. -/
theorem IsLocallyNetPSHOn.ne_top (hu : IsLocallyNetPSHOn U u)
    {x : RelativeSpectrum v A} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨W, _, hxW, _, hw⟩ := hu x hx
  exact hw.ne_top hxW

/-- Genuine local directed presentations imply upper semicontinuity of the original function. -/
theorem IsLocallyNetPSHOn.upperSemicontinuousOn (hu : IsLocallyNetPSHOn U u) :
    UpperSemicontinuousOn u U := by
  intro x hx c hc
  obtain ⟨W, hW, hxW, _, hw⟩ := hu x hx
  have hev := hw.upperSemicontinuousOn x hxW c hc
  have hle : 𝓝 x ≤ 𝓝[W] x := by
    change 𝓝 x ≤ 𝓝 x ⊓ Filter.principal W
    exact le_inf le_rfl (Filter.le_principal_iff.mpr (hW.mem_nhds hxW))
  exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds.trans hle) hev

/-- Actual local presentation neighbourhoods make the whole original domain open. -/
theorem IsLocallyNetPSHOn.isOpen (hu : IsLocallyNetPSHOn U u) : IsOpen U := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hW, hxW, hWU, _⟩ := hu x hx
  exact ⟨W, hWU, hW, hxW⟩

/-- Actual open restriction uses the original neighbourhood intersections. -/
theorem IsLocallyNetPSHOn.mono (hu : IsLocallyNetPSHOn U u) (hV : IsOpen V)
    (hVU : V ⊆ U) : IsLocallyNetPSHOn V u := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hlim⟩ := hu x (hVU hx)
  exact ⟨W ∩ V, hW.inter hV, ⟨hxW, hx⟩, Set.inter_subset_right,
    hlim.mono (hW.inter hV) Set.inter_subset_left⟩

/-- Domainwise equality preserves the same actual directed local presentations. -/
theorem IsLocallyNetPSHOn.congr (hu : IsLocallyNetPSHOn U u)
    (heq : ∀ y ∈ U, u y = w y) : IsLocallyNetPSHOn U w := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hlim⟩ := hu x hx
  exact ⟨W, hW, hxW, hWU, hlim.congr (fun y hy => heq y (hWU hy))⟩

section Scalar
variable {S : Type u} [CommRing S] [Algebra R S] {w : Valuation S ℝ≥0}
  (hwv : ∀ r, w (algebraMap R S r) = v r)

/-- Genuine whole scalar restriction preserves every original directed presentation. -/
theorem IsDecrConvexPLNetLimitOn.fc_comp_baseChangeRestriction
    (hu : IsDecrConvexPLNetLimitOn U u) :
    IsDecrConvexPLNetLimitOn (baseChangeRestriction hwv ⁻¹' U)
      (fun y => u (baseChangeRestriction hwv y)) := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, (fun j y => a j (baseChangeRestriction hwv y)),
    fun j => (ha j).fc_comp_baseChangeRestriction hwv,
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- Actual scalar change pulls back the whole original directed local class. -/
theorem IsLocallyNetPSHOn.fc_comp_baseChangeRestriction (hu : IsLocallyNetPSHOn U u) :
    IsLocallyNetPSHOn (baseChangeRestriction hwv ⁻¹' U)
      (fun y => u (baseChangeRestriction hwv y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu (baseChangeRestriction hwv y) hy
  exact ⟨baseChangeRestriction hwv ⁻¹' W,
    hW.preimage (continuous_baseChangeRestriction hwv), hyW,
    Set.preimage_mono hWU, hloc.fc_comp_baseChangeRestriction hwv⟩

end Scalar
end EnvelopeProperty.Berkovich.RelativeSpectrum
