import EnvelopeProperty.Berkovich.SpectrumNetPSH

/-! # Genuine directed regular-unit presentations on native scheme point spaces -/

open scoped NNReal Topology Classical
open Topology Filter CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {U V : Set (RelativeSchemeValuedPoint v f)}
  {u w : RelativeSchemeValuedPoint v f → EReal}

/-- Whole original regular-unit presentations indexed by a genuine nonempty directed preorder. -/
def IsDecrConvexPLNetLimitOn (U : Set (RelativeSchemeValuedPoint v f))
    (u : RelativeSchemeValuedPoint v f → EReal) : Prop :=
  ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
    (a : J → RelativeSchemeValuedPoint v f → EReal),
    (∀ j, IsConvexPLOn U (a j)) ∧
      (∀ y ∈ U, Antitone fun j => a j y) ∧ ∀ y ∈ U, u y = ⨅ j, a j y

/-- Actual original analytic neighbourhoods bearing directed regular-unit presentations. -/
def IsLocallyNetPSHOn (U : Set (RelativeSchemeValuedPoint v f))
    (u : RelativeSchemeValuedPoint v f → EReal) : Prop :=
  ∀ x ∈ U, ∃ W : Set (RelativeSchemeValuedPoint v f), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    IsDecrConvexPLNetLimitOn W u

/-- One actual original term gives openness of the entire presentation domain. -/
theorem IsDecrConvexPLNetLimitOn.isOpen (hu : IsDecrConvexPLNetLimitOn U u) : IsOpen U := by
  obtain ⟨J, hJ, hd, hn, a, ha, _⟩ := hu
  exact (ha (Classical.choice hn)).isOpen

/-- Whole directed presentations restrict to the actual same open subset. -/
theorem IsDecrConvexPLNetLimitOn.mono (hu : IsDecrConvexPLNetLimitOn U u)
    (hV : IsOpen V) (hVU : V ⊆ U) : IsDecrConvexPLNetLimitOn V u := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, a, fun j => (ha j).mono hV hVU,
    fun y hy => hanti y (hVU hy), fun y hy => hlim y (hVU hy)⟩

/-- Original domainwise equality retains every original term and the same directed index. -/
theorem IsDecrConvexPLNetLimitOn.congr (hu : IsDecrConvexPLNetLimitOn U u)
    (heq : ∀ y ∈ U, u y = w y) : IsDecrConvexPLNetLimitOn U w := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, a, ha, hanti, fun y hy => (heq y hy).symm.trans (hlim y hy)⟩

/-- The genuine directed presentation supplies its own actual local neighbourhood. -/
theorem IsDecrConvexPLNetLimitOn.isLocallyNetPSHOn (hu : IsDecrConvexPLNetLimitOn U u) :
    IsLocallyNetPSHOn U u := fun _ hx => ⟨U, hu.isOpen, hx, subset_rfl, hu⟩

/-- An original finite regular-unit term bounds the entire prescribed infimum above. -/
theorem IsDecrConvexPLNetLimitOn.ne_top (hu : IsDecrConvexPLNetLimitOn U u)
    {x : RelativeSchemeValuedPoint v f} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨J, hJ, hd, hn, a, ha, _, hlim⟩ := hu
  exact ne_top_of_le_ne_top ((ha (Classical.choice hn)).ne_top hx)
    ((hlim x hx).trans_le (iInf_le _ (Classical.choice hn)))

/-- Original term continuity gives genuine upper semicontinuity of the same infimum. -/
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

/-- The genuine local directed class is finite above at every original domain point. -/
theorem IsLocallyNetPSHOn.ne_top (hu : IsLocallyNetPSHOn U u)
    {x : RelativeSchemeValuedPoint v f} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨W, _, hxW, _, hw⟩ := hu x hx
  exact hw.ne_top hxW

/-- Actual original neighbourhoods and infima make the local directed class upper semicontinuous. -/
theorem IsLocallyNetPSHOn.upperSemicontinuousOn (hu : IsLocallyNetPSHOn U u) :
    UpperSemicontinuousOn u U := by
  intro x hx c hc
  obtain ⟨W, hW, hxW, _, hw⟩ := hu x hx
  have hev := hw.upperSemicontinuousOn x hxW c hc
  have hle : 𝓝 x ≤ 𝓝[W] x := by
    change 𝓝 x ≤ 𝓝 x ⊓ Filter.principal W
    exact le_inf le_rfl (Filter.le_principal_iff.mpr (hW.mem_nhds hxW))
  exact Filter.Eventually.filter_mono (nhdsWithin_le_nhds.trans hle) hev

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R S : Type u} [CommRing R] [CommRing S]
  {v : Valuation R ℝ≥0} {w : Valuation S ℝ≥0}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of S)} {fY : Y ⟶ Spec (CommRingCat.of R)}

/-- Entire actual regular-unit nets pull back through the original commuting scalar diagram. -/
theorem IsDecrConvexPLNetLimitOn.comp_mapOverBase (φ : R →+* S)
    (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hu : IsDecrConvexPLNetLimitOn U u) :
    IsDecrConvexPLNetLimitOn (mapOverBase φ hφ g hg ⁻¹' U)
      (fun y => u (mapOverBase φ hφ g hg y)) := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, (fun j y => a j (mapOverBase φ hφ g hg y)),
    fun j => (ha j).comp_mapOverBase φ hφ g hg,
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- Actual continuous scalar scheme maps preserve the entire original local directed class. -/
theorem IsLocallyNetPSHOn.comp_mapOverBase (φ : R →+* S)
    (hφ : ∀ r, w (φ r) = v r) (g : X ⟶ Y)
    (hg : g ≫ fY = fX ≫ Spec.map (CommRingCat.ofHom φ))
    {U : Set (RelativeSchemeValuedPoint v fY)} {u : RelativeSchemeValuedPoint v fY → EReal}
    (hu : IsLocallyNetPSHOn U u) :
    IsLocallyNetPSHOn (mapOverBase φ hφ g hg ⁻¹' U)
      (fun y => u (mapOverBase φ hφ g hg y)) := by
  intro y hy
  obtain ⟨W, hW, hyW, hWU, hloc⟩ := hu (mapOverBase φ hφ g hg y) hy
  exact ⟨mapOverBase φ hφ g hg ⁻¹' W,
    hW.preimage (continuous_mapOverBase φ hφ g hg), hyW,
    Set.preimage_mono hWU, hloc.comp_mapOverBase φ hφ g hg⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {v : Valuation R ℝ≥0}

/-- The actual affine homeomorphism retains the whole original directed index and every value. -/
theorem IsDecrConvexPLNetLimitOn.to_affineSpectrum
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal}
    (hu : IsDecrConvexPLNetLimitOn U u) :
    RelativeSpectrum.IsDecrConvexPLNetLimitOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, (fun j y => a j (affineSpectrumHomeomorph.symm y)),
    fun j => (ha j).to_affineSpectrum, fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- Genuine finite original-ring nets yield actual intrinsic regular-unit nets. -/
theorem IsDecrConvexPLNetLimitOn.of_affineSpectrum
    {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : RelativeSpectrum.IsDecrConvexPLNetLimitOn U u) :
    IsDecrConvexPLNetLimitOn (affineSpectrumHomeomorph ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph y)) := by
  obtain ⟨J, hJ, hd, hn, a, ha, hanti, hlim⟩ := hu
  exact ⟨J, hJ, hd, hn, (fun j y => a j (affineSpectrumHomeomorph y)),
    fun j => IsConvexPLOn.of_affineSpectrum (ha j),
    fun y hy => hanti _ hy, fun y hy => hlim _ hy⟩

/-- The whole actual affine homeomorphism carries original local directed neighbourhoods. -/
theorem IsLocallyNetPSHOn.to_affineSpectrum
    {U : Set (RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))))}
    {u : RelativeSchemeValuedPoint v (Spec.map (CommRingCat.ofHom (algebraMap R A))) → EReal}
    (hu : IsLocallyNetPSHOn U u) :
    RelativeSpectrum.IsLocallyNetPSHOn (affineSpectrumHomeomorph.symm ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph.symm y)) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hloc⟩ := hu (affineSpectrumHomeomorph.symm x) hx
  exact ⟨affineSpectrumHomeomorph.symm ⁻¹' W,
    hW.preimage affineSpectrumHomeomorph.symm.continuous,
    hxW, Set.preimage_mono hWU, hloc.to_affineSpectrum⟩

/-- The original affine coefficient local class gives genuine intrinsic directed presentations. -/
theorem IsLocallyNetPSHOn.of_affineSpectrum
    {U : Set (RelativeSpectrum v A)} {u : RelativeSpectrum v A → EReal}
    (hu : RelativeSpectrum.IsLocallyNetPSHOn U u) :
    IsLocallyNetPSHOn (affineSpectrumHomeomorph ⁻¹' U)
      (fun y => u (affineSpectrumHomeomorph y)) := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU, hloc⟩ := hu (affineSpectrumHomeomorph x) hx
  exact ⟨affineSpectrumHomeomorph ⁻¹' W, hW.preimage affineSpectrumHomeomorph.continuous,
    hxW, Set.preimage_mono hWU, IsDecrConvexPLNetLimitOn.of_affineSpectrum hloc⟩

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint
