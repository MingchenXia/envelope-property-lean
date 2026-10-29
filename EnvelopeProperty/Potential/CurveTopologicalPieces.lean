import EnvelopeProperty.Potential.LineAffinoidBasis
import EnvelopeProperty.Berkovich.SpectrumIntegralProper
import EnvelopeProperty.Berkovich.SpectrumFinite
import Mathlib.Topology.Separation.Hausdorff

/-! # Actual topological pieces of arbitrary finite fibres over every original line point -/

open scoped NNReal Polynomial Topology
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty

/-- A closed map and its actual finite fibre construct whole open separating neighbourhoods. -/
theorem exists_separated_opens_over_finite_fibre
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsClosedMap p) (w : Y) (hfinite : (p ⁻¹' {w}).Finite)
    (P : Set X) (hP : P ⊆ p ⁻¹' {w}) (N : Set X) (hN : N ∈ 𝓝ˢ P) :
    ∃ Q : Set Y, ∃ O O' : Set X,
      IsOpen Q ∧ w ∈ Q ∧ IsOpen O ∧ IsOpen O' ∧ O ⊆ N ∧ Disjoint O O' ∧
      p ⁻¹' Q ⊆ O ∪ O' ∧ O ∩ p ⁻¹' {w} = P := by
  obtain ⟨G,hGo,hPG,hGN⟩ := mem_nhdsSet_iff_exists.mp hN
  have hPfinite := hfinite.subset hP
  have hcompfinite := hfinite.subset (Set.sdiff_subset : (p ⁻¹' {w}) \ P ⊆ p ⁻¹' {w})
  have hdisj : Disjoint P ((p ⁻¹' {w}) \ P) := Set.disjoint_sdiff_right
  obtain ⟨O₀,O',hO₀o,hO'o,hPO₀,hcompO',hdisj₀⟩ :=
    SeparatedNhds.of_isCompact_isCompact hPfinite.isCompact hcompfinite.isCompact hdisj
  let O := O₀ ∩ G
  have hOo : IsOpen O := hO₀o.inter hGo
  have hPO : P ⊆ O := fun x hx => ⟨hPO₀ hx,hPG hx⟩
  have hON : O ⊆ N := fun _ hx => hGN hx.2
  have hOO' : Disjoint O O' := hdisj₀.mono_left Set.inter_subset_left
  have hfibrecover : p ⁻¹' {w} ⊆ O ∪ O' := by
    intro x hx
    by_cases hxP : x ∈ P
    · exact Or.inl (hPO hxP)
    · exact Or.inr (hcompO' ⟨hx,hxP⟩)
  let C := (O ∪ O')ᶜ
  have hC : IsClosed C := (hOo.union hO'o).isClosed_compl
  let Q := (p '' C)ᶜ
  have hQo : IsOpen Q := (hp C hC).isOpen_compl
  have hwQ : w ∈ Q := by
    rintro ⟨x,hxC,hxw⟩
    exact hxC (hfibrecover (show x ∈ p ⁻¹' {w} from hxw))
  have hprecover : p ⁻¹' Q ⊆ O ∪ O' := by
    intro x hx
    by_contra hn
    exact hx ⟨x,hn,rfl⟩
  have hOP : O ∩ p ⁻¹' {w} = P := by
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hxP
      exact Set.disjoint_left.mp hOO' hx.1 (hcompO' ⟨hx.2,hxP⟩)
    · exact fun x hx => ⟨hPO hx,hP hx⟩
  exact ⟨Q,O,O',hQo,hwQ,hOo,hO'o,hON,hOO',hprecover,hOP⟩

namespace Berkovich.RelativeSpectrum

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable {B : Type*} [CommRing B] [Algebra K B]

/-- The actual finite original algebra map produces actual clopen pieces over a standard neighbourhood of every line point. -/
theorem exists_standardAffinoid_clopen_piece (φ : K[X] →ₐ[K] B)
    (hφ : φ.toRingHom.Finite) (x : RelativeSpectrum w K[X])
    (P : Set (RelativeSpectrum w B)) (hP : P ⊆ comap φ ⁻¹' {x})
    (N : Set (RelativeSpectrum w B)) (hN : N ∈ 𝓝ˢ P) :
    ∃ (m : ℕ) (U : FCStandardAffinoid w m) (V : Set (RelativeSpectrum w B)),
      x ∈ interior U.carrier ∧ V ⊆ comap φ ⁻¹' U.carrier ∧ V ⊆ N ∧
      IsClopen (((↑) : (comap φ ⁻¹' U.carrier) → RelativeSpectrum w B) ⁻¹' V) ∧
      V ∩ (comap φ ⁻¹' {x}) = P := by
  obtain ⟨Q,O,O',hQo,hxQ,hOo,hO'o,hON,hdisj,hcover,hOP⟩ :=
    EnvelopeProperty.exists_separated_opens_over_finite_fibre (comap φ)
      (isClosedMap_comap_of_isIntegral φ hφ.to_isIntegral) x
      (finite_preimage_comap_singleton φ hφ x) P hP N hN
  obtain ⟨m,U,hxU,hUQ⟩ := fc_exists_standardAffinoid_nhds x (hQo.mem_nhds hxQ)
  let C := comap φ ⁻¹' U.carrier
  let V := C ∩ O
  have hCO : C ⊆ O ∪ O' := fun z hz => hcover (hUQ hz)
  have heV : ((↑) : C → RelativeSpectrum w B) ⁻¹' V =
      ((↑) : C → RelativeSpectrum w B) ⁻¹' O := by
    ext z
    exact and_iff_right z.2
  have hecompl : (((↑) : C → RelativeSpectrum w B) ⁻¹' O)ᶜ =
      ((↑) : C → RelativeSpectrum w B) ⁻¹' O' := by
    ext z
    change z.1 ∉ O ↔ z.1 ∈ O'
    constructor
    · intro hz
      exact (hCO z.2).resolve_left hz
    · intro hz' hz
      exact Set.disjoint_left.mp hdisj hz hz'
  have hVclopen : IsClopen (((↑) : C → RelativeSpectrum w B) ⁻¹' V) := by
    rw [heV]
    constructor
    · apply isOpen_compl_iff.mp
      rw [hecompl]
      exact hO'o.preimage continuous_subtype_val
    · exact hOo.preimage continuous_subtype_val
  have hPC : P ⊆ C := by
    intro z hz
    change comap φ z ∈ U.carrier
    rw [show comap φ z = x from hP hz]
    exact interior_subset hxU
  refine ⟨m,U,V,hxU,Set.inter_subset_left,fun z hz => hON hz.2,hVclopen,?_⟩
  change (C ∩ O) ∩ comap φ ⁻¹' {x} = P
  rw [Set.inter_assoc,hOP,Set.inter_eq_right.mpr hPC]

end Berkovich.RelativeSpectrum

end EnvelopeProperty
