import EnvelopeProperty.Potential.CurveAnalyticSubsetIdempotent
import EnvelopeProperty.Potential.CurveAnalyticSpectrumSpecialization
import EnvelopeProperty.Potential.CurveTopologicalPieces

/-! # Actual arbitrary-subset analytic pieces inside original curve neighbourhoods -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section

namespace EnvelopeProperty

/-- Genuine closed-image shrinking of an ACTUAL closed subset. -/
theorem exists_open_nhds_closed_piece_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : IsClosedMap p)
    (C : Set X) (hC : IsClosed C) (x : Y) (G : Set X) (hG : IsOpen G)
    (hcentral : C ∩ p ⁻¹' {x} ⊆ G) :
    ∃ Q : Set Y, IsOpen Q ∧ x ∈ Q ∧ C ∩ p ⁻¹' Q ⊆ G := by
  refine ⟨(p '' (C ∩ Gᶜ))ᶜ,(hp _ (hC.inter hG.isClosed_compl)).isOpen_compl,?_,?_⟩
  · rintro ⟨z,⟨hzC,hzG⟩,hzx⟩
    exact hzG (hcentral ⟨hzC,hzx⟩)
  · intro z hz
    by_contra hzG
    exact hz.2 ⟨z,⟨hz.1,hzG⟩,rfl⟩

namespace Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable (U : FCStandardAffinoid w m)
variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Fintype ι]

/-- The actual selected piece as a subset of the WHOLE original curve. -/
def curveIdempotentAmbientPiece (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) : Set (RelativeSpectrum w B) :=
  Subtype.val '' U.curveIdempotentOriginalPiece basis e

omit [Fintype ι] in
theorem curveIdempotentAmbientPiece_subset (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) :
    U.curveIdempotentAmbientPiece basis e ⊆ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' U.carrier := by
  rintro y ⟨z,hz,rfl⟩
  exact z.2

omit [Fintype ι] in
theorem mem_curveIdempotentAmbientPiece_iff (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (y : RelativeSpectrum w B)
    (hy : comap (IsScalarTower.toAlgHom K K[X] B) y ∈ U.carrier) :
    y ∈ U.curveIdempotentAmbientPiece basis e ↔
      (⟨y,hy⟩ : U.CurvePreimage (B := B)) ∈ U.curveIdempotentOriginalPiece basis e := by
  constructor
  · rintro ⟨z,hz,hzy⟩
    have heq : z = ⟨y,hy⟩ := Subtype.ext hzy
    exact heq ▸ hz
  · intro hyP
    exact ⟨⟨y,hy⟩,hyP,rfl⟩

/-- The literal selected piece is closed in the ENTIRE original curve. -/
theorem isClosed_curveIdempotentAmbientPiece (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) :
    IsClosed (U.curveIdempotentAmbientPiece basis e) := by
  have hclosed := U.isClosed_carrier.preimage (continuous_comap (IsScalarTower.toAlgHom K K[X] B))
  exact hclosed.isClosedEmbedding_subtypeVal.isClosedMap _
    (U.isClopen_curveIdempotentOriginalPiece basis he).isClosed

/-- Clopenness concerns the WHOLE original preimage, not just a finite central fibre. -/
theorem isClopen_preimage_curveIdempotentAmbientPiece (basis : Module.Basis ι K[X] B)
    {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e) :
    IsClopen ((Subtype.val : U.CurvePreimage (B := B) → RelativeSpectrum w B) ⁻¹'
      U.curveIdempotentAmbientPiece basis e) := by
  have heq : (Subtype.val : U.CurvePreimage (B := B) → RelativeSpectrum w B) ⁻¹'
      U.curveIdempotentAmbientPiece basis e = U.curveIdempotentOriginalPiece basis e := by
    ext y
    exact U.mem_curveIdempotentAmbientPiece_iff basis e y.1 y.2
  rw [heq]
  exact U.isClopen_curveIdempotentOriginalPiece basis he

variable (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier)

omit [Fintype ι] in
/-- The actual point condition is preserved by genuine WHOLE tensor restriction. -/
theorem mem_curveIdempotentOriginalPiece_restriction (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (y : V.CurvePreimage (B := B)) :
    y ∈ V.curveIdempotentOriginalPiece basis (U.curveAnalyticNormedRestriction V hVU basis e) ↔
      (⟨y.1,hVU y.2⟩ : U.CurvePreimage (B := B)) ∈ U.curveIdempotentOriginalPiece basis e := by
  change (Spectrum.fibrePoint (rfl : Spectrum.comap (algebraMap K[X] B) y.1.1 = _)).1.val
      (V.curveAnalyticSpecialization (V.curveOriginalBasePoint y)
        (U.curveAnalyticRestriction V hVU (U.curveAnalyticOriginalEquiv basis e))) = 1 ↔ _
  rw [U.curveAnalyticRestriction_specialization V hVU]
  rfl

omit [Fintype ι] in
/-- The restricted actual piece is the literal intersection in the original curve. -/
theorem curveIdempotentAmbientPiece_restriction (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) :
    V.curveIdempotentAmbientPiece basis (U.curveAnalyticNormedRestriction V hVU basis e) =
      U.curveIdempotentAmbientPiece basis e ∩ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' V.carrier := by
  ext y
  constructor
  · intro hy
    have hyV := V.curveIdempotentAmbientPiece_subset basis _ hy
    refine ⟨?_,hyV⟩
    rw [U.mem_curveIdempotentAmbientPiece_iff basis e y (hVU hyV)]
    exact (U.mem_curveIdempotentOriginalPiece_restriction V hVU basis e ⟨y,hyV⟩).mp
      ((V.mem_curveIdempotentAmbientPiece_iff basis _ y hyV).mp hy)
  · rintro ⟨hyU,hyV⟩
    rw [V.mem_curveIdempotentAmbientPiece_iff basis _ y hyV]
    exact (U.mem_curveIdempotentOriginalPiece_restriction V hVU basis e ⟨y,hyV⟩).mpr
      ((U.mem_curveIdempotentAmbientPiece_iff basis e y (hVU hyV)).mp hyU)

end Berkovich.RelativeSpectrum.FCStandardAffinoid

namespace Berkovich.RelativeSpectrum

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]

/-- An actual whole original seminorm-fibre point retains the prescribed base coefficients. -/
def fcRelativeFibrePoint (x : RelativeSpectrum w K[X]) (z : Spectrum.Fibre (B := B) x.1) :
    RelativeSpectrum w B :=
  ⟨z.1,fun a => by
    rw [IsScalarTower.algebraMap_apply K K[X] B]
    change (Spectrum.comap (algebraMap K[X] B) z.1).val (C a) = w a
    rw [z.2]
    exact x.2 a⟩

omit [IsAlgClosed K] [Fintype ι] in
theorem fcRelativeFibrePoint_base (x : RelativeSpectrum w K[X])
    (z : Spectrum.Fibre (B := B) x.1) :
    comap (IsScalarTower.toAlgHom K K[X] B) (fcRelativeFibrePoint x z) = x :=
  Subtype.ext z.2

/-- The constructed analytic idempotent selects EXACTLY any given original central subset. -/
theorem exists_standardAffinoid_analytic_central_piece
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B)
    (P : Set (RelativeSpectrum w B))
    (hP : P ⊆ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x}) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ _hx : x ∈ interior U.carrier,
      ∃ e : U.CurveAnalyticAlgebra basis, IsIdempotentElem e ∧
        U.curveIdempotentAmbientPiece basis e ∩
          comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} = P := by
  let Pabs := fcRelativeFibrePoint (B := B) x ⁻¹' P
  obtain ⟨m,U,hx,hUN,e,he,heval⟩ :=
    fc_exists_standardAffinoid_analytic_subset_idempotent_nhds x basis Pabs Set.univ Filter.univ_mem
  have hcentral (y : RelativeSpectrum w B)
      (hy : comap (IsScalarTower.toAlgHom K K[X] B) y = x) :
      y ∈ U.curveIdempotentAmbientPiece basis e ↔ y ∈ P := by
    have hyU : comap (IsScalarTower.toAlgHom K K[X] B) y ∈ U.carrier := hy ▸ interior_subset hx
    let z : Spectrum.Fibre (B := B) x.1 := ⟨y.1,congrArg Subtype.val hy⟩
    have hz : fcRelativeFibrePoint x z = y := Subtype.ext rfl
    have hval := heval z
    have hPabs : z ∈ Pabs ↔ y ∈ P := by change fcRelativeFibrePoint x z ∈ P ↔ _; rw [hz]
    rw [U.mem_curveIdempotentAmbientPiece_iff basis e y hyU]
    change (Spectrum.fibrePoint (rfl : Spectrum.comap (algebraMap K[X] B) y.1 = _)).1.val
      (U.curveAnalyticSpecialization ⟨comap (IsScalarTower.toAlgHom K K[X] B) y,hyU⟩
        (U.curveAnalyticOriginalEquiv basis e)) = 1 ↔ _
    subst x
    change ‖Spectrum.fibreHom z.2
      (U.curveAnalyticSpecialization ⟨comap (IsScalarTower.toAlgHom K K[X] B) y,interior_subset hx⟩
        (U.curveAnalyticOriginalEquiv basis e))‖₊ = 1 ↔ _
    rw [hval]
    by_cases hyP : y ∈ P
    · simp only [hPabs,hyP,if_true,nnnorm_one]
    · simp only [hPabs,hyP,if_false,nnnorm_zero,zero_ne_one]
  refine ⟨m,U,hx,e,he,?_⟩
  ext y
  constructor
  · rintro ⟨hy,hybase⟩
    exact (hcentral y hybase).mp hy
  · intro hy
    exact ⟨(hcentral y (hP hy)).mpr hy,hP hy⟩

/-- Actual analytic idempotents CONSTRUCT whole original curve pieces inside ANY
prescribed curve neighbourhood of ANY actual central fibre subset. -/
theorem exists_standardAffinoid_analytic_piece_subset
    (x : RelativeSpectrum w K[X]) (basis : Module.Basis ι K[X] B)
    (P : Set (RelativeSpectrum w B))
    (hP : P ⊆ comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x})
    (N : Set (RelativeSpectrum w B)) (hN : N ∈ 𝓝ˢ P) :
    ∃ m : ℕ, ∃ U : FCStandardAffinoid w m, ∃ _hx : x ∈ interior U.carrier,
      ∃ e : U.CurveAnalyticAlgebra basis, IsIdempotentElem e ∧
        U.curveIdempotentAmbientPiece basis e ⊆ N ∧
        IsClopen ((Subtype.val : U.CurvePreimage (B := B) → RelativeSpectrum w B) ⁻¹'
          U.curveIdempotentAmbientPiece basis e) ∧
        U.curveIdempotentAmbientPiece basis e ∩
          comap (IsScalarTower.toAlgHom K K[X] B) ⁻¹' {x} = P := by
  let := Module.Finite.of_basis basis
  let φ := IsScalarTower.toAlgHom K K[X] B
  have hφ : φ.toRingHom.Finite := RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨m,V,hxV,e,he,hcentral⟩ := exists_standardAffinoid_analytic_central_piece x basis P hP
  obtain ⟨G,hGo,hPG,hGN⟩ := mem_nhdsSet_iff_exists.mp hN
  obtain ⟨Q,hQo,hxQ,hCQ⟩ := exists_open_nhds_closed_piece_subset (comap φ)
    (isClosedMap_comap_of_isIntegral φ hφ.to_isIntegral)
    (V.curveIdempotentAmbientPiece basis e) (V.isClosed_curveIdempotentAmbientPiece basis he)
    x G hGo (by
      intro y hy
      exact hPG ((Set.ext_iff.mp hcentral y).mp hy))
  obtain ⟨n,U,hxU,hU⟩ := fc_exists_standardAffinoid_nhds x
    (Filter.inter_mem (hQo.mem_nhds hxQ) (isOpen_interior.mem_nhds hxV))
  let hUV : U.carrier ⊆ V.carrier := fun y hy => interior_subset (hU hy).2
  let a := V.curveAnalyticNormedRestriction U hUV basis e
  have ha : IsIdempotentElem a := he.map _
  have heq : U.curveIdempotentAmbientPiece basis a =
      V.curveIdempotentAmbientPiece basis e ∩ comap φ ⁻¹' U.carrier :=
    V.curveIdempotentAmbientPiece_restriction U hUV basis e
  refine ⟨n,U,hxU,a,ha,?_,U.isClopen_preimage_curveIdempotentAmbientPiece basis ha,?_⟩
  · intro y hy
    rw [heq] at hy
    exact hGN (hCQ ⟨hy.1,(hU hy.2).1⟩)
  · rw [heq]
    ext y
    constructor
    · rintro ⟨⟨hyV,hyU⟩,hyx⟩
      exact (Set.ext_iff.mp hcentral y).mp ⟨hyV,hyx⟩
    · intro hyP
      have hyVP := (Set.ext_iff.mp hcentral y).mpr hyP
      have hyU : comap φ y ∈ U.carrier := by
        rw [show comap φ y = x from hP hyP]
        exact interior_subset hxU
      exact ⟨⟨hyVP.1,hyU⟩,hyVP.2⟩

end Berkovich.RelativeSpectrum
end EnvelopeProperty
