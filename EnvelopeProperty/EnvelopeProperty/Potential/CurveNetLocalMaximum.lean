import EnvelopeProperty.Potential.CurveNetTrace
import EnvelopeProperty.Potential.CurvePieceMaximum
import EnvelopeProperty.Berkovich.RelativeLocalPSHContinuity

/-! # Genuine original intrinsic locally-psh local maxima are locally constant -/

open scoped NNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology Filter
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum

universe u
variable {K B : Type u} {ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]

/-- The intrinsic original regular-unit directed-net class DERIVES actual local maximum
constancy through constructed pieces and every genuine source harmonic comparison. -/
theorem IsLocallyNetPSHOn.eventually_eq_of_isLocalMax_finiteFree
    (basis : Module.Basis ι K[X] B) {Ω : Set (RelativeSpectrum w B)}
    {u : RelativeSpectrum w B → EReal} (hu : IsLocallyNetPSHOn Ω u)
    (hnt : ∃ t : K, 1 < w t) (y : RelativeSpectrum w B) (hy : y ∈ Ω)
    (hmax : IsLocalMax u y) : ∀ᶠ z in 𝓝 y, u z = u y := by
  classical
  by_cases hbot : u y = ⊥
  · exact hmax.mono (fun z hz => le_antisymm hz (hbot ▸ bot_le))
  let R := (u y).toReal
  have hR : u y = (R : EReal) := (EReal.coe_toReal (hu.ne_top hy) hbot).symm
  let p : RelativeSpectrum w B → RelativeSpectrum w K[X] := comap (IsScalarTower.toAlgHom K K[X] B)
  let x := p y
  obtain ⟨G,hGo,hyG,hGΩ,hGpres⟩ := hu y hy
  let N := G ∩ {z | u z ≤ u y}
  have hN : N ∈ 𝓝ˢ ({y} : Set (RelativeSpectrum w B)) := by
    simpa only [nhdsSet_singleton] using Filter.inter_mem (hGo.mem_nhds hyG) hmax
  have hP : {y} ⊆ p ⁻¹' {x} := by
    rintro z (rfl : z = y)
    rfl
  obtain ⟨m,U,hx,e,he,hUN,hcl,hcentral⟩ :=
    exists_standardAffinoid_analytic_piece_subset x basis {y} hP N hN
  let xx : U.carrier := ⟨x,interior_subset hx⟩
  have hUΩ : U.curveIdempotentAmbientPiece basis e ⊆ Ω := fun z hz => hGΩ (hUN hz).1
  have hupper : ∀ z ∈ U.curveIdempotentAmbientPiece basis e, u z ≤ (R : EReal) := by
    intro z hz
    exact (hUN hz).2.trans_eq hR
  let F := U.curveRelativePieceNorm basis he u
  have hsh : IsLineSubharmonicOn F (interior U.carrier) :=
    U.isLineSubharmonicOn_curveRelativePieceNorm_of_isLocallyNetPSHOn basis he hu hnt hUΩ
  have hFx : F x = (((U.curveIdempotentPieceWeight basis e xx : ℝ)*R : ℝ) : EReal) := by
    apply U.curveRelativePieceNorm_eq_const_of_central_eq basis he u R xx
    intro z hz hzx
    have hzy : z = y := (Set.ext_iff.mp hcentral z).mp ⟨hz,hzx⟩
    exact hzy ▸ hR
  have hFupper (z : U.carrier) : F z.1 ≤ F x := by
    rw [hFx]
    have hw := U.curveIdempotentPieceWeight_eq basis he z xx
    exact (U.curveRelativePieceNorm_le_const basis he u R hupper z).trans_eq (by rw [hw])
  have hnear : ∀ᶠ z in 𝓝 x, z ∈ interior U.carrier := isOpen_interior.mem_nhds hx
  have hFmax : IsLocalMax F x := hnear.mono (fun z hz => hFupper ⟨z,interior_subset hz⟩)
  have hflat := hsh.eventually_eq_of_isLocalMax hnt isOpen_interior x hx hFmax
  have hyC : y ∈ U.curveIdempotentAmbientPiece basis e :=
    ((Set.ext_iff.mp hcentral y).mpr rfl).1
  have hCnear := U.curveIdempotentAmbientPiece_mem_nhds basis he y hyC hx
  have hp : Tendsto p (𝓝 y) (𝓝 x) := (continuous_comap (IsScalarTower.toAlgHom K K[X] B)).tendsto y
  filter_upwards [hCnear,hp.eventually hflat,hp.eventually (isOpen_interior.mem_nhds hx)]
    with z hzC hzF hzint
  let zx : U.carrier := ⟨p z,interior_subset hzint⟩
  have hzFeq : U.curveRelativePieceNorm basis he u zx.1 =
      (((U.curveIdempotentPieceWeight basis e zx : ℝ)*R : ℝ) : EReal) := by
    rw [show U.curveRelativePieceNorm basis he u zx.1 = F (p z) from rfl,hzF,hFx,
      U.curveIdempotentPieceWeight_eq basis he xx zx]
  exact (U.eq_of_curveRelativePieceNorm_eq_const basis he u R hupper zx hzFeq z hzC rfl).trans hR.symm

end EnvelopeProperty.Berkovich.RelativeSpectrum
