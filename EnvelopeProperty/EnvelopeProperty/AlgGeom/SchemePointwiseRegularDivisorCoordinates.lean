import Hironaka.Scheme.Smooth.EtaleCoordinatesAdapted

/-! # Actual adapted etale charts from one native regular residual quotient -/
open AlgebraicGeometry CategoryTheory IsLocalRing KaehlerDifferential TensorProduct
noncomputable section
universe u
namespace EnvelopeProperty.SchemePointwiseRegularDivisorCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine regular residual stalk of dimension one produces an actual
adapted etale surface chart inside EVERY prescribed affine neighborhood. -/
theorem exists_etale_chart_within {F : Type u} [Field F] [PerfectField F]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of F)) [SmoothOfRelativeDimension 2 f]
    (J : Y.IdealSheafData) (z : Y) (hz : IsClosed ({z} : Set Y))
    [IsRegularLocalRing (Y.presheaf.stalk z ⧸ J.stalkIdeal z)]
    (hd : ringKrullDim (Y.presheaf.stalk z ⧸ J.stalkIdeal z) = 1)
    (V : Y.affineOpens) (hzV : z ∈ V.1) :
    ∃ (U : Y.affineOpens) (_hzU : z ∈ U.1) (_hUV : U.1 ≤ V.1)
      (v : Fin 2 → Γ(Y,U.1)), Etale (toAffineSpace f U.1 v) ∧
        J.comap U.1.ι = (coordinateSubspace F 2 1).comap (toAffineSpace f U.1 v) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  let := isRegularLocalRing_stalk f z
  obtain ⟨m,c,y,hcm,hm,hspan,hJ⟩ :=
    IsRegularLocalRing.exists_span_eq_maximalIdeal_and_eq_span_image_lt (J.stalkIdeal z)
  have hdim := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed f 2 hz
  have hm2 : m = 2 := by exact_mod_cast hm.trans hdim
  subst m
  have hq := ringKrullDim_quotient_span_image_lt y hspan hm hcm
  rw [← hJ,hd,hdim] at hq
  have hc1 : c = 1 := by
    have h : 1 + c = 2 := by exact_mod_cast hq
    omega
  subst c
  let := f.stalkAlgebra z
  obtain ⟨W,hzW,hWV,w,hw⟩ := exists_affineOpen_germ_eq V hzV y
  obtain ⟨b,hb⟩ := exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal f 2 hz y hspan
  have hb' : ∃ b' : Module.Basis (Fin 2) (ResidueField (Y.presheaf.stalk z))
      (ResidueField (Y.presheaf.stalk z) ⊗[Y.presheaf.stalk z] Ω[Y.presheaf.stalk z⁄F]),
      ∀ i, b' i = 1 ⊗ₜ D F (Y.presheaf.stalk z) (Y.presheaf.germ W.1 z hzW (w i)) :=
    ⟨b,fun i => by rw [hb i,hw i]⟩
  obtain ⟨U,hzU,hUW,hE⟩ := exists_etale_toAffineSpace_of_basis f 2 W hzW w hb'
  let w' : Fin 2 → Γ(Y,U.1) := fun i => Y.presheaf.map (homOfLE hUW).op (w i)
  have hJ' : J.stalkIdeal z =
      Ideal.span ((fun i => Y.presheaf.germ U.1 z hzU (w' i)) '' {i | i.val < 1}) := by
    rw [hJ]
    congr 1
    refine Set.image_congr fun i _ => ?_
    change y i = Y.presheaf.germ U.1 z hzU (Y.presheaf.map (homOfLE hUW).op (w i))
    rw [Y.presheaf.germ_res_apply,hw i]
  obtain ⟨U',hzU',hU'U,hAd⟩ := exists_comap_eq_comap_coordinateSubspace f 2 1 J U hzU w' hJ'
  let : Etale (toAffineSpace f U.1 w') := hE
  exact ⟨U',hzU',hU'U.trans (hUW.trans hWV),
    fun i => Y.presheaf.map (homOfLE hU'U).op (w' i),
    etale_toAffineSpace_restrict f hU'U w',hAd⟩

end EnvelopeProperty.SchemePointwiseRegularDivisorCoordinates
