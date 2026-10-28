import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGroupPointTransport
import EnvelopeProperty.Projective.NativeMultiplicativeGroupProjections

/-! # Original nonzero scalars as genuine native group points

The actual Laurent evaluation constructs the group point and computes its
actual multiplication followed by the original parameter inclusion.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedScalarGroupPoint
open ProjBerk ProjectiveCentralFiberEmbeddingNeighborhoodClosedParameterScalarCover
variable {k : Type u} [Field k]

/-- An original coefficient unit is an actual point of the SAME native group. -/
def scalarGroupPoint (u : kˣ) :
    𝟙_ (Over (Spec (.of k))) ⟶ nativeMultiplicativeGroup k :=
  Over.homMk (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) u))) (by
    change Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) u)) ≫
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹])) = 𝟙 _
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((LaurentPolynomial.eval₂ (RingHom.id k) u).comp
      LaurentPolynomial.C)) = 𝟙 _
    have h : (LaurentPolynomial.eval₂ (RingHom.id k) u).comp LaurentPolynomial.C =
        RingHom.id k := by ext a; simp
    rw [h]
    exact Spec.map_id _)

private def pointProductEval (u : kˣ) : k[T;T⁻¹][T;T⁻¹] →+* k[T;T⁻¹] :=
  LaurentPolynomial.eval₂
    (LaurentPolynomial.C.comp (LaurentPolynomial.eval₂ (RingHom.id k) u))
    (parameterLaurentUnit k)

private theorem pointProductEval_outer (u : kˣ) :
    (pointProductEval u).comp
        (AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : k →+* k[T;T⁻¹])) =
      RingHom.id k[T;T⁻¹] := by
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | C_mul_T m a =>
    have hc : AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : k →+* k[T;T⁻¹])
        (LaurentPolynomial.C a) = LaurentPolynomial.C (LaurentPolynomial.C a) := by
      change AddMonoidAlgebra.mapRingHom ℤ LaurentPolynomial.C (.single 0 a) =
        .single 0 (LaurentPolynomial.C a)
      rw [AddMonoidAlgebra.mapRingHom_single]
    have ht : AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : k →+* k[T;T⁻¹])
        (LaurentPolynomial.T m) = (LaurentPolynomial.T m : k[T;T⁻¹][T;T⁻¹]) := by
      change AddMonoidAlgebra.mapRingHom ℤ LaurentPolynomial.C (.single m 1) = .single m 1
      rw [AddMonoidAlgebra.mapRingHom_single, map_one]
    change pointProductEval u
      ((AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : k →+* k[T;T⁻¹]))
        (LaurentPolynomial.C a * LaurentPolynomial.T m)) =
      LaurentPolynomial.C a * LaurentPolynomial.T m
    rw [map_mul, hc, ht, map_mul]
    change LaurentPolynomial.eval₂
        (LaurentPolynomial.C.comp (LaurentPolynomial.eval₂ (RingHom.id k) u))
        (parameterLaurentUnit k) (LaurentPolynomial.C (LaurentPolynomial.C a)) *
      LaurentPolynomial.eval₂
        (LaurentPolynomial.C.comp (LaurentPolynomial.eval₂ (RingHom.id k) u))
        (parameterLaurentUnit k) (LaurentPolynomial.T m) = _
    rw [LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, parameterLaurentUnit_zpow]
    simp

private theorem scalarPointPair (u : kˣ) :
    (lift (toUnit (nativeMultiplicativeGroup k) ≫ scalarGroupPoint u)
      (𝟙 (nativeMultiplicativeGroup k))).left =
      Spec.map (CommRingCat.ofHom (pointProductEval u)) ≫
        (nativeMultiplicativeGroupProductIso k).hom := by
  apply pullback.hom_ext
  · simp only [Over.lift_left, pullback.lift_fst, Over.comp_left, Over.toUnit_left]
    erw [Category.assoc, nativeMultiplicativeGroupProductIso_fst]
    change Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k →+* k[T;T⁻¹])) ≫
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) u)) =
      Spec.map (CommRingCat.ofHom (pointProductEval u)) ≫
        Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : k[T;T⁻¹] →+* k[T;T⁻¹][T;T⁻¹]))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    change LaurentPolynomial.C ((LaurentPolynomial.eval₂ (RingHom.id k) u) p) =
      pointProductEval u (LaurentPolynomial.C p)
    simp [pointProductEval]
  · simp only [Over.lift_left, pullback.lift_snd, Over.id_left]
    erw [Category.assoc, nativeMultiplicativeGroupProductIso_snd]
    change 𝟙 (Spec (.of k[T;T⁻¹])) =
      Spec.map (CommRingCat.ofHom (pointProductEval u)) ≫
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : k →+* k[T;T⁻¹])))
    rw [← Spec.map_comp]
    change 𝟙 _ = Spec.map (CommRingCat.ofHom ((pointProductEval u).comp
      (AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : k →+* k[T;T⁻¹]))))
    rw [pointProductEval_outer]
    exact (Spec.map_id _).symm

/-- Actual native group multiplication at the original scalar point, followed
by the original parameter inclusion, is the literal SAME scalar map. -/
theorem scalarGroupPoint_multiply_parameter (u : kˣ) :
    (lift (toUnit (nativeMultiplicativeGroup k) ≫ scalarGroupPoint u)
      (𝟙 (nativeMultiplicativeGroup k)) ≫ μ[nativeMultiplicativeGroup k]).left ≫
        (nativeParameterGroupInclusion k).left =
      (nativeParameterGroupInclusion k).left ≫ parameterScalarMap u := by
  let pair : Spec (.of k[T;T⁻¹]) ⟶
      pullback (nativeMultiplicativeGroup k).hom (nativeMultiplicativeGroup k).hom :=
    (lift (toUnit (nativeMultiplicativeGroup k) ≫ scalarGroupPoint u)
      (𝟙 (nativeMultiplicativeGroup k))).left
  let mult : pullback (nativeMultiplicativeGroup k).hom
      (nativeMultiplicativeGroup k).hom ⟶ Spec (.of k[T;T⁻¹]) :=
    (μ[nativeMultiplicativeGroup k]).left
  let inc : Spec (.of k[T;T⁻¹]) ⟶ Spec (.of k[X]) :=
    (nativeParameterGroupInclusion k).left
  have hp : pair = Spec.map (CommRingCat.ofHom (pointProductEval u)) ≫
      (nativeMultiplicativeGroupProductIso k).hom := scalarPointPair u
  have hm : (nativeMultiplicativeGroupProductIso k).hom ≫ mult =
      Spec.map (CommRingCat.ofHom (parameterLaurentMultiplicationHom (R := k))) :=
    nativeMultiplicativeGroup_mul k
  have hi : inc = Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : k[X] →+* k[T;T⁻¹])) := nativeParameterGroupInclusion_left k
  have hpm : pair ≫ mult = Spec.map (CommRingCat.ofHom (pointProductEval u)) ≫
      Spec.map (CommRingCat.ofHom (parameterLaurentMultiplicationHom (R := k))) :=
    (congrArg (fun f => f ≫ mult) hp).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun f => Spec.map (CommRingCat.ofHom (pointProductEval u)) ≫ f) hm))
  change (pair ≫ mult) ≫ inc = inc ≫ parameterScalarMap u
  rw [hpm, hi]
  unfold parameterScalarMap
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    simp [pointProductEval, parameterLaurentMultiplicationHom]
  · simp [pointProductEval, parameterLaurentMultiplicationHom, parameterLaurentProductUnit,
      parameterLaurentUnit]

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedScalarGroupPoint
