import EnvelopeProperty.Cartier.GeometricCartierRestrictions
import EnvelopeProperty.AlgGeom.SchemeModuleBasisExtension

/-! # The original global geometric Cartier sheaf isomorphism -/
noncomputable section
namespace EnvelopeProperty.Cartier.GeometricSheafCartier
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
universe u

private theorem transport_restrict {Z : Scheme.{u}} (M N : Z.Modules)
    {U U' V V' : Z.Opens} (hU : U' = U) (hV : V' = V)
    (eU : M.val.obj (op U') ≅ N.val.obj (op U'))
    (eV : M.val.obj (op V') ≅ N.val.obj (op V'))
    (i : U ⟶ V) (j : U' ⟶ V')
    (h : ∀ s : M.val.obj (op V'),
      N.presheaf.map j.op (eV.hom.hom s) = eU.hom.hom (M.presheaf.map j.op s))
    (s : M.val.obj (op V)) :
    N.presheaf.map i.op
        ((Eq.mp (congrArg (fun W : Z.Opens => M.val.obj (op W) ≅ N.val.obj (op W)) hV) eV).hom.hom s) =
      (Eq.mp (congrArg (fun W : Z.Opens => M.val.obj (op W) ≅ N.val.obj (op W)) hU) eU).hom.hom
        (M.presheaf.map i.op s) := by
  cases hU
  cases hV
  have hj : j = i := Subsingleton.elim _ _
  subst j
  exact h s

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [SmoothOfRelativeDimension n f]
local notation "Y" => SchemeRelativeFrobenius.twist p f
local notation "Fr" => SchemeRelativeFrobenius.map p f
local notation "g" => pullback.snd f (SchemeRelativeFrobenius.baseMap (k := k) p)
local notation "K" => SchemeRelativeFrobeniusBasisDifferential.complex f p n
private def sourceModule (q : ℕ) : (Y).Modules :=
  CanonicalGeometry.exteriorCotangentSheaf g q

private def targetModule (q : ℕ) : (Y).Modules :=
  (SchemeRelativeFrobeniusBasisDifferential.complex f p n).homology q

local notation "Ω[" q "]" => sourceModule f p q
local notation "H[" q "]" => targetModule f p n q

private abbrev Basis := {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}
private def basisOpen (W : Basis f p n) : (Y).Opens := W.val

private theorem basisIsBasis : Opens.IsBasis (Set.range (basisOpen f p n)) := by
  have h : Set.range (basisOpen f p n) = RelativeTwistedAffineBasis.basicOpens f p n := by
    ext W
    constructor
    · rintro ⟨V, rfl⟩
      exact V.property
    · intro hW
      exact ⟨⟨W, hW⟩, rfl⟩
  exact h.symm ▸ RelativeTwistedAffineBasis.isBasis_basicOpens f p n

private abbrev sourceOpen (W : Basis f p n) : X.Opens := (Fr) ⁻¹ᵁ W.val

omit [SmoothOfRelativeDimension n f] in
private theorem sourceAffine (W : Basis f p n) : IsAffineOpen (sourceOpen f p n W) :=
  SchemeRelativeFrobeniusBasisDifferential.source_isAffine f p n W.val W.property

private def coordinateTuple (W : Basis f p n) : Fin n → Γ(X, sourceOpen f p n W) :=
  SchemeRelativeFrobeniusBasisDifferential.coordinates f p n W

omit [SmoothOfRelativeDimension n f] in
private theorem coordinateTuple_etale (W : Basis f p n) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f (sourceOpen f p n W);
    (MvPolynomial.aeval (R := k) (coordinateTuple f p n W)).toRingHom.Etale :=
  SchemeRelativeFrobeniusBasisDifferential.coordinates_etale f p n W

private def localBasisIso (q : ℕ) (W : Basis f p n) :
    (Ω[q]).val.obj (op (RelativeTwistedAffineBasis.twistedOpen f p (sourceOpen f p n W))) ≅
      (H[q]).val.obj (op (RelativeTwistedAffineBasis.twistedOpen f p (sourceOpen f p n W))) :=
  GeometricAffineHomology.localSheafCartierSectionsIso f p n (sourceAffine f p n W)
    (coordinateTuple f p n W) (coordinateTuple_etale f p n W) q

private theorem localBasisIso_restrict (q : ℕ) (U V : Basis f p n) (i : U.val ⟶ V.val)
    (s : (Ω[q]).val.obj (op (RelativeTwistedAffineBasis.twistedOpen f p (sourceOpen f p n V)))) :
    (H[q]).presheaf.map
        (GeometricTwistedChartRestrictions.twistedInclusion f p ((Opens.map (Fr).base).map i)).op
        ((localBasisIso f p n q V).hom.hom s) =
      (localBasisIso f p n q U).hom.hom ((Ω[q]).presheaf.map
        (GeometricTwistedChartRestrictions.twistedInclusion f p ((Opens.map (Fr).base).map i)).op s) :=
  GeometricCartierRestrictions.localSheafCartierSectionsIso_restrict
    (U := sourceOpen f p n U) (V := sourceOpen f p n V) f p n
    ((Opens.map (Fr).base).map i) (sourceAffine f p n U) (sourceAffine f p n V)
    (coordinateTuple f p n V) (coordinateTuple_etale f p n V)
    (coordinateTuple f p n U) (coordinateTuple_etale f p n U) q s

/-- Actual original Cartier isomorphism on each original principal basis open. -/
def basisIso (q : ℕ)
    (W : {W : (Y).Opens // W ∈ RelativeTwistedAffineBasis.basicOpens f p n}) :
    (Ω[q]).val.obj (op W.val) ≅ (H[q]).val.obj (op W.val) :=
  Eq.mp (congrArg (fun V : (Y).Opens => (Ω[q]).val.obj (op V) ≅ (H[q]).val.obj (op V))
    (RelativeTwistedOpenInverse.twistedOpen_relative_preimage f p W.val))
    (localBasisIso f p n q W)

/-- The entire original basis Cartier isomorphisms agree under actual original restriction. -/
theorem basisIso_restrict (q : ℕ) (U V : Basis f p n) (i : U.val ⟶ V.val)
    (s : (Ω[q]).val.obj (op V.val)) :
    (H[q]).presheaf.map i.op ((basisIso f p n q V).hom.hom s) =
      (basisIso f p n q U).hom.hom ((Ω[q]).presheaf.map i.op s) := by
  exact transport_restrict (Z := Y) (Ω[q]) (H[q])
    (RelativeTwistedOpenInverse.twistedOpen_relative_preimage f p U.val)
    (RelativeTwistedOpenInverse.twistedOpen_relative_preimage f p V.val)
    (localBasisIso f p n q U) (localBasisIso f p n q V)
    i (GeometricTwistedChartRestrictions.twistedInclusion f p ((Opens.map (Fr).base).map i))
    (localBasisIso_restrict f p n q U V i) s

private theorem inverse_square {A B C D : Type u} (e : A ≃ B) (e' : C ≃ D)
    (r : A → C) (s : B → D) (h : ∀ x, s (e x) = e' (r x)) (y : B) :
    r (e.symm y) = e'.symm (s y) :=
  (e'.symm_apply_apply (r (e.symm y))).symm.trans
    (congrArg e'.symm ((h (e.symm y)).symm.trans (congrArg s (e.apply_symm_apply y))))

private theorem basisIso_inv_restrict (q : ℕ) (U V : Basis f p n) (i : U.val ⟶ V.val)
    (s : (H[q]).val.obj (op V.val)) :
    (Ω[q]).presheaf.map i.op ((basisIso f p n q V).inv.hom s) =
      (basisIso f p n q U).inv.hom ((H[q]).presheaf.map i.op s) :=
  inverse_square (basisIso f p n q V).toLinearEquiv.toEquiv
    (basisIso f p n q U).toLinearEquiv.toEquiv
    ((Ω[q]).presheaf.map i.op) ((H[q]).presheaf.map i.op)
    (basisIso_restrict f p n q U V i) s

private def basisMap (q : ℕ) :
    (inducedFunctor (basisOpen f p n)).op ⋙ (Ω[q]).presheaf ⟶
      (inducedFunctor (basisOpen f p n)).op ⋙ (H[q]).presheaf where
  app W := AddCommGrpCat.ofHom (basisIso f p n q W.unop).hom.hom.toAddMonoidHom
  naturality := by
    intro V W i
    apply AddCommGrpCat.hom_ext
    ext s
    exact (basisIso_restrict f p n q W.unop V.unop
      ((inducedFunctor (basisOpen f p n)).map i.unop) s).symm

private def basisInvMap (q : ℕ) :
    (inducedFunctor (basisOpen f p n)).op ⋙ (H[q]).presheaf ⟶
      (inducedFunctor (basisOpen f p n)).op ⋙ (Ω[q]).presheaf where
  app W := AddCommGrpCat.ofHom (basisIso f p n q W.unop).inv.hom.toAddMonoidHom
  naturality := by
    intro V W i
    apply AddCommGrpCat.hom_ext
    ext s
    exact (basisIso_inv_restrict f p n q W.unop V.unop
      ((inducedFunctor (basisOpen f p n)).map i.unop) s).symm

/-- The original genuine basis Cartier maps extend to an actual global module-sheaf morphism. -/
def inverseCartierHom (q : ℕ) : Ω[q] ⟶ H[q] :=
  SchemeModuleBasisExtension.extension (X := Y) (basisOpen f p n) (basisIsBasis f p n) (Ω[q]) (H[q])
    (basisMap f p n q) (fun W r s => (basisIso f p n q W).hom.hom.map_smul r s)

/-- The original inverse basis Cartier maps also extend to an actual global module-sheaf morphism. -/
def cartierHom (q : ℕ) : H[q] ⟶ Ω[q] :=
  SchemeModuleBasisExtension.extension (X := Y) (basisOpen f p n) (basisIsBasis f p n) (H[q]) (Ω[q])
    (basisInvMap f p n q) (fun W r s => (basisIso f p n q W).inv.hom.map_smul r s)

/-- Every actual original basis section retains its entire original forward Cartier value. -/
theorem inverseCartierHom_app_basis (q : ℕ) (W : Basis f p n) (s : (Ω[q]).val.obj (op W.val)) :
    ((inverseCartierHom f p n q).val.app (op W.val)).hom s = (basisIso f p n q W).hom.hom s :=
  SchemeModuleBasisExtension.extension_app (X := Y) (basisOpen f p n) (basisIsBasis f p n) (Ω[q]) (H[q])
    (basisMap f p n q) (fun W r s => (basisIso f p n q W).hom.hom.map_smul r s) W s

/-- Every actual original basis target section retains the original inverse Cartier value. -/
theorem cartierHom_app_basis (q : ℕ) (W : Basis f p n) (s : (H[q]).val.obj (op W.val)) :
    ((cartierHom f p n q).val.app (op W.val)).hom s = (basisIso f p n q W).inv.hom s :=
  SchemeModuleBasisExtension.extension_app (X := Y) (basisOpen f p n) (basisIsBasis f p n) (H[q]) (Ω[q])
    (basisInvMap f p n q) (fun W r s => (basisIso f p n q W).inv.hom.map_smul r s) W s

/-- The actual original global geometric Cartier isomorphism in every degree. -/
def inverseCartierIso (q : ℕ) : Ω[q] ≅ H[q] where
  hom := inverseCartierHom f p n q
  inv := cartierHom f p n q
  hom_inv_id := by
    apply SchemeModuleBasisExtension.hom_ext (X := Y) (basisOpen f p n) (basisIsBasis f p n) (Ω[q]) (Ω[q])
    intro W s
    change ((cartierHom f p n q).val.app (op W.val)).hom
      (((inverseCartierHom f p n q).val.app (op W.val)).hom s) = s
    exact (congrArg ((cartierHom f p n q).val.app (op W.val)).hom
      (inverseCartierHom_app_basis f p n q W s)).trans
        ((cartierHom_app_basis f p n q W ((basisIso f p n q W).hom.hom s)).trans
          (Iso.hom_inv_id_apply (basisIso f p n q W) s))
  inv_hom_id := by
    apply SchemeModuleBasisExtension.hom_ext (X := Y) (basisOpen f p n) (basisIsBasis f p n) (H[q]) (H[q])
    intro W s
    change ((inverseCartierHom f p n q).val.app (op W.val)).hom
      (((cartierHom f p n q).val.app (op W.val)).hom s) = s
    exact (congrArg ((inverseCartierHom f p n q).val.app (op W.val)).hom
      (cartierHom_app_basis f p n q W s)).trans
        ((inverseCartierHom_app_basis f p n q W ((basisIso f p n q W).inv.hom s)).trans
          (Iso.inv_hom_id_apply (basisIso f p n q W) s))

private theorem localIso_transport {U V : X.Opens} (e : U = V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (v : Fin n → Γ(X, U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
    (w : Fin n → Γ(X, V))
    (hw : letI := CanonicalGeometry.cotangentOpenAlgebra f V;
      (MvPolynomial.aeval (R := k) w).toRingHom.Etale) (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    letI := CanonicalGeometry.cotangentOpenAlgebra f V;
    Eq.mp (congrArg (fun W : (Y).Opens => (Ω[q]).val.obj (op W) ≅ (H[q]).val.obj (op W))
      (congrArg (RelativeTwistedAffineBasis.twistedOpen f p) e))
      (GeometricAffineHomology.localSheafCartierSectionsIso f p n hU v hv q) =
        GeometricAffineHomology.localSheafCartierSectionsIso f p n hV w hw q := by
  cases e
  exact GeometricAffineHomology.localSheafCartierSectionsIso_chartChange f p n hU v hv w hw q

private theorem basisIso_eq_local {U : X.Opens} (hU : IsAffineOpen U)
    (v : Fin n → Γ(X, U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    basisIso f p n q
        ⟨RelativeTwistedAffineBasis.twistedOpen f p U,
          SchemeRelativeFrobeniusAffineDifferential.twistedOpen_mem_basis f p hU v hv⟩ =
      GeometricAffineHomology.localSheafCartierSectionsIso f p n hU v hv q := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let W : Basis f p n :=
    ⟨RelativeTwistedAffineBasis.twistedOpen f p U,
      SchemeRelativeFrobeniusAffineDifferential.twistedOpen_mem_basis f p hU v hv⟩
  exact localIso_transport f p n (RelativeTwistedAffineBasis.relative_preimage f p U)
    (sourceAffine f p n W) hU (coordinateTuple f p n W) (coordinateTuple_etale f p n W) v hv q

/-- On every original coordinate affine open the entire global Cartier map is its original local map. -/
theorem inverseCartierIso_app_twistedOpen {U : X.Opens} (hU : IsAffineOpen U)
    (v : Fin n → Γ(X, U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ)
    (s : (Ω[q]).val.obj (op (RelativeTwistedAffineBasis.twistedOpen f p U))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ((inverseCartierIso f p n q).hom.val.app
      (op (RelativeTwistedAffineBasis.twistedOpen f p U))).hom s =
        (GeometricAffineHomology.localSheafCartierSectionsIso f p n hU v hv q).hom.hom s := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  let W : Basis f p n :=
    ⟨RelativeTwistedAffineBasis.twistedOpen f p U,
      SchemeRelativeFrobeniusAffineDifferential.twistedOpen_mem_basis f p hU v hv⟩
  exact (inverseCartierHom_app_basis f p n q W s).trans
    (congrArg (fun e => e.hom.hom s) (basisIso_eq_local f p n hU v hv q))

/-- Every original unit form retains exactly its native Cartier and actual global homology image. -/
theorem inverseCartierIso_unit {U : X.Opens} (hU : IsAffineOpen U)
    (v : Fin n → Γ(X, U))
    (hv : letI := CanonicalGeometry.cotangentOpenAlgebra f U;
      (MvPolynomial.aeval (R := k) v).toRingHom.Etale) (q : ℕ)
    (ω : (CanonicalGeometry.exteriorCotangentPresheaf g q).obj
      (op (RelativeTwistedAffineBasis.twistedOpen f p U))) :
    letI := CanonicalGeometry.cotangentOpenAlgebra f U;
    ((inverseCartierIso f p n q).hom.val.app
      (op (RelativeTwistedAffineBasis.twistedOpen f p U))).hom
        ((CanonicalGeometry.exteriorSheafificationMap
          (CanonicalGeometry.cotangentPresheaf g) q).app
            (op (RelativeTwistedAffineBasis.twistedOpen f p U)) ω) =
      (GeometricAffineHomology.geometricHomologySectionsIso f p n hU q).hom.hom
        ((GeometricLocalCartier.nativeInverseCartierIso f p hU n v hv q).hom.hom
          ((GeometricLocalCartier.rawDomainIso f p hU q).hom.hom ω)) := by
  let := CanonicalGeometry.cotangentOpenAlgebra f U
  exact (inverseCartierIso_app_twistedOpen f p n hU v hv q
    ((GeometricLocalCartier.twistedUnitIso f p hU n v hv q).hom.hom ω)).trans
      (GeometricAffineHomology.localSheafCartierSectionsIso_unit f p n hU v hv q ω)

end EnvelopeProperty.Cartier.GeometricSheafCartier
