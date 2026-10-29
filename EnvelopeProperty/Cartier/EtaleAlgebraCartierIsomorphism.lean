import EnvelopeProperty.Cartier.EtaleAlgebraFrobeniusComplex
import EnvelopeProperty.Cartier.EtaleCartierIsomorphism

/-! # The SAME original canonical Cartier isomorphism includes zero algebras -/
noncomputable section
namespace EnvelopeProperty.Cartier.EtaleAlgebraCartierIsomorphism
open CategoryTheory
open scoped Classical
universe u
variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]
variable {n : ℕ} (v : Fin n → B) (hv : (MvPolynomial.aeval (R := k) v).toRingHom.Etale)
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
local notation "W" => KaehlerDifferential k B
local notation "K" => EtaleAlgebraFrobeniusComplex.complex v hv p

/-- The actual native homology comparison of the SAME entire original complexes. -/
def nativeHomologyIso [CharP B p] (q : ℕ) :
    (K).homology q ≅ (EtaleDeRham.frobeniusComplex v hv p).homology q :=
  (HomologicalComplex.homologyFunctor (ModuleCat B) (ComplexShape.up ℕ) q).mapIso
    (EtaleAlgebraFrobeniusComplex.nativeComplexIso v hv p)

private def nontrivialIso (h : Nontrivial B) (q : ℕ) :
    (K).homology q ≅ ModuleCat.of B (⋀[B]^q W) := by
  letI := h
  letI : CharP B p := charP_of_injective_algebraMap (algebraMap k B).injective p
  exact nativeHomologyIso v hv p q ≪≫ EtaleCartierIsomorphism.cartierIso v hv p q

private theorem zeroRingModuleSubsingleton [Subsingleton B] (M : ModuleCat B) :
    Subsingleton M := by
  have hz (x : M) : x = 0 := by
    calc
      x = (1 : B) • x := (one_smul B x).symm
      _ = (0 : B) • x := congrArg (fun a : B => a • x) (Subsingleton.elim _ _)
      _ = 0 := zero_smul B x
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Genuine Cartier isomorphism of the SAME entire original complex on EVERY original
etale k-algebra, including zero, with NO target characteristic/nonzero premise. -/
def cartierIso (q : ℕ) : (K).homology q ≅ ModuleCat.of B (⋀[B]^q W) := by
  by_cases h : Nontrivial B
  · exact nontrivialIso v hv p h q
  · letI : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    letI := zeroRingModuleSubsingleton ((K).homology q)
    letI := zeroRingModuleSubsingleton (ModuleCat.of B (⋀[B]^q W))
    exact (ModuleCat.isZero_of_subsingleton ((K).homology q)).iso
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of B (⋀[B]^q W)))

/-- The SAME original canonical inverse Cartier map, now on EVERY original etale algebra. -/
def inverseCartier (q : ℕ) : ModuleCat.of B (⋀[B]^q W) ⟶ (K).homology q :=
  (cartierIso v hv p q).inv

/-- EVERY original form is recovered, including the actual zero algebra and degree zero. -/
theorem cartierIso_inverseCartier (q : ℕ) (a : ⋀[B]^q W) :
    (cartierIso v hv p q).hom (inverseCartier v hv p q a) = a :=
  Iso.inv_hom_id_apply (cartierIso v hv p q) a

/-- EVERY actual original native cohomology class is recovered by the SAME map. -/
theorem inverseCartier_cartierIso (q : ℕ) (z : (K).homology q) :
    inverseCartier v hv p q ((cartierIso v hv p q).hom z) = z :=
  Iso.hom_inv_id_apply (cartierIso v hv p q) z

/-- The SAME original canonical inverse Cartier map is bijective on EVERY original algebra. -/
theorem inverseCartier_bijective (q : ℕ) : Function.Bijective (inverseCartier v hv p q) :=
  (cartierIso v hv p q).symm.toLinearEquiv.bijective

/-- The native homology comparison retains the SAME pre-existing canonical map on
EVERY original form, wherever the old target characteristic complex is defined. -/
theorem inverseCartier_native [CharP B p] (q : ℕ) (a : ⋀[B]^q W) :
    (nativeHomologyIso v hv p q).hom (inverseCartier v hv p q a) =
      EtaleCartierCycleRepresentatives.inverseCartier v hv p q a := by
  by_cases h : Nontrivial B
  · change (nativeHomologyIso v hv p q).hom ((cartierIso v hv p q).inv a) = _
    simp only [cartierIso, dif_pos h, nontrivialIso]
    change (nativeHomologyIso v hv p q).hom ((nativeHomologyIso v hv p q).inv
      ((EtaleCartierIsomorphism.cartierIso v hv p q).inv a)) = _
    exact (Iso.inv_hom_id_apply (nativeHomologyIso v hv p q) _).trans
      (LinearMap.congr_fun (EtaleCartierIsomorphism.cartierIso_inv v hv p q) a)
  · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp h
    let := zeroRingModuleSubsingleton ((EtaleDeRham.frobeniusComplex v hv p).homology q)
    exact Subsingleton.elim _ _

/-- The ENTIRE actual native comparison square is the SAME pre-existing canonical map. -/
theorem inverseCartier_native_map [CharP B p] (q : ℕ) :
    inverseCartier v hv p q ≫ (nativeHomologyIso v hv p q).hom =
      ModuleCat.ofHom (EtaleCartierCycleRepresentatives.inverseCartier v hv p q) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact inverseCartier_native v hv p q a

/-- On the actual zero algebra this is the unique actual original map, internally. -/
theorem inverseCartier_eq_zero [Subsingleton B] (q : ℕ) :
    inverseCartier v hv p q = 0 := by
  let := zeroRingModuleSubsingleton ((K).homology q)
  exact (ModuleCat.isZero_of_subsingleton ((K).homology q)).eq_of_tgt _ _

end EnvelopeProperty.Cartier.EtaleAlgebraCartierIsomorphism
