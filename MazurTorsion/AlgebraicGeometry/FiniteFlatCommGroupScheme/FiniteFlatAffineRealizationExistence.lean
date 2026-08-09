/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AffineRealizationFullness

/-!
# Affine realization of geometric finite-flat group schemes

A finite morphism to an affine base has affine source.  This file uses that fact together with
the affine `Spec`--global-sections equivalence to recover Hopf coordinates from an actual
finite-flat commutative group scheme over `Spec R`.

Over an arbitrary commutative ring the coordinate module is finite flat, not necessarily free,
so the reconstruction lands in `AffineFiniteFlatCommGroupScheme`; any finite-free upgrade would
require an additional base-ring theorem.  None of these results classifies prime-order models as
constant or multiplicative; Oort--Tate/Raynaud existence remains separate.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open IsDedekindDomain HeightOneSpectrum
open MazurTorsion.IntegerPrimeSpecialization

namespace AlgebraicGeometry

universe u

private theorem essImage_mapCommGrp_iff
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [CartesianMonoidalCategory C] [BraidedCategory C]
    [CartesianMonoidalCategory D] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] [F.Full] [F.Faithful]
    {G : CommGrp D} :
    F.mapCommGrp.essImage G ↔ F.essImage G.X := by
  constructor
  · rintro ⟨H, ⟨e⟩⟩
    exact ⟨H.X, ⟨(CommGrp.forget D).mapIso e⟩⟩
  · intro hG
    have hGrp : F.mapGrp.essImage G.toGrp :=
      (Functor.essImage_mapGrp (F := F)).2 hG
    rcases hGrp with ⟨H, ⟨e⟩⟩
    let FH : Grp D := F.mapGrp.obj H
    let q : FH.X ⟶ G.X := e.hom.hom.hom
    letI : IsIso q := by
      dsimp [q]
      change IsIso ((Grp.forget D).map e.hom)
      infer_instance
    letI : IsMonHom q := by
      exact e.hom.hom.isMonHom_hom
    have hcommImage : (β_ FH.X FH.X).hom ≫ μ[FH.X] = μ[FH.X] := by
      apply (cancel_mono q).1
      rw [Category.assoc, IsMonHom.mul_hom]
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
      rw [Category.assoc, IsCommMonObj.mul_comm]
    letI : IsCommMonObj H.X := ⟨by
      apply (Functor.FullyFaithful.ofFullyFaithful F).map_injective
      apply (cancel_epi (Functor.LaxMonoidal.μ F H.X H.X)).1
      rw [F.map_comp, Functor.LaxBraided.braided_assoc]
      exact hcommImage⟩
    let C' : CommGrp C := .mk H.X
    have eC : (F.mapCommGrp.obj C').toGrp ≅ G.toGrp := by
      exact Grp.mkIso ((Grp.forget D).mapIso e)
        (one_f := IsMonHom.one_hom q) (mul_f := IsMonHom.mul_hom q)
    let e' : F.mapCommGrp.obj C' ≅ G :=
      (CommGrp.fullyFaithfulForget₂Grp D).preimageIso eC
    exact ⟨C', ⟨e'⟩⟩

namespace AffineCommGroupScheme

variable {R : Type u} [CommRing R]

/-- The Hopf algebra contravariantly encoded by a commutative group object in affine
`R`-algebras. -/
private noncomputable def hopfOfCommAlgOp
    (G : CommGrp ((CommAlgCat.{u} R)ᵒᵖ)) : CommHopfAlgCat.{u} R :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj (op G.toGrp)

private noncomputable instance hopfOfCommAlgOp_isCocomm
    (G : CommGrp ((CommAlgCat.{u} R)ᵒᵖ)) :
    Coalgebra.IsCocomm R (hopfOfCommAlgOp G) := by
  constructor
  exact congrArg AlgHom.toLinearMap congr($(IsCommMonObj.mul_comm G.X).unop.hom)

/-- A commutative group object in opposite affine algebras, regarded as affine Hopf
coordinates. -/
private noncomputable def ofCommAlgOp
    (G : CommGrp ((CommAlgCat.{u} R)ᵒᵖ)) : AffineCommGroupScheme R :=
  op ⟨hopfOfCommAlgOp G, hopfOfCommAlgOp_isCocomm G⟩

private noncomputable def coordinateCommGroupFunctor_obj_ofCommAlgOpIso
    (G : CommGrp ((CommAlgCat.{u} R)ᵒᵖ)) :
    (coordinateCommGroupFunctor R).obj (ofCommAlgOp G) ≅ G := by
  apply (CommGrp.fullyFaithfulForget₂Grp _).preimageIso
  change
    (unop ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj
      ((commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj (op G.toGrp)))) ≅ G.toGrp
  exact ((commHopfAlgCatEquivCogrpCommAlgCat R).counitIso.app (op G.toGrp)).unop.symm

end AffineCommGroupScheme

namespace FiniteFlatCommGroupScheme

variable {R : Type u} [CommRing R]

/-- The underlying scheme of every finite-flat group scheme over an affine base is affine. -/
theorem isAffine_scheme (G : FiniteFlatCommGroupScheme (Spec (.of R))) :
    IsAffine G.scheme := by
  exact isAffine_of_isAffineHom G.structureMap

/-- The algebra structure on global sections induced by an object over `Spec R`. -/
private noncomputable def globalSectionsAlgebraMap
    (T : Over (Spec (.of R))) : R →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ T.hom.appTop).hom

/-- An affine object over `Spec R` lies in the essential image of relative spectrum. -/
private noncomputable def affineOverIsoTestObject
    (T : Over (Spec (.of R))) [IsAffine T.left] :
    letI := (globalSectionsAlgebraMap T).toAlgebra
    T ≅ AffineCommGroupScheme.testObject (R := R) Γ(T.left, ⊤) := by
  letI := (globalSectionsAlgebraMap T).toAlgebra
  exact Over.isoMk T.left.isoSpec (by
    change T.left.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (algebraMap R Γ(T.left, ⊤))) = T.hom
    rw [RingHom.algebraMap_toAlgebra]
    change T.left.toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ T.hom.appTop) = T.hom
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp)

/-- Every geometric finite-flat commutative group scheme over an affine base is the actual
geometric realization of finite-flat affine Hopf coordinates.  Over an arbitrary commutative
ring the coordinates are finite and flat; no freeness claim is made. -/
theorem exists_affineFiniteFlat_realization
    (G : FiniteFlatCommGroupScheme (Spec (.of R))) :
    ∃ A : AffineFiniteFlatCommGroupScheme R, Nonempty (G ≅ A.realize) := by
  letI : IsAffine G.scheme := G.isAffine_scheme
  let B := Γ(G.scheme, ⊤)
  letI : Algebra R B := (globalSectionsAlgebraMap G.obj.X).toAlgebra
  have hobject : (AffineCommGroupScheme.relativeSpecFunctor R).essImage G.obj.X := by
    refine ⟨op (CommAlgCat.of R B), ⟨?_⟩⟩
    exact (affineOverIsoTestObject G.obj.X).symm
  letI : (AffineCommGroupScheme.relativeSpecFunctor R).Full :=
    AffineCommGroupScheme.relativeSpecFullyFaithful.full
  letI : (AffineCommGroupScheme.relativeSpecFunctor R).Faithful :=
    AffineCommGroupScheme.relativeSpecFullyFaithful.faithful
  have hgroup :
      (AffineCommGroupScheme.relativeSpecFunctor R).mapCommGrp.essImage G.obj :=
    (essImage_mapCommGrp_iff (AffineCommGroupScheme.relativeSpecFunctor R)).2 hobject
  rcases hgroup with ⟨C, ⟨e⟩⟩
  let A : AffineCommGroupScheme R := AffineCommGroupScheme.ofCommAlgOp C
  let eCoordinates :
      (AffineCommGroupScheme.coordinateCommGroupFunctor R).obj A ≅ C :=
    AffineCommGroupScheme.coordinateCommGroupFunctor_obj_ofCommAlgOpIso C
  let eGeometric : A.toCommGroupScheme ≅ G.obj :=
    (AffineCommGroupScheme.relativeSpecFunctor R).mapCommGrp.mapIso eCoordinates ≪≫ e
  let q : A.scheme ⟶ G.scheme := eGeometric.hom.hom.hom.hom.left
  letI : IsIso q := by
    change IsIso ((Over.forget (Spec (.of R))).map eGeometric.hom.hom.hom.hom)
    infer_instance
  have hq : q ≫ G.structureMap = A.structureMap :=
    eGeometric.hom.hom.hom.hom.w
  letI : IsFinite A.structureMap := by
    rw [← hq]
    infer_instance
  letI : Flat A.structureMap := by
    rw [← hq]
    infer_instance
  letI : Module.Finite R A.coordinates := by
    rw [← RingHom.finite_algebraMap]
    apply (IsFinite.SpecMap_iff
      (CommRingCat.ofHom (algebraMap R A.coordinates))).mp
    change IsFinite A.structureMap
    infer_instance
  letI : Module.Flat R A.coordinates := by
    rw [← RingHom.flat_algebraMap_iff]
    apply (Flat.SpecMap_iff
      (f := CommRingCat.ofHom (algebraMap R A.coordinates))).mp
    change Flat A.structureMap
    infer_instance
  let A' : AffineFiniteFlatCommGroupScheme R := ⟨A, ⟨inferInstance, inferInstance⟩⟩
  refine ⟨A', ?_⟩
  exact ⟨ObjectProperty.isoMk (finiteFlatCommGroupSchemeProperty (Spec (.of R)))
    (X := G) (Y := A'.realize) eGeometric.symm⟩

end FiniteFlatCommGroupScheme

namespace AffineFiniteFlatCommGroupScheme

variable {R : Type u} [CommRing R]

/-- Functorial geometric realization on finite-flat affine Hopf morphisms. -/
def realizeMap {G H : AffineFiniteFlatCommGroupScheme R} (f : G ⟶ H) :
    G.realize ⟶ H.realize :=
  ObjectProperty.homMk ((AffineCommGroupScheme.realizationFunctor R).map f.hom)

/-- Geometric realization of finite-flat affine Hopf coordinates as a functor. -/
def realizationFunctor (R : Type u) [CommRing R] :
    AffineFiniteFlatCommGroupScheme R ⥤ FiniteFlatCommGroupScheme (Spec (.of R)) where
  obj G := G.realize
  map f := realizeMap f
  map_id G := by
    apply ObjectProperty.hom_ext
    exact (AffineCommGroupScheme.realizationFunctor R).map_id G.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (AffineCommGroupScheme.realizationFunctor R).map_comp f.hom g.hom

/-- Finite-flat affine realization is fully faithful on actual morphisms. -/
def realizationFunctorFullyFaithful (R : Type u) [CommRing R] :
    (realizationFunctor R).FullyFaithful where
  preimage f := ObjectProperty.homMk
    ((AffineCommGroupScheme.realizationFunctorFullyFaithful R).preimage f.hom)
  map_preimage f := by
    apply ObjectProperty.hom_ext
    exact (AffineCommGroupScheme.realizationFunctorFullyFaithful R).map_preimage f.hom
  preimage_map f := by
    apply ObjectProperty.hom_ext
    exact (AffineCommGroupScheme.realizationFunctorFullyFaithful R).preimage_map f.hom

/-- Recover the Hopf-coordinate morphism underlying an arbitrary geometric map between
finite-flat affine realizations. -/
def preimageRealizeMap {G H : AffineFiniteFlatCommGroupScheme R}
    (f : G.realize ⟶ H.realize) : G ⟶ H :=
  (realizationFunctorFullyFaithful R).preimage f

@[simp]
theorem realizeMap_preimageRealizeMap {G H : AffineFiniteFlatCommGroupScheme R}
    (f : G.realize ⟶ H.realize) :
    realizeMap (preimageRealizeMap f) = f :=
  (realizationFunctorFullyFaithful R).map_preimage f

/-- The geometric realization/base-change comparison is natural for finite-flat affine Hopf
morphisms. -/
theorem realizeBaseChangeIso_naturality
    {K : Type u} [CommRing K] [Algebra R K]
    {G H : AffineFiniteFlatCommGroupScheme R} (f : G ⟶ H) :
    (FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map (realizeMap f) ≫
        (realizeBaseChangeIso (K := K) H).hom =
      (realizeBaseChangeIso (K := K) G).hom ≫
        realizeMap ((baseChangeFunctor (R := R) (K := K)).map f) := by
  apply ObjectProperty.hom_ext
  exact AffineCommGroupScheme.realizationBaseChangeIso_naturality (K := K) f.hom

/-- Arbitrary geometric maps between finite-flat affine realizations over a domain are determined
by their actual geometric generic fibres. -/
theorem hom_ext_of_geometricGenericFiber_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : AffineFiniteFlatCommGroupScheme A} {f g : G.realize ⟶ H.realize}
    (hfg :
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map f =
      (FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map g) :
    f = g := by
  have hrealized :
      realizeMap ((baseChangeFunctor (R := A) (K := F)).map
          (preimageRealizeMap f)) =
        realizeMap ((baseChangeFunctor (R := A) (K := F)).map
          (preimageRealizeMap g)) := by
    apply (cancel_epi (realizeBaseChangeIso (K := F) G).hom).1
    rw [← realizeBaseChangeIso_naturality (K := F) (preimageRealizeMap f),
      ← realizeBaseChangeIso_naturality (K := F) (preimageRealizeMap g),
      realizeMap_preimageRealizeMap, realizeMap_preimageRealizeMap, hfg]
  have hcoordinates :
      (baseChangeFunctor (R := A) (K := F)).map (preimageRealizeMap f) =
        (baseChangeFunctor (R := A) (K := F)).map (preimageRealizeMap g) :=
    (realizationFunctorFullyFaithful F).map_injective hrealized
  have hintegral : preimageRealizeMap f = preimageRealizeMap g :=
    AffineFiniteFlatCommGroupScheme.hom_ext_of_genericFiber_eq hcoordinates
  simpa using congrArg realizeMap hintegral

end AffineFiniteFlatCommGroupScheme

namespace FiniteFlatCommGroupScheme

/-- Generic-fibre base change is faithful on arbitrary geometric finite-flat commutative group
schemes over an affine domain.  The affine Hopf models and their realization isomorphisms are
constructed internally; callers supply no presentation certificate. -/
theorem hom_ext_of_geometricGenericFiber_eq
    {A F : Type u} [CommRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    {G H : FiniteFlatCommGroupScheme (Spec (.of A))} {f g : G ⟶ H}
    (hfg :
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map f =
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map g) :
    f = g := by
  obtain ⟨AG, ⟨eG⟩⟩ := G.exists_affineFiniteFlat_realization
  obtain ⟨AH, ⟨eH⟩⟩ := H.exists_affineFiniteFlat_realization
  let f' : AG.realize ⟶ AH.realize := eG.inv ≫ f ≫ eH.hom
  let g' : AG.realize ⟶ AH.realize := eG.inv ≫ g ≫ eH.hom
  have hfg' :
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map f' =
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap A F)))).map g' := by
    simp only [f', g', Functor.map_comp, hfg]
  have h' : f' = g' :=
    AffineFiniteFlatCommGroupScheme.hom_ext_of_geometricGenericFiber_eq hfg'
  have h := congrArg (fun k ↦ eG.hom ≫ k ≫ eH.inv) h'
  simpa [f', g', Category.assoc] using h

/-- Actual geometric morphisms between arbitrary finite-flat commutative group schemes over the
five-adic completion integers are determined by base change to the five-adic field.  No affine
presentation of either object is a premise. -/
theorem arbitrary_hom_ext_of_completionGeometricGenericFiberAtFive_eq
    {G H : FiniteFlatCommGroupScheme
      (Spec (.of (atFive.adicCompletionIntegers ℚ)))} {f g : G ⟶ H}
    (hfg :
      (baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atFive.adicCompletionIntegers ℚ)
            (atFive.adicCompletion ℚ))))).map f =
      (baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atFive.adicCompletionIntegers ℚ)
            (atFive.adicCompletion ℚ))))).map g) :
    f = g :=
  hom_ext_of_geometricGenericFiber_eq hfg

/-- Actual geometric morphisms between arbitrary finite-flat commutative group schemes over the
eleven-adic completion integers are determined by base change to the eleven-adic field.  No
affine presentation of either object is a premise. -/
theorem arbitrary_hom_ext_of_completionGeometricGenericFiberAtEleven_eq
    {G H : FiniteFlatCommGroupScheme
      (Spec (.of (atEleven.adicCompletionIntegers ℚ)))} {f g : G ⟶ H}
    (hfg :
      (baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atEleven.adicCompletionIntegers ℚ)
            (atEleven.adicCompletion ℚ))))).map f =
      (baseChange
        (Spec.map (CommRingCat.ofHom
          (algebraMap (atEleven.adicCompletionIntegers ℚ)
            (atEleven.adicCompletion ℚ))))).map g) :
    f = g :=
  hom_ext_of_geometricGenericFiber_eq hfg

end FiniteFlatCommGroupScheme

end AlgebraicGeometry
