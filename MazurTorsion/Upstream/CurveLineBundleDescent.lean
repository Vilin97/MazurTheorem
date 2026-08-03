/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Effective descent boundary for curve line bundles

Mathlib provides the pseudofunctor of sheaves of modules and the category of coherent descent
data for a family of scheme morphisms. The current dependency graph does not yet prove that
these descent data are effective for a Zariski cover. The companion module
`CurveLineBundleLocality` proves that an effective global module assembled from invertible local
objects is globally invertible.

This file packages a coherent module descent datum whose local objects are actual Tau Ceti
invertible sheaves. It also separates the two logical existence inputs: `EffectiveModule`
asks only for a global module representing the datum, while `InvertibilityIsLocal` asks that
invertibility on this open cover detect global invertibility. Checked code combines those inputs
into `EffectiveInvertible`, whose consumers recover the chosen global line bundle, the descent
isomorphism, and every chart restriction isomorphism; the companion locality theorem discharges
the second input on every scheme open cover. It also packages specified overlap
isomorphisms, normalization, and the triple cocycle as Mathlib descent data. The file does not
construct divisor-specific overlap isomorphisms, prove their effectivity, or assert that the
module pseudofunctor is a stack.
-/

open CategoryTheory Bicategory CategoryTheory.Limits

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent.DescentDataPrime

open Opposite CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open CategoryTheory.Pseudofunctor.DescentData'

universe t v' v u' u

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {sq : ∀ i j, ChosenPullback (f i) (f j)}
  {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}

/-- Construct chosen-pullback descent data from overlap isomorphisms, a diagonal
normalization, and the triple-overlap cocycle. Factoring this constructor out keeps concrete
scheme instances within the default elaboration budget. -/
noncomputable def ofIso
    (obj : ∀ i, F.obj (.mk (Opposite.op (X i))))
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (normalization : ∀ i,
      pullHom' (fun i j ↦ (overlapIso i j).hom)
        (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _)
    (cocycle : ∀ i j k,
      pullHom' (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        pullHom' (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        pullHom' (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃) :
    F.DescentData' sq sq₃ where
  obj := obj
  hom i j := (overlapIso i j).hom
  pullHom'_hom_self := normalization
  pullHom'_hom_comp := cocycle

/-- An opaque wrapper around a chosen-overlap datum's diagonal field. -/
theorem pullHom'_hom_self_opaque
    (D : F.DescentData' sq sq₃) (i : ι) :
    pullHom' D.hom (f i) (𝟙 (X i)) (𝟙 (X i)) = 𝟙 _ :=
  D.pullHom'_hom_self i

/-- An opaque wrapper around a chosen-overlap datum's triple-coherence field. -/
theorem pullHom'_hom_comp_opaque
    (D : F.DescentData' sq sq₃) (i j k : ι) :
    pullHom' D.hom (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        pullHom' D.hom (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      pullHom' D.hom (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃ :=
  D.pullHom'_hom_comp i j k

end MazurTorsion.AlgebraicGeometry.LineBundleDescent.DescentDataPrime

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent.PseudofunctorDescent

universe t v' v u' u

open CategoryTheory

/-- Transport coherent descent data across a specified isomorphism on every local object.
The transition morphisms are conjugated by the pulled-back object isomorphisms, so
normalization and the triple cocycle are inherited from the original datum. -/
noncomputable def changeObjects
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (D : F.DescentData f)
    (obj : ∀ i, F.obj (.mk (.op (X i))))
    (e : ∀ i, D.obj i ≅ obj i) : F.DescentData f where
  obj := obj
  hom {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ :=
    (F.map f₁.op.toLoc).toFunctor.map (e _).inv ≫
      D.hom q f₁ f₂ hf₁ hf₂ ≫
      (F.map f₂.op.toLoc).toFunctor.map (e _).hom
  pullHom_hom {Y'} {Y} g q q' hq {i₁ i₂} f₁ f₂ hf₁ hf₂
      gf₁ gf₂ hgf₁ hgf₂ := by
    rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [← F.mapComp'_hom_naturality_assoc,
      F.mapComp'_inv_naturality]
    simpa only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      Category.assoc] using congrArg
      (fun k ↦ (F.map gf₁.op.toLoc).toFunctor.map (e i₁).inv ≫ k ≫
        (F.map gf₂.op.toLoc).toFunctor.map (e i₂).hom)
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂
        gf₁ gf₂ hgf₁ hgf₂)
  hom_self {Y} q {i} g hg := by
    rw [D.hom_self q g hg]
    simp
  hom_comp {Y} q {i₁ i₂ i₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    simp only [Category.assoc]
    rw [Iso.map_hom_inv_id_assoc]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ (F.map f₁.op.toLoc).toFunctor.map (e _).inv ≫ k ≫
        (F.map f₃.op.toLoc).toFunctor.map (e _).hom)
      (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- The original descent datum is isomorphic to its objectwise transport.  This is the
effectivity comparison used when a known global object is replaced by specified isomorphic local
models: the transition maps were defined by conjugation, so the supplied object isomorphisms are
automatically a morphism of descent data. -/
noncomputable def changeObjectsIso
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (D : F.DescentData f)
    (obj : ∀ i, F.obj (.mk (.op (X i))))
    (e : ∀ i, D.obj i ≅ obj i) :
    D ≅ changeObjects f D obj e :=
  Pseudofunctor.DescentData.isoMk e (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    simp only [changeObjects]
    simp)

end MazurTorsion.AlgebraicGeometry.LineBundleDescent.PseudofunctorDescent

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

universe u

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

/-- The scheme-module pseudofunctor with only its pullback functors retained. -/
noncomputable def modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp (Adj.forget₁ (B := Cat))

namespace ChosenOverlaps

universe w

/-- A chosen pullback built from the category's standard pullback. -/
noncomputable def chosenPullback
    {C : Type u} [Category.{w} C] [HasPullbacks C]
    {Y Z S : C} (f : Y ⟶ S) (g : Z ⟶ S) : ChosenPullback f g where
  pullback := pullback f g
  p₁ := pullback.fst f g
  p₂ := pullback.snd f g
  condition := pullback.condition
  isLimit := pullbackIsPullback f g

/-- A chosen triple pullback built from standard pairwise pullbacks. -/
noncomputable def chosenPullback₃
    {C : Type u} [Category.{w} C] [HasPullbacks C]
    {X₁ X₂ X₃ S : C} {f₁ : X₁ ⟶ S} {f₂ : X₂ ⟶ S} {f₃ : X₃ ⟶ S}
    (h₁₂ : ChosenPullback f₁ f₂)
    (h₂₃ : ChosenPullback f₂ f₃)
    (h₁₃ : ChosenPullback f₁ f₃) :
    ChosenPullback₃ h₁₂ h₂₃ h₁₃ where
  chosenPullback := chosenPullback h₁₂.p₂ h₂₃.p₁
  l := Classical.choice (ChosenPullback.LiftStruct.nonempty
    (by
      simp only [Category.assoc, h₁₂.hp₁, h₂₃.hp₂]
      rw [← h₁₂.hp₂, ← h₂₃.hp₁, ← Category.assoc, ← Category.assoc,
        (chosenPullback h₁₂.p₂ h₂₃.p₁).condition])
    (by simp))

end ChosenOverlaps

/-- The standard chosen pairwise overlap of two members of a scheme open cover. -/
noncomputable def overlap
    {X : Scheme.{u}} (cov : X.OpenCover) (i j : cov.I₀) :
    ChosenPullback (cov.f i) (cov.f j) :=
  ChosenOverlaps.chosenPullback (cov.f i) (cov.f j)

/-- The standard chosen triple overlap of three members of a scheme open cover. -/
noncomputable def tripleOverlap
    {X : Scheme.{u}} (cov : X.OpenCover) (i j k : cov.I₀) :
    ChosenPullback₃ (overlap cov i j) (overlap cov j k) (overlap cov i k) :=
  ChosenOverlaps.chosenPullback₃
    (overlap cov i j) (overlap cov j k) (overlap cov i k)

/-- Transport a module isomorphism from any explicit model of a fibre product to the standard
chosen pullback. The comparison uses only the pullback universal property, pullback
composition, and congruence along the two projection equations. -/
noncomputable def pullbackOverlapIsoOfModel
    {S X₁ X₂ W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)
    (p₁ : W ⟶ X₁) (p₂ : W ⟶ X₂)
    (hpb : IsPullback p₁ p₂ f₁ f₂)
    (M₁ : X₁.Modules) (M₂ : X₂.Modules)
    (e : (Scheme.Modules.pullback p₁).obj M₁ ≅
      (Scheme.Modules.pullback p₂).obj M₂) :
    (Scheme.Modules.pullback (pullback.fst f₁ f₂)).obj M₁ ≅
      (Scheme.Modules.pullback (pullback.snd f₁ f₂)).obj M₂ :=
  ((Scheme.Modules.pullbackCongr hpb.isoPullback_inv_fst).app M₁).symm ≪≫
    ((Scheme.Modules.pullbackComp hpb.isoPullback.inv p₁).app M₁).symm ≪≫
    (Scheme.Modules.pullback hpb.isoPullback.inv).mapIso e ≪≫
    (Scheme.Modules.pullbackComp hpb.isoPullback.inv p₂).app M₂ ≪≫
    (Scheme.Modules.pullbackCongr hpb.isoPullback_inv_snd).app M₂

/-- Pullback of the globally trivial line bundle along an open immersion is the trivial line
bundle on the source. This concrete comparison is used by the principal-divisor cocycle. -/
noncomputable def pullbackTrivialIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.pullback f).obj (InvertibleSheaf.trivial Y).obj ≅
      (InvertibleSheaf.trivial X).obj := by
  let efreeY : (InvertibleSheaf.trivial Y).obj ≅
      SheafOfModules.unit Y.ringCatSheaf :=
    Limits.coproductUniqueIso (fun _ : PUnit ↦
      SheafOfModules.unit Y.ringCatSheaf)
  let efreeX : (InvertibleSheaf.trivial X).obj ≅
      SheafOfModules.unit X.ringCatSheaf :=
    Limits.coproductUniqueIso (fun _ : PUnit ↦
      SheafOfModules.unit X.ringCatSheaf)
  exact ((Scheme.Modules.restrictFunctorIsoPullback f).app
    (InvertibleSheaf.trivial Y).obj).symm ≪≫
      (Scheme.Modules.restrictFunctor f).mapIso efreeY ≪≫
      Scheme.Modules.restrictUnitIso f ≪≫ efreeX.symm

/-- A coherent module descent datum all of whose local objects are invertible sheaves. The
coherence is exactly Mathlib's `DescentData`; this structure adds only the rank-one property
needed for divisor line bundles. -/
structure InvertibleDescentData {X : Scheme.{u}} (cov : X.OpenCover) where
  /-- The coherent underlying module descent datum. -/
  toDescentData : modulesPseudofunctor.DescentData cov.f
  /-- Every local object in the descent datum is an invertible sheaf. -/
  localInvertible (i : cov.I₀) :
    SheafOfModules.isInvertible (cov.X i) (toDescentData.obj i)

namespace InvertibleDescentData

/-- The actual local invertible sheaf carried by an invertible descent datum. -/
noncomputable def localLineBundle
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : InvertibleDescentData cov) (i : cov.I₀) : InvertibleSheaf (cov.X i) :=
  ⟨D.toDescentData.obj i, D.localInvertible i⟩

@[simp]
lemma localLineBundle_obj
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : InvertibleDescentData cov) (i : cov.I₀) :
    (D.localLineBundle i).obj = D.toDescentData.obj i :=
  rfl

/-- The coherent datum supplies the transition isomorphism after any two compatible pullbacks
of its local line bundles. -/
noncomputable def transitionIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : InvertibleDescentData cov) {Y : Scheme.{u}} (q : Y ⟶ X)
    {i₁ i₂ : cov.I₀} (f₁ : Y ⟶ cov.X i₁) (f₂ : Y ⟶ cov.X i₂)
    (hf₁ : f₁ ≫ cov.f i₁ = q := by cat_disch)
    (hf₂ : f₂ ≫ cov.f i₂ = q := by cat_disch) :
    (Scheme.Modules.pullback f₁).obj (D.localLineBundle i₁).obj ≅
      (Scheme.Modules.pullback f₂).obj (D.localLineBundle i₂).obj :=
  D.toDescentData.iso q f₁ f₂ hf₁ hf₂

/-- Package coherent descent data whose local objects are identified with chosen line bundles.
This is the direct entry point for a family of chartwise divisor line bundles once their
overlap-compatible descent datum has been constructed. -/
noncomputable def ofLineBundles
    {X : Scheme.{u}} {cov : X.OpenCover}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) : InvertibleDescentData cov where
  toDescentData := D
  localInvertible i :=
    (SheafOfModules.isInvertible (cov.X i)).prop_of_iso (e i).symm (L i).property

/-- Packaging chosen line bundles retains their specified local identifications. -/
noncomputable def ofLineBundlesLocalLineBundleIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) (i : cov.I₀) :
    ((ofLineBundles L D e).localLineBundle i).obj ≅ (L i).obj :=
  e i

end InvertibleDescentData

/-- Normalized coherent overlap isomorphisms for a specified family of local line bundles.
This is the concrete gluing input: one isomorphism on each chosen pairwise overlap, identity
after pullback along the diagonal, and the cocycle equation on each chosen triple overlap. -/
structure LineBundleCocycle
    {X : Scheme.{u}} (cov : X.OpenCover)
    (sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)) where
  /-- The specified isomorphism between the two restrictions on each pairwise overlap. -/
  overlapIso (i j : cov.I₀) :
    (Scheme.Modules.pullback (sq i j).p₁).obj (L i).obj ≅
      (Scheme.Modules.pullback (sq i j).p₂).obj (L j).obj
  /-- The transition isomorphism restricts to the identity on each diagonal. -/
  normalization (i : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := modulesPseudofunctor)
      (sq := sq)
      (fun i j ↦ (overlapIso i j).hom)
      (cov.f i) (𝟙 (cov.X i)) (𝟙 (cov.X i)) = 𝟙 _
  /-- The two composites of transition maps agree on every triple overlap. -/
  cocycle (i j k : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor)
        (sq := sq)
        (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor)
        (sq := sq)
        (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor)
        (sq := sq)
        (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃

namespace LineBundleCocycle

/-- Chosen-overlap descent data after transporting every local object across a specified
isomorphism. Naming this intermediate object keeps its coherence proofs opaque to later
consumers. -/
noncomputable def descentDataPrimeOfObjectIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    (sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) :
    modulesPseudofunctor.DescentData' sq sq₃ :=
  Pseudofunctor.DescentData'.ofDescentData sq sq₃
    (PseudofunctorDescent.changeObjects
      cov.f D (fun i ↦ (L i).obj) e)

/-- The chosen-overlap transition isomorphism obtained by transporting coherent descent data
across specified isomorphisms of its local objects. -/
noncomputable def overlapIsoOfDescentDataObjectIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) (i j : cov.I₀) :
    (Scheme.Modules.pullback (sq i j).p₁).obj (L i).obj ≅
      (Scheme.Modules.pullback (sq i j).p₂).obj (L j).obj := by
  let D' := descentDataPrimeOfObjectIso sq sq₃ L D e
  let hIso : IsIso (D'.hom i j) := by
    rw [← D'.pullHom'_eq_hom i j]
    infer_instance
  exact @asIso _ _ _ _ (D'.hom i j) hIso

/-- Objectwise transport preserves diagonal normalization on chosen overlaps. -/
theorem overlapIsoOfDescentDataObjectIso_normalization
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) (i : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := modulesPseudofunctor) (sq := sq)
      (fun i j ↦
        (overlapIsoOfDescentDataObjectIso
          (sq := sq) (sq₃ := sq₃) L D e i j).hom)
      (cov.f i) (𝟙 (cov.X i)) (𝟙 (cov.X i)) = 𝟙 _ := by
  change Pseudofunctor.DescentData'.pullHom'
    (F := modulesPseudofunctor) (sq := sq)
    (descentDataPrimeOfObjectIso sq sq₃ L D e).hom
    (cov.f i) (𝟙 (cov.X i)) (𝟙 (cov.X i)) = 𝟙 _
  exact DescentDataPrime.pullHom'_hom_self_opaque
    (descentDataPrimeOfObjectIso sq sq₃ L D e) i

/-- Objectwise transport preserves the triple-overlap cocycle. -/
theorem overlapIsoOfDescentDataObjectIso_cocycle
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) (i j k : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (fun i j ↦
          (overlapIsoOfDescentDataObjectIso
            (sq := sq) (sq₃ := sq₃) L D e i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (fun i j ↦
          (overlapIsoOfDescentDataObjectIso
            (sq := sq) (sq₃ := sq₃) L D e i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (fun i j ↦
          (overlapIsoOfDescentDataObjectIso
            (sq := sq) (sq₃ := sq₃) L D e i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃ := by
  change
    Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (descentDataPrimeOfObjectIso sq sq₃ L D e).hom
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (descentDataPrimeOfObjectIso sq sq₃ L D e).hom
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (descentDataPrimeOfObjectIso sq sq₃ L D e).hom
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃
  exact DescentDataPrime.pullHom'_hom_comp_opaque
    (descentDataPrimeOfObjectIso sq sq₃ L D e) i j k

/-- A coherent descent datum whose local objects are isomorphic to specified line bundles
induces a normalized line-bundle cocycle. Object transport inherits diagonal normalization and
the triple cocycle from the original datum. -/
noncomputable def ofDescentDataObjectIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) :
    LineBundleCocycle cov sq sq₃ L where
  overlapIso :=
    overlapIsoOfDescentDataObjectIso (sq := sq) (sq₃ := sq₃) L D e
  normalization :=
    overlapIsoOfDescentDataObjectIso_normalization (sq := sq) (sq₃ := sq₃) L D e
  cocycle :=
    overlapIsoOfDescentDataObjectIso_cocycle (sq := sq) (sq₃ := sq₃) L D e

/-- The chosen-overlap presentation of a line-bundle cocycle as Mathlib descent data. -/
noncomputable def toDescentDataPrime
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L) :
    modulesPseudofunctor.DescentData' sq sq₃ :=
  DescentDataPrime.ofIso
    (fun i ↦ (L i).obj) C.overlapIso C.normalization C.cocycle

/-- Extend the chosen overlap cocycle to coherent descent data on every common refinement. -/
noncomputable def toDescentData
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L) :
    modulesPseudofunctor.DescentData cov.f :=
  C.toDescentDataPrime.descentData

@[simp]
lemma toDescentData_obj
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L) (i : cov.I₀) :
    C.toDescentData.obj i = (L i).obj :=
  rfl

/-- Regard a line-bundle cocycle as coherent locally invertible descent data. -/
noncomputable def toInvertibleDescentData
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L) : InvertibleDescentData cov where
  toDescentData := C.toDescentData
  localInvertible i := (L i).property

@[simp]
lemma toDescentData_hom_on_overlap
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L) (i j : cov.I₀) :
    C.toDescentData.hom (sq i j).p (sq i j).p₁ (sq i j).p₂ =
      (C.overlapIso i j).hom := by
  exact Pseudofunctor.DescentData'.pullHom'_eq_hom C.toDescentDataPrime i j

@[simp]
lemma toDescentData_iso_on_overlap
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L) (i j : cov.I₀) :
    C.toDescentData.iso (sq i j).p (sq i j).p₁ (sq i j).p₂ =
      C.overlapIso i j := by
  ext
  exact C.toDescentData_hom_on_overlap i j

end LineBundleCocycle

/-- A specified coherent module descent datum is represented by some global module sheaf. This
is object-specific essential surjectivity, not a stack theorem. -/
noncomputable def EffectiveModule
    {X : Scheme.{u}} (cov : X.OpenCover)
    (D : modulesPseudofunctor.DescentData cov.f) : Prop :=
  ∃ M : X.Modules,
    Nonempty ((modulesPseudofunctor.toDescentData cov.f).obj M ≅ D)

namespace EffectiveModule

/-- The global module sheaf supplied by object-specific effectivity. -/
noncomputable def module
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveModule cov D) : X.Modules :=
  h.choose

/-- The chosen global module induces the specified coherent descent datum. -/
noncomputable def descentIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveModule cov D) :
    (modulesPseudofunctor.toDescentData cov.f).obj h.module ≅ D :=
  h.choose_spec.some

/-- Every cover restriction of the effective global module is the corresponding local object.
-/
noncomputable def restrictionIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveModule cov D) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj h.module ≅ D.obj i where
  hom := h.descentIso.hom.hom i
  inv := h.descentIso.inv.hom i
  hom_inv_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) h.descentIso.hom_inv_id
    change h.descentIso.hom.hom i ≫ h.descentIso.inv.hom i = 𝟙 _
    exact hi
  inv_hom_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) h.descentIso.inv_hom_id
    change h.descentIso.inv.hom i ≫ h.descentIso.hom.hom i = 𝟙 _
    exact hi
end EffectiveModule

/-- Object effectivity for every module descent datum on one specified open cover. This is the
essential-surjectivity half of a stack theorem, restricted to this cover. -/
noncomputable def ModuleEffectiveDescentFor
    {X : Scheme.{u}} (cov : X.OpenCover) : Prop :=
  ∀ D : modulesPseudofunctor.DescentData cov.f, EffectiveModule cov D

/-- Morphisms and isomorphisms of global module sheaves are detected by their coherent
restrictions to one specified open cover. This is the fully-faithful, or prestack, half of
module descent for that cover. -/
abbrev ModuleDescentFullyFaithfulFor
    {X : Scheme.{u}} (cov : X.OpenCover) : Type _ :=
  (modulesPseudofunctor.toDescentData cov.f).FullyFaithful

/-- A prestack theorem for the scheme-module pseudofunctor supplies fully faithful descent on
every Zariski open cover. Mathlib provides the generic implication and proves that an open cover
belongs to the Zariski topology; the required `IsPrestack` instance itself is not currently in
the dependency graph. -/
noncomputable def moduleDescentFullyFaithfulForOfIsPrestack
    {X : Scheme.{u}} (cov : X.OpenCover)
    [modulesPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology.{u}] :
    ModuleDescentFullyFaithfulFor cov :=
  modulesPseudofunctor.fullyFaithfulToDescentData
    cov.f cov.mem_grothendieckTopology

/-- The exact object-separation input needed to lift an isomorphism of coherent restrictions:
isomorphic descent data come from isomorphic global module sheaves. -/
def ModuleDescentEssentiallyInjectiveFor
    {X : Scheme.{u}} (cov : X.OpenCover) : Prop :=
  ∀ M N : X.Modules,
    Nonempty
      ((modulesPseudofunctor.toDescentData cov.f).obj M ≅
        (modulesPseudofunctor.toDescentData cov.f).obj N) →
      Nonempty (M ≅ N)

/-- A narrower object-separation input sufficient for principal divisor line bundles:
the coherent restrictions of a global module can be isomorphic to those of the trivial line
bundle only when the global module itself is trivial.  Unlike
`ModuleDescentEssentiallyInjectiveFor`, this does not compare two arbitrary global modules. -/
def ModuleDescentReflectsTrivialityFor
    {X : Scheme.{u}} (cov : X.OpenCover) : Prop :=
  ∀ M : X.Modules,
    Nonempty
      ((modulesPseudofunctor.toDescentData cov.f).obj M ≅
        (modulesPseudofunctor.toDescentData cov.f).obj
          (InvertibleSheaf.trivial X).obj) →
      Nonempty (M ≅ (InvertibleSheaf.trivial X).obj)

/-- Full object separation implies reflection of the one object actually used by the divisor
kernel argument. -/
theorem moduleDescentReflectsTrivialityFor_of_essentiallyInjective
    {X : Scheme.{u}} {cov : X.OpenCover}
    (hinjective : ModuleDescentEssentiallyInjectiveFor cov) :
    ModuleDescentReflectsTrivialityFor cov :=
  fun M e ↦ hinjective M (InvertibleSheaf.trivial X).obj e

/-- Fully faithful module descent is a standard sufficient source of the exact object-separation
property used below. -/
theorem moduleDescentEssentiallyInjectiveFor_of_fullyFaithful
    {X : Scheme.{u}} {cov : X.OpenCover}
    (hfaithful : ModuleDescentFullyFaithfulFor cov) :
    ModuleDescentEssentiallyInjectiveFor cov :=
  fun _ _ e ↦ ⟨hfaithful.preimageIso e.some⟩

/-- Fully faithful module descent implies reflection of global triviality. -/
theorem moduleDescentReflectsTrivialityFor_of_fullyFaithful
    {X : Scheme.{u}} {cov : X.OpenCover}
    (hfaithful : ModuleDescentFullyFaithfulFor cov) :
    ModuleDescentReflectsTrivialityFor cov :=
  moduleDescentReflectsTrivialityFor_of_essentiallyInjective
    (moduleDescentEssentiallyInjectiveFor_of_fullyFaithful hfaithful)

/-- A prestack theorem for scheme modules implies the exact object-separation property used for
principal divisor line bundles. This is the checked consumer of the missing prestack input. -/
theorem moduleDescentEssentiallyInjectiveFor_of_isPrestack
    {X : Scheme.{u}} (cov : X.OpenCover)
    [hprestack : modulesPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology.{u}] :
    ModuleDescentEssentiallyInjectiveFor cov :=
  moduleDescentEssentiallyInjectiveFor_of_fullyFaithful
    (@moduleDescentFullyFaithfulForOfIsPrestack X cov hprestack)

/-- A prestack theorem supplies the narrower trivial-object reflection used by the exact
divisor-kernel consumer. -/
theorem moduleDescentReflectsTrivialityFor_of_isPrestack
    {X : Scheme.{u}} (cov : X.OpenCover)
    [hprestack : modulesPseudofunctor.{u}.IsPrestack Scheme.zariskiTopology.{u}] :
    ModuleDescentReflectsTrivialityFor cov :=
  moduleDescentReflectsTrivialityFor_of_fullyFaithful
    (@moduleDescentFullyFaithfulForOfIsPrestack X cov hprestack)

/-- The exact open-cover localization input for line bundles: a global module whose pullback to
every cover member is invertible is itself invertible. The companion module
`CurveLineBundleLocality` proves this predicate for every scheme open cover. -/
def InvertibilityIsLocal {X : Scheme.{u}} (cov : X.OpenCover) : Prop :=
  ∀ M : X.Modules,
    (∀ i : cov.I₀,
      SheafOfModules.isInvertible (cov.X i)
        ((Scheme.Modules.pullback (cov.f i)).obj M)) →
      SheafOfModules.isInvertible X M

/-- A specified coherent module descent datum on an open cover is effectively represented by
a global invertible sheaf. This packages object-specific effectivity and global invertibility;
it does not assert effectivity for all module descent data or a stack theorem. -/
noncomputable def EffectiveInvertible
    {X : Scheme.{u}} (cov : X.OpenCover)
    (D : modulesPseudofunctor.DescentData cov.f) : Prop :=
  ∃ L : InvertibleSheaf X,
    Nonempty ((modulesPseudofunctor.toDescentData cov.f).obj L.obj ≅ D)

namespace EffectiveInvertible

/-- The global invertible sheaf supplied by effective descent. -/
noncomputable def lineBundle
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D) : InvertibleSheaf X :=
  h.choose

/-- The chosen global line bundle induces the specified coherent descent datum. -/
noncomputable def descentIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D) :
    (modulesPseudofunctor.toDescentData cov.f).obj h.lineBundle.obj ≅ D :=
  h.choose_spec.some

/-- On every member of the cover, the chosen global line bundle restricts to the corresponding
local object of the specified descent datum. This is the genuine consumer of
`EffectiveInvertible`. -/
noncomputable def restrictionIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj h.lineBundle.obj ≅ D.obj i where
  hom := h.descentIso.hom.hom i
  inv := h.descentIso.inv.hom i
  hom_inv_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) h.descentIso.hom_inv_id
    change h.descentIso.hom.hom i ≫ h.descentIso.inv.hom i = 𝟙 _
    exact hi
  inv_hom_id := by
    have hi := congrArg (fun φ ↦ φ.hom i) h.descentIso.inv_hom_id
    change h.descentIso.inv.hom i ≫ h.descentIso.hom.hom i = 𝟙 _
    exact hi

/-- Lift an isomorphism from the specified effective descent datum to any other global module
when module descent on the cover is fully faithful. -/
noncomputable def preimageIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D)
    (hfaithful : ModuleDescentFullyFaithfulFor cov)
    {M : X.Modules}
    (e : D ≅ (modulesPseudofunctor.toDescentData cov.f).obj M) :
    h.lineBundle.obj ≅ M :=
  hfaithful.preimageIso (h.descentIso ≪≫ e)

/-- The lifted isomorphism realizes exactly the supplied isomorphism of descent data. -/
@[simp]
lemma mapIso_preimageIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D)
    (hfaithful : ModuleDescentFullyFaithfulFor cov)
    {M : X.Modules}
    (e : D ≅ (modulesPseudofunctor.toDescentData cov.f).obj M) :
    (modulesPseudofunctor.toDescentData cov.f).mapIso
        (h.preimageIso hfaithful e) = h.descentIso ≪≫ e :=
  hfaithful.isoEquiv.apply_symm_apply _

/-- Effective invertible descent in particular gives ordinary module effectivity. -/
theorem toEffectiveModule
    {X : Scheme.{u}} {cov : X.OpenCover}
    {D : modulesPseudofunctor.DescentData cov.f}
    (h : EffectiveInvertible cov D) : EffectiveModule cov D :=
  ⟨h.lineBundle.obj, ⟨h.descentIso⟩⟩

/-- Module effectivity for locally invertible descent data produces an effective global line
bundle once invertibility is known to be local on the chosen cover. -/
theorem of_effectiveModule
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : InvertibleDescentData cov)
    (heffective : EffectiveModule cov D.toDescentData)
    (hlocal : InvertibilityIsLocal cov) :
    EffectiveInvertible cov D.toDescentData := by
  let M := heffective.module
  have hM : SheafOfModules.isInvertible X M := hlocal M fun i ↦
    (SheafOfModules.isInvertible (cov.X i)).prop_of_iso
      (heffective.restrictionIso i).symm (D.localInvertible i)
  exact ⟨⟨M, hM⟩, ⟨heffective.descentIso⟩⟩

end EffectiveInvertible

namespace LineBundleCocycle

/-- Effective descent identifies the global restriction with the original local line bundle,
not merely with an anonymous module object. -/
noncomputable def effectiveRestrictionIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L)
    (h : EffectiveInvertible cov C.toDescentData) (i : cov.I₀) :
    (Scheme.Modules.pullback (cov.f i)).obj h.lineBundle.obj ≅ (L i).obj :=
  h.restrictionIso i

end LineBundleCocycle

/-- Effective descent of every locally invertible module datum on one specified open cover.
Unlike a full stack assertion, this asks only for object effectivity and only for descent data
whose local objects are line bundles. -/
noncomputable def InvertibleEffectiveDescentFor
    {X : Scheme.{u}} (cov : X.OpenCover) : Prop :=
  ∀ D : InvertibleDescentData cov, EffectiveInvertible cov D.toDescentData

/-- Module effectivity together with open-cover locality of invertibility gives effective
descent for every locally invertible datum on that cover. -/
theorem invertibleEffectiveDescentFor_of_moduleEffectivity_of_locality
    {X : Scheme.{u}} {cov : X.OpenCover}
    (heffective : ModuleEffectiveDescentFor cov)
    (hlocal : InvertibilityIsLocal cov) :
    InvertibleEffectiveDescentFor cov :=
  fun D ↦ EffectiveInvertible.of_effectiveModule D
    (heffective D.toDescentData) hlocal

/-- For locally invertible descent data, module effectivity and invertible effectivity agree
once invertibility is known to be local on the chosen cover. This theorem separates rather than
hides the two remaining globalization inputs. -/
theorem effectiveInvertible_iff_effectiveModule
    {X : Scheme.{u}} {cov : X.OpenCover}
    (D : InvertibleDescentData cov) (hlocal : InvertibilityIsLocal cov) :
    EffectiveInvertible cov D.toDescentData ↔
      EffectiveModule cov D.toDescentData :=
  ⟨EffectiveInvertible.toEffectiveModule,
    fun h ↦ EffectiveInvertible.of_effectiveModule D h hlocal⟩

end MazurTorsion.AlgebraicGeometry.LineBundleDescent
