/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
import MazurTorsion.Upstream.CurveLineBundleCocycleForcesNormalization
import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Effective descent boundary for curve line bundles

Mathlib provides the pseudofunctor of sheaves of modules and the category of coherent descent
data for a family of scheme morphisms. This foundational module treats effectivity as an input;
the downstream `CurveLineBundleCompatibleFamilies` module discharges it for
universe-zero-indexed open covers. The companion module `CurveLineBundleLocality` proves that an
effective global module assembled from invertible local objects is globally invertible.

This file packages a coherent module descent datum whose local objects are actual Tau Ceti
invertible sheaves. It also separates the two logical existence inputs: `EffectiveModule`
asks only for a global module representing the datum, while `InvertibilityIsLocal` asks that
invertibility on this open cover detect global invertibility. Checked code combines those inputs
into `EffectiveInvertible`, whose consumers recover the chosen global line bundle, the descent
isomorphism, and every chart restriction isomorphism; the companion locality theorem discharges
the second input on every scheme open cover. It also packages specified overlap isomorphisms and
their all-index triple cocycle as Mathlib descent data; diagonal normalization is derived from
those two inputs. The file does not construct divisor-specific overlap isomorphisms, prove their
effectivity, or assert that the module pseudofunctor is a stack.
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

/-- Two chosen-overlap descent data with equal object fields and heterogeneously equal
transition fields are equal; the remaining structure fields are propositions. This is the
structure-extensionality helper used by the chosen-overlap/full-descent comparison below. -/
theorem eq_of_obj_hom_heq
    {D₁ D₂ : F.DescentData' sq sq₃}
    (hobj : D₁.obj = D₂.obj) (hhom : HEq D₁.hom D₂.hom) : D₁ = D₂ := by
  cases D₁
  cases D₂
  rw [Pseudofunctor.DescentData'.mk.injEq]
  exact ⟨hobj, hhom⟩

/-- Extending the chosen-overlap restriction of a full descent datum recovers it. This is the
counit of Mathlib's equivalence between chosen-overlap and full descent data. -/
noncomputable def descentDataOfDescentDataIso
    (sq : ∀ i j, ChosenPullback (f i) (f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (D : F.DescentData f) :
    (Pseudofunctor.DescentData'.ofDescentData sq sq₃ D).descentData ≅ D :=
  (Pseudofunctor.DescentData'.descentDataEquivalence F sq sq₃).counitIso.app D

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

/-- Reinterpret a one-object descent datum for the identity of `X` as descent data along a
monomorphism `f : X ⟶ S`.  Any two lifts through a monomorphism agree, so the identity-base
transition maps provide all transitions over `S`; their pullback, identity, and composition laws
are inherited from the original datum.  This is the categorical source of canonical normalized
self-overlap maps below. -/
noncomputable def rebaseSingleAlongMono
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {S X : C} (f : X ⟶ S) [Mono f]
    (D : F.DescentData (fun _ : Unit ↦ 𝟙 X)) :
    F.DescentData (fun _ : Unit ↦ f) := by
  refine
    { obj := D.obj
      hom := fun {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ ↦
        D.hom f₁ f₁ f₂ (by simp) (by
          simp only [Category.comp_id]
          apply (cancel_mono f).1
          exact hf₂.trans hf₁.symm)
      pullHom_hom := ?_
      hom_self := ?_
      hom_comp := ?_ }
  · intro Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    have hf₂₁ : f₂ = f₁ := by
      apply (cancel_mono f).1
      exact hf₂.trans hf₁.symm
    subst f₂
    simpa only [] using D.pullHom_hom g f₁ gf₁ hgf₁ f₁ f₁
      (by simp) (by simp) gf₁ gf₂ hgf₁ hgf₂
  · intro Y q i g hg
    simpa only [] using D.hom_self g g (by simp)
  · intro Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    have hf₂₁ : f₂ = f₁ := by
      apply (cancel_mono f).1
      exact hf₂.trans hf₁.symm
    have hf₃₁ : f₃ = f₁ := by
      apply (cancel_mono f).1
      exact hf₃.trans hf₁.symm
    subst f₂
    subst f₃
    simpa only [] using D.hom_comp f₁ f₁ f₁ f₁
      (by simp) (by simp) (by simp)

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

/-! ## Canonical normalized self-overlaps for monomorphisms -/

/-- The identity-base descent datum of a scheme module, transported so that its unique local
object is definitionally the supplied module. -/
noncomputable def identityModuleDescentData
    (X : Scheme.{u}) (M : X.Modules) :
    modulesPseudofunctor.DescentData (fun _ : Unit ↦ 𝟙 X) :=
  PseudofunctorDescent.changeObjects
    (fun _ : Unit ↦ 𝟙 X)
    ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ 𝟙 X)).obj M)
    (fun _ ↦ M)
    (fun _ ↦ (Scheme.Modules.pullbackId X).app M)

/-- Every module on the source of a monomorphism has coherent one-object descent data along that
monomorphism.  This asserts descent *data*, not effectivity on the target. -/
noncomputable def monoModuleDescentData
    {S X : Scheme.{u}} (f : X ⟶ S) [Mono f] (M : X.Modules) :
    modulesPseudofunctor.DescentData (fun _ : Unit ↦ f) :=
  PseudofunctorDescent.rebaseSingleAlongMono f (identityModuleDescentData X M)

/-- Restrict the coherent one-object datum along any chosen self-pullback of a monomorphism. -/
noncomputable def monoSelfOverlapDescentDataPrime
    {S X : Scheme.{u}} (f : X ⟶ S) [Mono f] (M : X.Modules)
    (sq : ChosenPullback f f) :
    modulesPseudofunctor.DescentData'
      (fun _ _ : Unit ↦ sq)
      (fun _ _ _ : Unit ↦ ChosenOverlaps.chosenPullback₃ sq sq sq) :=
  Pseudofunctor.DescentData'.ofDescentData _ _ (monoModuleDescentData f M)

/-- The canonical isomorphism between the two pullbacks of a module to a chosen self-overlap of
a monomorphism.  Unlike an arbitrary equality-induced isomorphism, this is extracted from a full
descent datum and therefore carries the required pseudofunctor coherence. -/
noncomputable def monoSelfOverlapIso
    {S X : Scheme.{u}} (f : X ⟶ S) [Mono f] (M : X.Modules)
    (sq : ChosenPullback f f) :
    (Scheme.Modules.pullback sq.p₁).obj M ≅
      (Scheme.Modules.pullback sq.p₂).obj M := by
  let D := monoSelfOverlapDescentDataPrime f M sq
  let hIso : IsIso (D.hom () ()) := by
    rw [← D.pullHom'_eq_hom () ()]
    infer_instance
  exact @asIso _ _ _ _ (D.hom () ()) hIso

/-- The canonical self-overlap isomorphism pulls back to the identity along the diagonal. -/
theorem monoSelfOverlapIso_normalization
    {S X : Scheme.{u}} (f : X ⟶ S) [Mono f] (M : X.Modules)
    (sq : ChosenPullback f f) :
    Pseudofunctor.DescentData'.pullHom' (i₁ := ()) (i₂ := ())
      (F := modulesPseudofunctor) (sq := fun _ _ : Unit ↦ sq)
      (fun _ _ : Unit ↦ (monoSelfOverlapIso f M sq).hom)
      f (𝟙 X) (𝟙 X) = 𝟙 _ := by
  change Pseudofunctor.DescentData'.pullHom'
    (F := modulesPseudofunctor) (sq := fun _ _ : Unit ↦ sq)
    (monoSelfOverlapDescentDataPrime f M sq).hom f (𝟙 X) (𝟙 X) = 𝟙 _
  exact DescentDataPrime.pullHom'_hom_self_opaque
    (monoSelfOverlapDescentDataPrime f M sq) ()

/-- Replace only the diagonal members of an arbitrary overlap-isomorphism family by the
canonical coherent self-overlap maps.  Off the diagonal the original family is unchanged. -/
noncomputable def normalizeOverlapDiagonal
    {X : Scheme.{u}} (cov : X.OpenCover)
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (raw : ∀ i j : cov.I₀,
      (Scheme.Modules.pullback (overlap cov i j).p₁).obj (L i).obj ≅
        (Scheme.Modules.pullback (overlap cov i j).p₂).obj (L j).obj)
    (i j : cov.I₀) :
    (Scheme.Modules.pullback (overlap cov i j).p₁).obj (L i).obj ≅
      (Scheme.Modules.pullback (overlap cov i j).p₂).obj (L j).obj := by
  classical
  by_cases hij : i = j
  · subst j
    exact monoSelfOverlapIso (cov.f i) (L i).obj (overlap cov i i)
  · exact raw i j

/-- Replacing the diagonal overlap maps as above genuinely proves the normalization field needed
by `LineBundleCocycle`, for every original family of off-diagonal isomorphisms. -/
theorem normalizeOverlapDiagonal_normalization
    {X : Scheme.{u}} (cov : X.OpenCover)
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (raw : ∀ i j : cov.I₀,
      (Scheme.Modules.pullback (overlap cov i j).p₁).obj (L i).obj ≅
        (Scheme.Modules.pullback (overlap cov i j).p₂).obj (L j).obj)
    (i : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := modulesPseudofunctor) (sq := overlap cov)
      (fun i j ↦ (normalizeOverlapDiagonal cov L raw i j).hom)
      (cov.f i) (𝟙 (cov.X i)) (𝟙 (cov.X i)) = 𝟙 _ := by
  classical
  have hdiag : normalizeOverlapDiagonal cov L raw i i =
      monoSelfOverlapIso (cov.f i) (L i).obj (overlap cov i i) := by
    simp [normalizeOverlapDiagonal]
  have hdiagHom : (fun i j ↦ (normalizeOverlapDiagonal cov L raw i j).hom) i i =
      (monoSelfOverlapIso (cov.f i) (L i).obj (overlap cov i i)).hom :=
    congrArg Iso.hom hdiag
  unfold Pseudofunctor.DescentData'.pullHom'
  rw [hdiagHom]
  simpa only [Pseudofunctor.DescentData'.pullHom'] using
    monoSelfOverlapIso_normalization (cov.f i) (L i).obj (overlap cov i i)

universe u' v v'

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

private theorem pullHom_comp_same_map
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {X₁ X₂ X₃ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {M₃ : F.obj (.mk (.op X₃))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (e₁₂ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (e₂₃ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶
      (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (gf₃ : Y' ⟶ X₃)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (hgf₃ : g ≫ f₃ = gf₃) :
    pullHom e₁₂ g gf₁ gf₂ hgf₁ hgf₂ ≫
      pullHom e₂₃ g gf₂ gf₃ hgf₂ hgf₃ =
      pullHom (e₁₂ ≫ e₂₃) g gf₁ gf₃ hgf₁ hgf₃ := by
  subst gf₁
  subst gf₂
  subst gf₃
  simp [pullHom, Functor.map_comp]

private theorem pullHom_id_same_map
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {X Y Y' : C} {M : F.obj (.mk (.op X))}
    {f : Y ⟶ X} (g : Y' ⟶ Y) (gf : Y' ⟶ X)
    (hgf : g ≫ f = gf) :
    pullHom (F := F) (𝟙 ((F.map f.op.toLoc).toFunctor.obj M))
        g gf gf hgf hgf =
      𝟙 ((F.map gf.op.toLoc).toFunctor.obj M) := by
  subst gf
  simp [pullHom]

/-- Pull an isomorphism along a further map using the pseudofunctor's canonical comparison
maps. The underlying forward morphism is definitionally `pullHom`, so later naturality theorems
do not have to unfold a separately assembled composite isomorphism. -/
noncomputable def pullIso
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map gf₁.op.toLoc).toFunctor.obj M₁ ≅
      (F.map gf₂.op.toLoc).toFunctor.obj M₂ where
  hom := pullHom e.hom g gf₁ gf₂ hgf₁ hgf₂
  inv := pullHom e.inv g gf₂ gf₁ hgf₂ hgf₁
  hom_inv_id := by
    rw [pullHom_comp_same_map, e.hom_inv_id]
    exact pullHom_id_same_map g gf₁ hgf₁
  inv_hom_id := by
    rw [pullHom_comp_same_map, e.inv_hom_id]
    exact pullHom_id_same_map g gf₂ hgf₂

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
  pullIso (F := modulesPseudofunctor) e hpb.isoPullback.inv
    (pullback.fst f₁ f₂) (pullback.snd f₁ f₂)
    hpb.isoPullback_inv_fst hpb.isoPullback_inv_snd

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

/-- Coherent overlap isomorphisms for a specified family of local line bundles.
This is the concrete gluing input: one isomorphism on each chosen pairwise overlap and the
cocycle equation on every chosen triple overlap, including repeated indices. Diagonal
normalization is forced by invertibility and the repeated-index cocycle, so it is derived below
rather than stored as a potentially inconsistent extra field. -/
structure LineBundleCocycle
    {X : Scheme.{u}} (cov : X.OpenCover)
    (sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)) where
  /-- The specified isomorphism between the two restrictions on each pairwise overlap. -/
  overlapIso (i j : cov.I₀) :
    (modulesPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
      (modulesPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (L j).obj
  /-- The two composites of transition maps agree on every triple overlap. -/
  cocycle (i j k : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := sq)
        (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃

namespace LineBundleCocycle

/-- Every isomorphism-valued all-index line-bundle cocycle is normalized on the diagonal.
The triple cocycle with three equal indices makes the diagonal transition idempotent, and an
invertible idempotent is the identity. -/
theorem normalization
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    (C : LineBundleCocycle cov sq sq₃ L) (i : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := modulesPseudofunctor) (sq := sq)
      (fun i j ↦ (C.overlapIso i j).hom)
      (cov.f i) (𝟙 (cov.X i)) (𝟙 (cov.X i)) = 𝟙 _ := by
  exact normalization_of_iso_cocycle
    (F := modulesPseudofunctor) (Y := cov.X) (g := cov.f)
    (sq := sq) (sq₃ := sq₃) (obj := fun i ↦ (L i).obj)
    C.overlapIso C.cocycle i

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
    (modulesPseudofunctor.map (sq i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
      (modulesPseudofunctor.map (sq i j).p₂.op.toLoc).toFunctor.obj (L j).obj := by
  let D' := descentDataPrimeOfObjectIso sq sq₃ L D e
  let hIso : IsIso (D'.hom i j) := by
    rw [← D'.pullHom'_eq_hom i j]
    infer_instance
  exact @asIso _ _ _ _ (D'.hom i j) hIso

/-- Objectwise transport preserves diagonal normalization on chosen overlaps. This specialized
comparison remains useful independently of the fact that normalization is forced for every
`LineBundleCocycle`. -/
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
induces a line-bundle cocycle. Object transport inherits the triple cocycle from the original
datum, and diagonal normalization then follows automatically. -/
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

private theorem toDescentDataPrime_ofDescentDataObjectIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) :
    (ofDescentDataObjectIso (sq := sq) (sq₃ := sq₃) L D e).toDescentDataPrime =
      Pseudofunctor.DescentData'.ofDescentData sq sq₃
        (PseudofunctorDescent.changeObjects cov.f D (fun i ↦ (L i).obj) e) := by
  apply DescentDataPrime.eq_of_obj_hom_heq
  · rfl
  · exact HEq.rfl

private noncomputable def ofDescentDataObjectIsoToDescentDataPrimeIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) :
    (ofDescentDataObjectIso (sq := sq) (sq₃ := sq₃) L D e).toDescentDataPrime ≅
      Pseudofunctor.DescentData'.ofDescentData sq sq₃
        (PseudofunctorDescent.changeObjects cov.f D (fun i ↦ (L i).obj) e) :=
  eqToIso (toDescentDataPrime_ofDescentDataObjectIso L D e)

/-- Reconstructing full descent data from the normalized chosen-overlap cocycle obtained by
objectwise transport recovers the transported full descent datum. This compares the actual
cocycle consumer with its full coherent source; it does not assume effectivity. -/
noncomputable def ofDescentDataObjectIso_toDescentDataIso
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (D : modulesPseudofunctor.DescentData cov.f)
    (e : ∀ i, D.obj i ≅ (L i).obj) :
    (ofDescentDataObjectIso (sq := sq) (sq₃ := sq₃) L D e).toDescentData ≅
      PseudofunctorDescent.changeObjects cov.f D (fun i ↦ (L i).obj) e := by
  let D' := PseudofunctorDescent.changeObjects cov.f D (fun i ↦ (L i).obj) e
  let C := ofDescentDataObjectIso (sq := sq) (sq₃ := sq₃) L D e
  let E : C.toDescentDataPrime ≅
      Pseudofunctor.DescentData'.ofDescentData sq sq₃ D' :=
    ofDescentDataObjectIsoToDescentDataPrimeIso L D e
  let Efull : C.toDescentData ≅
      (Pseudofunctor.DescentData'.ofDescentData sq sq₃ D').descentData :=
    (Pseudofunctor.DescentData'.toDescentDataFunctor
      modulesPseudofunctor sq sq₃).mapIso E
  let Ecounit :
      (Pseudofunctor.DescentData'.ofDescentData sq sq₃ D').descentData ≅ D' :=
    DescentDataPrime.descentDataOfDescentDataIso sq sq₃ D'
  change C.toDescentData ≅ D'
  exact Efull.trans Ecounit

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
