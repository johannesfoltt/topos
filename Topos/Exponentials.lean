/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
--import Mathlib.CategoryTheory.Topos.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Topos.Basic

/-!
# Exponential Objects

Proves that a topos has exponential objects (internal homs).
Consequently, every topos is Cartesian closed.

## Main definitions

* `Hom A B` is the exponential object, and `eval A B` is the associated
  "evaluation map" `A ⨯ Hom A B ⟶ B`.

* `IsExponentialObject` says what it means to be an exponential object.

## Main results

* `ToposHasExponentials` shows that a topos has exponential objects.
  This is done by showing `IsExponentialObject (eval A B)`.

* `ExpAdjEquiv` exhibits `(A ⨯ X ⟶ B) ≃ (X ⟶ Hom A B)` for any `A B X : C`
  in a topos `C`.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

-/

open CategoryTheory Category Limits MonoClassifier Power Topos

universe u v

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Topos

noncomputable section

variable [IsTopos C]

/-- The exponential object B^A. -/
def hom (A B : C) : C :=
  pullback
    ((((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^ ≫ Predicate.isSingleton B)^)
    ⌈Predicate.true_ A⌉

/-- The map which sends `A ⟶ B` to its graph as a subobject of `B ⨯ A`. -/
def homToGraph (A B : C) : hom A B ⟶ pow (B ⨯ A) := pullback.fst _ _

/-- The map sending a morphism to its graph is a monomorphism, so that
the graphs of morphisms `A ⟶ B` may be regarded as subobjects of `B ⨯ A`.
-/
instance homToGraphMono {A B : C} : Mono (homToGraph A B) := pullback.fst_of_mono

/-- Convenience lemma used in `Hom_comm`. -/
lemma exp_cone_snd (A B : C) :
    pullback.snd _ _ = terminal.from (hom A B) := Unique.eq_default _

/-- Convenience lemma used in `EvalDef_comm`. -/
lemma hom_comm (A B : C) :
    homToGraph A B ≫ ((((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^ ≫ Predicate.isSingleton B)^)
    = terminal.from (hom A B) ≫ ⌈Predicate.true_ A⌉ := by
  rw [←exp_cone_snd]; exact pullback.condition

/-- This lemma states that the following diagram commutes:
```
    A ⨯ Hom A B ---------terminal.from _----------> ⊤_ C
      |                                               |
      |                                               |
(𝟙 A) ⨯ homToGraph A B                              t C
      |                                               |
      |                                               |
      v                                               v
    A ⨯ Pow (B ⨯ A) ------------u-------------------> Ω
```
where `u` intuitively is the predicate:
(a,S) ↦ "there is exactly one b in B such that (b,a) in S".
This is used to define the map `eval A B : A ⨯ Hom A B ⟶ B`
as a `pullback.lift` where the object `B` serves as the pullback.
-/
lemma eval_def_comm (A B : C) :
  (prod.map (𝟙 A) (homToGraph A B)
  ≫ ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^) ≫ Predicate.isSingleton B
  = Predicate.true_ (A ⨯ hom A B) := by
    let id_m : A ⨯ hom A B ⟶ A ⨯ pow (B ⨯ A) := prod.map (𝟙 _) (homToGraph A B)
    let v := (((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^)
    let σ_B := Predicate.isSingleton B
    let u := ((v ≫ Predicate.isSingleton B)^)
    let id_u := prod.map (𝟙 A) u
    have comm_middle : v ≫ σ_B = id_u ≫ (in_ A) := (comm A (v ≫ σ_B)).symm
    have comm_left :
    id_m ≫ id_u
    =  prod.map (𝟙 _) (terminal.from _) ≫ prod.map (𝟙 _) ⌈Predicate.true_ A⌉ := by
      rw [prod.map_map, prod.map_map]
      ext; simp
      rw [prod.map_snd, prod.map_snd, hom_comm]
    have h_terminal :
    (prod.map (𝟙 A) (terminal.from (hom A B)) ≫ prod.fst) ≫ terminal.from A = terminal.from _ :=
      Unique.eq_default _
    rw [assoc, comm_middle, ←assoc, comm_left, assoc, Predicate.NameDef]
    dsimp [Predicate.true_]
    rw [←assoc, ←assoc, h_terminal]

/-- The evaluation map eval : A ⨯ B^A ⟶ B. -/
def eval (A B : C) : A ⨯ (hom A B) ⟶ B :=
  IsPullback.lift (isPullback _) _ _ (eval_def_comm _ _)

/-- This states the commutativity of the square relating
`eval A B` to `singleton B` and `homToGraph A B`, which
arises from its definition.
-/
lemma eval_condition (A B : C) :
    eval A B ≫ singleton B
    = prod.map (𝟙 _) (homToGraph A B) ≫ ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^ :=
  IsPullback.lift_fst (isPullback _) _ _ (eval_def_comm _ _)

variable {A B X : C} (f : A ⨯ X ⟶ B)

/-- Useful definition in the context of the construction of `eval A B`.
This is the composition of `homMap f` with `homToGraph A B`, as exhibited
in `homMapCondition` below.
-/
abbrev h_map : X ⟶ pow (B ⨯ A) :=
  ((prod.associator _ _ _).hom ≫ prod.map (𝟙 _) f ≫ Predicate.eq _)^


/-- Helper lemma which shows that the appropriate square commutes
in the definition of `homMap`.
-/
lemma homMap_comm :
    h_map f ≫ (((prod.associator B A (pow (B ⨯ A))).inv
    ≫ in_ (B ⨯ A))^ ≫ Predicate.isSingleton B)^ =
    terminal.from X ≫ ⌈Predicate.true_ A⌉ := by
  -- consider (1⨯f) ≫ (eq B) : B ⨯ A ⨯ X ⟶ Ω C.
  let id_f'eq : B ⨯ A ⨯ X ⟶ Ω C := prod.map (𝟙 _) f ≫ Predicate.eq _
  -- h is the map that, in `Set`, takes an element of X to the graph of the corresponding function.
  -- We want to lift this to a map X ⟶ Exp A B.
  -- The idea is to show that this map actually "maps elements of X to graphs of functions", which,
  -- in an arbitrary topos, is the same as checking commutativity of the obvious square.
  let h : X ⟶ pow (B ⨯ A) := (((prod.associator _ _ _).hom ≫ id_f'eq)^)
  -- h is by definition a P-transpose
  have h_condition : (prod.associator _ _ _).hom ≫ id_f'eq
  = (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
    rw [prod.map_id_id]
    symm
    apply Power.comm
  -- moving the associator to the rhs of `h_condition`.
  have h_condition₂ : id_f'eq
  = (prod.associator _ _ _).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
    rw [←h_condition, ←assoc, (prod.associator _ _ _).inv_hom_id, id_comp]
  -- this is the map v: A ⨯ P(B⨯A) ⟶ P(B) which was used in the definition of `Exp A B`.
  let v : A ⨯ pow (B ⨯ A) ⟶ pow B := (((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^)
  -- v is by definition a P-transpose
  have v_condition : (prod.associator _ _ _).inv ≫ in_ (B ⨯ A)
  = prod.map (𝟙 _) v ≫ in_ _ := (comm _ _).symm
  have lhs : (prod.map (𝟙 A) h ≫ v ≫ Predicate.isSingleton B)^
  = h ≫ (v ≫ Predicate.isSingleton B)^ := by
    apply Power.unique
    rw [prod.map_id_comp, assoc _ _ (in_ A), Power.comm, ←assoc]
  rw [←lhs]
  -- Claim that f ≫ {•}_B = (1⨯h) ≫ v.
  -- This is obtained by showing that both maps are the P-transpose of (1⨯f) ≫ (eq B).
  -- There might be a slightly faster way to do this.
  have transpose₁ : id_f'eq^ = f ≫ singleton _ := by
    apply Power.unique
    dsimp only [Topos.singleton]
    rw [prod.map_id_comp, assoc, (comm B (Predicate.eq B))]
  have shuffle_h_around : (prod.associator B A X).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h)
  = prod.map (𝟙 _) (prod.map (𝟙 _) h) ≫ (prod.associator _ _ _).inv := by simp
  have transpose₂ : id_f'eq^ = (prod.map (𝟙 _) h) ≫ v := by
    apply Power.unique
    rw [h_condition₂, ←assoc, shuffle_h_around, prod.map_id_comp, assoc _ _ (in_ B),
    ←v_condition, assoc]
  have eqn₁ : f ≫ singleton _ = (prod.map (𝟙 _) h) ≫ v := transpose₁.symm.trans transpose₂
  -- now compose by the `isSingleton B` predicate.
  have eqn₂ : f ≫ singleton _ ≫ Predicate.isSingleton _
  = (prod.map (𝟙 _) h) ≫ v ≫ Predicate.isSingleton _ := by
    rw [←assoc, ←assoc, eqn₁]
  rw [←eqn₂]
  -- from here, the argument is mostly definition unpacking.
  apply Power.unique
  dsimp only [name, Predicate.true_, Predicate.isSingleton]
  have f_terminal : f ≫ terminal.from B = terminal.from _ := Unique.eq_default _
  have rightUnitor_terminal : (Limits.prod.rightUnitor A).hom ≫ terminal.from A
  = terminal.from _ :=
    Unique.eq_default _
  have A_X_terminal : prod.map (𝟙 A) (terminal.from X) ≫ terminal.from (A ⨯ ⊤_ C)
  = terminal.from _ :=
    Unique.eq_default _
  have obv : terminal.from (A ⨯ ⊤_ C) ≫ t C
  = prod.map (𝟙 A) ((terminal.from (A ⨯ ⊤_ C) ≫ t C)^) ≫ in_ A :=
    (comm _ _).symm
  have map_def : (Limits.prod.rightUnitor A).hom = prod.fst := rfl
  rw [MonoClassifier.comm (singleton _), ←assoc, ←map_def, rightUnitor_terminal, ←assoc,
  f_terminal, prod.map_id_comp, assoc, ←obv, ←assoc, A_X_terminal]

/-- Given a map `f : A ⨯ X ⟶ B`, `homMap f`
is the associated map `X ⟶ Hom A B`.
-/
def homMap : X ⟶ hom A B :=
  pullback.lift (h_map f) (terminal.from X) (homMap_comm f)

/-- composing `homMap f` with the map sending a morphism to its graph
is the map `h_map f` defined above.
-/
@[simp]
lemma homMap_condition : homMap f ≫ (homToGraph A B) = h_map f :=
  pullback.lift_fst _ _ _

/-- `homMap f` satisfies the condition that
the following diagram commutes:
```
        A ⨯ X ---f----> B
          |             ^
          |            /
          |           /
    (𝟙 A) ⨯ homMap  /
          |         /
          |     eval A B
          |       /
          |      /
          |     /
          |    /
          v   /
        A ⨯ (Hom A B)
```
-/
@[reassoc]
theorem hom_exponentiates : prod.map (𝟙 _ ) (homMap f) ≫ eval A B = f := by
  rw [←cancel_mono (singleton B), assoc, eval_condition, ←assoc,
    prod.map_map, id_comp, homMap_condition]
  have h : transposeInv (f ≫ singleton B)
      = transposeInv (prod.map (𝟙 A) (h_map f)
      ≫ transpose ((prod.associator B A (Power.pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))) := by
    rw [transposeInv, transposeInv, prod.map_id_comp, assoc, singleton,
      Power.comm, prod.map_id_comp, assoc, Power.comm, ←assoc]
    have h' : (prod.map (𝟙 B) (prod.map (𝟙 A) (h_map f))
        ≫ (prod.associator B A (Power.pow (B ⨯ A))).inv)
      = (prod.associator B A X).inv ≫ (prod.map (𝟙 _) (h_map f)) := by simp
    rw [h', assoc, h_map, Power.comm, ←assoc, Iso.inv_hom_id, id_comp]
  have h₀ := congrArg (fun k => transpose k) h
  have t₁ : ((f ≫ singleton B)^)^ = f ≫ singleton B := (transposeEquiv _ _).right_inv _
  have t₂ : (((prod.map (𝟙 A) (h_map f)
    ≫ ((prod.associator B A (Power.pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))^))^)^
    = (prod.map (𝟙 A) (h_map f) ≫ ((prod.associator B A (Power.pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))^) :=
      transpose_right_inv _
  simp only [t₁, t₂] at h₀
  exact h₀.symm

/-- Proof of the uniqueness of `homMap f` as a map
`X ⟶ Hom A B` satisfying commutativity of the associated
diagram. See `Hom_Exponentiates`.
-/
theorem Hom_Unique {exp' : X ⟶ hom A B} (h : prod.map (𝟙 _) exp' ≫ (eval A B) = f) :
    homMap f = exp' := by
  have h_singleton := congrArg (fun k ↦ k ≫ singleton B) h
  simp only at h_singleton
  let v : A ⨯ pow (B ⨯ A) ⟶ pow B := (((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^)
  -- want to rewrite (1⨯g) ≫ eval A B ≫ singleton B = (1⨯(g≫m)) ≫ v
  have rhs : eval A B ≫ singleton B = prod.map (𝟙 _) (homToGraph A B) ≫ v := by
    apply PullbackCone.IsLimit.lift_fst
  rw [assoc, rhs, ←assoc, ←prod.map_id_comp] at h_singleton
  let id_f'eq : B ⨯ A ⨯ X ⟶ Ω C := prod.map (𝟙 _) f ≫ Predicate.eq _
  have h₁ : id_f'eq^ = f ≫ singleton B := by
    apply Power.unique
    dsimp only [id_f'eq, singleton]
    rw [prod.map_id_comp, assoc, comm _ (Predicate.eq B)]
  have h₂ : (prod.map (𝟙 _) (prod.map (𝟙 _) (exp' ≫ homToGraph A B))
      ≫ (prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^
      = prod.map (𝟙 _) (exp' ≫ homToGraph A B) ≫ v := by
    apply Power.unique
    rw [prod.map_id_comp, assoc, Power.comm]
  have h₃ := Power.comm _ ((prod.map (𝟙 B) (prod.map (𝟙 A) (exp' ≫ homToGraph A B))
      ≫ (prod.associator B A (Power.pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)))
  rw [h₂, h_singleton, ←h₁, Power.comm _ id_f'eq, ←assoc] at h₃
  have h' := hom_exponentiates f
  have h'_singleton := congrArg (fun k ↦ k ≫ singleton B) h'
  simp only at h'_singleton
  rw [assoc, rhs, ←assoc, ←prod.map_id_comp] at h'_singleton
  have h₂' : (prod.map (𝟙 _) (prod.map (𝟙 _) (homMap f ≫ homToGraph A B))
      ≫ (prod.associator _ _ _).inv ≫ in_ (B ⨯ A))^
      = prod.map (𝟙 _) (homMap f ≫ homToGraph A B) ≫ v := by
    apply Power.unique
    rw [prod.map_id_comp, assoc, Power.comm]
  have h₃' := Power.comm _ ((prod.map (𝟙 B) (prod.map (𝟙 A) (homMap f ≫ homToGraph A B))
    ≫ (prod.associator B A (Power.pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)))
  rw [h₂', h'_singleton, ←h₁, Power.comm _ id_f'eq, ←assoc] at h₃'

  have hx := h₃'.symm.trans h₃
  have c₀ : prod.map (𝟙 B) (prod.map (𝟙 A) (exp' ≫ homToGraph A B)) ≫ (prod.associator _ _ _).inv
    = (prod.associator _ _ _).inv ≫ (prod.map (𝟙 _) (exp' ≫ homToGraph A B)) := by simp
  have c₁ : prod.map (𝟙 B) (prod.map (𝟙 A) (homMap f ≫ homToGraph A B))
      ≫ (prod.associator _ _ _).inv
      = (prod.associator _ _ _).inv ≫ (prod.map (𝟙 _) (homMap f ≫ homToGraph A B)) := by simp
  rw [c₀, c₁] at hx
  have hy := congrArg (fun k ↦ (prod.associator B A X).hom ≫ k) hx
  simp only at hy
  rw [←assoc, ←assoc, Iso.hom_inv_id, id_comp, ←assoc, ←assoc, Iso.hom_inv_id, id_comp] at hy
  have hz := congrArg (fun k ↦ transpose k) hy
  simp only at hz
  rw [transpose_right_inv, transpose_right_inv] at hz
  rw [cancel_mono] at hz
  assumption

variable {Y Z : C}

/-- The inverse to `Hom_map`, which sends a morphism `X ⟶ Hom Y Z`
to its "un-curried" version `Y ⨯ X ⟶ Z`.
-/
abbrev homMapInv (f : X ⟶ hom Y Z) : Y ⨯ X ⟶ Z := prod.map (𝟙 _) f ≫ eval _ _

/-- The equivalence between arrows `A ⨯ X ⟶ B` and arrows `X ⟶ Hom A B`. -/
def ExpAdjEquiv (A B X : C) : (A ⨯ X ⟶ B) ≃ (X ⟶ hom A B) where
  toFun := homMap
  invFun := homMapInv
  left_inv := fun f => hom_exponentiates f
  right_inv := by
    intro f
    apply Hom_Unique; rfl

/-- The map `Hom A X ⟶ Hom A Y` associated to a map `X ⟶ Y`.
This is how `ExpFunctor` acts on morphisms.
-/
def ExpHom {X Y : C} (A : C) (f : X ⟶ Y) : hom A X ⟶ hom A Y := homMap (eval A _ ≫ f)

/-- The covariant functor `C ⥤ C` associated to an object `A : C`
sending an object `B` to the "internal hom" `Hom A B`.
-/
def ExpFunctor (A : C) : C ⥤ C where
  obj := fun B ↦ hom A B
  map := fun {X Y} f ↦ ExpHom A f
  map_id := by
    intro X
    dsimp only [ExpHom]
    rw [comp_id]
    apply Hom_Unique
    rw [prod.map_id_id, id_comp]
  map_comp := by
    intro X Y Z f g
    change ExpHom A (f ≫ g) = ExpHom A f ≫ ExpHom A g
    dsimp only [ExpHom]
    apply Hom_Unique
    rw [prod.map_id_comp, assoc, hom_exponentiates, hom_exponentiates_assoc, assoc]


/-- A topos is a monoidal category with monoidal structure coming from binary products. -/
instance ToposMonoidal : MonoidalCategory C := monoidalOfHasFiniteProducts C

/-- The adjunction between the product and the "internal hom" `Hom A B`. -/
def TensorHomAdjunction (A : C) : MonoidalCategory.tensorLeft A ⊣ ExpFunctor A := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  · intro X B
    exact ExpAdjEquiv A B X

  · intro X X' Y f g
    change prod.map (𝟙 _) (f ≫ g) ≫ eval _ _ = (prod.map (𝟙 _) f) ≫ prod.map (𝟙 _) g ≫ eval _ _
    rw [prod.map_map_assoc, id_comp]

  · intro X Y Y' f g
    change homMap (f ≫ g) = homMap f ≫ ExpHom A g
    apply Hom_Unique
    dsimp only [ExpHom]
    rw [prod.map_id_comp, assoc, hom_exponentiates, hom_exponentiates_assoc]

end

section

variable [ChosenFiniteProducts C] [HasClassifier C] [HasPullbacks C] [HasPowerObjects C]


-- instance exponentiable (B : C) : Exponentiable B := Exponentiable.mk B (ExpFunctor B) (by
--  exact TensorHomAdjunction B)

/-
TODO: figure out what the right approach is to get the result below.

The main issue is this: `ChosenFiniteProducts C` is required for `CartesianClosed C`.
this is because often there is an explicit formulation for finite products.
However, this conflicts with the current definitions in files leading up to the definition
of a topos. For example, a subobject classifier is in terms of a map `⊤_ C ⟶ Ω`, not a map
`𝟙_ C ⟶ Ω`, and it Power.lean everything is in terms of the `HasBinaryProducts` product `⨯`
instead of the monoidal structure `⊗` product.
-/

def cartesianClosed : CartesianClosed C := sorry

end
end CategoryTheory.Topos
