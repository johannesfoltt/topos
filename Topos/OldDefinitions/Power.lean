/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen
-/
--import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Topos.OldDefinitions.Classifier

/-!
# Power Objects

Defines power objects for a category C with a subobject classifier and pullbacks.

## Main definitions

Let `C` be a category with a terminal object, a subobject classifier, and pullbacks.

* For an object `B : C`, `CategoryTheory.Power.PowerObject B` contains the data
  of a power object for `B`.

* `CategoryTheory.Power.HasPowerObjects C` says that every object in `C` has a power object.

* If `C` has all power objects, then there is a functor `powFunctor C : Cᵒᵖ ⥤ C` which
  sends an object `B : C` to its power object `pow B`, and sends a morphism `f : A ⟶ B` to the
  corresponding "inverse image" morphism `inverseImage f : pow B ⟶ pow A`.

## Main results

* `powFunctor C` is self adjoint, in the sense that its adjoint is the corresponding
  functor `powFunctorOp C : C ⥤ Cᵒᵖ`. This is exhibited as `powSelfAdj C`.

## Notation

* if `f : B ⨯ A ⟶ Ω C` is a morphism in a category with power objects, then
  `f^` denotes the corresponding morphism `A ⟶ pow B`.
* If `g : A ⟶ pow B` is a morphism in a category with power objects, then
  `g^` denotes the corresponding morphism `B ⨯ A ⟶ Ω C`.
* To "curry" maps in the other coordinate, put the caret `^` before the function argument
  instead of after.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MLM92]

-/


open CategoryTheory Category Limits HasClassifier MonoidalCategory

namespace CategoryTheory.Power

universe u v
variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasClassifier C]
variable [CartesianMonoidalCategory C]

variable (A B : C)

#synth MonoidalCategory C

#check A ⊗ B

/-- An object `PB` and a map `in_B : B ⨯ PB ⟶ Ω C` form a power object for `B : C`
if, for any map `f : B ⨯ A ⟶ Ω C`, there is a unique map `f' : A ⟶ PB` such that
the following diagram commutes:
```

        B ⨯ A ---f---> Ω C
          |             ^
          |            /
          |           /
    (𝟙 B) ⨯ f'       /
          |         /
          |       in_B
          |       /
          |      /
          |     /
          |    /
          v   /
        B ⨯ PB
```
-/
structure PowerObject (B : C) where
  /-- The power object -/
  pow : C
  /-- The membership predicate -/
  in_ : B ⨯ pow ⟶ Ω C
  /-- The transpose of a map -/
  transpose {A : C} (f : B ⨯ A ⟶ Ω C) : A ⟶ pow
  /-- the characterizing property of the transpose -/
  comm {A : C} (f : B ⨯ A ⟶ Ω C) : prod.map (𝟙 B) (transpose f) ≫ in_ = f
  /-- `transpose f` is the only map which satisfies the commutativity condition-/
  uniq {A : C} {f : B ⨯ A ⟶ Ω C} {hat' : A ⟶ pow} (hat'_comm : prod.map (𝟙 B) hat' ≫ in_ = f) : transpose f = hat'

variable (C)

/-- A category has power objects if each of its objects has a power object. -/
class HasPowerObjects : Prop where
  /-- Each `B : C` has a power object. -/
  has_power_object (B : C) : Nonempty (PowerObject B)

variable {C}

variable [HasPowerObjects C]

noncomputable section

/-- Notation for the power object of an object. -/
abbrev pow (B : C) : C := (HasPowerObjects.has_power_object B).some.pow

/-- Notation for the predicate "b ∈ S" as a map `B ⨯ pow B ⟶ Ω`. -/
abbrev in_ (B : C) : B ⨯ pow B ⟶ Ω C := (HasPowerObjects.has_power_object B).some.in_

/-- The map Hom(B⨯A,Ω) → Hom(A,P(B)).
This is currying the left argument.
-/
def transpose {B A} (f : B ⨯ A ⟶ Ω C) : A ⟶ pow B :=
  (HasPowerObjects.has_power_object B).some.transpose f

/-- Shorthand for currying the left argument. -/
notation f "^" => transpose f

/-- The characterizing property of `transpose`. -/
@[reassoc]
lemma comm (B) {A} (f : B ⨯ A ⟶ Ω C) : prod.map (𝟙 _) (f^) ≫ in_ B = f :=
  (HasPowerObjects.has_power_object B).some.comm f

/-- `transpose` is the only map which satisfies the commutativity condition. -/
lemma unique (B) {A} {f : B ⨯ A ⟶ Ω C} {hat' : A ⟶ pow B} (hat'_comm : prod.map (𝟙 _) hat' ≫ in_ B = f ) :
    f^ = hat' :=
  (HasPowerObjects.has_power_object B).some.uniq hat'_comm

/-- Un-currying on the left. -/
abbrev transposeInv {B A} (f : A ⟶ pow B) : B ⨯ A ⟶ Ω C :=
  (prod.map (𝟙 _) f) ≫ in_ B

/-- Shorthand for un-currying on the left. -/
notation f "^" => transposeInv f

/-- Equivalence between Hom(B⨯A,Ω) and Hom(A,P(B)). -/
def transposeEquiv (A B : C) : (B ⨯ A ⟶ Ω C) ≃ (A ⟶ pow B) where
  toFun := transpose
  invFun := transposeInv
  left_inv := fun f => comm _ _
  right_inv := by
    intro g
    apply unique
    rfl

/-- `transposeInv` is a left inverse of `transpose`. -/
@[reassoc (attr := simp)]
lemma transpose_left_inv {B A} (f : B ⨯ A ⟶ Ω C) : (f^)^ = f :=
  (transposeEquiv _ _).left_inv _

/-- `transposeInv` is a right inverse of `transpose`. -/
@[reassoc (attr := simp)]
lemma transpose_right_inv {B A : C} (f : A ⟶ pow B) : (f^)^ = f :=
  (transposeEquiv _ _).right_inv _

/-- The map Hom(B⨯A,Ω) → Hom(B,P(A)).
This is currying the right argument.
-/
def transposeSymm {B A} (f : B ⨯ A ⟶ Ω C) : B ⟶ pow A :=
  transpose ((prod.braiding A B).hom ≫ f)

/-- Shorthand for currying the right argument. -/
notation "^" f => transposeSymm f

/-- Un-currying on the right. -/
abbrev transposeSymmInv {B A} (f : B ⟶ pow A) : B ⨯ A ⟶ Ω C :=
  (prod.braiding A B).inv ≫ (transposeInv f)

/-- Shorthand for un-currying on the right. -/
notation "^" f => transposeSymmInv f

/-- Equivalence between Hom(B⨯A,Ω) and Hom(B,P(A)). -/
def transposeEquivSymm (A B : C) : (B ⨯ A ⟶ Ω C) ≃ (B ⟶ pow A) where
  toFun := transposeSymm
  invFun := transposeSymmInv
  left_inv := by
    intro f
    dsimp only [transposeSymm, transposeInv, transposeSymmInv]
    rw [comm, ←assoc, Iso.inv_hom_id, id_comp]
  right_inv := by
    intro g
    apply unique
    rw [←assoc, Iso.hom_inv_id, id_comp]

/-- `transposeSymmInv` is the left inverse
of `transposeSymm`.
-/
@[simp]
lemma transpose_symm_left_inv {B A} (f : B ⨯ A ⟶ Ω C) :
    (^(^f)) = f :=
  (transposeEquivSymm _ _).left_inv _

/-- `transposeSymmInv` is the right inverse
of `transposeSymm`.
-/
@[simp]
lemma transpose_symm_right_inv {B A : C} (f : B ⟶ pow A) :
    (^(^f)) = f :=
  (transposeEquivSymm _ _).right_inv _

/-- Equivalence between Hom(A,P(B)) and Hom(B, P(A)).
This is just the composition of `transposeEquiv` and `transposeEquivSymm`.
-/
def transpose_transpose_Equiv (A B : C) : (B ⟶ pow A) ≃ (A ⟶ pow B) :=
  -- (transposeEquivSymm A B).symm.trans (transposeEquiv A B)
  Equiv.trans (transposeEquivSymm A B).symm (transposeEquiv A B)

lemma transposeInvInj {A B : C} {f g : A ⟶ pow B} (eq: f^ = g^) : f = g := by {
  apply (transposeEquiv A B).symm.injective
  unfold transposeEquiv
  simp
  assumption
}

/--
  The power object functor's action on arrows.
  Sends `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ pow B ⟶ B ⨯ pow B ⟶ Ω`.
-/
def inverseImage {B A : C} (h : A ⟶ B) : pow B ⟶ pow A :=
  ((prod.map h (𝟙 (pow B))) ≫ (in_ B))^

/-- The following diagram commutes:
```
    A ⨯ Pow B ----(𝟙 A) ⨯ Pow_map h----> A ⨯ Pow A
      |                                    |
      |                                    |
    h ⨯ (𝟙 (Pow B))                      in_ A
      |                                    |
      v                                    v
    B ⨯ Pow B ----------in_ B-----------> Ω C
```
-/
lemma inverseImage_comm {A B : C} (h : A ⟶ B) :
    (prod.map (𝟙 A) (inverseImage h)) ≫ in_ A = (prod.map h (𝟙 (pow B))) ≫ (in_ B) := by
  dsimp [inverseImage]
  apply comm

/-- `powMap` sends the identity on an object `X` to the identity on `pow X`. -/
@[simp]
lemma inverseImage_id {B : C} : inverseImage (𝟙 B) = 𝟙 (pow B) := by
  apply unique; rfl


variable (C)

/--
  The power object functor.
  Sends objects `B` to their power objects `pow B`.
  Sends arrows `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ pow B ⟶ B ⨯ pow B ⟶ Ω`,
  which is the "preimage" morphism `pow B ⟶ pow A`.
-/
def powFunctor : Cᵒᵖ ⥤ C where
  obj := fun ⟨B⟩ ↦ pow B
  map := fun ⟨h⟩ ↦ inverseImage h
  map_id := by
    intro _
    apply unique
    rfl
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩
    apply unique
    dsimp [inverseImage]
    symm
    calc
      prod.map (g ≫ f)  (𝟙 (pow X)) ≫ in_ X
        = (prod.map g (𝟙 (pow X))) ≫ (prod.map f  (𝟙 (pow X))) ≫ in_ X  := by
        rw [←assoc, ←prod.map_comp_id]
      _ = (prod.map g (𝟙 (pow X))) ≫ (prod.map (𝟙 Y) (inverseImage f)) ≫ in_ Y := by
        rw [inverseImage_comm]
      _ = (prod.map (𝟙 Z) (inverseImage f)) ≫ (prod.map g (𝟙 (pow Y))) ≫ in_ Y := by
        repeat rw [prod.map_map_assoc, comp_id, id_comp]
      _ = (prod.map (𝟙 Z) (inverseImage f)) ≫ (prod.map (𝟙 Z) (inverseImage g)) ≫ in_ Z := by
        rw [inverseImage_comm]
      _ = prod.map (𝟙 Z) (inverseImage f ≫ inverseImage g ) ≫ in_ Z  := by
        rw [←assoc, prod.map_id_comp]

/-- The power object functor, treated as a functor `C ⥤ Cᵒᵖ`. -/
def powFunctorOp : C ⥤ Cᵒᵖ where
  obj := fun B ↦ ⟨pow B⟩
  map := fun h ↦ ⟨inverseImage h⟩
  map_id := by
    intro _
    apply congrArg Opposite.op
    apply (powFunctor C).map_id
  map_comp := by
    intros
    apply congrArg Opposite.op
    apply (powFunctor C).map_comp

/-- exhibiting that the pow functor is adjoint to itself on the right. -/
def powSelfAdj : powFunctorOp C ⊣ powFunctor C := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  -- homEquiv step
  · exact fun X ⟨Y⟩ => {
      toFun := fun ⟨f⟩ => (transpose_transpose_Equiv X Y).toFun f
      invFun := fun g => ⟨(transpose_transpose_Equiv X Y).invFun g⟩
      left_inv := fun ⟨f⟩ => by simp
      right_inv := fun g => by simp
    }

  -- homEquiv_naturality_left_symm step
  · intro X' X ⟨Y⟩ f g
    simp
    congr
    show (transpose_transpose_Equiv X' Y).symm (f ≫ g) =
      (transpose_transpose_Equiv X Y).symm g ≫ inverseImage f
    dsimp only [transpose_transpose_Equiv, transposeEquivSymm, transposeEquiv]
    simp
    dsimp only [transposeSymm, transposeInv, inverseImage]
    apply unique
    rw [prod.map_id_comp _ (transpose _), assoc _ _ (in_ X'), comm, ←assoc _ _ (in_ X),
      prod.map_map, id_comp, comp_id, ←comp_id f, ←id_comp (transpose _), ←prod.map_map,
      assoc, comm]
    have h : prod.map f (𝟙 Y) ≫ (prod.braiding X Y).hom = (prod.braiding _ _).hom ≫ prod.map (𝟙 _) f := by simp
    rw [←assoc (prod.map f (𝟙 _)), h]
    simp

  -- homEquiv_naturality_right step
  · intro X ⟨Y⟩ ⟨Y'⟩ ⟨f⟩ ⟨g⟩
    dsimp only [transpose_transpose_Equiv, transposeEquiv, transposeEquivSymm]
    simp only [prod.lift_map_assoc, comp_id, Equiv.toFun_as_coe, Equiv.trans_apply,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
      Equiv.symm_symm]
    show transpose ((prod.braiding X Y').inv ≫ prod.map (𝟙 X) (g ≫ f) ≫ in_ X) =
      transpose ((prod.braiding X Y).inv ≫ prod.map (𝟙 X) f ≫ in_ X) ≫ inverseImage g
    dsimp only [transposeInv, inverseImage]
    apply unique
    rw [prod.map_id_comp (transpose _), assoc, comm, ←assoc _ _ (in_ Y),
      prod.map_map, id_comp, comp_id, ←comp_id g]
    have h : prod.map g (𝟙 X) ≫ (prod.braiding X Y).inv = (prod.braiding _ _).inv ≫ prod.map (𝟙 _) g := by simp
    rw [←id_comp (transpose _), ←prod.map_map, assoc, comm, ←assoc (prod.map g _), h]
    simp only [prod.braiding_inv, prod.lift_map_assoc, comp_id, prod.lift_map, assoc]


end
end CategoryTheory.Power
