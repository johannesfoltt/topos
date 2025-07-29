import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Opposites
import Topos.NewDefinitions.NewClassifier

open CategoryTheory Category Limits MonoidalCategory CartesianMonoidalCategory ChosenTerminalObject Classifier

namespace CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [Classifier C]

class PowerObject (X : C) where
  /-- The power object -/
  {pow : C}
  /-- The membership predicate -/
  in_ : X ⊗ pow ⟶ Ω
  /-- The transpose of a map -/
  transpose {Y : C} (f : X ⊗ Y ⟶ Ω) : Y ⟶ pow
  /-- the characterizing property of the transpose -/
  comm {Y : C} (f : X ⊗ Y ⟶ Ω) : ((𝟙 X) ⊗ (transpose f)) ≫ in_ = f
  /-- `transpose f` is the only map which satisfies the commutativity condition-/
  uniq {Y : C} {f : X ⊗ Y ⟶ Ω} {hat' : Y ⟶ pow} (hat'_comm : ((𝟙 X) ⊗ hat') ≫ in_ = f) : transpose f = hat'

variable (C)

class ChosenPowerObjects where
  [powerObject (X : C) : PowerObject X]

namespace PowerObject

instance : BraidedCategory C := BraidedCategory.ofCartesianMonoidalCategory

variable {C} {X : C} [PowerObject X] {Y : C}

abbrev transposeInv (f : Y ⟶ pow X) : X ⊗ Y ⟶ Ω :=
  ((𝟙 _) ⊗ f) ≫ in_

notation f "^" => transpose f
notation f "^" => transposeInv f

/-- Equivalence between Hom(B⨯A,Ω) and Hom(A,P(B)). -/
def transposeEquiv (X Y : C) [PowerObject X] : (X ⊗ Y ⟶ Ω) ≃ (Y ⟶ pow X) where
  toFun := transpose
  invFun := transposeInv
  left_inv := fun f ↦ comm f
  right_inv := by exact fun f ↦ uniq rfl

/-- `transposeInv` is a left inverse of `transpose`. -/
@[reassoc (attr := simp)]
lemma transpose_left_inv (f : X ⊗ Y ⟶ Ω) : (f^)^ = f := (transposeEquiv _ _).left_inv _

/-- `transposeInv` is a right inverse of `transpose`. -/
@[reassoc (attr := simp)]
lemma transpose_right_inv (f : Y ⟶ pow X) : (f^)^ = f := (transposeEquiv _ _).right_inv _

/-- The map Hom(B⨯A,Ω) → Hom(B,P(A)).
This is currying the right argument.
-/
def transposeSymm (f : Y ⊗ X ⟶ Ω) : Y ⟶ pow X :=
  ((β_ X Y).hom ≫ f)^

/-- Un-currying on the right. -/
abbrev transposeSymmInv (f : Y ⟶ pow X) : Y ⊗ X ⟶ Ω :=
  (β_ X Y).inv ≫ f^

/-- Equivalence between Hom(B⨯A,Ω) and Hom(B,P(A)). -/
def transposeEquivSymm (X Y : C) [PowerObject X] : (Y ⊗ X ⟶ Ω) ≃ (Y ⟶ pow X) where
  toFun := transposeSymm
  invFun := transposeSymmInv
  left_inv := by
    intro f
    dsimp only [transposeSymm, transposeInv, transposeSymmInv]
    rw [comm, ←assoc, Iso.inv_hom_id, id_comp]
  right_inv := by {
    intro f
    unfold transposeSymm
    unfold transposeSymmInv
    simp
  }

/-- `transposeSymmInv` is the left inverse
of `transposeSymm`.
-/
@[simp]
lemma transpose_symm_left_inv (f : Y ⊗ X ⟶ Ω) :
    transposeSymmInv (transposeSymm f) = f :=
  (transposeEquivSymm  _ _).left_inv _

/-- `transposeSymmInv` is the right inverse
of `transposeSymm`.
-/
@[simp]
lemma transpose_symm_right_inv (f : Y ⟶ pow X) :
    transposeSymm (transposeSymmInv f) = f :=
  (transposeEquivSymm _ _).right_inv _

/-- Equivalence between Hom(A,P(B)) and Hom(B, P(A)).
This is just the composition of `transposeEquiv` and `transposeEquivSymm`.
-/
def transpose_transpose_Equiv (X Y : C) [PowerObject X] [PowerObject Y] : (Y ⟶ pow X) ≃ (X ⟶ pow Y) :=
  Equiv.trans (transposeEquivSymm X Y).symm (transposeEquiv Y X)

end PowerObject

namespace ChosenPowerObjects

open PowerObject

variable {C} [ChosenPowerObjects C]

instance powerObject' (X : C) : PowerObject X := powerObject X
/--
  The power object functor's action on arrows.
  Sends `h : X ⟶ Y` to the P-transpose of the map `h⨯1 ≫ ∈_Y : X × pow Y ⟶ Y × pow Y ⟶ Ω`.
-/
def inverseImage {X Y : C} (h : X ⟶ Y) : pow Y ⟶ pow X:=
  ((h ⊗ (𝟙 (pow Y))) ≫ in_)^

/-- The following diagram commutes:
```
    X ⨯ Pow Y ---(𝟙 X) ⨯ inverseImage h---> X ⨯ Pow X
      |                                      |
      |                                      |
    h ⨯ (𝟙 (Pow Y))                        in_ X
      |                                      |
      v                                      v
    Y ⨯ Pow Y ----------in_ Y-------------> Ω C
```
-/
lemma inverseImage_comm {X Y : C} (h : X ⟶ Y) : ((𝟙 X) ⊗ (inverseImage h)) ≫ in_ = (h ⊗ (𝟙 (pow Y))) ≫ in_ := by {
  unfold inverseImage
  exact transpose_left_inv ((h ⊗ 𝟙 (pow Y)) ≫ in_)
}

/-- `powMap` sends the identity on an object `X` to the identity on `pow X`. -/
@[simp]
lemma inverseImage_id {X : C} : inverseImage (𝟙 X) = 𝟙 (pow X) := by {
  unfold inverseImage
  apply PowerObject.uniq
  simp
}

variable (C)

/--
  The power object functor.
  Sends objects `B` to their power objects `pow B`.
  Sends arrows `h : A ⟶ B` to the P-transpose of the map `h⨯1 ≫ ∈_B : A ⨯ pow B ⟶ B ⨯ pow B ⟶ Ω`,
  which is the "preimage" morphism `pow B ⟶ pow A`.
-/

def powFunctor : Cᵒᵖ ⥤ C where
  obj := fun ⟨X⟩ ↦ pow X
  map := fun ⟨h⟩ ↦ inverseImage h
  map_id := by {
    intro X
    apply PowerObject.uniq
    rfl
  }
  map_comp := by
    intro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨f⟩ ⟨g⟩
    apply PowerObject.uniq
    unfold inverseImage
    symm
    calc
      ((g ≫ f) ⊗ (𝟙 (pow X))) ≫ in_
        = (g ⊗ (𝟙 (pow X))) ≫ (f ⊗ (𝟙 (pow X))) ≫ in_  :=
          comp_tensor_id_assoc g f in_
      _ = (g ⊗ (𝟙 (pow X))) ≫ ((𝟙 Y) ⊗ (inverseImage f)) ≫ in_ := by rw [inverseImage_comm]
      _ = ((𝟙 Z) ⊗ (inverseImage f)) ≫ (g ⊗ (𝟙 (pow Y))) ≫ in_ := by rw [tensor_id_comp_id_tensor_assoc, id_tensor_comp_tensor_id_assoc]
      _ = ((𝟙 Z) ⊗ (inverseImage f)) ≫ ((𝟙 Z) ⊗ (inverseImage g)) ≫ in_ := by rw [inverseImage_comm]
      _ = ((𝟙 Z) ⊗ (inverseImage f ≫ inverseImage g)) ≫ in_  := by rw [id_tensor_comp_assoc]

/-- The power object functor, treated as a functor `C ⥤ Cᵒᵖ`. -/
def powFunctorOp : C ⥤ Cᵒᵖ where
  obj := fun X ↦ ⟨pow X⟩
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
      toFun := fun ⟨f⟩ => (transpose_transpose_Equiv _ _).toFun f
      invFun := fun g => ⟨(transpose_transpose_Equiv _ _).invFun g⟩
      left_inv := fun ⟨f⟩ => by simp
      right_inv := fun g => by simp
    }

  -- homEquiv_naturality_left_symm step
  · intro X' X ⟨Y⟩ f g
    simp
    congr
    show (transpose_transpose_Equiv X' Y).symm (f ≫ g) =
      (transpose_transpose_Equiv X Y).symm g ≫ inverseImage f
    dsimp only [PowerObject.transpose_transpose_Equiv, PowerObject.transposeEquivSymm, PowerObject.transposeEquiv]
    simp
    dsimp only [PowerObject.transposeSymm, PowerObject.transposeInv, inverseImage]
    apply PowerObject.uniq
    rw [id_tensor_comp, assoc, PowerObject.comm, ← assoc, ← tensor_comp, id_comp, comp_id, ←comp_id f, ←id_comp (transpose _), tensor_comp, assoc, PowerObject.comm]
    simp

  -- homEquiv_naturality_right step
  · intro X ⟨Y⟩ ⟨Y'⟩ ⟨f⟩ ⟨g⟩
    dsimp only [PowerObject.transpose_transpose_Equiv, PowerObject.transposeEquiv, PowerObject.transposeEquivSymm]
    simp only [prod.lift_map_assoc, comp_id, Equiv.toFun_as_coe, Equiv.trans_apply,
      Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Equiv.invFun_as_coe, Equiv.symm_trans_apply,
      Equiv.symm_symm]
    show transpose ((β_ X Y').inv ≫ ((𝟙 X) ⊗ (g ≫ f)) ≫ in_) = transpose ((β_ X Y).inv ≫ ((𝟙 X) ⊗ f) ≫ in_) ≫ inverseImage g
    dsimp only [PowerObject.transposeInv, inverseImage]
    apply PowerObject.uniq
    rw [id_tensor_comp_assoc, PowerObject.comm, ← assoc, ← tensor_comp, id_comp, comp_id, ← comp_id g, ← id_comp (transpose _), tensor_comp]
    show ((g ⊗ 𝟙 X) ≫ ((𝟙 Y) ⊗ transpose ((β_ X Y).inv ≫ (𝟙 X ⊗ f) ≫ in_))) ≫ in_ = (β_ X Y').inv ≫ (𝟙 X ⊗ (g ≫ (𝟙 Y)) ≫ f) ≫ in_
    slice_lhs 2 4 => rw [PowerObject.comm]
    aesop_cat


variable {C}

/-- The "singleton" map `X ⟶ Pow X`.
In Set, this map sends `x ∈ X` to the
singleton set containing just `x`.
-/
def singleton (X : C) : X ⟶ pow X := transpose (Classifier.Predicate.eq X)


/-- `singleton X : X ⟶ Pow X` is a monomorphism. -/
instance singletonMono (X : C) : Mono (singleton X) where
  right_cancellation := by {
    intro Z b b' h
    rw [singleton] at h
    have h₁ : ((𝟙 _) ⊗ (b ≫ (transpose (Classifier.Predicate.eq X)))) ≫ in_
    = ((𝟙 _) ⊗ (b' ≫ (transpose (Classifier.Predicate.eq X)))) ≫ in_ := congrFun (congrArg CategoryStruct.comp (congrArg (tensorHom (𝟙 X)) h)) in_
    rw [id_tensor_comp_assoc, PowerObject.comm, id_tensor_comp_assoc, PowerObject.comm] at h₁
    have comm : (b ≫ from_ _) ≫ t = lift b (𝟙 _) ≫ ((𝟙 _) ⊗ b) ≫ Classifier.Predicate.eq _ := by {
      rw [comp_from, ←assoc, lift_map, comp_id, id_comp, Classifier.lift_eq, Classifier.Predicate.true_]
    }
    rw [comp_from, h₁, ←assoc, lift_map, id_comp, comp_id] at comm
    exact Classifier.eq_of_lift_eq (id (Eq.symm comm))
  }


/-- The predicate on `Pow X` which picks out the subobject of "singletons".
-/
def Predicate.isSingleton (X : C) : pow X ⟶ Ω := char (singleton X)


/-- The name ⌈φ⌉ : ⊤_ C ⟶ Pow B of a predicate `φ : X ⟶ Ω C`.
This is the global element of `Pow X` associated to a predicate
on `X`.
-/
def name {X : C} (φ : X ⟶ Ω) : 𝟙_ C ⟶ (pow X) := transpose ((fst X (𝟙_ C)) ≫ φ)

notation "⌜" φ "⌝" => name φ

/-- The inverse of `Name`, sending a global element of `Pow B`
to the corresponding predicate on `B`.
-/
def Predicate.fromName {X : C} (φ' : (𝟙_ C) ⟶ pow X) : X ⟶ Ω :=
  (lift (𝟙 X) (toUnit X)) ≫ transposeInv φ'


/-- The condition from the definition of `Name`
as the `P_transpose` of a morphism.
-/

lemma Predicate.NameDef {X : C} (φ : X ⟶ Ω) : ((𝟙 _) ⊗ ⌜φ⌝) ≫ (in_) = (fst X (𝟙_ C)) ≫ φ :=
  PowerObject.comm _


/-- The equivalence between morphisms `X ⟶ Ω C` and morphisms `⊤_ C ⟶ pow X`,
which comes from the more general equivalence between morphisms `Y ⨯ X ⟶ Ω C`
and morphisms `X ⟶ pow Y`.
-/
def NameEquiv (X : C) : (X ⟶ Ω) ≃ (𝟙_ C ⟶ pow X) where
  toFun := name
  invFun := Predicate.fromName
  left_inv := by
    intro φ
    dsimp [name, Predicate.fromName]
    rw [PowerObject.transpose_left_inv, ←assoc, lift_fst, id_comp]
  right_inv := by
    intro φ'
    dsimp only [name, Predicate.fromName]
    have h := (ρ_ X).hom_inv_id
    simp_rw [rightUnitor_hom, rightUnitor_inv] at h
    rw [←assoc, h, id_comp, transpose_right_inv]
