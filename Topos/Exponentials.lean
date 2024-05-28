import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Closed.Cartesian
import Topos.Basic


namespace CategoryTheory

open Category Limits Classifier Power Topos

universe u v

variable {C : Type u} [Category.{v} C] [Topos C]

/-!
# Exponential Objects

Proves that a topos has exponential objects (internal homs).
Consequently, every topos is Cartesian closed.
-/


namespace Topos

noncomputable section

/-- The exponential object B^A. -/
def Hom (A B : C) : C :=
  pullback
    (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B))
    (Name (Predicate.true_ A))

/-- The map which, in Set, sends a function (A → B) ∈ B^A to its graph as a subset of B ⨯ A. -/
def Hom_toGraph (A B : C) : Hom A B ⟶ Pow (B ⨯ A) := pullback.fst

instance Hom_toGraph_Mono {A B : C} : Mono (Hom_toGraph A B) := pullback.fst_of_mono

lemma ExpConeSnd_Terminal (A B : C) : pullback.snd = terminal.from (Hom A B) := Unique.eq_default _

lemma Hom_comm (A B : C) : Hom_toGraph A B ≫ (P_transpose (P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B))
  = terminal.from (Hom A B) ≫ Name (Predicate.true_ A) := by
    rw [←ExpConeSnd_Terminal]; exact pullback.condition

lemma evalDef_comm (A B : C) :
  (prod.map (𝟙 A) (Hom_toGraph A B) ≫ P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))) ≫ Predicate.isSingleton B
  = Predicate.true_ (A ⨯ Hom A B) := by
    let id_m : A ⨯ Hom A B ⟶ A ⨯ Pow (B ⨯ A) := prod.map (𝟙 _) (Hom_toGraph A B)
    let v := P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
    let σ_B := Predicate.isSingleton B
    let u := P_transpose (v ≫ Predicate.isSingleton B)
    let id_u := prod.map (𝟙 A) u
    have comm_middle : v ≫ σ_B = id_u ≫ (in_ A) := Pow_powerizes A (v ≫ σ_B)
    have comm_left : id_m ≫ id_u =  prod.map (𝟙 _) (terminal.from _) ≫ prod.map (𝟙 _) (Name (Predicate.true_ A)) := by
      rw [prod.map_map, prod.map_map]
      ext; simp
      rw [prod.map_snd, prod.map_snd, Hom_comm]
    have h_terminal : (prod.map (𝟙 A) (terminal.from (Hom A B)) ≫ prod.fst) ≫ terminal.from A = terminal.from _ :=
      Unique.eq_default _
    rw [assoc, comm_middle, ←assoc, comm_left, assoc, ←Predicate.NameDef]
    dsimp [Predicate.true_]
    rw [←assoc, ←assoc, h_terminal]

/-- The evaluation map eval : A ⨯ B^A ⟶ B. -/
def eval (A B : C) : A ⨯ (Hom A B) ⟶ B :=
  ClassifierCone_into (comm' := evalDef_comm A B)

lemma evalCondition (A B : C) : eval A B ≫ singleton B = prod.map (𝟙 _) (Hom_toGraph A B) ≫ P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A)) :=
  ClassifierCone_into_comm _ _ _

abbrev Exponentiates {A B X HomAB : C}  (e : A ⨯ HomAB ⟶ B) (f : A ⨯ X ⟶ B) (f_exp : X ⟶ HomAB) :=
  (prod.map (𝟙 _) f_exp) ≫ e = f

structure IsExponentialObject {A B HomAB : C} (e : A ⨯ HomAB ⟶ B) where
  exp : ∀ {X} (_ : A ⨯ X ⟶ B), X ⟶ HomAB
  exponentiates : ∀ {X} (f : A ⨯ X ⟶ B), Exponentiates e f (exp f)
  unique' : ∀ {X} {f : A ⨯ X ⟶ B} {exp' : X ⟶ HomAB}, Exponentiates e f exp' → exp f = exp'

class HasExponentialObject (A B : C) where
  HomAB : C
  e : A ⨯ HomAB ⟶ B
  is_exp : IsExponentialObject e

variable (C)

class HasExponentialObjects where
  has_exponential_object : ∀ (A B : C), HasExponentialObject A B

variable {C}

attribute [instance] HasExponentialObjects.has_exponential_object

-- ## TODO
-- exhibit the type class instance `HasExponentialObjects C` for a topos `C`.

variable {A B X : C} (f : A ⨯ X ⟶ B)

abbrev h_map : X ⟶ Pow (B ⨯ A) := P_transpose ((prod.associator _ _ _).hom ≫ prod.map (𝟙 _) f ≫ Predicate.eq _)

lemma HomMapSquareComm :
  h_map f ≫ P_transpose (P_transpose ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)) ≫ Predicate.isSingleton B) =
  terminal.from X ≫ Name (Predicate.true_ A) := by
    -- consider (1⨯f) ≫ (eq B) : B ⨯ A ⨯ X ⟶ Ω C.
    let id_f'eq : B ⨯ A ⨯ X ⟶ Ω C := prod.map (𝟙 _) f ≫ Predicate.eq _
    -- h is the map that, in `Set`, takes an element of X to the graph of the corresponding function.
    -- We want to lift this to a map X ⟶ Exp A B.
    -- The idea is to show that this map actually "maps elements of X to graphs of functions", which,
    -- in an arbitrary topos, is the same as checking commutativity of the obvious square.
    let h : X ⟶ Pow (B ⨯ A) := P_transpose ((prod.associator _ _ _).hom ≫ id_f'eq)
    -- h is by definition a P-transpose
    have h_condition : (prod.associator _ _ _).hom ≫ id_f'eq = (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
      rw [prod.map_id_id]
      apply Pow_powerizes
    -- moving the associator to the rhs of `h_condition`.
    have h_condition₂ : id_f'eq = (prod.associator _ _ _).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h) ≫ in_ _ := by
      rw [←h_condition, ←assoc, (prod.associator _ _ _).inv_hom_id, id_comp]
    -- this is the map v: A ⨯ P(B⨯A) ⟶ P(B) which was used in the definition of `Exp A B`.
    let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
    -- v is by definition a P-transpose
    have v_condition : (prod.associator _ _ _).inv ≫ in_ (B ⨯ A) = prod.map (𝟙 _) v ≫ in_ _ := Pow_powerizes _ _
    have lhs : P_transpose (prod.map (𝟙 A) h ≫ v ≫ Predicate.isSingleton B) = h ≫ P_transpose (v ≫ Predicate.isSingleton B) := by
      apply Pow_unique
      dsimp only [Powerizes]
      rw [prod.map_id_comp, assoc _ _ (in_ A), ←Pow_powerizes _ _, ←assoc]
    rw [←lhs]
    -- Claim that f ≫ {•}_B = (1⨯h) ≫ v.
    -- This is obtained by showing that both maps are the P-transpose of (1⨯f) ≫ (eq B).
    -- There might be a slightly faster way to do this.
    have transpose₁ : P_transpose id_f'eq = f ≫ singleton _ := by
      apply Pow_unique
      dsimp only [Powerizes, Topos.singleton]
      rw [prod.map_id_comp, assoc, ←(Pow_powerizes B (Predicate.eq B))]
    have shuffle_h_around : (prod.associator B A X).inv ≫ (prod.map (prod.map (𝟙 _) (𝟙 _)) h) = prod.map (𝟙 _) (prod.map (𝟙 _) h) ≫ (prod.associator _ _ _).inv := by simp
    have transpose₂ : P_transpose id_f'eq = (prod.map (𝟙 _) h) ≫ v := by
      apply Pow_unique
      dsimp only [Powerizes]
      rw [h_condition₂, ←assoc, shuffle_h_around, prod.map_id_comp, assoc _ _ (in_ B), ←v_condition, assoc]
    have eqn₁ : f ≫ singleton _ = (prod.map (𝟙 _) h) ≫ v := transpose₁.symm.trans transpose₂
    -- now compose by the `isSingleton B` predicate.
    have eqn₂ : f ≫ singleton _ ≫ Predicate.isSingleton _ = (prod.map (𝟙 _) h) ≫ v ≫ Predicate.isSingleton _ := by
      rw [←assoc, ←assoc, eqn₁]
    rw [←eqn₂]

    -- from here, the argument is mostly definition unpacking.
    apply Pow_unique
    dsimp only [Name, Predicate.true_, Powerizes, Predicate.isSingleton]
    have f_terminal : f ≫ terminal.from B = terminal.from _ := Unique.eq_default _
    have rightUnitor_terminal : (prod.rightUnitor A).hom ≫ terminal.from A = terminal.from _ := Unique.eq_default _
    have A_X_terminal : prod.map (𝟙 A) (terminal.from X) ≫ terminal.from (A ⨯ ⊤_ C) = terminal.from _ := Unique.eq_default _
    have obv : terminal.from (A ⨯ ⊤_ C) ≫ t C = prod.map (𝟙 A) (P_transpose (terminal.from (A ⨯ ⊤_ C) ≫ t C)) ≫ in_ A := Pow_powerizes _ _
    rw [(Classifies (singleton _)).comm, ←assoc, f_terminal, ←assoc, rightUnitor_terminal, prod.map_id_comp, assoc, ←obv, ←assoc, A_X_terminal]

def Hom_map : X ⟶ Hom A B :=
  pullback.lift (h_map f) (terminal.from X) (HomMapSquareComm f)

@[simp]
lemma Hom_mapCondition : Hom_map f ≫ (Hom_toGraph A B) = h_map f :=
  pullback.lift_fst _ _ _

theorem Hom_Exponentiates : Exponentiates (eval A B) f (Hom_map f) := by
  dsimp only [Exponentiates]
  rw [←cancel_mono (singleton B), assoc, evalCondition, ←assoc, prod.map_map, id_comp, Hom_mapCondition]
  have h : toPredicate (f ≫ singleton B) = toPredicate (prod.map (𝟙 A) (h_map f) ≫ P_transpose ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))) := by
    rw [toPredicate, toPredicate, prod.map_id_comp, assoc, singleton, ←Pow_powerizes, prod.map_id_comp, assoc, ←Pow_powerizes, ←assoc]
    have h' : (prod.map (𝟙 B) (prod.map (𝟙 A) (h_map f)) ≫ (prod.associator B A (Power.Pow (B ⨯ A))).inv)
      = (prod.associator B A X).inv ≫ (prod.map (𝟙 _) (h_map f)) := by simp
    rw [h', assoc, h_map, ←Pow_powerizes, ←assoc, Iso.inv_hom_id, id_comp]
  have h₀ := congrArg (fun k => P_transpose k) h
  have t₁ : P_transpose (toPredicate (f ≫ singleton B)) = f ≫ singleton B := (transposeEquiv _ _).right_inv _
  have t₂ : P_transpose (toPredicate ((prod.map (𝟙 A) (h_map f) ≫ P_transpose ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)))))
    = (prod.map (𝟙 A) (h_map f) ≫ P_transpose ((prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A))) :=
      (transposeEquiv _ _).right_inv _
  simp only [t₁, t₂] at h₀
  exact h₀.symm

theorem Hom_Unique : ∀ {exp' : X ⟶ Hom A B}, Exponentiates (eval A B) f exp' → Hom_map f = exp' := by
  intro exp' h
  dsimp only [Exponentiates] at h
  have h_singleton := congrArg (fun k ↦ k ≫ singleton B) h
  simp only at h_singleton
  let v : A ⨯ Pow (B ⨯ A) ⟶ Pow B := P_transpose ((prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
  -- want to rewrite (1⨯g) ≫ eval A B ≫ singleton B = (1⨯(g≫m)) ≫ v
  have rhs : eval A B ≫ singleton B = prod.map (𝟙 _) (Hom_toGraph A B) ≫ v := by
    apply PullbackCone.IsLimit.lift_fst
  rw [assoc, rhs, ←assoc, ←prod.map_id_comp] at h_singleton
  let id_f'eq : B ⨯ A ⨯ X ⟶ Ω C := prod.map (𝟙 _) f ≫ Predicate.eq _
  have h₁ : P_transpose (id_f'eq) = f ≫ singleton B := by
    apply Pow_unique
    dsimp only [Powerizes, id_f'eq, singleton]
    rw [prod.map_id_comp, assoc, ←(Pow_powerizes _ (Predicate.eq B))]
  have h₂ : P_transpose (prod.map (𝟙 _) (prod.map (𝟙 _) (exp' ≫ Hom_toGraph A B)) ≫ (prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
    = prod.map (𝟙 _) (exp' ≫ Hom_toGraph A B) ≫ v := by
      apply Pow_unique
      dsimp only [Powerizes]
      nth_rewrite 2 [prod.map_id_comp]
      rw [assoc, ←(Pow_powerizes _ _)]
  have h₃ := Pow_powerizes _ ((prod.map (𝟙 B) (prod.map (𝟙 A) (exp' ≫ Hom_toGraph A B)) ≫ (prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)))
  dsimp only [Powerizes] at h₃
  rw [h₂, h_singleton, ←h₁, ←(Pow_powerizes _ id_f'eq), ←assoc] at h₃
  have h' := Hom_Exponentiates f
  dsimp only [Exponentiates] at h'
  have h'_singleton := congrArg (fun k ↦ k ≫ singleton B) h'
  simp only at h'_singleton
  rw [assoc, rhs, ←assoc, ←prod.map_id_comp] at h'_singleton
  have h₂' : P_transpose (prod.map (𝟙 _) (prod.map (𝟙 _) (Hom_map f ≫ Hom_toGraph A B)) ≫ (prod.associator _ _ _).inv ≫ in_ (B ⨯ A))
    = prod.map (𝟙 _) (Hom_map f ≫ Hom_toGraph A B) ≫ v := by
      apply Pow_unique
      dsimp only [Powerizes]
      nth_rewrite 2 [prod.map_id_comp]
      rw [assoc, ←(Pow_powerizes _ _)]
  have h₃' := Pow_powerizes _ ((prod.map (𝟙 B) (prod.map (𝟙 A) (Hom_map f ≫ Hom_toGraph A B)) ≫ (prod.associator B A (Power.Pow (B ⨯ A))).inv ≫ in_ (B ⨯ A)))
  dsimp only [Powerizes] at h₃'
  rw [h₂', h'_singleton, ←h₁, ←(Pow_powerizes _ id_f'eq), ←assoc] at h₃'
  have hx := h₃.trans h₃'.symm
  have c₀ : prod.map (𝟙 B) (prod.map (𝟙 A) (exp' ≫ Hom_toGraph A B)) ≫ (prod.associator _ _ _).inv
    = (prod.associator _ _ _).inv ≫ (prod.map (𝟙 _) (exp' ≫ Hom_toGraph A B)) := by simp
  have c₁ : prod.map (𝟙 B) (prod.map (𝟙 A) (Hom_map f ≫ Hom_toGraph A B)) ≫ (prod.associator _ _ _).inv
    = (prod.associator _ _ _).inv ≫ (prod.map (𝟙 _) (Hom_map f ≫ Hom_toGraph A B)) := by simp
  rw [c₀, c₁] at hx
  have hy := congrArg (fun k ↦ (prod.associator B A X).hom ≫ k) hx
  simp only at hy
  rw [←assoc, ←assoc, Iso.hom_inv_id, id_comp, ←assoc, ←assoc, Iso.hom_inv_id, id_comp] at hy
  have hz := congrArg (fun k ↦ P_transpose k) hy
  simp only at hz
  rw [transposeEquiv.proof_3, transposeEquiv.proof_3] at hz
  rw [cancel_mono] at hz
  exact hz.symm


instance Hom_isExponential : IsExponentialObject (eval A B) where
  exp := Hom_map
  exponentiates := Hom_Exponentiates
  unique' := by apply Hom_Unique

instance ExponentialObject_inst (A B : C) : HasExponentialObject A B where
  HomAB := Hom A B
  e := eval A B
  is_exp := Hom_isExponential

instance ToposHasExponentials : HasExponentialObjects C where
  has_exponential_object := ExponentialObject_inst

variable (X Y Z W)

def InternalComposition : (Hom X Y) ⨯ (Hom Y Z) ⟶ Hom X Z :=
  Hom_map ((prod.associator X (Hom X Y) (Hom Y Z)).inv ≫ (prod.map (eval X Y) (𝟙 _)) ≫ eval Y Z)

variable {X Y Z W}

def FnName (f : X ⟶ Y) : ⊤_ C ⟶ Hom X Y :=
  Hom_map (prod.fst ≫ f)

abbrev Hom_map_inv (f : X ⟶ Hom Y Z) := prod.map (𝟙 _) f ≫ eval _ _

def ExpAdjEquiv (A B X : C) : (A ⨯ X ⟶ B) ≃ (X ⟶ Hom A B) where
  toFun := Hom_map
  invFun := Hom_map_inv
  left_inv := fun f => Hom_Exponentiates f
  right_inv := by
    intro g
    apply Hom_Unique
    rw [Exponentiates]

variable (X Y)


def ExpHom {X Y : C} (A : C) (f : X ⟶ Y) : Hom A X ⟶ Hom A Y := Hom_map (eval A _ ≫ f)


def ExpFunctor (A : C) : C ⥤ C where
  obj := fun B ↦ Hom A B
  map := fun {X Y} f ↦ ExpHom A f
  map_id := by
    intro X
    dsimp only [ExpHom]
    rw [comp_id]
    apply Hom_Unique
    dsimp only [Exponentiates]
    rw [prod.map_id_id, id_comp]
  map_comp := by
    intro X Y Z f g
    change ExpHom A (f ≫ g) = ExpHom A f ≫ ExpHom A g
    dsimp only [ExpHom]
    apply Hom_Unique
    dsimp only [Exponentiates]
    rw [prod.map_id_comp, assoc, Hom_Exponentiates, ←assoc, Hom_Exponentiates, assoc]

instance ToposMonoidal : MonoidalCategory C := monoidalOfHasFiniteProducts C

def TensorHomAdjunction (A : C) : MonoidalCategory.tensorLeft A ⊣ ExpFunctor A := by
  apply Adjunction.mkOfHomEquiv
  fapply Adjunction.CoreHomEquiv.mk

  intro X B
  exact ExpAdjEquiv A B X

  intro X X' Y f g
  change prod.map (𝟙 _) (f ≫ g) ≫ eval _ _ = (prod.map (𝟙 _) f) ≫ prod.map (𝟙 _) g ≫ eval _ _
  rw [←assoc, prod.map_map, id_comp]

  intro X Y Y' f g
  change Hom_map (f ≫ g) = Hom_map f ≫ ExpHom A g
  apply Hom_Unique
  dsimp only [Exponentiates, ExpHom]
  rw [prod.map_id_comp, assoc, Hom_Exponentiates, ←assoc, Hom_Exponentiates]

instance CartesianClosed : CartesianClosed C where
  closed := by
    intro B
    use ExpFunctor B
    exact TensorHomAdjunction B


end
end Topos
end CategoryTheory
