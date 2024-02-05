
{-# OPTIONS --allow-unsolved-metas #-}

module GrCore where

open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Maybe
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)

open import Semiring

open Semiring.Semiring {{...}} public

-- # Types of GrCore

data Type {{R : Semiring}} : Set where
  FunTy : (A : Type) -> (r : grade) -> (B : Type) -> Type -- A r -> B
  Unit  : Type
  Box   : (r : grade) -> Type -> Type
  --------------------------------------------------
  -- Prod  : Type -> Type -> Type
  -- Sum   : Type -> Type -> Type
  BoolTy : Type

-- # Contexts for GrCore

data Assumption {{R : Semiring}} : Set where
--  Lin : (A : Type)                    -> Assumption A
  Grad : (A : Type) -> (r : grade) -> Assumption

data Context {{R : Semiring}} : ℕ -> Set where
  Empty   : Context 0
  Ext     : {n : ℕ} -> Context n -> Assumption -> Context (1 + n)

-- # Some properties of contexts

injGradTy : {{R : Semiring}} {A A' : Type} {r r' : grade} -> Grad A r ≡ Grad A' r' -> A ≡ A'
injGradTy refl = refl

injGradR : {{R : Semiring}} {A A' : Type} {r r' : grade} -> Grad A r ≡ Grad A' r' -> r ≡ r'
injGradR refl = refl

injExt1 : {{R : Semiring}} {s : ℕ} {Γ Γ' : Context s} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> Γ ≡ Γ'
injExt1 refl = refl

injExt2 : {{R : Semiring}} {s : ℕ} {Γ Γ' : Context s} {A A' : Assumption} -> Ext Γ A ≡ Ext Γ' A' -> A ≡ A'
injExt2 refl = refl

-- # Context operations

-- Disjoint context concatentation
_,,_ : {{R : Semiring}} {s t : ℕ} -> Context s -> Context t -> Context (s + t)
Empty      ,, G2 = G2
(Ext G1 a) ,, G2 = Ext (G1 ,, G2) a
--G1 ,, Empty = G1
--G1 ,, (Ext G2 a) = Ext (G1 ,, G2) a

-- Context scalar multiplication
_·_ : {{R : Semiring}} {s : ℕ} -> grade -> Context s -> Context s
r · Empty = Empty
r · Ext g (Grad A s) = Ext (r · g) (Grad A (r *R s))

-- Context addition
_++_ : {{R : Semiring}} {s : ℕ} -> Context s -> Context s -> Context s
Empty ++ Empty = Empty
(Ext G (Grad A r)) ++ (Ext G' (Grad B s)) = Ext (G ++ G') (Grad A (r +R s))

-- Context scalar multiplication distributes with context contactentation
multConcatDistr : {{R : Semiring}} {s t : ℕ} {r : grade} {Γ1 : Context s} {Γ2 : Context t} ->
                  r · (Γ1 ,, Γ2) ≡ ((r · Γ1) ,, (r · Γ2))
multConcatDistr ⦃ R ⦄ {.0} {t} {r} {Empty} {Γ2} = refl
multConcatDistr ⦃ R ⦄ {suc n} {t} {r} {Ext Γ1 (Grad A s)} {Γ2} 
  rewrite multConcatDistr {n} {t} {r} {Γ1} {Γ2} = refl

postulate -- TODO: Vilem prove these
  -- keeps things simple with the above definition
  sameTypes : {{R : Semiring}} {s : ℕ} {Γ1 Γ2 : Context s} {Γ : Context (suc s)} {A A' : Type} {r1 r2 : grade}
            -> (Ext Γ1 (Grad A r1)) ++ (Ext Γ2 (Grad A' r2)) ≡ Γ -> A ≡ A'

  absorptionContext : {{R : Semiring}} {s : ℕ} {Γ Γ' : Context s} -> (0R · Γ) ++ Γ' ≡ Γ'
  leftUnitContext : {{R : Semiring}} {s : ℕ} {Γ : Context s} -> 1R · Γ ≡ Γ

Γlength : {{R : Semiring}} {s : ℕ} -> Context s -> ℕ
Γlength Empty = 0
Γlength (Ext g a) = 1 + Γlength g

-- # Term calculus

data Term : Set where
  Var : ℕ -> Term
  App : Term -> Term -> Term
  Abs : ℕ -> Term -> Term
  unit : Term
  Promote : Term -> Term
  -- handling bools (TODO: generalise to sums)
  vtrue : Term
  vfalse : Term
  If : Term -> Term -> Term -> Term


syntacticSubst : Term -> ℕ -> Term -> Term
syntacticSubst t x (Var y) with x ≟ y
... | yes p = t
... | no ¬p = Var y
syntacticSubst t x (App t1 t2) = App (syntacticSubst t x t1) (syntacticSubst t x t2)
syntacticSubst t x (Abs y t1) with x ≟ y
... | yes p = Abs y t1
... | no ¬p = Abs y (syntacticSubst t x t1)
syntacticSubst t x (Promote t1) = Promote (syntacticSubst t x t1)
syntacticSubst t x unit = unit
syntacticSubst t x vtrue = vtrue
syntacticSubst t x vfalse = vfalse
syntacticSubst t x (If t1 t2 t3) = If (syntacticSubst t x t1) (syntacticSubst t x t2) (syntacticSubst t x t3)

discrimBool : vtrue ≡ vfalse -> ⊥
discrimBool ()

absInj2 : {x y : ℕ} {e1 e2 : Term} -> Abs x e1 ≡ Abs y e2 -> e1 ≡ e2
absInj2 refl = refl

absInj1 : {x y : ℕ} {e1 e2 : Term} -> Abs x e1 ≡ Abs y e2 -> x ≡ y
absInj1 refl = refl


-------------------------------------------------
-- # Typing

data _⊢_∶_ {{R : Semiring}} : {s : ℕ} -> Context s -> Term -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : {s1 s2 : ℕ}
        { A : Type }
        { Γ : Context ((1 + s1) + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        (pos : Γ ≡ ((Ext (0R · Γ1) (Grad A 1R)) ,, (0R · Γ2)))
    ->  ---------------------
        Γ ⊢ Var (Γlength Γ1) ∶ A


  app : {s : ℕ}
        { Γ Γ1 Γ2 : Context s }
        { r : grade }
        { A B : Type}
        { t1 t2 : Term }

     ->   Γ1 ⊢ t1 ∶ FunTy A r B
     ->   Γ2 ⊢ t2 ∶ A
     ->   { Γ ≡ (Γ1 ++ (r · Γ2))}
     -> -----------------------------
          Γ ⊢ App t1 t2 ∶ B


  abs : {s1 s2 : ℕ}
        { Γ : Context ((1 + s1) + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        { Γ' : Context (s1 + s2) }
        { r : grade }
        { A B : Type }
        { t : Term }

      -> (pos : Γ ≡ (Ext Γ1 (Grad A r)) ,, Γ2)
      -> Γ ⊢ t ∶ B
      -> { Γ' ≡ (Γ1 ,, Γ2)}
      -> --------------------------------------
         Γ' ⊢ Abs (Γlength Γ1 + 1) t ∶ FunTy A r B


  pr : {s : ℕ}
    -> { Γ Γ' : Context s }
    -> { r : grade }
    -> { A : Type }
    -> { t : Term }

    -> Γ ⊢ t ∶ A
    -> { Γ' ≡ r · Γ }
    --------------------------------
    -> Γ' ⊢ Promote t ∶ Box r A


  unitConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ) ⊢ unit ∶ Unit

  trueConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ) ⊢ vtrue ∶ BoolTy

  falseConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ) ⊢ vfalse ∶ BoolTy

  if : {s : ℕ}
       { Γ Γ1 Γ2 : Context s }
       { B : Type }
       { t1 t2 t3 : Term }
       { r : grade }
       { used : r ≤ 1R }

    -> Γ1 ⊢ t1 ∶ BoolTy
    -> Γ2 ⊢ t2 ∶ B
    -> Γ2 ⊢ t3 ∶ B
    -> { res : ((r · Γ1) ++ Γ2) ≡ Γ }
   ----------------------------------
    -> Γ ⊢ If t1 t2 t3 ∶ B


-- # Operational semantics

-- Value predicate
data Value : Term -> Set where
  unitValue    : Value unit
  varValue     : {n : ℕ} -> Value (Var n)
  absValue     : {n : ℕ} -> (t : Term) -> Value (Abs n t)
  promoteValue : (t : Term) -> Value (Promote t)
  trueValue    : Value vtrue
  falseValue   : Value vfalse

-- Substitution lemma
-- TODO: Vilem
substitution : {{R : Semiring}} {s1 s2 : ℕ} {Γ : Context ((1 + s1) + s2)} {Γ1 : Context s1} {Γ2 : Context (s1 + s2)} {Γ3 : Context s2} {r : grade} {A B : Type} {t1 t2 : Term}
      -> Γ ⊢ t1 ∶ B
      -> (pos : Γ ≡ ((Ext (0R · Γ1) (Grad A r)) ,, (0R · Γ3)))
      -> Γ2 ⊢ t2 ∶ A
      -> ((Γ1 ,, Γ3) ++ (r · Γ2)) ⊢ syntacticSubst t2 (Γlength Γ1) t1 ∶ B

--substitution {Γ1} {Γ2} {.1r} {A} {.A} {Var .0} {t2} (var (Here .Γ1 .A (Γ1' , allZeroesPrf))) substitee
--  rewrite allZeroesPrf | absorptionContext {Γ1'} {1r · Γ2} | leftUnitContext {Γ2} =
--    t2 , substitee

substitution {Γ} {Γ1} {Γ2} {Γ3} {r} {A} {B} {t1} {t2} substitutee pos e = {!subs!}


-- Progress lemma
redux : {{R : Semiring}} {s : ℕ} {Γ : Context s} {A : Type} {t : Term}
      -> Γ ⊢ t ∶ A
      -> (Value t) ⊎ ∃ (\t' -> Γ ⊢ t' ∶ A)

redux {{_}} {s} {Γ} {A} {Var _} (var pos) = inj₁ varValue

redux {{_}} {s} {Γ} {A} {.(App (Abs _ _) _)} (app (abs pos deriv) deriv₁) = {!!}

redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) with redux deriv1
redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 with redux deriv2
redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₁ v2 = inj₁ {!!}

redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₂ (t2' , deriv2') = inj₂ (App t1 t2' , app deriv1 deriv2')

redux {{_}} {s} {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₂ (t1' , deriv1') = inj₂ (App t1' t2 , app deriv1' deriv2)

redux {{_}} {s} {Γ} {.(FunTy _ _ _)} {(Abs n t)} (abs pos deriv) with redux deriv
... | inj₁ v = inj₁ {!!}
... | inj₂ (t' , deriv') = inj₂ (Abs n t' , abs pos deriv')

redux {{_}} {s} {Γ} {A} {unit} _ = inj₁ unitValue
redux {{_}} {s} {Γ} {A} {t} t1 = {!!}


-- Untyped reduction
untypedRedux : Term -> Maybe Term
untypedRedux (App (Abs x t) t') = just (syntacticSubst t' x t)
untypedRedux (App t1 t2) with untypedRedux t1
... | just t1' = just (App t1' t2)
... | nothing  = nothing
untypedRedux (If vtrue t1 _) = just t1
untypedRedux (If vfalse _ t2) = just t2
untypedRedux (If t t1 t2) with untypedRedux t
... | just t' = just (If t' t1 t2)
... | nothing = nothing
untypedRedux _ = nothing

{-# TERMINATING #-}
multiRedux : Term -> Term
multiRedux t with untypedRedux t
... | just t' = multiRedux t'
... | nothing = t

multiReduxProducesValues : {{R : Semiring}} {A : Type} {t : Term} -> Empty ⊢ t ∶ A -> Value (multiRedux t)
multiReduxProducesValues {A} {Var _} ()
multiReduxProducesValues {A} {App t1 t2} (app typing1 typing2) = {!!}
multiReduxProducesValues {FunTy _ _ _} {Abs x t} _
  with untypedRedux (Abs x t) | inspect untypedRedux (Abs x t)
... | just t' | [ () ]
... | nothing | [ prf ] = absValue {x} t
multiReduxProducesValues {A} {unit} typing = unitValue
multiReduxProducesValues {A} {Promote t} typing = promoteValue t
multiReduxProducesValues {A} {vtrue} typing = trueValue
multiReduxProducesValues {A} {vfalse} typing = falseValue
multiReduxProducesValues {A} {If t t₁ t₂} typing = {!!}

postulate
  multReduxCongruence : {t1 v : Term} {C : Term -> Term}
                   -> multiRedux t1 ≡ v -> multiRedux (C t1) ≡ multiRedux (C v)
  
  preservation : {{R : Semiring}} {s : ℕ} {Γ : Context s} {A : Type} {t : Term}
             -> Γ ⊢ t ∶ A
             -> Γ ⊢ multiRedux t ∶ A

  valuesDontReduce : {t : Term} -> Value t -> multiRedux t ≡ t

  determinism : {t t1 t2 : Term}
             -> multiRedux t ≡ t1 
             -> multiRedux t ≡ t2
             -> t1 ≡ t2

-- # Equality 

data FullBetaEq : Term -> Term -> Set where
  VarEq     : {x : ℕ} -> FullBetaEq (Var x) (Var x)
  AppEq     : {t1 t1' t2 t2' : Term} -> FullBetaEq t1 t1' -> FullBetaEq t2 t2' -> FullBetaEq (App t1 t2) (App t1' t2')
  AbsEq     : {x : ℕ} {t1 t2 : Term} -> FullBetaEq t1 t2 -> FullBetaEq (Abs x t1) (Abs x t2)
  UnitEq    : FullBetaEq unit unit
  PromoteEq : {t1 t2 : Term} -> FullBetaEq t1 t2 -> FullBetaEq (Promote t1) (Promote t2)
  VTrue     : FullBetaEq vtrue vtrue
  VFalse    : FullBetaEq vfalse vfalse
  IfEq      : {t t' t1 t1' t2 t2' : Term} -> FullBetaEq t t' -> FullBetaEq t1 t1' -> FullBetaEq t2 t2'
               -> FullBetaEq (If t t1 t2) (If t' t1' t2')
  BetaEq    : {x : ℕ} {t1 t2 : Term} -> FullBetaEq (App (Abs x t1) t2) (syntacticSubst t1 x t2)
  EmbedRedux : {t : Term} -> FullBetaEq (multiRedux t) t

_==_ : Term -> Term -> Set
t == t' = FullBetaEq t t'

embedReduxCong : {t1 t2 : Term} -> multiRedux t1 ≡ multiRedux t2 -> FullBetaEq t1 t2
embedReduxCong = {!!}

embedEq : {t1 t2 : Term} -> t1 ≡ t2 -> FullBetaEq t1 t2
embedEq {Var x} {Var .x} refl = VarEq
embedEq {App t1 t2} {App .t1 .t2} refl = AppEq (embedEq {t1} {t1} refl) (embedEq {t2} {t2} refl)
embedEq {Abs x t1} {Abs x₁ t2} prf = {!!}
embedEq {unit} {unit} refl = UnitEq
embedEq {Promote t1} {Promote .t1} refl = PromoteEq (embedEq {t1} {t1} refl)
embedEq {vtrue} {vtrue} refl = VTrue
embedEq {vfalse} {vfalse} refl = VFalse
embedEq {If t1 t2 t3} {If .t1 .t2 .t3} refl = IfEq (embedEq {t1} {t1} refl) (embedEq {t2} {t2} refl) (embedEq {t3} {t3} refl)

transFullBetaEq : {t1 t2 t3 : Term} -> t1 == t2 -> t2 == t3 -> t1 == t3
transFullBetaEq = {!!}
