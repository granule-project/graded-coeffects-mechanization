
{-# OPTIONS --allow-unsolved-metas #-}

module GrCore where

open import Data.Product
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_≟_)

data Semiring : Set where

postulate
  1r : Semiring
  0r : Semiring
  _+R_ : Semiring -> Semiring -> Semiring
  _*R_ : Semiring -> Semiring -> Semiring
  leftUnit : {r : Semiring} -> 1r *R r ≡ r
  pre : Semiring -> Semiring -> Bool

data Type : Set where
  FunTy : (A : Type) -> (r : Semiring) -> (B : Type) -> Type -- A r -> B
  Unit  : Type
  Box   : (r : Semiring) -> Type -> Type
  --------------------------------------------------
  -- Prod  : Type -> Type -> Type
  -- Sum   : Type -> Type -> Type
  BoolTy : Type


data Assumption : Set where
--  Lin : (A : Type)                    -> Assumption A
  Grad : (A : Type) -> (r : Semiring) -> Assumption

data Context : Set where
  Empty   : Context
  Ext     : Context -> Assumption -> Context

_,,_ : Context -> Context -> Context
G1 ,, Empty = G1
G1 ,, (Ext G2 a) = Ext (G1 ,, G2) a

_·_ : Semiring -> Context -> Context
r · Empty = Empty
r · Ext g (Grad A s) = Ext (r · g) (Grad A (r *R s))

-- Make contexts a module
postulate
  -- TODO
  _++_ : Context -> Context -> Context
   -- _++_ = {!!}

  absorptionContext : {Γ Γ' : Context} -> (0r · Γ) ++ Γ' ≡ Γ'
  leftUnitContext : {Γ : Context} -> 1r · Γ ≡ Γ

length : Context -> ℕ
length Empty = 0
length (Ext g _) = 1 + length g

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

subs : Term -> ℕ -> Term -> Term
subs t x (Var y) with x ≟ y
... | yes p = t
... | no ¬p = Var y
subs t x (App t1 t2) = App (subs t x t1) (subs t x t2)
subs t x (Abs y t1) with x ≟ y
... | yes p = Abs y t1
... | no ¬p = Abs y (subs t x t1)
subs t x (Promote t1) = Promote (subs t x t1)
subs t x unit = unit
subs t x vtrue = vtrue
subs t x vfalse = vfalse
subs t x (If t1 t2 t3) = If (subs t x t1) (subs t x t2) (subs t x t3)

-------------------------------------------------
-- Typing
data _⊢_∶_ : Context -> Term -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : { A : Type }
        { Γ Γ1 Γ2 : Context }
        (pos : Γ ≡ ((Ext (0r · Γ1) (Grad A 1r)) ,, (0r · Γ2)))
    ->  ---------------------
        Γ ⊢ Var (length Γ1) ∶ A


  app : { Γ1 Γ2 : Context }
        { r : Semiring }
        { A B : Type}
        { t1 t2 : Term }

     ->   Γ1 ⊢ t1 ∶ FunTy A r B
     ->   Γ2 ⊢ t2 ∶ A
     -> -----------------------------
          (Γ1 ++ (r · Γ2)) ⊢ App t1 t2 ∶ B


  abs : { Γ Γ1 Γ2 : Context }
        { r : Semiring}
        { A B : Type }
        { t : Term }

      -> (pos : Γ ≡ (Ext Γ1 (Grad A r)) ,, Γ2)
      -> Γ ⊢ t ∶ B
      -> --------------------------------------
         (Γ1 ,, Γ2) ⊢ Abs (length Γ1 + 1) t ∶ FunTy A r B


  pr : { Γ : Context }
    -> { r : Semiring }
    -> { A : Type }
    -> { t : Term }

    -> Γ ⊢ t ∶ A
    --------------------------------
    -> (r · Γ) ⊢ Promote t ∶ Box r A


  unitConstr : { Γ : Context }
      -> --------------------------------
          (0r · Γ) ⊢ unit ∶ Unit

  trueConstr : { Γ : Context }
      -> --------------------------------
           (0r · Γ) ⊢ vtrue ∶ BoolTy

  falseConstr : { Γ : Context }
      -> --------------------------------
           (0r · Γ) ⊢ vfalse ∶ BoolTy

  if : { Γ1 Γ2 : Context }
       { B : Type }
       { t1 t2 t3 : Term }

    -> Γ1 ⊢ t1 ∶ BoolTy
    -> Γ2 ⊢ t2 ∶ B
    -> Γ2 ⊢ t3 ∶ B
   ----------------------------------
    -> (Γ1 ++ Γ2) ⊢ If t1 t2 t3 ∶ B


-- Value predicate
data Value : Term -> Set where
  unitValue : Value unit
  varValue : {n : ℕ} -> Value (Var n)
  absValue : {n : ℕ} -> {t : Term} -> Value t -> Value (Abs n t)
  appValue : {t1 t2 : Term} -> Value t1 -> Value t2 -> Value (App t1 t2)
  promoteValue : {t : Term} -> Value t -> Value (Promote t)

-- substitution
substitution : {Γ Γ1 Γ2 Γ3 : Context} {r : Semiring} {A B : Type} {t1 t2 : Term}
      -> Γ ⊢ t1 ∶ B
      -> (pos : Γ ≡ ((Ext (0r · Γ1) (Grad A 1r)) ,, (0r · Γ2)))
      -> Γ3 ⊢ t2 ∶ A
      -> ∃ (\t -> ((Γ1 ++ (r · Γ2)) ++ Γ3) ⊢ t ∶ B)

--substitution {Γ1} {Γ2} {.1r} {A} {.A} {Var .0} {t2} (var (Here .Γ1 .A (Γ1' , allZeroesPrf))) substitee
--  rewrite allZeroesPrf | absorptionContext {Γ1'} {1r · Γ2} | leftUnitContext {Γ2} =
--    t2 , substitee

substitution {Γ} {Γ1} {Γ2} {Γ3} {r} {A} {B} {t1} {t2} subs pos e = {!subs!}


-- constructive progress
redux : {Γ : Context} {A : Type} {t : Term}
      -> Γ ⊢ t ∶ A
      -> (Value t) ⊎ ∃ (\t' -> Γ ⊢ t' ∶ A)

redux {Γ} {A} {Var _} (var _) = inj₁ varValue

redux {Γ} {A} {.(App (Abs _ _) _)} (app (abs pos deriv) deriv₁) = {!!}

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) with redux deriv1
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 with redux deriv2
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₁ v2 = inj₁ (appValue v1 v2)

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₂ (t2' , deriv2') = inj₂ (App t1 t2' , app deriv1 deriv2')

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₂ (t1' , deriv1') = inj₂ (App t1' t2 , app deriv1' deriv2)

redux {Γ} {.(FunTy _ _ _)} {(Abs n t)} (abs pos deriv) with redux deriv
... | inj₁ v = inj₁ (absValue v)
... | inj₂ (t' , deriv') = inj₂ (Abs n t' , abs pos deriv')

redux {Γ} {A} {unit} _ = inj₁ unitValue
redux {Γ} {A} {t} t1 = {!!}

multiRedux : Term -> Term
multiRedux = {!!}

valuesDontReduce : {t : Term} -> Value t -> multiRedux t ≡ t
valuesDontReduce {t} v = {!!}
