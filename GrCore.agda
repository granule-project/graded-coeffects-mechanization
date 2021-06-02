module GrCore where

open import Data.Product
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality

data Semiring : Set where

postulate
  1r : Semiring
  0r : Semiring
  _+R_ : Semiring -> Semiring -> Semiring
  _*R_ : Semiring -> Semiring -> Semiring
  leftUnit : {r : Semiring} -> 1r *R r ≡ r


data Type : Set where
  FunTy : (A : Type) -> (r : Semiring) -> (B : Type) -> Type -- A r -> B
  Unit  : Type
  Box   : (r : Semiring) -> Type -> Type

data Assumption : Type -> Set where
--  Lin : (A : Type)                    -> Assumption A
  Grad : (A : Type) -> (r : Semiring) -> Assumption A

data Context : Set where
  Empty   : Context
  Ext     : {A : Type} -> Context -> Assumption A -> Context

-- Make contexts a module
postulate
  -- TODO
  _++_ : Context -> Context -> Context
   -- _++_ = {!!}

  -- TODO: pointwise
  _·_ : Semiring -> Context -> Context
  -- _·_ = {!!}

  absorptionContext : {Γ Γ' : Context} -> (0r · Γ) ++ Γ' ≡ Γ'
  leftUnitContext : {Γ : Context} -> 1r · Γ ≡ Γ



data Member : Type -> Context -> Set where
  Here  : (Γ : Context) (A : Type)  (allZero : Σ Context (\Γ' -> Γ ≡ 0r · Γ')) -> Member A (Ext Γ (Grad A 1r))
  There : (Γ : Context) (A B : Type) -> (mem : Member A Γ) -> Member A (Ext Γ (Grad B 0r))

data Term : Set where
  Var : ℕ -> Term
  App : Term -> Term -> Term
  Abs : Term -> Term


toIndex : {A : Type} {Γ : Context} -> Member A Γ -> ℕ
toIndex (Here Γ _ _)      = 0
toIndex (There Γ _ _ c) = 1 + toIndex c

-------------------------------------------------
-- Typing
data _⊢_∶_ : Context -> Term -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : { A : Type }
        { Γ : Context }
        (mem : Member A Γ)  --- contains the hard work of doing 0*G', x : 1 A
      -> -------------------
         Γ ⊢ Var (toIndex mem) ∶ A


  app : { Γ1 Γ2 : Context }
        { r : Semiring }
        { A B : Type}
        { t1 t2 : Term }

     ->   Γ1 ⊢ t1 ∶ FunTy A r B
     ->   Γ2 ⊢ t2 ∶ A
     -> -----------------------------
          (Γ1 ++ (r · Γ2)) ⊢ App t1 t2 ∶ B


  abs : { Γ : Context }
        { r : Semiring}
        { A B : Type }
        { t : Term }

      ->  Ext Γ (Grad A r) ⊢ t ∶ B
      -> ------------------------
          Γ ⊢ Abs t ∶ FunTy A r B

-- Value predicate
data Value : Term -> Set where
  varValue : {n : ℕ} -> Value (Var n)
  absValue : {t : Term} -> Value t -> Value (Abs t)
  appValue : {t1 t2 : Term} -> Value t1 -> Value t2 -> Value (App t1 t2)

-- substitution
substitution : {Γ1 Γ2 : Context} {r : Semiring} {A B : Type} {t1 t2 : Term}
      -> Ext Γ1 (Grad A r) ⊢ t1 ∶ B
      -> Γ2 ⊢ t2 ∶ A
      -> ∃ (\t -> (Γ1 ++ (r · Γ2)) ⊢ t ∶ B)

substitution {Γ1} {Γ2} {.1r} {A} {.A} {Var .0} {t2} (var (Here .Γ1 .A (Γ1' , allZeroesPrf))) substitee
  rewrite allZeroesPrf | absorptionContext {Γ1'} {1r · Γ2} | leftUnitContext {Γ2} =
    t2 , substitee

substitution {Γ1} {Γ2} {.0r} {A} {B} {Var .(suc (toIndex mem))} {t2} (var (There .Γ1 .B .A mem)) substitee = {!!}


substitution {Γ1} {Γ2} {r} {A} {B} {App t1 t3} {t2} receiver substitee = {!!}
substitution {Γ1} {Γ2} {r} {A} {.(FunTy _ _ _)} {Abs t1} {t2} (abs receiver) substitee = {!!}



-- constructive progress
redux : {Γ : Context} {A : Type} {t : Term}
      -> Γ ⊢ t ∶ A
      -> (Value t) ⊎ ∃ (\t' -> Γ ⊢ t' ∶ A)

redux {Γ} {A} {Var _} (var mem) = inj₁ varValue

redux {Γ} {A} {.(App (Abs _) _)} (app (abs deriv) deriv₁) = {!!}

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) with redux deriv1
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 with redux deriv2
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₁ v2 = inj₁ (appValue v1 v2)

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₂ (t2' , deriv2') = inj₂ (App t1 t2' , app deriv1 deriv2')

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₂ (t1' , deriv1') = inj₂ (App t1' t2 , app deriv1' deriv2)

redux {Γ} {.(FunTy _ _ _)} {(Abs t)} (abs deriv) with redux deriv
... | inj₁ v = inj₁ (absValue v)
... | inj₂ (t' , deriv') = inj₂ (Abs t' , abs deriv')
