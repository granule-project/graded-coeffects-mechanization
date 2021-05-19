module GrCore where

open import Data.Product
open import Data.Sum

data Semiring : Set where

data Type : Set where
  FunTy : Type -> Type -> Type
  Unit  : Type
  Box   : (r : Semiring) -> Type -> Type

data Assumption : Type -> Set where
  Lin : (A : Type)                    -> Assumption A
  Grad : (A : Type) -> (r : Semiring) -> Assumption A

data Context : Set where
  Empty   : Context
  Ext     : {A : Type} -> Context -> Assumption A -> Context



data Member : Type -> Context -> Set where
  Here  : (Γ : Context) (A : Type) (Hyp : Assumption A) -> Member A (Ext Γ Hyp)
  There : (Γ : Context) (A : Type) (Hyp : Assumption A) -> (mem : Member A Γ) -> Member A (Ext Γ Hyp)

data Term : Set where
  Var : Term
  App : Term -> Term -> Term
  Abs : Term -> Term

-------------------------------------------------
-- Typing


data _⊢_∶_ : Context -> Term -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : { A : Type }
        { Γ : Context }
        (mem : Member A Γ)
      -> -------------------
         Γ ⊢ Var ∶ A


  app : { Γ : Context }
        { A B : Type}
        { t1 t2 : Term }

     ->   Γ ⊢ t1 ∶ FunTy A B
     ->   Γ ⊢ t2 ∶ A
     -> ----------------------
          Γ ⊢ App t1 t2 ∶ B


  abs : { Γ : Context }
        { A B : Type }
        { t : Term }

      ->   Ext Γ (Lin A) ⊢ t ∶ B
      -> ------------------------
          Γ ⊢ Abs t ∶ FunTy A B

-- Value predicate
data Value : Term -> Set where
  varValue : Value Var
  absValue : {t : Term} -> Value t -> Value (Abs t)
  appValue : {t1 t2 : Term} -> Value t1 -> Value t2 -> Value (App t1 t2)

-- substitution
subst : {Γ : Context} {A B : Type} {t1 t2 : Term}
      -> Ext Γ (Lin A) ⊢ t1 ∶ B
      -> Γ ⊢ t2 ∶ A
      -> ∃ (\t -> Γ ⊢ t ∶ B)
subst {Γ'} {A} {.A} {.Var} {t2} (var (Here Γ' A .(Lin A))) deriv2 = (t2 , deriv2)

subst {Γ} {A} {B} {t1} {t2} (var (There _ A' .(Lin _) mem)) deriv2 = {!!}
subst {Γ} {A} {B} {t1} {t2} (app deriv1 deriv3) deriv2 = {!!}
subst {Γ} {A} {B} {t1} {t2} (abs deriv1) deriv2 = {!!}



-- constructive progress
redux : {Γ : Context} {A : Type} {t : Term}
      -> Γ ⊢ t ∶ A
      -> (Value t) ⊎ ∃ (\t' -> Γ ⊢ t' ∶ A)

redux {Γ} {A} {.Var} (var mem) = inj₁ varValue

redux {Γ} {A} {.(App (Abs _) _)} (app (abs deriv) deriv₁) = {!!}

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) with redux deriv1
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 with redux deriv2
redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₁ v2 = inj₁ (appValue v1 v2)

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₁ v1 | inj₂ (t2' , deriv2') = inj₂ (App t1 t2' , app deriv1 deriv2')

redux {Γ} {A} {App t1 t2} (app deriv1 deriv2) | inj₂ (t1' , deriv1') = inj₂ (App t1' t2 , app deriv1' deriv2)

redux {Γ} {.(FunTy _ _)} {(Abs t)} (abs deriv) with redux deriv
... | inj₁ v = inj₁ (absValue v)
... | inj₂ (t' , deriv') = inj₂ (Abs t' , abs deriv')
