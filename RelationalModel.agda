{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModel where

open import GrCore
open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool
open import Data.List
open import Data.Nat

-- Based on Vineet and Deepak's paper model but without
-- heaps (as we don't have references) and without step indexing
-- (as we aren't considering recursion here).

-- Unary interpretation of types
[_]u : Type -> Term -> Set
[ Unit ]u unit = ⊤
[ FunTy A r B ]u (Abs x e) =
     forall (v : Term)
  -> [ A ]u v
  -> [ B ]u (subs v x e)
[ Box r A ]u tm = [ A ]u tm
[ _ ]u _ = ⊥

-- Relational interpretation of types

Rel : (A1 : Set) -> (A2 : Set) -> Set₁
Rel A1 A2 = A1 -> A2 -> Set

WRel : (W : Set) -> (A1 : Set) -> (A2 : Set) -> Set₁
WRel W A1 A2 = W -> Rel A1 A2

mutual

  ⟦_⟧v : Type ->  (Adv : Semiring) -> {W : Set} -> {≤ : W -> W -> Set} -> WRel W Term Term
  ⟦ Unit ⟧v adv w unit unit = ⊤

  ⟦ FunTy A r B ⟧v adv {W} {_≤_} w (Abs x e1) (Abs y e2) =
    forall (w' : W)
    -> w ≤ w'
    -> forall (v1 : Term) (v2 : Term)

   -- In the original model this:
   -- -> ⟦ A ⟧v adv {W} {_≤_} w' v1 v2
   -- But we have graded arrows here

    -> ⟦ Box r A ⟧v adv {W} {_≤_} w' (Promote v1) (Promote v2)
    -> ⟦ B ⟧e adv {W} {_≤_} w' (subs v1 x e1) (subs v2 y e2)

  --

  -- TODO:
  ⟦ Box r A ⟧v adv {W} {_≤_} w (Promote v1) (Promote v2) with pre r adv
  ... | false = ([ A ]u v1) × ([ A ]u v2)
  ... | true  = ⟦ A ⟧v adv {W} {_≤_} w v1 v2

  ⟦ _ ⟧v adv w _ _ = ⊥

  ⟦_⟧e : Type -> (Adv : Semiring) -> {W : Set} -> {≤ : W -> W -> Set} -> WRel W Term Term
  ⟦ tau ⟧e adv {W} {_≤_} w e1 e2 =
       forall (v1 v2 : Term)
    -> multiRedux e1 ≡ v1
    -> multiRedux e2 ≡ v2
    -> Σ W (\w' -> w ≤ w' -> ⟦ tau ⟧v adv {W} {_≤_} w' v1 v2)

--------------
-- Contexts

⟦_⟧Γ : Context -> (Adv : Semiring) -> {W : Set} -> {≤ : W -> W -> Set}
  -> W ->  List Term -> List Term -> Set
⟦ Empty ⟧Γ adv {W} {_≤_} _ _ _ = ⊤
⟦ Ext _ _ ⟧Γ adv {W} {_≤_} _ [] _ = ⊥
⟦ Ext g (Grad A r) ⟧Γ adv {W} {_≤_} w (v1 ∷ vs1) (v2 ∷ vs2) =
   -- model like they have come from a box
   -- actually maybe? this isn't need and just
   -- ⟦ A ⟧v adv {W} {_≤_} w v1 v2 ?
   ⟦ Box r A ⟧v adv {W} {_≤_} w (Promote v1) (Promote v2)
   ×
   ⟦ g ⟧Γ adv {W} {_≤_} w vs1 vs2

-----------------------------

multisubst' : ℕ -> List Term -> Term -> Term
multisubst' n [] t' = t'
multisubst' n (t ∷ ts) t' =
  multisubst' (n + 1) ts (subs t n t')

multisubst : List Term -> Term -> Term
multisubst [] t' = t'
multisubst ts t' = multisubst' 0 ts t'

-------------------------------
-- Binary fundamental theorem

theorem :  {W : Set}
        -> {≤ : W -> W -> Set}
        -> {Γ : Context} {e : Term} {τ : Type}

        -> Γ ⊢ e ∶ τ
        -> {w : W}
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : Semiring)
        -> ⟦ Γ ⟧Γ adv {W} {≤} w γ1 γ2
        -> ⟦ τ ⟧e adv {W} {≤} w (multisubst γ1 e) (multisubst γ2 e)
theorem = {!!}

-------------------------------
-- Non-interference

nonInterf : {A : Type} {li l : Semiring} {e : Term}
        -> (pre li l ≡ false)  -- condition on labels

        -> Ext Empty (Grad A li) ⊢ e ∶ Box l BoolTy

        -> (v1 v2 : Term)
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A

        -> multiRedux (subs v1 0 e) ≡ multiRedux (subs v2 0 e)

nonInterf {A} {li} {l} {e} rel typing v1 v2 v1typing v2typing =
  let  ev1 = theorem {⊤} {\tt -> \tt -> ⊤} {Empty} {Promote v1} {Box li A}
                  (pr v1typing) {tt} {[]} {[]} li tt

       x = theorem {⊤} {\tt -> \tt -> ⊤} {Ext Empty (Grad A li)} {e}
              {Box l BoolTy} typing {tt} {v1 ∷ []} {v2 ∷ []} l ({!!} , tt)
  in {!!}
