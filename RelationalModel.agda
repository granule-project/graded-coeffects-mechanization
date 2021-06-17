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
open import Function

-- Based on Vineet and Deepak's paper model but without
-- heaps (as we don't have references) and without step indexing
-- (as we aren't considering recursion here).

-- # Unary interpretation of values in types
-- (as an indexed data type)

data [_]v : Type -> Term -> Set where
  unitInterpV : [ Unit ]v unit
  funInterpV  : {A B : Type} {r : Semiring}
             -> {x : ℕ}
             -> (e v : Term)
             -> [ A ]v v -> [ B ]v (subs v x e) -> [ FunTy A r B ]v (Abs x e)

  boxInterpV  : {A : Type} {r : Semiring}
             -> (e : Term)
             -> [ A ]v e -> [ Box r A ]v (Promote e)

  boolInterpTrue  : [ BoolTy ]v vtrue
  boolInterpFalse : [ BoolTy ]v vfalse

-- # Unary interpretation of expressions in types

[_]e : Type -> Semiring -> Term -> Set
[ τ ]e r t =
  forall (v : Term)
  -> multiRedux t ≡ v -> [ τ ]v v

-- # Relational interpretation of types

Rel : (A1 : Set) -> (A2 : Set) -> Set₁
Rel A1 A2 = A1 -> A2 -> Set

mutual
  -- # Binary interpretation of values in types

  ⟦_⟧v : Type ->  (Adv : Semiring) -> Rel Term Term
  ⟦ Unit ⟧v adv unit unit = ⊤

  ⟦ FunTy A r B ⟧v adv (Abs x e1) (Abs y e2) =
    (forall (v1 : Term) (v2 : Term)

   -- In the original model this:
   -- -> ⟦ A ⟧v adv {W} {_≤_} w' v1 v2
   -- But we have graded arrows here

    -> ⟦ Box r A ⟧v adv (Promote v1) (Promote v2)
    -> ⟦ B ⟧e adv (subs v1 x e1) (subs v2 y e2))

   × (forall (vc : Term)
      -> [ A ]v vc -> [ B ]e {!a!} (subs vc x e1))

   × (forall (vc : Term)
      -> [ A ]v vc -> [ B ]e {!!} (subs vc y e2))


  ⟦ Box r A ⟧v adv (Promote v1) (Promote v2) with pre r adv
  ... | false = ([ A ]v v1) × ([ A ]v v2)
  ... | true  = ⟦ A ⟧v adv v1 v2

  ⟦ BoolTy ⟧v adv vtrue vtrue = ⊤

  ⟦ BoolTy ⟧v adv vfalse vfalse = ⊤

  ⟦ _ ⟧v adv _ _ = ⊥


  -- # Binary interpretation of expressions in types
  ⟦_⟧e : Type -> (Adv : Semiring) -> Rel Term Term
  ⟦ tau ⟧e adv e1 e2 =
       forall (v1 v2 : Term)
    -> multiRedux e1 ≡ v1
    -> multiRedux e2 ≡ v2
    -> ⟦ tau ⟧v adv v1 v2

--------------
-- Contexts

-- unary
[_]Γ : Context -> List Term -> Set
[ Empty            ]Γ _ = ⊤
[ Ext _ _          ]Γ [] = ⊥
[ Ext g (Grad A r) ]Γ (v ∷ vs) =
  ([ A ]v v) × ([ g ]Γ vs)

-- binary
⟦_⟧Γ : Context -> (Adv : Semiring) -> List Term -> List Term -> Set
⟦ Empty   ⟧Γ adv _ _  = ⊤
⟦ Ext _ _ ⟧Γ adv _ [] = ⊥
⟦ Ext _ _ ⟧Γ adv _ [] = ⊥
⟦ Ext g (Grad A r) ⟧Γ adv (v1 ∷ vs1) (v2 ∷ vs2) =
   -- model like they have come from a box
   -- actually maybe? this isn't need and just
   -- ⟦ A ⟧v adv {W} {_≤_} w v1 v2 ?
   ⟦ Box r A ⟧v adv (Promote v1) (Promote v2)
   ×
   ⟦ g ⟧Γ adv vs1 vs2

-----------------------------

multisubst' : ℕ -> List Term -> Term -> Term
multisubst' n [] t' = t'
multisubst' n (t ∷ ts) t' =
  multisubst' (n + 1) ts (subs t n t')

multisubst : List Term -> Term -> Term
multisubst [] t' = t'
multisubst ts t' = multisubst' 0 ts t'

-------------------------------
-- Unary fundamental theorem

utheorem : {adv : Semiring}
        -> {γ : List Term}
        -> {Γ : Context} {e : Term} {τ : Type}
        -> Γ ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ τ ]e adv e
utheorem = {!!}

-------------------------------
-- Binary fundamental theorem

biFundamentalTheorem :
          {Γ : Context} {e : Term} {τ : Type}

        -> Γ ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : Semiring)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ τ ⟧e adv (multisubst γ1 e) (multisubst γ2 e)
biFundamentalTheorem = {!!}

lem : {adv : Semiring}
      {A : Type} {v1 v2 : Term}
   -> Value v1
   -> Value v2
   -> ⟦ A ⟧e adv v1 v2
   -> ⟦ A ⟧v adv v1 v2
lem {adv} {A} {v1} {v2} isvalv1 isvalv2 mem =
  mem v1 v2 (valuesDontReduce {v1} isvalv1) (valuesDontReduce {v2} isvalv2)

ulem :  {A : Type}
     -> {l : Semiring}
     -> {v1 v2 : Term}
     -> [ A ]v v1
     -> [ A ]v v2
     -> ⟦ Box Hi A ⟧v l (Promote v1) (Promote v2)
ulem {FunTy A r A₁} {l} {v1} {v2} val1 val2 = {!v1 v2 val1 val2!}
ulem {Unit} {l} {.unit} {.unit} unitInterpV unitInterpV = {!!}
ulem {Box r A} {l} {v1} {v2} val1 val2 = {!!}
ulem {BoolTy} {l} {vtrue} {vtrue} boolInterpTrue boolInterpTrue = {!!}
ulem {BoolTy} {l} {vfalse} {vfalse} boolInterpFalse boolInterpFalse = {!!}
ulem {BoolTy} {l} {vtrue} {vfalse} boolInterpTrue boolInterpFalse = {!!}

ulem {BoolTy} {l} {v1} {v2} val1 val2 = {!v1 val1 v2 val2!}


boolToSet : Bool -> Set
boolToSet true = ⊤
boolToSet false = ⊥

binaryImpliesUnary : {A : Type} {adv : Semiring}
  -> (v0 : Term)
  -> ⟦ A ⟧v adv v0 v0 -> [ A ]v v0
binaryImpliesUnary = {!!}

-------------------------------
-- Non-interference

nonInterfSpecialised : {A : Type} {e : Term}
        -> Ext Empty (Grad A Hi) ⊢ e ∶ Box Lo BoolTy

        -> (v1 v2 : Term)
        -> {v1' v2' : Term}
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A
        -> Value v1
        -> Value v2

        -> multiRedux (subs v1 0 e) ≡ v1'
        -> multiRedux (subs v2 0 e) ≡ v2'
        -> v1' ≡ v2'

nonInterfSpecialised {A} {e} typing v1 v2 {v1'} {v2'} v1typing v2typing isvalv1 isvalv2 v1redux v2redux rewrite v1redux | v2redux =
 let
--   ww = utheorem {Semiring} {ord} {Lo} {

   ev1 = biFundamentalTheorem {Empty} {Promote v1} {Box Hi A}
                  (pr v1typing) {[]} {[]} Hi tt (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue isvalv1))
                  (valuesDontReduce {Promote v1} (promoteValue isvalv1))

   ev2 = biFundamentalTheorem {Empty} {Promote v2} {Box Hi A}
                  (pr v2typing)  {[]} {[]} Hi tt (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue isvalv2))
                  (valuesDontReduce {Promote v2} (promoteValue isvalv2))

   valEv1 = binaryImpliesUnary {A} {Hi} v1 ev1
   valEv2 = binaryImpliesUnary {A} {Hi} v2 ev2


   z = biFundamentalTheorem {Ext Empty (Grad A Lo)} {Var 0} {A}
          (var {A} {Ext Empty (Grad A Lo)} {Empty} {Empty} refl)
          {v1 ∷ []} {v2 ∷ []} Hi ((valEv1 , valEv2) , tt)


   zAsVal = lem {Hi} {A} {v1} {v2} isvalv1 isvalv2 z

   res = biFundamentalTheorem {Ext Empty (Grad A Hi)} {e}
        {Box Lo BoolTy} typing {v1 ∷ []} {v2 ∷ []} Hi (zAsVal , tt) v1' v2' v1redux v2redux
 in {!!}

nonInterf : {A : Type} {li l : Semiring} {e : Term}
        -> (pre li l ≡ false)  -- condition on labels
        -> Ext Empty (Grad A li) ⊢ e ∶ Box l BoolTy

        -> (v1 v2 : Term)
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A
        -> Value v1
        -> Value v2

        -> multiRedux (subs v1 0 e) ≡ multiRedux (subs v2 0 e)

nonInterf {A} {li} {l} {e} rel typing v1 v2 v1typing v2typing isvalv1 isvalv2 =
  let
       ev1 = biFundamentalTheorem {Empty} {Promote v1} {Box li A}
                  (pr v1typing) {[]} {[]} l tt

      -- uth1 = utheorem {Semiring} {ord} {{!!}} {[]} {Empty} {v1} {A} v1typing {{!!}} tt
      -- uth2 = utheorem {Semiring} {ord} {{!!}} {[]} {Empty} {v2} {A} v2typing {{!!}} tt

      -- fromUtoV = ulem {Semiring} {ord} {{!!}} {{!!}} {{!!}} {{!!}} (uth1 {!!} {!!}) {!!}

      -- (l' , (rel , ev1')) = lem {Semiring} {ord} {li} {l} {Box li A}
      --     {Promote v1} {Promote v1} (promoteValue isvalv1) (promoteValue isvalv1) ev1

       x = biFundamentalTheorem {Ext Empty (Grad A li)} {e}
              {Box l BoolTy} typing {v1 ∷ []} {v2 ∷ []} l ({!!} , tt)
  in {!!}
