{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModel where

open import GrCore
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool hiding (_≤_)
open import Data.List
open import Data.Nat hiding (_≤_)
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

             -> [ A ]v v -> [ B ]v (syntacticSubst v x e)

             -> [ FunTy A r B ]v (Abs x e)

  boxInterpV  : {A : Type} {r : Semiring}
             -> (e : Term)
             -> [ A ]v e -> [ Box r A ]v (Promote e)

  boolInterpTrue  : [ BoolTy ]v vtrue
  boolInterpFalse : [ BoolTy ]v vfalse

-- # Unary interpretation of expressions in types

[_]e : Type -> Term -> Set
[ A ]e t =
  forall (v : Term)
  -> multiRedux t ≡ v -> [ A ]v v

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
    -> ⟦ B ⟧e adv (syntacticSubst v1 x e1) (syntacticSubst v2 y e2))

  {- × (forall (vc : Term)
      -> [ A ]v vc -> [ B ]e {!a!} (subs vc x e1))

   × (forall (vc : Term)
      -> [ A ]v vc -> [ B ]e {!!} (subs vc y e2))
  -}

  -- pre Hi Lo   false
  -- Lo ≤ Hi means adversary is lo, box is hi, so cannot observe the
  -- equality

  ⟦ Box r A ⟧v adv (Promote v1) (Promote v2) with r ≤ adv -- wrong way round?
  ... | true  = ⟦ A ⟧v adv v1 v2
  ... | false = ([ A ]v v1) × ([ A ]v v2)

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
⟦ Ext _ _ ⟧Γ adv [] _ = ⊥
⟦ Ext g (Grad A r) ⟧Γ adv (v1 ∷ vs1) (v2 ∷ vs2) =

   ⟦ Box r A ⟧v adv (Promote v1) (Promote v2)
   ×
   ⟦ g ⟧Γ adv vs1 vs2

-----------------------------

multisubst' : ℕ -> List Term -> Term -> Term
multisubst' n [] t' = t'
multisubst' n (t ∷ ts) t' =
  multisubst' (n + 1) ts (syntacticSubst t n t')

multisubst : List Term -> Term -> Term
multisubst [] t' = t'
multisubst ts t' = multisubst' 0 ts t'

-------------------------------
-- Unary fundamental theorem

utheorem : {γ : List Term}
        -> {Γ : Context} {e : Term} {τ : Type}
        -> Γ ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ τ ]e (multisubst γ e)
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

{-
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
-}

boolToSet : Bool -> Set
boolToSet true = ⊤
boolToSet false = ⊥

binaryImpliesUnary : {A : Type} {adv : Semiring}
  -> (v0 : Term)
  -> ⟦ A ⟧v adv v0 v0 -> [ A ]v v0
binaryImpliesUnary = {!!}

boolBinaryValueInterpEquality : (v1 v2 : Term) -> ⟦ BoolTy ⟧v Lo v1 v2 -> v1 ≡ v2
boolBinaryValueInterpEquality (Var x) (Var x₁) ()
boolBinaryValueInterpEquality (Var x) (App v2 v3) ()
boolBinaryValueInterpEquality (Var x) (Abs x₁ v2) ()
boolBinaryValueInterpEquality (Var x) unit ()
boolBinaryValueInterpEquality (Var x) (Promote v2) ()
boolBinaryValueInterpEquality (Var x) vtrue ()
boolBinaryValueInterpEquality (Var x) vfalse ()
boolBinaryValueInterpEquality (Var x) (If v2 v3 v4) ()
boolBinaryValueInterpEquality (App v1 v2) (Var x) ()
boolBinaryValueInterpEquality (App v1 v2) (App v3 v4) ()
boolBinaryValueInterpEquality (App v1 v2) (Abs x v3) ()
boolBinaryValueInterpEquality (App v1 v2) unit ()
boolBinaryValueInterpEquality (App v1 v2) (Promote v3) ()
boolBinaryValueInterpEquality (App v1 v2) vtrue ()
boolBinaryValueInterpEquality (App v1 v2) vfalse ()
boolBinaryValueInterpEquality (App v1 v2) (If v3 v4 v5) ()
boolBinaryValueInterpEquality (Abs x v1) (Var x₁) ()
boolBinaryValueInterpEquality (Abs x v1) (App v2 v3) ()
boolBinaryValueInterpEquality (Abs x v1) (Abs x₁ v2) ()
boolBinaryValueInterpEquality (Abs x v1) unit ()
boolBinaryValueInterpEquality (Abs x v1) (Promote v2) ()
boolBinaryValueInterpEquality (Abs x v1) vtrue ()
boolBinaryValueInterpEquality (Abs x v1) vfalse ()
boolBinaryValueInterpEquality (Abs x v1) (If v2 v3 v4) ()
boolBinaryValueInterpEquality unit (Var x) ()
boolBinaryValueInterpEquality unit (App v2 v3) ()
boolBinaryValueInterpEquality unit (Abs x v2) ()
boolBinaryValueInterpEquality unit unit ()
boolBinaryValueInterpEquality unit (Promote v2) ()
boolBinaryValueInterpEquality unit vtrue ()
boolBinaryValueInterpEquality unit vfalse ()
boolBinaryValueInterpEquality unit (If v2 v3 v4) ()
boolBinaryValueInterpEquality (Promote v1) (Var x) ()
boolBinaryValueInterpEquality (Promote v1) (App v2 v3) ()
boolBinaryValueInterpEquality (Promote v1) (Abs x v2) ()
boolBinaryValueInterpEquality (Promote v1) unit ()
boolBinaryValueInterpEquality (Promote v1) (Promote v2) ()
boolBinaryValueInterpEquality (Promote v1) vtrue ()
boolBinaryValueInterpEquality (Promote v1) vfalse ()
boolBinaryValueInterpEquality (Promote v1) (If v2 v3 v4) ()
boolBinaryValueInterpEquality vtrue (Var x) ()
boolBinaryValueInterpEquality vtrue (App v2 v3) ()
boolBinaryValueInterpEquality vtrue (Abs x v2) ()
boolBinaryValueInterpEquality vtrue unit ()
boolBinaryValueInterpEquality vtrue (Promote v2) ()
boolBinaryValueInterpEquality vtrue vtrue tt = refl
boolBinaryValueInterpEquality vtrue vfalse ()
boolBinaryValueInterpEquality vtrue (If v2 v3 v4) ()
boolBinaryValueInterpEquality vfalse (Var x) ()
boolBinaryValueInterpEquality vfalse (App v2 v3) ()
boolBinaryValueInterpEquality vfalse (Abs x v2) ()
boolBinaryValueInterpEquality vfalse unit ()
boolBinaryValueInterpEquality vfalse (Promote v2) ()
boolBinaryValueInterpEquality vfalse vtrue ()
boolBinaryValueInterpEquality vfalse vfalse tt = refl
boolBinaryValueInterpEquality vfalse (If v2 v3 v4) ()
boolBinaryValueInterpEquality (If v1 v2 v3) (Var x) ()
boolBinaryValueInterpEquality (If v1 v2 v3) (App v4 v5) ()
boolBinaryValueInterpEquality (If v1 v2 v3) (Abs x v4) ()
boolBinaryValueInterpEquality (If v1 v2 v3) unit ()
boolBinaryValueInterpEquality (If v1 v2 v3) (Promote v4) ()
boolBinaryValueInterpEquality (If v1 v2 v3) vtrue ()
boolBinaryValueInterpEquality (If v1 v2 v3) vfalse ()
boolBinaryValueInterpEquality (If v1 v2 v3) (If v4 v5 v6) ()

-- Value lemma for promotion
promoteValueLemma : {v : Term} {r : Semiring} {A : Type}

  -> Empty ⊢ v ∶ Box r A
  -> Value v
  -> Σ Term (\v' -> v ≡ Promote v')

promoteValueLemma (var {A} {.Empty} {Γ1} {Γ2} pos) varValue = ⊥-elim (unequal pos)
  where
    unequal : {G G' : Context} {A : Assumption} -> Empty ≡ Ext G A ,, G' -> ⊥
    unequal {Empty} {Empty} {A} ()
    unequal {Empty} {Ext G' x} {A} ()
    unequal {Ext G x} {Empty} {A} ()
    unequal {Ext G x} {Ext G' x₁} {A} ()
promoteValueLemma typing (promoteValue t) = t , refl


-- Non-interference

nonInterfSpecialised : {A : Type} {e : Term}
        -> Ext Empty (Grad A Hi) ⊢ e ∶ Box Lo BoolTy

        -> (v1 v2 : Term)
        -> {v1' v2' : Term}
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) ≡ v1'
        -> multiRedux (syntacticSubst v2 0 e) ≡ v2'
        -> v1' ≡ v2'

nonInterfSpecialised {A} {e} typing v1 v2 {v1'} {v2'} v1typing v2typing isvalv1 isvalv2 v1redux v2redux =
 let
--   ww = utheorem {Semiring} {ord} {Lo} {

   (valv1 , valv1') = biFundamentalTheorem {Empty} {Promote v1} {Box Hi A}
                  (pr v1typing) {[]} {[]} Lo tt (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue v1))
                  (valuesDontReduce {Promote v1} (promoteValue v1))

   (valv2 , valv2') = biFundamentalTheorem {Empty} {Promote v2} {Box Hi A}
                  (pr v2typing)  {[]} {[]} Lo tt (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  (valuesDontReduce {Promote v2} (promoteValue v2))

   substTy1 = substitution {Ext Empty (Grad A Hi)} {Empty} {Empty} {Empty} {Hi} typing refl v1typing
   (v1'' , prf1) = promoteValueLemma {multiRedux (syntacticSubst v1 0 e)} {Lo} {BoolTy} (preservation {Empty} {Box Lo BoolTy} {syntacticSubst v1 0 e} substTy1)   (multiReduxProducesValues substTy1)

   substTy2  = substitution {Ext Empty (Grad A Hi)} {Empty} {Empty} {Empty} {Hi} typing refl v2typing
   (v2'' , prf2) = promoteValueLemma {_} {Lo} {BoolTy} (preservation substTy2) (multiReduxProducesValues substTy2)

   res = biFundamentalTheorem {Ext Empty (Grad A Hi)} {e}
        {Box Lo BoolTy} typing {v1 ∷ []} {v2 ∷ []} Lo (((valv1 ,
        valv2)) , tt) (Promote v1'') (Promote v2'') prf1 prf2

--   res = biFundamentalTheorem {Ext Empty (Grad A Hi)} {e}
--        {Box Lo BoolTy} typing {v1 ∷ []} {v2 ∷ []} Lo (((valv1 ,
--        valv2)) , tt) (multiRedux (syntacticSubst v1 0 e)) (multiRedux (syntacticSubst v2 0 e)) refl refl


   --aieou = boolBinaryValueInterpEquality (multiRedux (syntacticSubst v1 0 e)) (multiRedux (syntacticSubst v2 0 e)) {!!}

   aieou = boolBinaryValueInterpEquality v1'' v2'' res

   aieou' = trans (sym v1redux) prf1
   oo = trans (sym v2redux) prf2

   meagle = trans aieou' (cong Promote aieou)

 in trans meagle (sym oo)


nonInterf : {A : Type} {li l : Semiring} {e : Term}
        -> (li ≤ l ≡ false)  -- condition on labels
        -> Ext Empty (Grad A li) ⊢ e ∶ Box l BoolTy

        -> (v1 v2 : Term)
        -> Empty ⊢ v1 ∶ A
        -> Empty ⊢ v2 ∶ A
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) ≡ multiRedux (syntacticSubst v2 0 e)

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
