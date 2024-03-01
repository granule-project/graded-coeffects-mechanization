{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module RelationalModel where

open import GrCore
open import Data.Unit hiding (_≤_; _≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool hiding (_≤_; _≟_)
open import Data.List hiding (_++_)
open import Data.Nat hiding (_≤_)
open import Function
open import Data.Maybe
open import Relation.Nullary
open import Data.Sum
open import Data.Fin hiding (_≤_)

open import Semiring

open import OperationalModel

-- Based on Vineet and Deepak's paper model but without
-- heaps (as we don't have references) and without step indexing
-- (as we aren't considering recursion here).

-- # Unary interpretation of values in types
-- (as an indexed data type)

mutual

  {-# NO_POSITIVITY_CHECK #-}
  data [_]v {{R : Semiring}} : Type -> {s : ℕ} -> Term s -> Set where
    unitInterpV : {s : ℕ} -> [ Unit ]v {s} unit

    funInterpV  : {A B : Type} {r : grade} {s : ℕ}
               -> (e : Term (suc s))
               -> (forall (v : Term s) ->
                    [ Box r A ]e (Promote v) -> [ B ]e (syntacticSubst v zero e))

               -> [ FunTy A r B ]v (Abs e)

    boxInterpV  : {A : Type} {r : grade} {s : ℕ}
               -> (e : Term s)
               -> [ A ]e e -> [ Box r A ]v (Promote e)

    boolInterpTrue  : {s : ℕ} -> [ BoolTy ]v {s} vtrue
    boolInterpFalse : {s : ℕ} -> [ BoolTy ]v {s} vfalse

  -- # Unary interpretation of expressions in types

  [_]e : {{R : Semiring}} -> Type -> {s : ℕ} -> Term s -> Set
  [ A ]e {s} t =
    forall (v : Term s)
    -> multiRedux t ≡ v -> [ A ]v v

-- # Relational interpretation of types

Rel : (A1 : Set) -> (A2 : Set) -> Set₁
Rel A1 A2 = A1 -> A2 -> Set

mutual
  -- # Binary interpretation of values in types

  {-# NO_POSITIVITY_CHECK #-}
  data ⟦_⟧v {{R : Semiring}} : Type -> {s : ℕ} -> (adv : grade) -> Rel (Term s) (Term s) where
    unitInterpBi : {s : ℕ} {adv : grade} -> ⟦ Unit ⟧v {s} adv unit unit

    funInterpBi : {s : ℕ} {adv : grade} {A B : Type} {r : grade}
             -> {x y : ℕ}
             -> (e1 e2 : Term (suc s))
             -> (forall (v1 : Term s) (v2 : Term s)

               -- In the original model this:
               -- -> ⟦ A ⟧v adv {W} {_≤_} w' v1 v2
               -- But we have graded arrows here

                 -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
                 -> ⟦ B ⟧e adv (syntacticSubst v1 zero e1) (syntacticSubst v2 zero e2))
             -- unary parts
             -> (forall (v : Term s)
                  -> [ Box r A ]e (Promote v)
                  -> [ B ]e (syntacticSubst v zero e1))
             -> (forall (v : Term s)
                  -> [ Box r A ]e (Promote v)
                  -> [ B ]e (syntacticSubst v zero e2))
             --------------
             ->   ⟦ FunTy A r B ⟧v adv (Abs e1) (Abs e2)

    -- Note:
    -- pre Hi Lo   false
    -- Lo ≤ Hi means adversary is lo, box is hi, so cannot observe the
    -- equality

    boxInterpBiobs : {adv : grade} -> {A : Type} {r : grade}
              -> (r ≤ adv)
              -> (t1 t2 : Term s)
              -> ⟦ A ⟧e adv t1 t2
              -> ⟦ Box r A ⟧v adv (Promote t1) (Promote t2)

    boxInterpBiunobs : {adv : grade} -> {A : Type} {r : grade}
              -> ¬ (r ≤ adv)
              -> (t1 t2 : Term s)
              -> ([ A ]e t1) × ([ A ]e t2)
              -> ⟦ Box r A ⟧v adv (Promote t1) (Promote t2)

    boolInterpTrueBi  : {s : ℕ} {adv : grade} -> ⟦ BoolTy ⟧v {s} adv vtrue vtrue
    boolInterpFalseBi : {s : ℕ} {adv : grade} -> ⟦ BoolTy ⟧v {s} adv vfalse vfalse

  {-# TERMINATING #-}
  -- # Binary interpretation of expressions in types
  ⟦_⟧e : {{R : Semiring}} -> Type -> (adv : grade) -> {s : ℕ} -> Rel (Term s) (Term s)
  ⟦ tau ⟧e adv {s} e1 e2 =
       forall (v1 v2 : Term s)
    -> multiRedux e1 ≡ v1
    -> multiRedux e2 ≡ v2
    -> ⟦ tau ⟧v adv v1 v2

--------------
-- Contexts

-- unary
[_]Γ : {{R : Semiring}} -> {s : ℕ} -> Context s -> Telescope s -> Set
[ Empty            ]Γ Empty = ⊤
[ Ext g (Grad A r) ]Γ (Cons v vs) = ([ Box r A ]e (Promote v)) × ([ g ]Γ vs)

-- binary
⟦_⟧Γ : {{R : Semiring}} -> {s : ℕ} -> Context s -> (adv : grade) -> Telescope s -> Telescope s -> Set
⟦ Empty   ⟧Γ adv Empty Empty  = ⊤
⟦ Ext g (Grad A r) ⟧Γ adv (Cons t1 ts1) (Cons t2 ts2) =

   ⟦ Box r A ⟧e adv (Promote t1) (Promote t2)
   ×
   ⟦ g ⟧Γ adv ts1 ts2

-------------------------------------------------------
-- # Binary interpretation implies unary interpretation

mutual
  binaryImpliesUnaryV : {{R : Semiring}} {s : ℕ} {A : Type} {t1 t2 : Term s} {adv : grade}
                    -> ⟦ A ⟧v adv t1 t2 -> [ A ]v t1 × [ A ]v t2
  binaryImpliesUnaryV {_} {FunTy A r B} {Abs e1} {Abs e2} {adv} (funInterpBi e1 e2 body ubody1 ubody2) =
     (funInterpV e1 ubody1) , (funInterpV e2 ubody2)

  binaryImpliesUnaryV {s} {Unit} {.unit} {.unit} {adv} unitInterpBi = unitInterpV {s} , unitInterpV {s}
  binaryImpliesUnaryV {_} {Box r A} {.(Promote t1)} {.(Promote t2)} {adv} (boxInterpBiobs x t1 t2 inner)
   with binaryImpliesUnary {_} {A} {t1} {t2} {adv} inner
  ... | (fst , snd) = (boxInterpV t1 fst) , (boxInterpV t2 snd)
  binaryImpliesUnaryV {_} {Box r A} {.(Promote t1)} {.(Promote t2)} {adv} (boxInterpBiunobs x t1 t2 (fst , snd)) =
    (boxInterpV t1 fst) , (boxInterpV t2 snd)
  binaryImpliesUnaryV {s} {BoolTy} {.vtrue} {.vtrue} {adv} boolInterpTrueBi = boolInterpTrue {s} , boolInterpTrue {s}
  binaryImpliesUnaryV {s} {BoolTy} {.vfalse} {.vfalse} {adv} boolInterpFalseBi = boolInterpFalse {s} , boolInterpFalse {s}

  binaryImpliesUnary : {{R : Semiring}} {A : Type} {t1 t2 : Term s} {adv : grade}
                    -> ⟦ A ⟧e adv t1 t2 -> [ A ]e t1 × [ A ]e t2
  binaryImpliesUnary {_} {A} {t1} {t2} {adv} pre = (left , right)
  -- pre takes two arguments- two values v1 and v2 that t1 and t2 reduce into
  --   given these then v1 and v2 are in the value relation
    where
      left : [ A ]e t1
      left v0 redux = proj₁ (binaryImpliesUnaryV (pre v0 (multiRedux t2) redux refl))

      right : [ A ]e t2
      right v0 redux = proj₂ (binaryImpliesUnaryV (pre (multiRedux t1) v0 refl redux))

  binaryImpliesUnaryG : {{R : Semiring}} {sz : ℕ} { Γ : Context sz } {adv : grade} {γ1 γ2 : Telescope sz}
                    -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ([ Γ ]Γ γ1) × ([ Γ ]Γ γ2)
  binaryImpliesUnaryG {.0} {Empty} {adv} {Empty} {Empty} pre = tt , tt
  binaryImpliesUnaryG {suc sz} {Ext Γ (Grad A r)} {adv} {Cons v1 γ1} {Cons v2 γ2} (arg , rest)
    with binaryImpliesUnary {_} {Box r A} {Promote v1} {Promote v2} {adv} arg | binaryImpliesUnaryG {sz} {Γ} {adv} {γ1} {γ2} rest
  ... | ( arg1 , arg2 ) | ( rest1 , rest2 ) = ( (arg1 , rest1) , (arg2 , rest2) )


-------------------------------
-- Conversion theorems for expressions and contexts

unaryPlusElimLeft : {{R : Semiring}} {A : Type} {r1 r2 : grade} {x : Term s} -> [ Box (r1 +R r2) A ]e (Promote x) -> [ Box r1 A ]e (Promote x)
unaryPlusElimLeft {A} {r1} {r2} {x} arg v0 v0redux with arg v0 v0redux
... | boxInterpV e inner = boxInterpV e inner

unaryPlusElimLeftΓ : {{R : Semiring}} {sz : ℕ} {γ : Telescope sz} {Γ1 Γ2 : Context sz} -> [ Γ1 ++ Γ2 ]Γ γ -> [ Γ1 ]Γ γ
unaryPlusElimLeftΓ {.0} {Empty} {Empty} {Empty} tt = tt
unaryPlusElimLeftΓ {suc s} {Cons x γ} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (head , tail) =
  unaryPlusElimLeft {_} {A} {r1} {r2} {x} head , unaryPlusElimLeftΓ {s} {γ} {Γ1} {Γ2} tail

unaryPlusElimRight : {{R : Semiring}}{A : Type} {r1 r2 : grade} {x : Term s} -> [ Box (r1 +R r2) A ]e (Promote x) -> [ Box r2 A ]e (Promote x)
unaryPlusElimRight {A} {r1} {r2} {x} arg v0 v0redux with arg v0 v0redux
... | boxInterpV e inner = boxInterpV e inner

unaryPlusElimRightΓ : {{R : Semiring}} {sz : ℕ} {γ : Telescope sz} {Γ1 Γ2 : Context sz} -> [ Γ1 ++ Γ2 ]Γ γ -> [ Γ2 ]Γ γ
unaryPlusElimRightΓ {.0} {Empty} {Empty} {Empty} tt = tt
unaryPlusElimRightΓ {suc s} {Cons x γ} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (head , tail)
  rewrite sym (sameTypes {s} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl) =
    unaryPlusElimRight {_} {A} {r1} {r2} {x} head , unaryPlusElimRightΓ {s} {γ} {Γ1} {Γ2} tail

binaryPlusElimLeftΓ : {{R : Semiring}} {sz : ℕ} {adv : grade} {γ1 γ2 : Telescope sz} {Γ1 Γ2 : Context sz}
                   -> (convertVal : ({sz : ℕ} {r1 r2 adv : grade} {v1 v2 : Term sz} {A : Type}
                          -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)))
                   -> ⟦ Γ1 ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
binaryPlusElimLeftΓ {{R}} {0} {adv} {Empty} {empty} {Empty} {Empty} convertVal x = x
binaryPlusElimLeftΓ {{R}} {(suc s)} {adv} {Cons v1 γ1} {Cons v2 γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} convertVal (arg , rest) =
    convert {s} {r1} {r2} {adv} {v1} {v2} {A} arg , binaryPlusElimLeftΓ {s} {adv} {γ1} {γ2} {Γ1} {Γ2} convertVal rest
  where
    convert : {s : ℕ} {r1 r2 adv : grade} {v1 v2 : Term s} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧e adv (Promote v1) (Promote v2)
    convert {s} {r1} {r2} {adv} {v1} {v2} {A} arg v1' v2' v1redux' v2redux'
     rewrite trans (sym v1redux') (reduxProm {_} {v1})
          | trans (sym v2redux') (reduxProm {_} {v2}) =
          convertVal {_} {r1} {r2} {adv} {v1} {v2} {A} (arg (Promote v1) ((Promote v2)) refl refl)

binaryPlusElimRightΓ : {{R : Semiring}}
                       {sz : ℕ} {adv : grade} {γ1 γ2 : Telescope sz} {Γ1 Γ2 : Context sz}
                    -> (convertVal : {sz : ℕ} {r1 r2 adv : grade} {v1 v2 : Term sz} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r2 A ⟧v adv (Promote v1) (Promote v2))
                    -> ⟦ Γ1 ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ2 ⟧Γ adv γ1 γ2
binaryPlusElimRightΓ {{R}} {0} {adv} {Empty} {Empty} {Empty} {Empty} _ _ = tt
binaryPlusElimRightΓ {{R}} {(suc s)} {adv} {Cons v1 γ1} {Cons v2 γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} convertVal2 (arg , rest)
      rewrite sym (sameTypes {s} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl) =
        convert2 {s} {r1} {r2} {v1} {v2} {A} arg , binaryPlusElimRightΓ {s} {adv} {γ1} {γ2} {Γ1} {Γ2} convertVal2 rest
  where
    convert2 : {s : ℕ} {r1 r2 : grade} {v1 v2 : Term s} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box r2 A ⟧e adv (Promote v1) (Promote v2)
    convert2 {s} {r1} {r2} {v1} {v2} {A} arg v1' v2' v1redux' v2redux'
      rewrite trans (sym v1redux') (reduxProm {_} {v1})
            | trans (sym v2redux') (reduxProm {_} {v2}) =
            convertVal2 {_} {r1} {r2} {adv} {v1} {v2} {A} (arg (Promote v1) ((Promote v2)) refl refl)



binaryPlusElimRightBox :
    {{R : Semiring}} {{R' : NonInterferingSemiring }}
    {s : ℕ}
    {r1 r2 adv : grade}
    {v1 v2 : Term s} {A : Type}
    -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2)
    -> ⟦ Box r2 A ⟧v adv (Promote v1) (Promote v2)
binaryPlusElimRightBox {_} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with (r1 +R r2) ≤d adv | r2 ≤d adv
... | no eqo  | yes eq' = ⊥-elim (eqo eq)
... | no eqo  | no eq'  = boxInterpBiunobs  eq' v1 v2 (binaryImpliesUnary {_} {A} {v1} {v2} {adv} arg)
... | yes eqo | yes eq' = boxInterpBiobs   eq' v1 v2 arg
... | yes eqo | no eq'  = boxInterpBiunobs  eq' v1 v2 (binaryImpliesUnary {_} {A} {v1} {v2} {adv} arg)
binaryPlusElimRightBox {_} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) =
   boxInterpBiunobs (decreasing+Inv' {r1} {r2} {adv} eq) v1 v2 argInterp


binaryPlusElimLeftBox :
    {{R : Semiring}} {{R' : NonInterferingSemiring}}
    {s : ℕ}
    {r1 r2 adv : grade}
    {v1 v2 : Term s} {A : Type}
    -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2)
    -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)
binaryPlusElimLeftBox {{R}} {_} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with r1 ≤d adv
... | no  eqo = boxInterpBiunobs eqo v1 v2 ((binaryImpliesUnary {_} {A} {v1} {v2} {adv} arg))
... | yes eqo = boxInterpBiobs eqo v1 v2 arg
binaryPlusElimLeftBox {{R}} {{R'}} {_} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) = boxInterpBiunobs (decreasing+Inv {r1} {r2} {adv} eq) v1 v2 argInterp


convertValNISemiring :
    {{R : Semiring}} {{R' : NonInterferingSemiring}}
    {s : ℕ}
    {r1 r2 adv : grade}
    {v1 v2 : Term s} {A : Type}
    -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2)
    -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)
convertValNISemiring {_} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with r1 ≤d adv
... | no  eqo = boxInterpBiunobs eqo v1 v2 ((binaryImpliesUnary {_} {A} {v1} {v2} {adv} arg))
... | yes eqo = boxInterpBiobs eqo v1 v2 arg
convertValNISemiring {_} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) = boxInterpBiunobs (decreasing+Inv eq) v1 v2 argInterp

binaryTimesElimRightΓ :
    {{R : Semiring}}
    {sz : ℕ}
    {γ1 γ2 : Telescope sz}
    {Γ : Context sz} {r adv : grade} ->
     (convertVal : {sz : ℕ} {s : grade} {v1 v2 : Term sz} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2))
   -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ ⟧Γ adv γ1 γ2
binaryTimesElimRightΓ {_} {Empty} {Empty} {Empty} {r} {adv} _ g = tt
binaryTimesElimRightΓ {suc n} {Cons v1 γ1} {Cons v2 γ2} {Ext Γ (Grad A s)} {r} {adv} convertVal (ass , g) =
    convertExp {s} {v1} {v2} {A} ass , binaryTimesElimRightΓ {n} {γ1} {γ2} {Γ} {r} {adv} convertVal g
  where
        convertExp : {s : grade} {v1 v2 : Term _} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧e adv (Promote v1) (Promote v2)
        convertExp {s} {v1} {v2} {A} arg1 v1' v2' v1redux' v2redux' rewrite trans (sym v1redux') (reduxProm {_} {v1}) | trans (sym v2redux') (reduxProm {_} {v2}) =
           convertVal  {_} {s} {v1} {v2} {A} (arg1 (Promote v1) (Promote v2) refl refl)

convertUnaryBox :
    {{R : Semiring}}
    {sz : ℕ}
    {A : Type} {r s : grade} {t : Term sz}
  -> [ Box r A ]e (Promote t)
  -> [ Box s A ]e (Promote t)
convertUnaryBox pre v0 v0redux with pre v0 v0redux
... | boxInterpV e inner = boxInterpV e inner


unaryTimesElimRightΓ :
    {{R : Semiring}}
    {sz : ℕ} {γ1 : Telescope sz} {Γ : Context sz} {r : grade}
   -> [ r · Γ ]Γ γ1 -> [ Γ ]Γ γ1
unaryTimesElimRightΓ ⦃ R ⦄ {.0} {Empty} {Empty} {r} inp = tt
unaryTimesElimRightΓ ⦃ R ⦄ {suc n} {Cons x γ1} {Ext Γ (Grad A s)} {r} (ass , g) =
  convertUnaryBox ass , unaryTimesElimRightΓ {{R}} {n} {γ1} {Γ} {r} g
