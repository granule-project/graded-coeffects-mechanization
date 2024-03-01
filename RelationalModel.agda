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

open import Semiring

open import OperationalModel

-- Based on Vineet and Deepak's paper model but without
-- heaps (as we don't have references) and without step indexing
-- (as we aren't considering recursion here).

-- # Unary interpretation of values in types
-- (as an indexed data type)

mutual

  {-# NO_POSITIVITY_CHECK #-}
  data [_]v {{R : Semiring}} : Type -> Term -> Set where
    unitInterpV : [ Unit ]v unit

    funInterpV  : {A B : Type} {r : grade}
               -> {x : ℕ}
               -> (e : Term)
               -> (forall (v : Term) ->
                    [ Box r A ]e (Promote v) -> [ B ]e (syntacticSubst v x e))

               -> [ FunTy A r B ]v (Abs x e)

    boxInterpV  : {A : Type} {r : grade}
               -> (e : Term)
               -> [ A ]e e -> [ Box r A ]v (Promote e)

    boolInterpTrue  : [ BoolTy ]v vtrue
    boolInterpFalse : [ BoolTy ]v vfalse

  -- # Unary interpretation of expressions in types

  [_]e : {{R : Semiring}} -> Type -> Term -> Set
  [ A ]e t =
    forall (v : Term)
    -> multiRedux t ≡ v -> [ A ]v v

-- # Relational interpretation of types

Rel : (A1 : Set) -> (A2 : Set) -> Set₁
Rel A1 A2 = A1 -> A2 -> Set

mutual
  -- # Binary interpretation of values in types

  {-# NO_POSITIVITY_CHECK #-}
  data ⟦_⟧v {{R : Semiring}} : Type -> (adv : grade) -> Rel Term Term where
    unitInterpBi : {adv : grade} -> ⟦ Unit ⟧v adv unit unit

    funInterpBi : {adv : grade} {A B : Type} {r : grade}
             -> {x y : ℕ}
             -> (e1 e2 : Term)
             -> (forall (v1 : Term) (v2 : Term)

               -- In the original model this:
               -- -> ⟦ A ⟧v adv {W} {_≤_} w' v1 v2
               -- But we have graded arrows here

                 -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2)
                 -> ⟦ B ⟧e adv (syntacticSubst v1 x e1) (syntacticSubst v2 y e2))
             -- unary parts
             -> (forall (v : Term)
                  -> [ Box r A ]e (Promote v)
                  -> [ B ]e (syntacticSubst v x e1))
             -> (forall (v : Term)
                  -> [ Box r A ]e (Promote v)
                  -> [ B ]e (syntacticSubst v y e2))
             --------------
             ->   ⟦ FunTy A r B ⟧v adv (Abs x e1) (Abs y e2)

    -- Note:
    -- pre Hi Lo   false
    -- Lo ≤ Hi means adversary is lo, box is hi, so cannot observe the
    -- equality

    boxInterpBiobs : {adv : grade} -> {A : Type} {r : grade}
              -> (r ≤ adv)
              -> (t1 t2 : Term)
              -> ⟦ A ⟧e adv t1 t2
              -> ⟦ Box r A ⟧v adv (Promote t1) (Promote t2)

    boxInterpBiunobs : {adv : grade} -> {A : Type} {r : grade}
              -> ¬ (r ≤ adv)
              -> (t1 t2 : Term)
              -> ([ A ]e t1) × ([ A ]e t2)
              -> ⟦ Box r A ⟧v adv (Promote t1) (Promote t2)

    boolInterpTrueBi  : {adv : grade} -> ⟦ BoolTy ⟧v adv vtrue vtrue
    boolInterpFalseBi : {adv : grade} -> ⟦ BoolTy ⟧v adv vfalse vfalse

  {-# TERMINATING #-}
  -- # Binary interpretation of expressions in types
  ⟦_⟧e : {{R : Semiring}} -> Type -> (adv : grade) -> Rel Term Term
  ⟦ tau ⟧e adv e1 e2 =
       forall (v1 v2 : Term)
    -> multiRedux e1 ≡ v1
    -> multiRedux e2 ≡ v2
    -> ⟦ tau ⟧v adv v1 v2

--------------
-- Contexts

-- unary
[_]Γ : {{R : Semiring}} -> {s : ℕ} -> Context s -> List Term -> Set
[ Empty            ]Γ _ = ⊤
[ Ext g (Grad A r) ]Γ (v ∷ vs) = ([ Box r A ]e (Promote v)) × ([ g ]Γ vs)
[ Ext _ _          ]Γ _ = ⊥

-- binary
⟦_⟧Γ : {{R : Semiring}} -> {s : ℕ} -> Context s -> (adv : grade) -> List Term -> List Term -> Set
⟦ Empty   ⟧Γ adv [] []  = ⊤
⟦ Empty   ⟧Γ adv _ _  = ⊥
⟦ Ext _ _ ⟧Γ adv _ [] = ⊥
⟦ Ext _ _ ⟧Γ adv [] _ = ⊥
⟦ Ext g (Grad A r) ⟧Γ adv (t1 ∷ ts1) (t2 ∷ ts2) =

   ⟦ Box r A ⟧e adv (Promote t1) (Promote t2)
   ×
   ⟦ g ⟧Γ adv ts1 ts2

-------------------------------------------------------
-- # Binary interpretation implies unary interpretation

mutual
  binaryImpliesUnaryV : {{R : Semiring}} {A : Type} {t1 t2 : Term} {adv : grade}
                    -> ⟦ A ⟧v adv t1 t2 -> [ A ]v t1 × [ A ]v t2
  binaryImpliesUnaryV {FunTy A r B} {Abs x e1} {Abs x' e2} {adv} (funInterpBi e1 e2 body ubody1 ubody2) =
     (funInterpV e1 ubody1) , (funInterpV e2 ubody2)

  binaryImpliesUnaryV {Unit} {.unit} {.unit} {adv} unitInterpBi = unitInterpV , unitInterpV
  binaryImpliesUnaryV {Box r A} {.(Promote t1)} {.(Promote t2)} {adv} (boxInterpBiobs x t1 t2 inner)
   with binaryImpliesUnary {A} {t1} {t2} {adv} inner
  ... | (fst , snd) = (boxInterpV t1 fst) , (boxInterpV t2 snd)
  binaryImpliesUnaryV {Box r A} {.(Promote t1)} {.(Promote t2)} {adv} (boxInterpBiunobs x t1 t2 (fst , snd)) =
    (boxInterpV t1 fst) , (boxInterpV t2 snd)
  binaryImpliesUnaryV {BoolTy} {.vtrue} {.vtrue} {adv} boolInterpTrueBi = boolInterpTrue , boolInterpTrue
  binaryImpliesUnaryV {BoolTy} {.vfalse} {.vfalse} {adv} boolInterpFalseBi = boolInterpFalse , boolInterpFalse

  binaryImpliesUnary : {{R : Semiring}} {A : Type} {t1 t2 : Term} {adv : grade}
                    -> ⟦ A ⟧e adv t1 t2 -> [ A ]e t1 × [ A ]e t2
  binaryImpliesUnary {A} {t1} {t2} {adv} pre = (left , right)
  -- pre takes two arguments- two values v1 and v2 that t1 and t2 reduce into
  --   given these then v1 and v2 are in the value relation
    where
      left : [ A ]e t1
      left v0 redux = proj₁ (binaryImpliesUnaryV (pre v0 (multiRedux t2) redux refl))

      right : [ A ]e t2
      right v0 redux = proj₂ (binaryImpliesUnaryV (pre (multiRedux t1) v0 refl redux))

  binaryImpliesUnaryG : {{R : Semiring}} {sz : ℕ} { Γ : Context sz } {adv : grade} {γ1 γ2 : List Term}
                    -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ([ Γ ]Γ γ1) × ([ Γ ]Γ γ2)
  binaryImpliesUnaryG {.0} {Empty} {adv} {_} {_} pre = tt , tt
  binaryImpliesUnaryG {suc sz} {Ext Γ (Grad A r)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} (arg , rest)
    with binaryImpliesUnary {Box r A} {Promote v1} {Promote v2} {adv} arg | binaryImpliesUnaryG {sz} {Γ} {adv} {γ1} {γ2} rest
  ... | ( arg1 , arg2 ) | ( rest1 , rest2 ) = ( (arg1 , rest1) , (arg2 , rest2) )


-------------------------------
-- Conversion theorems for expressions and contexts

unaryPlusElimLeft : {{R : Semiring}} {A : Type} {r1 r2 : grade} {x : Term} -> [ Box (r1 +R r2) A ]e (Promote x) -> [ Box r1 A ]e (Promote x)
unaryPlusElimLeft {A} {r1} {r2} {x} arg v0 v0redux with arg v0 v0redux
... | boxInterpV e inner = boxInterpV e inner

unaryPlusElimLeftΓ : {{R : Semiring}} {sz : ℕ} {γ : List Term} {Γ1 Γ2 : Context sz} -> [ Γ1 ++ Γ2 ]Γ γ -> [ Γ1 ]Γ γ
unaryPlusElimLeftΓ {.0} {γ} {Empty} {Empty} tt = tt
unaryPlusElimLeftΓ {suc s} {x ∷ γ} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (head , tail) =
  unaryPlusElimLeft {A} {r1} {r2} {x} head , unaryPlusElimLeftΓ {s} {γ} {Γ1} {Γ2} tail

unaryPlusElimRight : {{R : Semiring}}{A : Type} {r1 r2 : grade} {x : Term} -> [ Box (r1 +R r2) A ]e (Promote x) -> [ Box r2 A ]e (Promote x)
unaryPlusElimRight {A} {r1} {r2} {x} arg v0 v0redux with arg v0 v0redux
... | boxInterpV e inner = boxInterpV e inner

unaryPlusElimRightΓ : {{R : Semiring}} {sz : ℕ} {γ : List Term} {Γ1 Γ2 : Context sz} -> [ Γ1 ++ Γ2 ]Γ γ -> [ Γ2 ]Γ γ
unaryPlusElimRightΓ {.0} {γ} {Empty} {Empty} tt = tt
unaryPlusElimRightΓ {suc s} {x ∷ γ} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} (head , tail)
  rewrite sym (sameTypes {s} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl) =
    unaryPlusElimRight {A} {r1} {r2} {x} head , unaryPlusElimRightΓ {s} {γ} {Γ1} {Γ2} tail

binaryPlusElimLeftΓ : {{R : Semiring}} {sz : ℕ} {adv : grade} {γ1 γ2 : List Term} {Γ1 Γ2 : Context sz}
                   -> (convertVal : ({r1 r2 adv : grade} {v1 v2 : Term} {A : Type}
                          -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)))
                   -> ⟦ Γ1 ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ1 ⟧Γ adv γ1 γ2
binaryPlusElimLeftΓ {{R}} {0} {adv} {[]} {[]} {Empty} {Empty} convertVal _ = tt
binaryPlusElimLeftΓ {{R}} {0} {adv} {γ1} {γ2} {Empty} {Empty} convertVal p = p
binaryPlusElimLeftΓ {{R}} {.(suc _)} {adv} {[]} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} _ ()
binaryPlusElimLeftΓ {{R}} {.(suc _)} {adv} {[]} {x ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} _ ()
binaryPlusElimLeftΓ {{R}} {.(suc _)} {adv} {x ∷ γ1} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} _ ()
binaryPlusElimLeftΓ {{R}} {(suc s)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} convertVal (arg , rest) =
    convert {r1} {r2} {adv} {v1} {v2} {A} arg , binaryPlusElimLeftΓ {s} {adv} {γ1} {γ2} {Γ1} {Γ2} convertVal rest
  where
    convert : {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧e adv (Promote v1) (Promote v2)
    convert {r1} {r2} {adv} {v1} {v2} {A} arg v1' v2' v1redux' v2redux'
     rewrite trans (sym v1redux') (reduxProm {v1})
          | trans (sym v2redux') (reduxProm {v2}) = convertVal {r1} {r2} {adv} {v1} {v2} {A} (arg (Promote v1) ((Promote v2)) refl refl)

binaryPlusElimRightΓ : {{R : Semiring}}
                       {sz : ℕ} {adv : grade} {γ1 γ2 : List Term} {Γ1 Γ2 : Context sz}
                    -> (convertVal : {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r2 A ⟧v adv (Promote v1) (Promote v2))
                    -> ⟦ Γ1 ++ Γ2 ⟧Γ adv γ1 γ2 -> ⟦ Γ2 ⟧Γ adv γ1 γ2
binaryPlusElimRightΓ {{R}} {0} {adv} {[]} {[]} {Empty} {Empty} _ _ = tt
binaryPlusElimRightΓ {{R}} {0} {adv} {γ1} {γ2} {Empty} {Empty} _ p = p
binaryPlusElimRightΓ {{R}} {.(suc _)} {adv} {[]} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} _ ()
binaryPlusElimRightΓ {{R}} {.(suc _)} {adv} {[]} {x ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} _ ()
binaryPlusElimRightΓ {{R}} {.(suc _)} {adv} {x ∷ γ1} {[]} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} _ ()
binaryPlusElimRightΓ {{R}} {(suc s)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} convertVal2 (arg , rest)
      rewrite sym (sameTypes {s} {Γ1} {Γ2} {Ext (Γ1 ++ Γ2) (Grad A (r1 +R r2))} {A} {A'} {r1} {r2} refl) =
        convert2 {r1} {r2} {v1} {v2} {A} arg , binaryPlusElimRightΓ {s} {adv} {γ1} {γ2} {Γ1} {Γ2} convertVal2 rest
  where
    convert2 : {r1 r2 : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box r2 A ⟧e adv (Promote v1) (Promote v2)
    convert2 {r1} {r2} {v1} {v2} {A} arg v1' v2' v1redux' v2redux'
      rewrite trans (sym v1redux') (reduxProm {v1})
            | trans (sym v2redux') (reduxProm {v2}) = convertVal2 {r1} {r2} {adv} {v1} {v2} {A} (arg (Promote v1) ((Promote v2)) refl refl)

binaryPlusElimRightBox : {{R : Semiring}} {{R' : NonInterferingSemiring }} {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r2 A ⟧v adv (Promote v1) (Promote v2)
binaryPlusElimRightBox {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with (r1 +R r2) ≤d adv | r2 ≤d adv
... | no eqo  | yes eq' = ⊥-elim (eqo eq)
... | no eqo  | no eq'  = boxInterpBiunobs  eq' v1 v2 (binaryImpliesUnary {A} {v1} {v2} {adv} arg)
... | yes eqo | yes eq' = boxInterpBiobs   eq' v1 v2 arg
... | yes eqo | no eq'  = boxInterpBiunobs  eq' v1 v2 (binaryImpliesUnary {A} {v1} {v2} {adv} arg)
binaryPlusElimRightBox {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) =
   boxInterpBiunobs (decreasing+Inv' {r1} {r2} {adv} eq) v1 v2 argInterp

binaryPlusElimLeftBox : {{R : Semiring}} {{R' : NonInterferingSemiring}} {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)
binaryPlusElimLeftBox {{R}} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with r1 ≤d adv
... | no  eqo = boxInterpBiunobs eqo v1 v2 ((binaryImpliesUnary {A} {v1} {v2} {adv} arg))
... | yes eqo = boxInterpBiobs eqo v1 v2 arg
binaryPlusElimLeftBox {{R}} {{R'}} {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) = boxInterpBiunobs (decreasing+Inv {r1} {r2} {adv} eq) v1 v2 argInterp


convertValNISemiring : {{R : Semiring}} {{R' : NonInterferingSemiring}} {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)
convertValNISemiring {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs eq .v1 .v2 arg) with r1 ≤d adv
... | no  eqo = boxInterpBiunobs eqo v1 v2 ((binaryImpliesUnary {A} {v1} {v2} {adv} arg))
... | yes eqo = boxInterpBiobs eqo v1 v2 arg
convertValNISemiring {r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 argInterp) = boxInterpBiunobs (decreasing+Inv eq) v1 v2 argInterp

binaryTimesElimRightΓ : {{R : Semiring}} {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} {r adv : grade} ->
     (convertVal : {s : grade} {v1 : Term} {v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2))
   -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ ⟧Γ adv γ1 γ2
binaryTimesElimRightΓ {_} {[]} {[]} {Empty} {r} {adv} _ g = tt
binaryTimesElimRightΓ {suc n} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A s)} {r} {adv} convertVal (ass , g) =
    convertExp {s} {v1} {v2} {A} ass , binaryTimesElimRightΓ {n} {γ1} {γ2} {Γ} {r} {adv} convertVal g
  where
        convertExp : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧e adv (Promote v1) (Promote v2)
        convertExp {s} {v1} {v2} {A} arg1 v1' v2' v1redux' v2redux' rewrite trans (sym v1redux') (reduxProm {v1}) | trans (sym v2redux') (reduxProm {v2}) =
           convertVal  {s} {v1} {v2} {A} (arg1 (Promote v1) (Promote v2) refl refl)
binaryTimesElimRightΓ {_} {[]} {[]} {Ext Γ (Grad A r₁)} {r} {adv} _ ()
binaryTimesElimRightΓ {_} {[]} {x ∷ γ5} {Ext Γ (Grad A r₁)} {r} {adv} _ ()
binaryTimesElimRightΓ {_} {x ∷ γ4} {[]} {Ext Γ (Grad A r₁)} {r} {adv} _ ()

convertUnaryBox : {{R : Semiring}} {A : Type} {r s : grade} {t : Term} -> [ Box r A ]e (Promote t) -> [ Box s A ]e (Promote t)
convertUnaryBox pre v0 v0redux with pre v0 v0redux
... | boxInterpV e inner = boxInterpV e inner


unaryTimesElimRightΓ : {{R : Semiring}} {sz : ℕ} {γ1 : List Term} {Γ : Context sz} {r : grade}
   -> [ r · Γ ]Γ γ1 -> [ Γ ]Γ γ1
unaryTimesElimRightΓ ⦃ R ⦄ {.0} {[]} {Empty} {r} inp = tt
unaryTimesElimRightΓ ⦃ R ⦄ {.0} {x ∷ γ1} {Empty} {r} tt = tt
unaryTimesElimRightΓ ⦃ R ⦄ {.(suc _)} {[]} {Ext Γ (Grad A s)} {r} ()
unaryTimesElimRightΓ ⦃ R ⦄ {suc n} {x ∷ γ1} {Ext Γ (Grad A s)} {r} (ass , g) =
  convertUnaryBox ass , unaryTimesElimRightΓ {{R}} {n} {γ1} {Γ} {r} g
