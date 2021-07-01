module Other where

open import GrCore
open import Semiring
open import RelationalModel

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty

open import Sec hiding (_≤_ ; _+R_ ; _*R_ ; propInvTimesMonoAsym ; propertyConditionalNI; propertyConditionalNI2 ; plusMonoInv)

-------------------------------------
-- Theorems that definitely cannot hold
-- (as a reminder to myself)

noUnarySplitToBinary : ({A : Type} {t1 t2 : Term} {adv : Sec}
                    -> [ A ]e t1 × [ A ]e t2 -> ⟦ A ⟧e adv t1 t2)
                    -> ⊥
noUnarySplitToBinary theorem =
  let instance
        seca : Semiring
        seca = secSemiring
  in use
  where
    left : [ BoolTy ]e vfalse
    left v0 v0redux rewrite trans (sym v0redux) reduxFalse = boolInterpFalse

    right : [ BoolTy ]e vtrue
    right v0 v0redux rewrite trans (sym v0redux) reduxTrue = boolInterpTrue

    apply : ⟦ BoolTy ⟧e Lo vfalse vtrue
    apply = theorem {BoolTy} {vfalse} {vtrue} {Lo} (left , right)

    use : ⊥
    use with apply vfalse vtrue refl refl
    ... | ()
