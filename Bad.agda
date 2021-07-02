module Bad where

open import Data.List
open import GrCore
open import Levels
open import RelationalModel
open import Relation.Binary.PropositionalEquality
open import Levels
open import Data.Product
open import Data.Unit
open import Relation.Nullary

controlFlowAttackLevel : Ext Empty (Grad BoolTy Private) ⊢ If (Var 0) (Promote vtrue) (Promote vfalse) ∶ Box Public BoolTy
controlFlowAttackLevel = if {_} {Γ = Ext Empty (Grad BoolTy Private)}
              {Γ1 = Ext Empty (Grad BoolTy Private)}
              {Γ2 = Ext Empty (Grad BoolTy Unused)}
              {B = Box Public BoolTy}
              {_} {_} {_}
              {Private}
              {Refl Private}
         (var {0} {0} {BoolTy} {Γ = Ext Empty (Grad BoolTy Private)} {Γ1 = Empty} {Γ2 = Empty} refl)
         (pr {_} {Ext Empty (Grad BoolTy Unused)} {Ext Empty (Grad BoolTy Unused)} {Public} {BoolTy} {_}
               (trueConstr {_} {Ext Empty (Grad BoolTy Unused)}) {refl})
         (pr {_} {Ext Empty (Grad BoolTy Unused)} {Ext Empty (Grad BoolTy Unused)} {Public} {BoolTy} {_}
               (falseConstr {_} {Ext Empty (Grad BoolTy Unused)}) {refl})
         {refl}

noLeakWitness : ¬ (Order Public Private)
noLeakWitness with Private ≤d Public
... | yes ()
... | no ¬p = ¬p

test : ⟦ Box Public BoolTy ⟧v Public (Promote vtrue) (Promote vfalse)
test = biFundamentalTheorem controlFlowAttackLevel {vtrue ∷ []} {vfalse ∷ []} Public (arg , tt) (Promote vtrue) (Promote vfalse) red1 red2
 where
   argi1 : [ BoolTy ]e vtrue
   argi1 v x rewrite trans (sym x) (valuesDontReduce trueValue) = boolInterpTrue

   argi2 : [ BoolTy ]e vfalse
   argi2 v x rewrite trans (sym x) (valuesDontReduce falseValue) = boolInterpFalse

   argV : ⟦ Box Private BoolTy ⟧v Public (Promote vtrue) (Promote vfalse)
   argV = boxInterpBiunobs noLeakWitness vtrue vfalse (argi1 , argi2)

   arg : ⟦ Box Private BoolTy ⟧e Public (Promote vtrue) (Promote vfalse)
   arg v1 v2 v1redux v2redux
     rewrite trans (sym v1redux) (valuesDontReduce (promoteValue vtrue))
           | trans (sym v2redux) (valuesDontReduce (promoteValue vfalse))
           = argV

   red1 : multiRedux
      (multisubst (vtrue ∷ [])
       (If (Var 0) (Promote vtrue) (Promote vfalse)))
      ≡ Promote vtrue
   red1 = refl

   red2 : multiRedux
      (multisubst (vfalse ∷ [])
       (If (Var 0) (Promote vtrue) (Promote vfalse)))
      ≡ Promote vfalse
   red2 = refl

-------------------


open import Sec

-- Not typable
controlFlowAttackSec : Ext Empty (Grad BoolTy Hi) ⊢ If (Var 0) (Promote vtrue) (Promote vfalse) ∶ Box Lo BoolTy
controlFlowAttackSec = if {_} {Γ = Ext Empty (Grad BoolTy Hi)}
              {Γ1 = Ext Empty (Grad BoolTy {!!})} -- Needs to be Hi
              {Γ2 = Ext Empty (Grad BoolTy 0R)}
              {B = Box Lo BoolTy}
              {_} {_} {_}
              {Hi}
              {{!!}} -- wants Hi ≤ Lo  which is not possible
         (var {0} {0} {BoolTy} {Γ = Ext Empty (Grad BoolTy Lo)} {Γ1 = Empty} {Γ2 = Empty} refl)
         (pr {_} {Ext Empty (Grad BoolTy 0R)} {Ext Empty (Grad BoolTy 0R)} {Lo} {BoolTy} {_}
               (trueConstr {_} {Ext Empty (Grad BoolTy 0R)}) {refl})
         (pr {_} {Ext Empty (Grad BoolTy 0R)} {Ext Empty (Grad BoolTy 0R)} {Lo} {BoolTy} {_}
               (falseConstr {_} {Ext Empty (Grad BoolTy 0R)}) {refl})
         {refl}
