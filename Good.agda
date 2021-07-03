module Good where

open import Data.List
open import GrCore hiding (_⊢_∶_)
open import GrCoreGhost
open import Levels
open import RelationalModel
open import Relation.Binary.PropositionalEquality
open import Levels
open import Data.Product
open import Data.Unit
open import Relation.Nullary

open import Level

-- Not typeable and that's good!
controlFlowAttackLevel : ((Ext Empty (Grad BoolTy Private)) , Private) ⊢ If (Var 0) (Promote vtrue) (Promote vfalse) ∶ Box Public BoolTy
controlFlowAttackLevel = if {_} {Γ = Ext Empty (Grad BoolTy Private)}
              {Γ1 = Ext Empty (Grad BoolTy Private)}
              {Γ2 = Ext Empty (Grad BoolTy Unused)}
              {ghost = Private}
              {B = Box Public BoolTy}
              {_} {_} {_}
              {Private}
              {Refl Private}
         (var {0} {0} {BoolTy} {Γ = ((Ext Empty (Grad BoolTy Private)) , 1R)} {Γ1 = Empty} {Γ2 = Empty} refl)
         (pr {_} {(Ext Empty (Grad BoolTy Unused)) , ?} {((Ext Empty (Grad BoolTy Unused)) , ?)} {Public} {BoolTy} {_}
               (trueConstr {_} {Ext Empty (Grad BoolTy Unused)}) {refl})
         (pr {_} {(Ext Empty (Grad BoolTy Unused)) , ?} {((Ext Empty (Grad BoolTy Unused)) , ?)} {Public} {BoolTy} {_}
               (falseConstr {_} {Ext Empty (Grad BoolTy Unused)}) {refl})
         {refl}
