
{-# OPTIONS --allow-unsolved-metas #-}

module GrCoreGhost where

open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Maybe
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)

open import GrCore hiding (_⊢_∶_)


open import Semiring

-- open Semiring.Semiring {{...}} public

open Semiring.InformationFlowSemiring {{...}} public

ContextG : {{ R : Semiring }} -> ℕ -> Set
-- pair of context and grade for the ghost
ContextG sz = Context sz × grade

-- Disjoint context concatentation
_,,g_ : {{R : Semiring}} {s t : ℕ} -> ContextG s -> ContextG t -> ContextG (s + t)
(G , h) ,,g (G' , h') = (G ,, G' , h +R h')

-- Context scalar multiplication
_·g_ : {{R : Semiring}} {s : ℕ} -> grade -> ContextG s -> ContextG s
r ·g (G , r') = (G , r *R r')

-- Context addition
_++g_ : {{R : Semiring}} {s : ℕ} -> ContextG s -> ContextG s -> ContextG s
(G , r) ++g (G' , r') = (G ++ G' , r +R r')

Γlengthg : {{R : Semiring}} {s : ℕ} -> ContextG s -> ℕ
Γlengthg (G , _) = Γlength G

-- Typing
data _⊢_∶_ {{R : Semiring}} {{R' : InformationFlowSemiring R}} : {s : ℕ} -> ContextG s -> Term -> Type -> Set where

--  (x : A) ∈ Γ
----------------------------
--  Γ |- x : A

  var : {s1 s2 : ℕ}
        { A : Type }
        { Γ : ContextG ((1 + s1) + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        -- ghost 1R
        (pos : Γ ≡ (((Ext (0R · Γ1) (Grad A 1R)) ,, (0R · Γ2)) , 1R))
    ->  ---------------------
        Γ ⊢ Var (Γlength Γ1) ∶ A


  app : {s : ℕ}
        { Γ Γ1 Γ2 : ContextG s }
        { r : grade }
        { A B : Type}
        { t1 t2 : Term }

     ->   Γ1 ⊢ t1 ∶ FunTy A r B
     ->   Γ2 ⊢ t2 ∶ A
     ->   { Γ ≡ (Γ1 ++g (r ·g Γ2))}
     -> -----------------------------
          Γ ⊢ App t1 t2 ∶ B


  abs : {s1 s2 : ℕ}
        { Γ : ContextG ((1 + s1) + s2) }
        { Γ1 : Context s1 }
        { Γ2 : Context s2 }
        { Γ' : ContextG (s1 + s2) }
        { r ghost : grade }
        { A B : Type }
        { t : Term }

      -> (pos : Γ ≡ ((Ext Γ1 (Grad A r)) ,, Γ2 , ghost))
      -> Γ ⊢ t ∶ B
      -> { Γ' ≡ ((Γ1 ,, Γ2) , ghost)}
      -> --------------------------------------
         Γ' ⊢ Abs (Γlength Γ1 + 1) t ∶ FunTy A r B


  pr : {s : ℕ}
    -> { Γ Γ' : ContextG s }
    -> { r : grade }
    -> { A : Type }
    -> { t : Term }

    -> Γ ⊢ t ∶ A
    -> { Γ' ≡ r ·g Γ }
    --------------------------------
    -> Γ' ⊢ Promote t ∶ Box r A


  unitConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ , 1R) ⊢ unit ∶ Unit

  trueConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ , 1R) ⊢ vtrue ∶ BoolTy

  falseConstr : {s : ℕ} { Γ : Context s }
      -> --------------------------------
          (0R · Γ , 1R) ⊢ vfalse ∶ BoolTy

  if : {s : ℕ}
       { Γ Γ1 Γ2 : Context s }
       { ghost : grade }
       { B : Type }
       { t1 t2 t3 : Term }
       { r : grade }
       { used : r ≤ 1R }

    -> (Γ1 , ghost) ⊢ t1 ∶ BoolTy
    -> (Γ2 , (r # ghost)) ⊢ t2 ∶ B
    -> (Γ2 , (r # ghost)) ⊢ t3 ∶ B
    -> { res : ((r · Γ1) ++ Γ2) ≡ Γ }
   ----------------------------------
    -> (Γ , ghost) ⊢ If t1 t2 t3 ∶ B

substitutionG : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {s1 s2 : ℕ} {Γ : Context ((1 + s1) + s2)} {Γ1 : Context s1} {Γ2 : Context (s1 + s2)} {Γ3 : Context s2} {ghost1 ghost2 : grade} {r : grade} {A B : Type} {t1 t2 : Term}
      -> (Γ , ghost1) ⊢ t1 ∶ B
      -> (pos : Γ ≡ (Ext (0R · Γ1) (Grad A r)) ,, (0R · Γ3))
      -> (Γ2 , ghost2) ⊢ t2 ∶ A
      -> (((Γ1 ,, Γ3) ++ (r · Γ2)) , ghost1 +R (r *R ghost2)) ⊢ syntacticSubst t2 (Γlength Γ1) t1 ∶ B
substitutionG =  {!!}

multiReduxProducesValuesG : {{R : Semiring}} {{R' :  InformationFlowSemiring R}} {A : Type} {t : Term} {r : grade} -> (Empty , r) ⊢ t ∶ A -> Value (multiRedux t)
multiReduxProducesValuesG = {!!}

preservationG : {{R : Semiring}} {{R' :  InformationFlowSemiring R}} {s : ℕ} {Γ : Context s} {A : Type} {t : Term} {gr : grade}
             -> (Γ , gr) ⊢ t ∶ A
             -> (Γ , gr) ⊢ multiRedux t ∶ A
preservationG = {!!}
