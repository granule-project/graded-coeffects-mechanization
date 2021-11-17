{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --inversion-max-depth=100 #-}

module RelationalModelGhostAlt where

open import GrCore hiding (_⊢_∶_)
open import GrCoreGhost

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
open import Data.Maybe.Properties

open import Semiring

-- open Semiring.Semiring {{...}} public
-- open NonInterferingSemiring  {{...}} public
-- open InformationFlowSemiring {{...}} public

open import RelationalModel
open ≡-Reasoning

-- # Helpers

injPair1 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> a ≡ a'
injPair1 refl = refl

injPair2 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> b ≡ b'
injPair2 refl = refl

-- # Derived properties

rearrange : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {r s g' : grade} -> ((r *R s) *R g') ≡ ((r *R (s *R g')) *R s)
rearrange {{R}} {{R'}} {r} {s} {g'} =
          begin
            (r *R s) *R g'
          ≡⟨ cong (λ h → (r *R h) *R g') (sym (idem* R' {s})) ⟩
            (r *R (s *R s)) *R g'
          ≡⟨  assoc* {r} {s *R s} {g'} ⟩
            r *R ((s *R s) *R g')
          ≡⟨ cong (\h -> r *R h) (assoc* {s} {s} {g'}) ⟩
            r *R (s *R (s *R g'))
          ≡⟨ cong (\h -> r *R (s *R h)) (com* {R} {s} {g'} ) ⟩
            r *R (s *R (g' *R s))
          ≡⟨ cong (\h -> r *R h) (sym (assoc* {s} {g'} {s}))  ⟩
            r *R ((s *R g') *R s)
          ≡⟨ sym (assoc* {r} {s *R g'} {s})  ⟩
            (r *R (s *R g')) *R s
          ∎

-- Contexts

-- unary
-- [_]Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> List Term -> Set
-- [ (Γ , ghostGrade) ]Γg γ = [ Γ ]Γ γ

-- binary
data ⟦_⟧Γg {{R : Semiring}} : {s : ℕ} -> ContextG s -> (adv : grade) -> List Term -> List Term -> Set where
    visible : {sz : ℕ} {Γ : Context sz} {ghost adv : grade} {γ1 γ2 : List Term}
            -> ghost ≤ adv -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2

    invisible : {sz : ℕ} {Γ : Context sz} {ghost adv : grade} {γ1 γ2 : List Term}
            -> ¬ (ghost ≤ adv) -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2 -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2



unpackObs : {{R : Semiring}} {A : Type} {v1 v2 : Term} {r adv : grade}
          -> (r ≤ adv)
          -> ⟦ Box r A ⟧e adv (Promote v1) (Promote v2) -> ⟦ A ⟧e adv v1 v2
unpackObs {A} {v1} {v2} {r} {adv} pre inner v1' v2' v1redux v2redux with inner (Promote v1) (Promote v2) refl refl
... | (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp v1' v2' v1redux v2redux
... | (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq pre)

unpackUnobs : {{R : Semiring}} {A : Type} {v1 v2 : Term} {r adv : grade}
          -> ¬ (r ≤ adv)
          -> ⟦ Box r A ⟧v adv (Promote v1) (Promote v2) -> ([ A ]e v1 × [ A ]e v2)
unpackUnobs {A} {v1} {v2} {r} {adv} pre (boxInterpBiobs eq .v1 .v2 innerExprInterp) = ⊥-elim (pre eq)
unpackUnobs {A} {v1} {v2} {r} {adv} pre (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = innerExprInterp

justInj : {A : Set} {a1 a2 : A} -> just a1 ≡ just a2 -> a1 ≡ a2
justInj {A} {a1} {.a1} refl = refl


binaryImpliesUnaryGg : {{R : Semiring}} {sz : ℕ} { Γ : Context sz } {adv : grade} {γ1 γ2 : List Term}
                    -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ([ Γ ]Γ γ1) × ([ Γ ]Γ γ2)
binaryImpliesUnaryGg {.0} {Empty} {adv} {_} {_} pre = tt , tt
binaryImpliesUnaryGg {suc sz} {Ext Γ (Grad A r)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} (arg , rest)
  with binaryImpliesUnary {Box r A} {Promote v1} {Promote v2} {adv} arg | binaryImpliesUnaryG {sz} {Γ} {adv} {γ1} {γ2} rest
... | ( arg1 , arg2 ) | ( rest1 , rest2 ) = ( (arg1 , rest1) , (arg2 , rest2) )

postulate
  multiSubstTyG : {{R : Semiring}} {{R' : InformationFlowSemiring R }} -> {n : ℕ} {Γ : ContextG n} {t : Term} {A : Type} {γ : List Term} {ghost : grade} -> Γ ⊢ t ∶ A -> (Empty , ghost) ⊢ multisubst' 0 γ t ∶ A

  reduxTheoremAppTyG : {{R : Semiring}} {{R' : InformationFlowSemiring R }}
                 -> {t1 t2 v : Term} {s : ℕ} {Γ : Context s} {A B : Type} {r : grade} {ghost : grade}
                 -> multiRedux (App t1 t2) ≡ v
                 -> (Γ , ghost) ⊢ t1 ∶ FunTy A r B
                 -> Σ (ℕ × Term) (\(z , v1') -> multiRedux t1 ≡ Abs z v1' × (((Ext Γ (Grad A r)) , ghost) ⊢ (Abs z v1') ∶  B))

  multireduxPromoteLemma :
    {{ R : Semiring }}
    {adv r : grade}
    {τ : Type}
    {t1 t2 : Term}
    -> ⟦ Box r τ ⟧e adv t1 t2
    -> Σ (Term × Term) (\(v1 , v2) -> multiRedux t1 ≡ Promote v1 × multiRedux t2 ≡ Promote v2)


promoteLemma : {t t' t'' : Term} -> Promote t ≡ t' -> Σ Term (\t'' -> Promote t'' ≡ t')
promoteLemma {t} {t'} {t''} pre = t , pre

extractUn : {{R : Semiring}} {r : grade} {A : Type} {v : Term} -> [ Box r A ]e (Promote v) -> [ A ]e v
extractUn {r} {A} {v} ab v1 v1redux with ab (Promote v) refl
... | boxInterpV _ inner = inner v1 v1redux

utheoremG : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {s : ℕ} {γ : List Term}
        -> {Γ : Context s} {ghost : grade} {e : Term} {τ : Type}
        -> (Γ , ghost) ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ τ ]e (multisubst γ e)
utheoremG = {!!}


-- under some constraints perhaps
-- unaryImpliesBinarySpecialised : {e : Term} {τ : Type}
--  ⟦ τ ⟧e t

-- Probably going to delete this
sameContext : {{R : Semiring}}
              {sz : ℕ} {Γ : Context sz}
              {s adv : grade}
              {γ1 γ2 : List Term}
            -> ⟦ s · Γ ⟧Γ adv γ1 γ2
            -> (s ≤ adv)
            -> γ1 ≡ γ2
sameContext ⦃ R ⦄ {.0} {Empty} {s} {adv} {[]} {[]} ctxt pre = refl
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ x} {s} {adv} {[]} {[]} ctxt pre = refl
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ (Grad A r)} {s} {adv} {[]} {x₁ ∷ γ2} () pre
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ (Grad A r)} {s} {adv} {x₁ ∷ γ1} {[]} () pre
sameContext ⦃ R ⦄ {.(suc _)} {Ext Γ (Grad A r)} {s} {adv} {x₁ ∷ γ1} {x₂ ∷ γ2} (ctxtHd , ctxtTl) pre
 with s · (Ext Γ (Grad A r)) | ctxtHd (Promote x₁) (Promote x₂) refl refl
... | Ext sΓ (Grad A' sr) | boxInterpBiobs pre2 .x₁ .x₂ inner = {!!}
... | Ext sΓ (Grad A' sr) | boxInterpBiunobs pre2 .x₁ .x₂ inner = {!!}

{-
equalUnderSubst : {{R : Semiring}}
              {sz : ℕ} {Γ : Context sz} {e : Term} {τ : Type}
              {s adv : grade}
              {γ1 γ2 : List Term}
            -> ⟦ s · Γ ⟧Γ adv γ1 γ2
            -> Γ ⊢ e ∶ τ
            -> (s ≤ adv)
            -> multisubst γ1 e ≡ multisubst γ2 e
equalUnderSubst = ?
-}

deltaU : {{R : Semiring}} {t : Term} {r s : grade} {A : Type}
       -> [ Box (r *R s) A ]e (Promote t)
       -> [ Box r (Box s A) ]e (Promote (Promote t))
deltaU = {!!}

delta : {{R : Semiring}}
        {adv r s : grade}
        {t1 t2 : Term}
        {τ : Type}
      -> ⟦ Box (s *R r) τ ⟧v adv (Promote t1) (Promote t2)
      -> ⟦ Box s (Box r τ) ⟧v adv (Promote (Promote t1)) (Promote (Promote t2))

delta ⦃ R ⦄ {adv} {r} {s} {t1} {t2} {τ} (boxInterpBiobs pre .t1 .t2 inpInner)
  with s ≤d adv | r ≤d adv
... | yes p1 | yes p2 = boxInterpBiobs p1 (Promote t1) (Promote t2) inner
  where
    inner : ⟦ Box r τ ⟧e adv (Promote t1) (Promote t2)
    inner v1 v2 v1redux v2redux
     rewrite (sym v1redux) | (sym v2redux) =
       boxInterpBiobs p2 t1 t2 inpInner

... | yes p1 | no ¬p2 = boxInterpBiobs p1 (Promote t1) (Promote t2) {!!}
  where
    innerInp : [ τ ]v t1 × [ τ ]v t2
    innerInp = {!!}

    inner : ⟦ Box r τ ⟧e adv (Promote t1) (Promote t2)
    inner v1 v2 v1redux v2redux
      rewrite (sym v1redux) | (sym v2redux) =
        boxInterpBiunobs ¬p2 t1 t2 {!!}


... | no ¬p1 | yes p2 =
  boxInterpBiunobs ¬p1 (Promote t1) (Promote t2) ({!!} , {!!})

... | no ¬p1 | no ¬p2 = {!!}

delta ⦃ R ⦄ {adv} {r} {s} {t1} {t2} {τ} (boxInterpBiunobs pre .t1 .t2 inpInner) = {!!}

{-
delta {{R}} {adv} {r} {s} {t1} {t2} {τ} inp with s ≤d adv | r ≤d adv | (s *R r) ≤d adv
delta ⦃ R ⦄ {adv} {r} {s} {t1} {t2} {τ} (boxInterpBiobs pre .t1 .t2 inpInner) | yes p1 | yes p2 | yes p3 =
   boxInterpBiobs p1 (Promote t1) (Promote t2) inner
  where
   inner : ⟦ Box r τ ⟧e adv (Promote t1) (Promote t2)
   inner v1 v2 v1redux v2redux
     rewrite (sym v1redux) | (sym v2redux) =
       boxInterpBiobs p2 t1 t2 inpInner

delta ⦃ R ⦄ {adv} {r} {s} {t1} {t2} {τ} (boxInterpBiunobs pre .t1 .t2 x₁) | yes p1 | yes p2 | yes p3 =
  ⊥-elim (pre p3)

... | yes p1 | yes p2 | no ¬p3 =
  {!!}

... | yes p1 | no ¬p2 | yes p3 = {!!}
... | yes p1 | no ¬p2 | no ¬p3 = {!!}
... | no ¬p1 | yes p2 | yes p3 = {!!}
... | no ¬p1 | yes p2 | no ¬p3 = {!!}
... | no ¬p1 | no ¬p2 | yes p3 = {!!}
... | no ¬p1 | no ¬p2 | no ¬p3 = {!!}
-}

-- elimInversion

convertValL+ : {{R : Semiring}} {{R' : InformationFlowSemiring R}}
             -> {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r1 A ⟧v adv (Promote v1) (Promote v2)
convertValL+ {r1 = r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs pre .v1 .v2 inner)   with r1 ≤d adv
... | yes p = boxInterpBiobs p v1 v2 inner
... | no ¬p = boxInterpBiunobs ¬p v1 v2 (binaryImpliesUnary {A} {v1} {v2} {adv} inner)
convertValL+ {{R}} {{R'}} {r1 = r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs pre .v1 .v2 inner) = boxInterpBiunobs (\eq -> pre (decreasing+NF eq)) v1 v2 inner

convertValR+ : {{R : Semiring}} {{R' : InformationFlowSemiring R}}
             -> {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r1 +R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r2 A ⟧v adv (Promote v1) (Promote v2)
convertValR+ {r1 = r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiobs pre .v1 .v2 inner)   with r2 ≤d adv
... | yes p = boxInterpBiobs p v1 v2 inner
... | no ¬p = boxInterpBiunobs ¬p v1 v2 (binaryImpliesUnary {A} {v1} {v2} {adv} inner)
convertValR+ {{R}} {{R'}} {r1 = r1} {r2} {adv} {v1} {v2} {A} (boxInterpBiunobs pre .v1 .v2 inner) =
  boxInterpBiunobs (\pre' -> pre (decreasing+NFSym pre')) v1 v2 inner

contextSplitLeft : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {sz : ℕ} {Γ1 Γ2 : ContextG sz} {γ1 γ2 : List Term} {adv : grade}
                   -> ⟦ Γ1 ++g Γ2 ⟧Γg adv γ1 γ2 -> ⟦ Γ1 ⟧Γg adv γ1 γ2
contextSplitLeft {{R}} {{R'}} {sz = sz} {Γ1 , g1} {Γ2 , g2} {γ1} {γ2} {adv} (visible pre inner) with g1 ≤d adv
... | yes p = visible p (binaryPlusElimLeftΓ convertValL+ inner)
... | no ¬p = invisible ¬p (binaryImpliesUnaryG (binaryPlusElimLeftΓ convertValL+ inner)) -- okay because we can do binaryImpliesUnary
contextSplitLeft {{R}} {{R'}} {sz = sz} {Γ1 , g1} {Γ2 , g2} {γ1} {γ2} {adv} (invisible pre inner) with g1 ≤d adv
... | yes p = ⊥-elim (pre (decreasing+NF p))
... | no ¬p = invisible ¬p (unaryPlusElimLeftΓ (proj₁ inner) , unaryPlusElimLeftΓ (proj₂ inner))

contextSplitRight : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {sz : ℕ} {Γ1 Γ2 : ContextG sz} {γ1 γ2 : List Term} {adv : grade}
                    -> ⟦ Γ1 ++g Γ2 ⟧Γg adv γ1 γ2 -> ⟦ Γ2 ⟧Γg adv γ1 γ2
contextSplitRight {{R}} {{R'}} {sz = sz} {Γ1 , g1} {Γ2 , g2} {γ1} {γ2} {adv} (visible pre inner) with g2 ≤d adv
... | yes p = visible p (binaryPlusElimRightΓ convertValR+ inner)
... | no ¬p = invisible ¬p (binaryImpliesUnaryG (binaryPlusElimRightΓ convertValR+ inner))
contextSplitRight {{R}} {{R'}} {sz = sz} {Γ1 , g1} {Γ2 , g2} {γ1} {γ2} {adv} (invisible pre inner) with g2 ≤d adv
... | yes p = ⊥-elim (pre (decreasing+NFSym p))
... | no ¬p = invisible ¬p ((unaryPlusElimRightΓ (proj₁ inner)) , (unaryPlusElimRightΓ (proj₂ inner)))


convertValR* : {{R : Semiring}} {{R' : InformationFlowSemiring R}}
            -> {r1 r2 adv : grade} {v1 v2 : Term} {A : Type} -> (r1 ≤ adv) -> ⟦ Box (r1 *R r2) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box r2 A ⟧v adv (Promote v1) (Promote v2)
convertValR* {r1 = r1} {r2} {adv} {v1} {v2} {A} preA (boxInterpBiobs pre .v1 .v2 inner)   with r2 ≤d adv
... | yes p = boxInterpBiobs p v1 v2 inner
... | no ¬p = boxInterpBiunobs ¬p v1 v2 (binaryImpliesUnary {A} {v1} {v2} {adv} inner)
convertValR* {{R}} {{R'}} {r1 = r1} {r2} {adv} {v1} {v2} {A} preA (boxInterpBiunobs pre .v1 .v2 inner) =
  boxInterpBiunobs (\preB -> pre (subst (\h -> (r1 *R r2) ≤ h) (idem* R' {adv}) (monotone* preA preB))) v1 v2 inner

contextElimTimesAlt : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {sz : ℕ} {Γ1 : ContextG sz} {γ1 γ2 : List Term} {r adv : grade}
                    -> (r ≤ adv) -> ⟦ r ·g Γ1 ⟧Γg adv γ1 γ2 -> ⟦ Γ1 ⟧Γg adv γ1 γ2
contextElimTimesAlt {{R}} {{R'}} {sz = sz} {Γ1 , g1} {γ1} {γ2} {r} {adv} pre0 (visible pre inner) with g1 ≤d adv
... | yes p = visible p (binaryTimesElimRightΓ (convertValR* pre0) inner)
... | no ¬p = invisible ¬p (binaryImpliesUnaryG (binaryTimesElimRightΓ (convertValR* pre0) inner))
contextElimTimesAlt {{R}} {{R'}} {sz = sz} {Γ1 , g1} {γ1} {γ2} {r} {adv} pre0 (invisible pre inner) with g1 ≤d adv
... | yes p rewrite com* {R} {r} {g1} = ⊥-elim (pre (subst (\h -> (g1 *R r) ≤ h) (idem* R' {adv}) (monotone* p pre0)))
... | no ¬p = invisible ¬p ((unaryTimesElimRightΓ (proj₁ inner)) , (unaryTimesElimRightΓ (proj₂ inner)))

promoteUnary : {{R : Semiring}} {A : Type} {r : grade} {e : Term} -> [ A ]e e -> [ Box r A ]e (Promote e)
promoteUnary {_} {_} {e} inp v1 v1redux rewrite sym v1redux = boxInterpV e inp

promoteUnaryPair : {{R : Semiring}} {A : Type} {r : grade} {e e' : Term} -> ([ A ]e e × [ A ]e e') -> ([ Box r A ]e (Promote e)) × ([ Box r A ]e (Promote e'))
promoteUnaryPair {_} {_} {e} (u1 , u2) = (promoteUnary u1 , promoteUnary u2)

promoteInj : {t1 t2 : Term} -> Promote t1 ≡ Promote t2 -> t1 ≡ t2
promoteInj {t1} {.t1} refl = refl

contextElimTimesUnaryUnary : {{R : Semiring}} {sz : ℕ} {γ1 : List Term} {Γ : Context sz} {r adv : grade}
                        -> [ r · Γ ]Γ γ1 -> [ Γ ]Γ γ1
contextElimTimesUnaryUnary {.0} {[]} {Empty} inp = tt
contextElimTimesUnaryUnary {sz = .(1 + _)} {[]} {Ext Γ (Grad A s)} ()
contextElimTimesUnaryUnary {.0} {x ∷ γ1} {Empty} inp = tt
contextElimTimesUnaryUnary {.(1 + _)} {x ∷ γ1} {Ext Γ (Grad A s)} (head , rest) =
  convertUnaryBox head , contextElimTimesUnaryUnary rest

contextElimTimesToUnary' : {{R : Semiring}} {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} {r adv : grade}
                        -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2
contextElimTimesToUnary' {_} {_} {_} {Empty} g = (tt , tt)
contextElimTimesToUnary' {_} {[]} {[]} {Ext Γ (Grad A r)} ()
contextElimTimesToUnary' {_} {[]} {x ∷ γ2} {Ext Γ (Grad A r)} ()
contextElimTimesToUnary' {_} {x ∷ γ1} {[]} {Ext Γ (Grad A r)} ()
contextElimTimesToUnary' {suc sz} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A r')} (arg , g) =
         let
          (left , right) = contextElimTimesToUnary' {sz} {γ1} {γ2} {Γ} g
          (lA , rA) = binaryImpliesUnary arg
          l = convertUnaryBox lA
          r = convertUnaryBox rA
         in
           (l , left) , (r , right)

contextElimTimesToUnary : {{R : Semiring}} {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} {r g adv : grade}
                      -> ⟦ r ·g (Γ , g) ⟧Γg adv γ1 γ2 -> [ Γ ]Γ γ1 × [ Γ ]Γ γ2
contextElimTimesToUnary (visible x inner)   = contextElimTimesToUnary' inner
contextElimTimesToUnary (invisible x (innerLeft , innerRight)) = (contextElimTimesUnaryUnary innerLeft , contextElimTimesUnaryUnary innerRight)


mutual


    intermediateSub : {{R : Semiring}} {{R' : InformationFlowSemiring R}}  {sz : ℕ}
                  {Γ : Context sz}
                  {ghost r adv : grade}
                  {γ1 γ2 : List Term}
                  {e : Term}
                  {A : Type}
               -> (Γ , ghost) ⊢ e ∶ A
               -> r ≤ adv
               -> ⟦ r ·g (Γ , ghost) ⟧Γg adv γ1 γ2
               -> [ Box (r *R ghost) A ]e (Promote (multisubst γ1 e))
               -> [ Box (r *R ghost) A ]e (Promote (multisubst γ2 e))
               -> ⟦ Box (r *R ghost) A ⟧e adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))
    intermediateSub {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {e} {A} typ pre context u1 u2 v1 v2 v1redux v2redux with typ

    -- ### Var case
    intermediateSub {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {e} {A} typ pre context u1 u2 v1 v2 v1redux v2redux
      | (var {Γ1 = Empty} {Γ2} pos) with γ1 | γ2
    intermediateSub {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {e} {A} typ pre context u1 u2 v1 v2 v1redux v2redux
      | (var {Γ1 = Empty} {Γ2} pos) | a1 ∷ γ1' | a2 ∷ γ2' rewrite (injPair1 pos) with context | r · Γ


     -- Case where
    --  (x : A, ghost) ⊢ x : A
    intermediateSub {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {.(Var 0)} {A} typ pre context u1 u2 v1 v2 v1redux v2redux
      | (var {Γ1 = Empty} {Γ2} pos) | a1 ∷ γ1' | a2 ∷ γ2' | visible pre2 (arg , _) | Ext ad (Grad A' r₁)
         rewrite sym v1redux | sym v2redux | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} = conc
        where
          conc : ⟦ Box (r *R ghost) A ⟧v adv (Promote a1) (Promote a2)
          conc with arg (Promote a1) (Promote a2) refl refl
          ... | boxInterpBiobs _ .a1 .a2 argInner = boxInterpBiobs pre2 a1 a2 argInner

          ... | boxInterpBiunobs preN .a1 .a2 argInner = ⊥-elim (preN (transitive≤ rightUnit* pre))
            -- Previous version when we had equalities
            -- ⊥-elim ((subst (\h -> h ≤ adv -> ⊥) rightUnit* preN) pre)

       -- Here we have that `r ≤ adv` but `¬ ((r * ghost) ≤ adv)`
    -- ah but we also know that `ghost = 1` so ... we get a contradiction
    intermediateSub {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {e} {A} typ pre context u1 u2 v1 v2 v1redux v2redux
      | (var {Γ1 = Empty} {Γ2} pos) | a1 ∷ γ1' | a2 ∷ γ2' | invisible pre2 inner | Ext ad x =
        -- ⊥-elim (pre2 (subst (\h -> (r *R ghost) ≤ h) (idem* R' {adv}) (monotone* pre {!!}) ))
        ⊥-elim (pre2 (timesLeft pre))

    intermediateSub {{R}} {{R'}} {Γ = Γ} {ghost} {r} {adv} {γ1} {γ2} {.(Var _)} {A} typ pre context u1 u2 v1 v2 v1redux v2redux
     | (var {Γ1 = _} {Γ2} pos) =
      {!!} -- generalises the above, skipping for simplicity (just apply exchange basically)

    -- ### App case
    intermediateSub {sz = sz} {Γ = Γ} {ghost} {r} {adv} {γ1} {γ2} {.(App t1 t2)} {.B} typ pre context u1 u2 v1 v2 v1redux v2redux
     | (app {Γ1 = (Γ1 , g1)} {Γ2 = (Γ2 , g2)} {s} {A} {B} {t1} {t2} typ1 typ2 {ctxtP}) rewrite sym v1redux | sym v2redux =
     {!!}

{- -- Done but temporarily redacted from here
       let

        ih1 = biFundamentalTheoremGhost typ1 adv subContext1bi
        ih2 = biFundamentalTheoremGhost (pr {sz} {(Γ2 , g2)} {r = s} typ2) adv subContext2bi
       in goal ih1 ih2
         where

           context' : ⟦ (r ·g (Γ1 , g1)) ++g (r ·g (s ·g (Γ2 , g2))) ⟧Γg adv γ1 γ2
           context' = subst (\h -> ⟦ h ⟧Γg adv γ1 γ2) (trans (cong (_·g_ r) ctxtP) Γg-distrib*+) context

           subContext1bi : ⟦ ( Γ1 ,  g1) ⟧Γg adv γ1 γ2
           subContext1bi = contextElimTimesAlt pre (contextSplitLeft context')

           subContext2bi : ⟦ s ·g ( Γ2 , g2) ⟧Γg adv γ1 γ2
           subContext2bi = contextElimTimesAlt pre (contextSplitRight context')


           applyFun : {x y : ℕ} {ta ta' bodyt bodyt' v1 v2 : Term}
             -> ⟦ FunTy A s B ⟧v adv (Abs x bodyt) (Abs y bodyt')
             -> ⟦ Box s A ⟧e adv (Promote ta) (Promote ta')
             -> multiRedux (syntacticSubst ta x bodyt) ≡ v1
             -> multiRedux (syntacticSubst ta' y bodyt') ≡ v2
             -> ⟦ B ⟧v adv v1 v2
           applyFun {x} {y} {ta} {ta'} {bodyt} {bodyt'} {v1} {v2} fun arg v1redux' v2redux' with fun
           ... | funInterpBi {adv} {A} {B} {r} {x'} {y'} e1 e2 bodyBi bodyUn1 bodyUni2 =
             let
               bodySubst = bodyBi ta ta' arg
               result = bodySubst v1 v2 v1redux' v2redux'
             in result

           innerGoal : ⟦ FunTy A s B ⟧e adv (multisubst γ1 t1) (multisubst γ2 t1)
                   ->  ⟦ Box s A ⟧e adv (multisubst γ1 (Promote t2)) (multisubst γ2 (Promote t2))
                   ->  ⟦ B ⟧e adv (multisubst γ1 (App t1 t2)) (multisubst γ2 (App t1 t2))
           innerGoal funIn argIn v1a v2a v1aredux v2aredux =
            let
                v1redux' = trans (sym (cong multiRedux (substPresApp {0} {γ1} {t1} {t2}))) v1aredux
                ((x , t) , (funRed , substRed)) = reduxTheoremAll {multisubst γ1 t1} {multisubst γ1 t2} {v1a} v1redux'

                v2redux' = trans (sym (cong multiRedux (substPresApp {0} {γ2} {t1} {t2}))) v2aredux
                ((x' , t') , (funRed' , substRed')) = reduxTheoremAll {multisubst γ2 t1} {multisubst γ2 t2} {v2a} v2redux'

                body = funIn (Abs x t) (Abs x' t') funRed funRed'
                argument = subst₂ (\h1 h2 -> ⟦ Box s A ⟧e adv h1 h2) (substPresProm {0} {γ1} {t2}) (substPresProm {0} {γ2} {t2}) argIn

            in applyFun body argument substRed substRed'

           applyFunUnary : {x : ℕ} {ta bodyt v1 : Term}
             -> [ FunTy A s B ]v (Abs x bodyt)
             -> [ Box s A ]e (Promote ta)
             -> multiRedux (syntacticSubst ta x bodyt) ≡ v1
             -> [ B ]v v1
           applyFunUnary {x} {ta} {bodyt} {v1} fun arg v1redux' with fun
           ... | funInterpV {A} {B} {r} {x'} e1 body =
             let
               bodySubst = body ta  arg
               result = bodySubst v1 v1redux'
             in result

           innerGoalUnary : {γ : List Term} -> [ FunTy A s B ]e (multisubst γ t1)
                   ->  [ Box s A ]e (multisubst γ (Promote t2))
                   ->  [ B ]e (multisubst γ (App t1 t2))
           innerGoalUnary {γ} funIn argIn v1a v1aredux =
            let
                v1redux' = trans (sym (cong multiRedux (substPresApp {0} {γ} {t1} {t2}))) v1aredux
                ((x , t) , (funRed , substRed)) = reduxTheoremAll {multisubst γ t1} {multisubst γ t2} {v1a} v1redux'

                body = funIn (Abs x t) funRed
                argument = subst (\h1 -> [ Box s A ]e h1) (substPresProm {0} {γ} {t2}) argIn

            in applyFunUnary body argument substRed


           goal : ⟦ Box g1 (FunTy A s B) ⟧e adv (Promote (multisubst γ1 t1)) (Promote (multisubst γ2 t1))
               -> ⟦ Box (s *R g2) (Box s A) ⟧e adv (Promote (multisubst γ1 (Promote t2))) (Promote (multisubst γ2 (Promote t2)))
               -> ⟦ Box ghost B ⟧v adv (Promote (multisubst' 0 γ1 (App t1 t2))) (Promote (multisubst' 0 γ2 (App t1 t2)))
           goal inp1 inp2 with inp1 (Promote (multisubst γ1 t1)) (Promote (multisubst γ2 t1)) refl refl | inp2 (Promote (multisubst γ1 (Promote t2))) (Promote (multisubst γ2 (Promote t2))) refl refl
           ... | boxInterpBiobs pre1 _ _ inner1 | boxInterpBiobs pre2 _ _ inner2 =
               boxInterpBiobs p (multisubst γ1 (App t1 t2)) (multisubst γ2 (App t1 t2)) (innerGoal inner1 inner2)

           ... | boxInterpBiobs pre1 _ _ inner1 | boxInterpBiunobs pre2 _ _ inner2 =
             let
               (inner1a , inner1b) = binaryImpliesUnary inner1
               res1 = innerGoalUnary {γ1} inner1a (proj₁ inner2)
               res2 = innerGoalUnary {γ2} inner1b (proj₂ inner2)
               result = intermediateSub typ pre context (promoteUnary res1) (promoteUnary res2)
             in
               result (Promote (multisubst' zero γ1 (App t1 t2))) (Promote (multisubst' zero γ2 (App t1 t2))) refl refl

           ... | boxInterpBiunobs pre1 _ _ inner1 | boxInterpBiobs pre2 _ _ inner2 =
             let
               (inner2a , inner2b) = binaryImpliesUnary inner2
               res1 = innerGoalUnary {γ1} (proj₁ inner1) inner2a
               res2 = innerGoalUnary {γ2} (proj₂ inner1) inner2b
               result = intermediateSub typ pre context (promoteUnary res1) (promoteUnary res2)
             in
               result (Promote (multisubst' zero γ1 (App t1 t2))) (Promote (multisubst' zero γ2 (App t1 t2))) refl refl

           ... | boxInterpBiunobs pre1 _ _ inner1 | boxInterpBiunobs pre2 _ _ inner2 =
              let
                res1 = innerGoalUnary {γ1} (proj₁ inner1) (proj₁ inner2)
                res2 = innerGoalUnary {γ2} (proj₂ inner1) (proj₂ inner2)
                result = intermediateSub typ pre context (promoteUnary res1) (promoteUnary res2)
             in result (Promote (multisubst' zero γ1 (App t1 t2))) (Promote (multisubst' zero γ2 (App t1 t2))) refl refl
-}

    -- #### Abs case
    intermediateSub {{R}} {{R'}} {sz} {Γ = Γ} {ghost} {r} {adv} {γ1} {γ2}  {Abs .(Γlength Γ1 + 1) t} {FunTy A s B} typ pre context u1 u2 v1 v2 v1redux v2redux
     | (abs {_} {_} {Γbody  , gbody} {Γ1} {Γ2} {_} {.s} {g} {.A} {.B} {.t} pos typBody {pos2}) rewrite sym v1redux | sym v2redux =
         {-

         ((G1 ,, Grad A r ,, G2) , ghost) |- t : B
         -------------------------------------------
         (G1 ,, G2), ghost |- \x . t : A r -> B

         -}
         goal
        where

          ihcontextAlt : {t t' : Term} {γ1 γ2 : List Term}
                 -> ⟦ Box s A ⟧e adv (Promote t) (Promote t')
                 -> ⟦ ((Γ1 ,, Γ2) , ghost) ⟧Γg adv γ1 γ2 -> ⟦ (((Ext Γ1 (Grad A s)) ,, Γ2) , ghost) ⟧Γg adv (t ∷ γ1) (t' ∷ γ2)
          ihcontextAlt {t} {t'} {γ1} {γ2} inp ctxt with ctxt
          ... | visible pre' inner   = visible pre' (inp , inner)
          ... | invisible pre' (inner1 , inner2) =
            let
              (arg1 , arg2) = binaryImpliesUnary { Box s A } {Promote t} {Promote t'} {adv} inp
            in invisible pre' ((arg1 , inner1) , (arg2 , inner2))


          bodyContext : {v3 v4 : Term}
                     -> ⟦ ((Γ1 ,, Γ2) , ghost) ⟧Γg adv γ1 γ2
                     -> ⟦ Box s A ⟧e adv (Promote v3) (Promote v4)
                     -> ⟦ r ·g (Γbody , gbody) ⟧Γg adv (v3 ∷ γ1) (v4 ∷ γ2)
          bodyContext {v3} {v4} ctxt arg rewrite injPair1 pos | injPair2 pos with ctxt
          ... | visible pre'  inner = visible (timesLeft pre) ({!!} , {!inner!})
          ... | invisible pre' inner = {!!}

          bodyContextMain : ⟦ (Γ1 ,, Γ2) , ghost ⟧Γg adv γ1 γ2
          bodyContextMain rewrite injPair1 pos2 | injPair2 pos2 = contextElimTimesAlt pre context

          unwrap2 : {v3 v4 : Term}
                 -> ⟦ Box ((R Semiring.*R r) gbody) B ⟧e adv (Promote (multisubst (v3 ∷ γ1) t)) (Promote (multisubst (v4 ∷ γ2) t))
                 -> ⟦ B ⟧e adv (multisubst (v3 ∷ γ1) t) (multisubst (v4 ∷ γ2) t)
          unwrap2 inp with inp {!!} {!!}  refl refl
          ... | boxInterpBiobs preA _ _ inner   = inner
          ... | boxInterpBiunobs preA _ _ inner = ⊥-elim (preA (timesLeft pre))

          goalUInner : { γ1 : List Term }
                    -> [ Box ((R Semiring.*R r) ghost) (FunTy A s B) ]e (Promote (multisubst γ1 (Abs (Γlength Γ1 + 1) t)))
                    -> (v : Term)
                    -> [ Box s A ]e (Promote v)
                    -> [ B ]e (syntacticSubst v (Γlength Γ1 + 1) (multisubst γ1 t))
          goalUInner {γ1} fun v arg with fun (Promote (multisubst γ1 (Abs (Γlength Γ1 + 1) t))) refl
          ... | boxInterpV _ inner with subst (\h -> [ FunTy A s B ]e h) (substPresAbs {_} {γ1} {Γlength Γ1 + 1} {t}) inner (Abs (Γlength Γ1 + 1) (multisubst γ1 t)) refl
          ... | funInterpV _ body = body v arg

          goalUInner' : {v3 : Term} {γ1 : List Term}
           -> [ Box ((R Semiring.*R r) ghost) (FunTy A s B) ]e (Promote (multisubst γ1 (Abs (Γlength Γ1 + 1) t)))
           -> [ Box s A ]e (Promote v3)
           -> [ Box ((R Semiring.*R r) gbody) B ]e (Promote (multisubst (v3 ∷ γ1) t))
          goalUInner' {v3} {γ1} fun arg v0 v0redux =
            let result = goalUInner {γ1} fun v3 arg
                result' = subst (\h -> [ B ]e h) ((substitutionResult {{R}} {_} {v3} {γ1} {t} {Γ1})) result
            in subst (\h -> [ Box (r *R gbody) B ]v h) v0redux (boxInterpV (multisubst (v3 ∷ γ1) t) result')

          goalBiInner : ⟦ (Γ1 ,, Γ2) , ghost ⟧Γg adv γ1 γ2
                  -> (v3 v4 : Term) →
                  ⟦ Box s A ⟧e adv (Promote v3) (Promote v4) →
                  ⟦ B ⟧e adv (syntacticSubst v3 (Γlength Γ1 + 1) (multisubst γ1 t)) (syntacticSubst v4 (Γlength Γ1 + 1) (multisubst γ2 t))

          goalBiInner ctxt v3 v4 arg b1 b2 b1redux b2redux rewrite sym b1redux | sym b2redux = --  rewrite injPair1 pos2 | injPair2 pos2 =
           let
              --ctxt' = ihcontextAlt {v3} {v4} {γ1} {γ2} arg ctxt
              --ctxt2 = subst (\h -> ⟦ Ext (Γ1 ,, Γ2) (Grad A s) , h ⟧Γg adv (v3 ∷ γ1) (v4 ∷ γ2)) (injPair2 pos2) ctxt'

              --typBody' = subst₂ (\h1 h2 -> (h1 , h2) ⊢ t ∶ B) (injPair1 pos) (injPair2 pos) typBody
              --bih = biFundamentalTheoremGhost {{R}} {{R'}} {suc sz} {((Ext Γ1 (Grad A s)) ,, Γ2)} {g} {t} typBody' {v3 ∷ γ1} {v4 ∷ γ2} adv ctxt2

              (uarg1 , uarg2) = binaryImpliesUnary {{R}} {Box s A} {Promote v3} {Promote v4} {adv} arg
              iih = intermediateSub {γ1 = v3 ∷ γ1} {γ2 = v4 ∷ γ2} typBody pre (bodyContext {v3} {v4} ctxt arg) (goalUInner' {v3} {γ1} u1 uarg1) (goalUInner' {v4} {γ2} u2 uarg2)
              goala = unwrap2 iih (multiRedux (multisubst (v3 ∷ γ1) t)) (multiRedux (multisubst (v4 ∷ γ2) t)) refl refl 
           
           in subst₂ (\h1 h2 -> ⟦ B ⟧v adv h1 h2) (cong multiRedux (sym (substitutionResult {{R}} {_} {v3} {γ1} {t} {Γ1})))
                                                  (cong multiRedux (sym (substitutionResult {{R}} {_} {v4} {γ2} {t} {Γ1}))) goala

          goalAbs : ⟦ FunTy A s B ⟧e adv (multisubst γ1 (Abs (Γlength Γ1 + 1) t)) (multisubst γ2 (Abs (Γlength Γ1 + 1) t))
          goalAbs v1a v2a v1aredux v2aredux =
              let
                goal = funInterpBi (multisubst' zero γ1 t) (multisubst' zero γ2 t) (goalBiInner bodyContextMain) (goalUInner {γ1} u1) (goalUInner {γ2} u2)
              in
                subst₂ (\h1 h2 -> ⟦ FunTy A s B ⟧v adv h1 h2)
                  (trans (trans (sym reduxAbs) (cong multiRedux (sym (substPresAbs {0} {γ1} {Γlength Γ1 + 1} {t})))) v1aredux)
                  (trans (trans (sym reduxAbs) (cong multiRedux (sym (substPresAbs {0} {γ2} {Γlength Γ1 + 1} {t})))) v2aredux)
                  goal

          goal : ⟦ Box ((R Semiring.*R r) ghost) (FunTy A s B) ⟧v adv (Promote (multisubst γ1 (Abs (Γlength Γ1 + 1) t))) (Promote (multisubst γ2 (Abs (Γlength Γ1 + 1) t)))
          goal = boxInterpBiobs (timesLeft pre) (multisubst γ1 (Abs (Γlength Γ1 + 1) t)) (multisubst γ2 (Abs (Γlength Γ1 + 1) t)) goalAbs


    -- #### pr
    intermediateSub {{R}} {{R'}} {Γ = Γ'} {g} {r} {adv} {γ1} {γ2} {.(Promote t)} {.(Box s A)} typ pre inp e1 e2 v1 v2 v1redux v2redux
     |  (pr {_} {(Γ , g')} {(.Γ' , .g)} {s} {A} {t} typInner {ctxtPre}) rewrite sym v1redux | sym v2redux | injPair2 ctxtPre =
     {-
              (Γ , g') |- t : A
     ----------------------------
      (s . Γ , s . g') |- [t] : Box s A
    -}
     let
       u1 = convertUnaryBox (subst (\h -> [ Box s A ]e h) (substPresProm {zero} {γ1} {t}) (extractUn e1))
       u2 = convertUnaryBox (subst (\h -> [ Box s A ]e h) (substPresProm {zero} {γ2} {t}) (extractUn e2))
       ih0 = intermediateSub typInner (timesLeft {R} {r} {s} {adv} pre) ihContext' u1 u2
     in
     idem ih0
      where
        -- Γ =
        

        idem : ⟦ Box ((R Semiring.*R (R Semiring.*R r) s) g') A ⟧e adv (Promote (multisubst γ1 t)) (Promote (multisubst γ2 t))
            -> ⟦ Box ((R Semiring.*R r) (s *R g')) (Box s A) ⟧v adv (Promote (multisubst γ1 (Promote t))) (Promote (multisubst γ2 (Promote t)))
        idem inp rewrite (sym (substPresProm {_} {γ1} {t})) | substPresProm {_} {γ2} {t} =
          let inp' = subst (\h -> ⟦ Box h A ⟧e adv (Promote (multisubst γ1 t)) (Promote (multisubst γ2 t))) rearrange inp
              out = delta (inp' (Promote (multisubst γ1 t)) (Promote (multisubst γ2 t)) refl refl)
          in subst₂ (\h1 h2 ->  ⟦
           Box ((R Semiring.*R r) ((R Semiring.*R s) g')) (Box s A) ⟧v
           adv (Promote h1) (Promote h2)) (sym (substPresProm {_} {γ1} {t})) (sym (substPresProm {_} {γ2} {t})) out

        ihContext' : ⟦ (r *R s) ·g (Γ , g') ⟧Γg adv γ1 γ2
        ihContext' rewrite injPair1 ctxtPre | injPair2 ctxtPre =
          subst₂ (\h1 h2 -> ⟦ (h1 , h2) ⟧Γg adv γ1 γ2) (actionAssoc Γ) (sym (assoc* {r} {s} {g'})) inp


    intermediateSub {{R}} {{R'}} {_} {_} {ghost} {r} {adv} {γ1} {γ2} {.unit} {.Unit} type pre inp e1 e2 v1 v2 v1redux v2redux
     | (unitConstr {_} {Γ}) rewrite sym v1redux | sym v2redux with 1R ≤d adv
    ... | yes qp =  boxInterpBiobs (InformationFlowSemiring.timesLeft R' pre) (multisubst γ1 unit) (multisubst γ2 unit) (goal e1 e2)
        where
          goal : [ Box (r *R ghost) Unit ]e (Promote (multisubst γ1 unit))
              -> [ Box (r *R ghost) Unit ]e (Promote (multisubst γ2 unit))
              -> ⟦ Unit ⟧e adv (multisubst γ1 unit) (multisubst γ2 unit)
          goal u1 u2 v3 v4 v3redux v4redux with u1 (Promote (multisubst γ1 unit)) reduxProm | u2 (Promote (multisubst γ2 unit)) reduxProm
          ... | boxInterpV .(multisubst' 0 γ1 unit) x1 | boxInterpV .(multisubst' 0 γ2 unit) x2 rewrite sym v3redux | sym v4redux | substPresUnit {γ1} {0} | substPresUnit {γ2} {0} | reduxUnit = unitInterpBi

    ... | no gp = boxInterpBiunobs {!!} (multisubst γ1 unit) (multisubst γ2 unit) (goaleo {γ1} e1 , goaleo {γ2} e2)
       where
         goaleo : {γ :  List Term}
              -> [ Box (r *R ghost) Unit ]e (Promote (multisubst γ unit))
              -> [ Unit ]e (multisubst γ unit)
         goaleo {γ} u1 v3 v3redux with u1 (Promote (multisubst γ unit)) reduxProm
         ... | boxInterpV _ _ rewrite sym v3redux | substPresUnit {γ} {0} | reduxUnit = unitInterpV


    intermediateSub {_} {_} {ghost} {r} {adv} {γ1} {γ2} {.vtrue} {.BoolTy} type pre inp e1 e2 v1 v2 v1redux v2redux
     | (trueConstr {_} {Γ}) = {!!}

    intermediateSub {_} {_} {ghost} {r} {adv} {γ1} {γ2} {.vfalse} {.BoolTy} type pre inp e1 e2 v1 v2 v1redux v2redux
     | (falseConstr {_} {Γ}) = {!!}

    intermediateSub {_} {_} {ghost} {r} {adv} {γ1} {γ2} {_} {_} type pre inp e1 e2 v1 v2 v1redux v2redux
     | (if {_} {Γ} {Γ1} {Γ2} {ghost} {B} {t1} {t2} {t3} {s} {pre'} typG typ1 typ2 {ctxtPre}) = {!!}

    -- intermediateSub {Γ = Γ} {ghost} {r} {adv} {γ1} {γ2} {term} {A} type pre inp e1 e2 = {!!}

    {- intermediate : {{R : Semiring}} {{R' : InformationFlowSemiring R}} {sz : ℕ}
                {Γ : Context sz}
                {ghost r adv : grade}
                {γ1 γ2 : List Term}
                {τ : Type}
                {e : Term}
                -> (Γ , ghost) ⊢ e ∶ τ
                -> ⟦ r ·g ( Γ , ghost) ⟧Γg adv γ1 γ2
                -> (r ≤ adv)
                -> ⟦ Box ghost τ ⟧v adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))
                -> ¬ (ghost ≤ adv)
                -> ⟦ Box (ghost *R r) τ ⟧v adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))
    intermediate {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {τ} {e} _ inp pre1 inner pre2
     with (ghost *R r) ≤d adv

    --   But what if s = Public, g = Private, adv = Public
    --   then we have s ≤ adv (Public ≤ Public) yes
    --              ¬ (ghost ≤ adv) meaning ¬ (Private ≤ Public) yes
    --              (ghost *R s) = Public * Private = Public
    --         therefore (ghost *R s) ≤ Public is Public ≤ Public which is true.
    --  therefore adversary cannot see inside Box ghost τ but should be able to see inside Box (ghost *R s).

    intermediate {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {τ} {e} _ inp pre1 inner pre2 | yes p with inner

    intermediate ⦃ R ⦄ {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {τ} {e} _ inp pre1 inner pre2
      | yes p | boxInterpBiobs x .(multisubst' 0 γ1 e) .(multisubst' 0 γ2 e) inner' =
        boxInterpBiobs p (multisubst' zero γ1 e) (multisubst' zero γ2 e) inner'

    intermediate ⦃ R ⦄ {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {τ} {e} typ inp pre1 inner pre2
      | yes p | boxInterpBiunobs x .(multisubst' 0 γ1 e) .(multisubst' 0 γ2 e) inner' =
        -- boxInterpBiobs p (multisubst' zero γ1 e) (multisubst' zero γ2 e)
          let sub =  (intermediateSub {sz} {Γ} {ghost} {r} {adv} typ pre1 inp {!!} {!!}) -- (proj₁ inner') (proj₂ inner'))
          in boxInterpBiobs (timesLeftSym pre1) {!!} {!!} {!!}

    intermediate {{R}} {{R'}} {sz} {Γ} {ghost} {r} {adv} {γ1} {γ2} {τ} {e} typ inp pre1 inner pre2 | no ¬p with inner
    ... | boxInterpBiobs pre3 .(multisubst' 0 γ1 e) .(multisubst' 0 γ2 e) _ = ⊥-elim (pre2 pre3)
    ... | boxInterpBiunobs pre3 .(multisubst' 0 γ1 e) .(multisubst' 0 γ2 e) inner' =
      boxInterpBiunobs ¬p (multisubst' zero γ1 e) (multisubst' zero γ2 e) inner'
  -}

    biFundamentalTheoremGhost : {{R : Semiring}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
              {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

            -> (Γ , ghost) ⊢ e ∶ τ
            -> {γ1 : List Term} {γ2 : List Term}
            -> (adv : grade)
            -> ⟦ (Γ , ghost) ⟧Γg adv γ1 γ2
            -> ⟦ Box ghost τ ⟧e adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))

            -- another idea is `Box 1 τ` here

    -- ## var
    biFundamentalTheoremGhost {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux
     rewrite injPair1 pos | sym (injPair2 pos) with Γ1 | γ1 | γ2 | contextInterp
    -- var at head of context (key idea, without out loss of generality as position in context is irrelevant
    -- to rest of the proof)
    ... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | visible eq (argInterp , restInterp) rewrite sym v1redux | sym v2redux = conc

      where
        conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
        conc with argInterp (Promote a1) (Promote a2) refl refl
        -- goal : ghost ≤ adv
        -- eq   : 1 ≤ adv
        ... | boxInterpBiobs   eq .a1 .a2 inner
           rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
              boxInterpBiobs eq a1 a2 inner

        ... | boxInterpBiunobs neq .a1 .a2 inner
           rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
              ⊥-elim (neq eq)

    ... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | invisible neq ((argInterp1 , restInterp1) , (argInterp2 , restInterp2)) rewrite sym v1redux | sym v2redux = conc
      where
        conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
        conc rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiunobs neq a1 a2 (extractUn argInterp1 , extractUn argInterp2)

    -- var generalisation here
    ... | _ | _ | _ | _ = {!!}

    -- ## pr
    biFundamentalTheoremGhost {{R}} {{R'}} {sz} {Γ'} {ghost} {Promote t} {Box r A} (pr {sz} {Γ , ghost'} {Γ' , .ghost} {.r} typ {prf}) {γ1} {γ2} adv contextInterpG v1 v2 v1redux v2redux rewrite prf with r ≤d adv
    {-
      G, ghost g' |- t : A
    ------------------------------
      G, ghost g |- [t] : Box r A

     where g = r * g'

     model is then
       Box g ⟦ G ⟧ -> Box g (Box r ⟦ A ⟧)
    -}
   -- biFundamentalTheoremGhost {{R}} {{R'}} {sz} {Γ'} {ghost} {Promote t} {Box r A} (pr {sz} {Γ , ghost'} {Γ' , .ghost} {.r} typ {prf}) {γ1} {γ2} adv contextInterpG v1 v2 v1redux v2redux | visible eq0 contextInterp 
    ... | yes eq rewrite sym (injPair2 prf) | idem* R' {r} rewrite sym v1redux | sym v2redux = main
      where
        convertVal : {s : grade} {v1 : Term} {v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧v adv (Promote v1) (Promote v2)
        convertVal = convertValR* eq

        convertExp : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ⟦ Box s A ⟧e adv (Promote v1) (Promote v2)
        convertExp {s} {v1} {v2} {A} arg1 v1' v2' v1redux' v2redux' rewrite trans (sym v1redux') (reduxProm {v1}) | trans (sym v2redux') (reduxProm {v2}) =
           convertVal  {s} {v1} {v2} {A} (arg1 (Promote v1) (Promote v2) refl refl)

        underBox : {sz : ℕ} {γ1 γ2 : List Term} {Γ : Context sz} -> ⟦ r · Γ ⟧Γ adv γ1 γ2 -> ⟦ Γ ⟧Γ adv γ1 γ2
        underBox {_} {[]} {[]} {Empty}   g = tt
        underBox {suc n} {v1 ∷ γ1} {v2 ∷ γ2} {Ext Γ (Grad A s)} (ass , g) = convertExp {s} {v1} {v2} {A} ass , underBox {n} {γ1} {γ2} {Γ} g
        underBox {_} {[]} {[]} {Ext Γ (Grad A r₁)} ()
        underBox {_} {[]} {x ∷ γ5} {Ext Γ (Grad A r₁)} ()
        underBox {_} {x ∷ γ4} {[]} {Ext Γ (Grad A r₁)} ()

        thm : {v : Term} {γ : List Term} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
        thm {v} {γ} redux =
           let qr = cong multiRedux (substPresProm {0} {γ} {t})
               qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
           in sym (trans (sym redux) qr')

        binaryToUnaryVal : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ([ Box s A ]v (Promote v1)) × ([ Box s A ]v (Promote v2))
        binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiobs eq' .v1 .v2 ainterp) =
          let (a , b) = binaryImpliesUnary {A} {v1} {v2} {adv} ainterp in (boxInterpV v1 a , boxInterpV v2 b)

        binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 (left , right)) = (boxInterpV v1 left) , (boxInterpV v2 right)


        binaryToUnaryExp : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ([ Box s A ]e (Promote v1)) × ([ Box s A ]e (Promote v2))
        binaryToUnaryExp {s} {v1} {v2} {A} arg1 = (left , right)
          where
            left : [ Box s A ]e (Promote v1)
            left v0 redux rewrite trans (sym redux) (reduxProm {v1}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
            ... | (left' , right') = left'

            right : [ Box s A ]e (Promote v2)
            right v0 redux rewrite trans (sym redux) (reduxProm {v2}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
            ... | (left' , right') = right'

        -- lift multiplication idempotence to contexts
        idemContext : {sz : ℕ} {Γ : Context sz} -> (r · Γ) ≡  r · (r · Γ)
        idemContext {sz} {Γ} rewrite actionAssoc {_} {r} {r} Γ | idem* R' {r} = refl

        convertLast : ⟦ Box ((R Semiring.*R r) ghost) (Box r A) ⟧v adv (Promote (multisubst γ1 (Promote t))) (Promote (multisubst γ2 (Promote t)))
                   -> ⟦ Box ghost (Box r A) ⟧v adv (Promote (multisubst' 0 γ1 (Promote t))) (Promote (multisubst' 0 γ2 (Promote t)))
        convertLast (boxInterpBiobs pre t1 t2 inner)  with ghost ≤d adv
        ... | yes geq = boxInterpBiobs geq t1 t2 inner
        ... | no ¬geq = boxInterpBiunobs ¬geq t1 t2 (binaryImpliesUnary {{R}} {Box r A} {t1} {t2} {adv} inner)
        convertLast (boxInterpBiunobs pre t1 t2 inner) = ⊥-elim (pre (timesLeft eq))

        main : ⟦ Box ghost (Box r A) ⟧v adv (Promote (multisubst' 0 γ1 (Promote t))) (Promote (multisubst' 0 γ2 (Promote t)))
        main rewrite injPair1 prf with ghost' ≤d adv
        ... | yes geq' = boxInterpBiobs (subst (\h -> h ≤ adv) (sym (injPair2 prf)) (timesLeftSym geq')) (multisubst γ1 (Promote t))  (multisubst γ2 (Promote t)) conclusion
          where
           conclusion : ⟦ Box r A ⟧e adv (multisubst' 0 γ1 (Promote t)) (multisubst' 0 γ2 (Promote t))
           conclusion v1 v2 v1redux v2redux rewrite sym (injPair2 prf) | sym (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux) | sym (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux) =
             let ih = biFundamentalTheoremGhost {sz} {Γ} {ghost'} {t} {A} typ {γ1} {γ2} adv (contextElimTimesAlt {sz} {Γ , ghost'} {γ1} {γ2} eq (subst (\h ->  ⟦ (r · Γ) , h ⟧Γg adv γ1 γ2) (injPair2 prf)  contextInterpG))
             in boxInterpBiobs eq (multisubst' zero γ1 t) (multisubst' zero γ2 t) (unpackObs geq' ih)


        ... | no geq' rewrite sym (injPair2 prf) =
          let
            contextInterpG' = subst (\h ->  ⟦ (r · Γ) , h ⟧Γg adv γ1 γ2) (injPair2 prf) contextInterpG
            ih = biFundamentalTheoremGhost {sz} {Γ} {ghost'} {t} {A} typ {γ1} {γ2} adv (invisible geq' (contextElimTimesToUnary {_} {γ1} {γ2} {Γ} {r} contextInterpG'))
            (ihu1 , ihu2) = binaryImpliesUnary {Box ghost' A} {Promote (multisubst γ1 t)} {Promote (multisubst γ2 t)} {adv = adv} ih
            -- put context into the right form
            contextInterpG' = subst (\h -> ⟦ (r · Γ) , h ⟧Γg adv γ1 γ2) (injPair2 prf) contextInterpG -- (sym (injPair2 prf))
            contextInterpG'' = subst (\h -> ⟦ (r · Γ) , h *R ghost'  ⟧Γg adv γ1 γ2) (sym (idem* R' {r})) contextInterpG'
            contextInterpG3 = subst (\h -> ⟦ (r · Γ) , h  ⟧Γg adv γ1 γ2) (assoc* {r} {r} {ghost'}) contextInterpG''
            contextInterpG4 = subst (\h -> ⟦ (r · Γ) , r *R h ⟧Γg adv γ1 γ2) (sym (injPair2 prf)) contextInterpG3
            contextInterpG5 = subst (\h -> ⟦ h , r *R ghost ⟧Γg adv γ1 γ2) idemContext contextInterpG4
            contextInterpG6 = subst (\h -> ⟦ r · h , r *R ghost ⟧Γg adv γ1 γ2) (sym (injPair1 prf)) contextInterpG5

            -- put input unary relations into the right form
            ihu1c = convertUnaryBox {r = ghost'} {s = _*R_ (_*R_ r ghost) r} ihu1
            ihu2c = convertUnaryBox {r = ghost'} {s = _*R_ (_*R_ r ghost) r} ihu2

            ihu1c' = subst (\h -> [ Box (r *R ghost) (Box r A) ]e (Promote h)) (sym (substPresProm {0} {γ1} {t})) (deltaU ihu1c)
            ihu2c' = subst (\h -> [ Box (r *R ghost) (Box r A) ]e (Promote h)) (sym (substPresProm {0} {γ2} {t})) (deltaU ihu2c)

            out = intermediateSub {ghost = ghost} (pr {sz} {Γ , ghost'} {Γ' , ghost} {r} typ {prf}) eq contextInterpG6 ihu1c' ihu2c'
            goalOld = out (Promote (multisubst γ1 (Promote t))) (Promote (multisubst γ2 (Promote t))) (reduxProm {multisubst γ1 (Promote t)}) (reduxProm {multisubst γ2 (Promote t)})

          in convertLast goalOld


    ... | no ¬req rewrite sym v1redux | sym v2redux = main
      where
        binaryToUnaryVal : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧v adv (Promote v1) (Promote v2) -> ([ Box s A ]v (Promote v1)) × ([ Box s A ]v (Promote v2))
        binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiobs eq' .v1 .v2 ainterp) =
          let (a , b) = binaryImpliesUnary {A} {v1} {v2} {adv} ainterp in (boxInterpV v1 a , boxInterpV v2 b)

        binaryToUnaryVal {s} {v1} {v2} {A} (boxInterpBiunobs eq .v1 .v2 (left , right)) = (boxInterpV v1 left) , (boxInterpV v2 right)

        binaryToUnaryExp : {s : grade} {v1 v2 : Term} {A : Type} -> ⟦ Box (r *R s) A ⟧e adv (Promote v1) (Promote v2) -> ([ Box s A ]e (Promote v1)) × ([ Box s A ]e (Promote v2))
        binaryToUnaryExp {s} {v1} {v2} {A} arg1 = (left , right)
          where
            left : [ Box s A ]e (Promote v1)
            left v0 redux rewrite trans (sym redux) (reduxProm {v1}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
            ... | (left' , right') = left'

            right : [ Box s A ]e (Promote v2)
            right v0 redux rewrite trans (sym redux) (reduxProm {v2}) with binaryToUnaryVal {s} {v1} {v2} {A} (arg1 (Promote v1) ((Promote v2)) refl refl)
            ... | (left' , right') = right'

        main : ⟦ Box ghost (Box r A) ⟧v adv (Promote (multisubst' 0 γ1 (Promote t))) (Promote (multisubst' 0 γ2 (Promote t)))
        main with ghost ≤d adv
        ... | yes geq = boxInterpBiobs geq (multisubst γ1 (Promote t))  (multisubst γ2 (Promote t)) conclusion
          where

            conclusion : ⟦ Box r A ⟧e adv (multisubst' 0 γ1 (Promote t)) (multisubst' 0 γ2 (Promote t))
            conclusion v1 v2 v1redux v2redux rewrite injPair1 prf =

              let
                (uinterp1 , uinterp2) = contextElimTimesToUnary {sz} {γ1} {γ2} {Γ} contextInterpG
                ih1 = utheoremG {sz} {γ1} {Γ} {ghost'} {t} {A} typ uinterp1
                ih2 = utheoremG {sz} {γ2} {Γ} {ghost'} {t} {A} typ uinterp2
                out = boxInterpBiunobs ¬req (multisubst γ1 t) (multisubst γ2 t) (ih1 , ih2)
              in subst₂ (\h1 h2 -> ⟦ Box r A ⟧v adv h1 h2)
                (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux)
                (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux) out

        ... | no ¬geq = boxInterpBiunobs ¬geq (multisubst γ1 (Promote t)) (multisubst γ2 (Promote t)) (conclusion1 , conclusion2)
          where
            conclusion1 : [ Box r A ]e (multisubst' 0 γ1 (Promote t))
            conclusion1 v1 v1redux rewrite injPair1 prf | sym (reduxAndSubstCombinedProm {v1} {t} {γ1} v1redux) =
              let
                (uinterp1 , uinterp2) = contextElimTimesToUnary {sz} {γ1} {γ2} {Γ} contextInterpG
                ih1 = utheoremG {sz} {γ1} {Γ} {ghost'} {t} {A} typ uinterp1
              in boxInterpV (multisubst γ1 t) ih1

            conclusion2 : [ Box r A ]e (multisubst' 0 γ2 (Promote t))
            conclusion2 v2 v2redux rewrite injPair1 prf | sym (reduxAndSubstCombinedProm {v2} {t} {γ2} v2redux) =
              let
                (uinterp1 , uinterp2) = contextElimTimesToUnary {sz} {γ1} {γ2} {Γ} contextInterpG
                ih2 = utheoremG {sz} {γ2} {Γ} {ghost'} {t} {A} typ uinterp2
              in boxInterpV (multisubst γ2 t) ih2

    -- ## abs
    biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {.(FunTy A s B)} (abs {_} {_} {Γa} {Γ1} {Γ2} {.(Γ , ghost)} {s} {ghost'} {A} {B} {t'} pos ty {pre}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite sym v1redux | sym v2redux =
      goal
     where
      goal : ⟦ Box ghost (FunTy A s B) ⟧v adv (Promote (multisubst γ1 (Abs (Γlength Γ1 + 1) t'))) (Promote (multisubst γ2 (Abs (Γlength Γ1 + 1) t')))
      goal = {!!}


    -- ## app
    biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {B} (app {_} {.(Γ , ghost)} {Γ1 , g1} {Γ2 , g2} {s} {A} {.B} {t1} {t2} ty1 ty2 {pre})  {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite sym v1redux | sym v2redux = 
       goal
      where
       goal : ⟦ Box ghost B ⟧v adv (multiRedux (Promote (multisubst γ1 (App t1 t2)))) (multiRedux (Promote (multisubst γ2 (App t1 t2))))
       goal rewrite valuesDontReduce (promoteValue (multisubst γ1 (App t1 t2)))
                  | valuesDontReduce (promoteValue (multisubst γ2 (App t1 t2)))
                  | injPair1 pre | injPair2 pre =
         let ih1 = biFundamentalTheoremGhost ty1 adv (contextSplitLeft contextInterp) 
             ih2 = biFundamentalTheoremGhost (pr ty2) adv (contextSplitRight contextInterp)

             -- Reducability of `App t1 t2` implies that there exists a value `Abs var1 bod1` which can be obtained by
             -- reducing `t1` underneath context `γ1` and `Abs var2 bod2` underneath context `γ2`
             ((var1 , bod1) , (fun1redux , bodTy1)) =
               reduxTheoremAppTyG {multisubst' 0 γ1 t1} {multisubst' 0 γ1 t2} {v1} {0} {Empty} {A} {B} {!!} {!!}
             --(subst (\r -> multiRedux r ≡ v1) (substPresApp {0} {γ1} {t1} {t2}) {!!}) {!!} -- (multiSubstTy {sz} {Γ1} {t1} {FunTy A s B} {γ1} ty1)
             ((var2 , bod2) , (fun2redux , bodTy2)) =
               reduxTheoremAppTyG {multisubst' 0 γ2 t1} {multisubst' 0 γ2 t2} {v2} {0} {Empty} {A} {B} {!!} {!!}
             -- (subst (\r -> multiRedux r ≡ v2) (substPresApp {0} {γ2} {t1} {t2}) {!!}) {!!} -- (multiSubstTy {sz} {Γ1} {t1} {FunTy A s B} {γ2} ty1)
             fun1 = Abs var1 bod1
             fun2 = Abs var2 bod2

         in {!!}

    -- ## if
    biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {B} (if {_} {.Γ} {Γ1} {Γ2} {ghost} {.B} {t1} {t2} {t3} {r} {used} ty1 ty2 ty3 {pre})  {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

    -- ## constant true
    biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {.Unit} (unitConstr {s} {Γa}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux =
      {!!}
 
    {- -- ## constants false
    biFundamentalTheoremGhost {sz} {.(0R · Γ)} {.1R} {t} {.BoolTy} (trueConstr {s} {Γ}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

{-
    -- ## constants false
    biFundamentalTheoremGhost {sz} {.(0R · Γ)} {.1R} {t} {.BoolTy} (falseConstr {s} {Γ}) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!} -}


    biFundamentalTheoremGhost {sz} {Γ} {ghost} {t} {A} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


{-
nonInterferenceGhostAlt :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
   {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> (Ext Empty (Grad BoolTy s) , r) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> (Empty , default) ⊢ v1 ∶ BoolTy
        -> (Empty , default) ⊢ v2 ∶ BoolTy
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterferenceGhostAlt {{R}} {{R'}} {{R''}} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 =
 {!!}
-}
