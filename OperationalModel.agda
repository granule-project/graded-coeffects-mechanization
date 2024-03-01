{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

module OperationalModel where

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
open import Data.Fin hiding (_+_; _≟_)

open import Semiring


multisubst' : (xs : List (Term s)) -> Fin (suc (length xs + s)) -> Term (length xs + s) -> Term s
multisubst' [] _ t' = t'
multisubst' (t ∷ ts) n t' =
  multisubst' ts {!!} (syntacticSubst (raiseTermℕ (length ts) t) {!!} t')

multisubst : (xs : List (Term s)) -> Term (length xs + s) -> Term s
multisubst ts t' = multisubst' ts zero t'


postulate
  multiReduxHere : {t : Term s} {γ : List (Term s)}
                  -> multisubst (t ∷ γ) (Var zero) ≡ t

  betaVariant1 : {bod : Term (suc s)} {t2 : Term s}
                -> multiRedux (App (Abs bod) t2)
                 ≡ multiRedux (syntacticSubst t2 zero bod)

isSimultaneous' : {t t' : Term s} {γ : List (Term s)}
  -> multiRedux (multisubst (t ∷ γ) (Var zero)) ≡ t'
  -> multiRedux t ≡ t'
isSimultaneous' {s} {t} {t'} {γ} p rewrite multiReduxHere {s} {t} {γ} = p

{-

-- Various preservation results about substitutions and values

substPresUnit : {γ : List (Term s)} {n : ℕ} -> multisubst' n γ unit ≡ unit
substPresUnit {γ = []}    {n} = refl
substPresUnit {γ = x ∷ g} {n} = substPresUnit {_} {g} {n + 1}

substPresTrue : {γ : List (Term s)} {n : ℕ} -> multisubst' n γ vtrue ≡ vtrue
substPresTrue {γ = []}    {n} = refl
substPresTrue {γ = x ∷ g} {n} = substPresTrue {_} {g} {n + 1}

substPresFalse : {γ : List (Term s)} {n : ℕ} -> multisubst' n γ vfalse ≡ vfalse
substPresFalse {γ = []}    {n} = refl
substPresFalse {γ = x ∷ g} {n} = substPresFalse {_} {g} {n + 1}

substPresProm : {n : ℕ} {γ : List (Term s)} {t : Term s}
             -> multisubst' n γ (Promote t) ≡ Promote (multisubst' n γ t)
substPresProm {_} {n} {[]} {t} = refl
substPresProm {_} {n} {x ∷ γ} {t} = substPresProm {_} {n + 1} {γ} {syntacticSubst x n t}

substPresApp : {n : ℕ} {γ : List Term} {t1 t2 : Term} -> multisubst' n γ (App t1 t2) ≡ App (multisubst' n γ t1) (multisubst' n γ t2)
substPresApp {n} {[]} {t1} {t2} = refl
substPresApp {n} {x ∷ γ} {t1} {t2} = substPresApp {n + 1} {γ} {syntacticSubst x n t1} {syntacticSubst x n t2}

substPresAbs : {n : ℕ} {γ : List Term} {x : ℕ} {t : Term} -> multisubst' n γ (Abs x t) ≡ Abs x (multisubst' n γ t)
substPresAbs {n} {[]} {x} {t} = refl
substPresAbs {n} {v ∷ γ} {x} {t} with n ≟ x
... | yes refl = {!!}
... | no ¬p = substPresAbs {n + 1} {γ} {x} {syntacticSubst v n t}

substPresIf : {n : ℕ} {γ : List Term} {tg t1 t2 : Term} -> multisubst' n γ (If tg t1 t2) ≡ If (multisubst' n γ tg) (multisubst' n γ t1) (multisubst' n γ t2)
substPresIf {n} {[]} {tg} {t1} {t2} = refl
substPresIf {n} {x ∷ γ} {tg} {t1} {t2} = substPresIf {n + 1} {γ} {syntacticSubst x n tg} {syntacticSubst x n t1} {syntacticSubst x n t2}

reduxProm : {v : Term} -> multiRedux (Promote v) ≡ Promote v
reduxProm {v} = refl

reduxAbs : {x : ℕ} {t : Term} -> multiRedux (Abs x t) ≡ Abs x t
reduxAbs = refl

reduxFalse : multiRedux vfalse ≡ vfalse
reduxFalse = refl

reduxTrue : multiRedux vtrue ≡ vtrue
reduxTrue = refl

reduxUnit : multiRedux unit ≡ unit
reduxUnit = refl

postulate -- postulate now for development speed
  reduxTheoremApp : {t1 t2 t v : Term} -> multiRedux (App t1 t2) ≡ v -> Σ (ℕ × Term) (\(z , v1') -> multiRedux t1 ≡ Abs z v1')

   --  t1 ↓ \x.t   t2 ↓ v2   t[v2/x] ↓ v3
   -- --------------------------------------
   --   t1 t2 ⇣ v3

  reduxTheoremAll : {t1 t2 v : Term}
                  -> multiRedux (App t1 t2) ≡ v
                  -> Σ (ℕ × Term) (\(x , t) ->
                      ((multiRedux t1 ≡ (Abs x t)) ×
                        (multiRedux (syntacticSubst t2 x t) ≡ v)))


  multiSubstTy : {{R : Semiring}} -> {n : ℕ} {Γ : Context n} {t : Term} {A : Type} {γ : List Term} -> Γ ⊢ t ∶ A -> Empty ⊢ multisubst' 0 γ t ∶ A
  reduxTheoremAppTy : {{R : Semiring}}
                 -> {t1 t2 v : Term} {s : ℕ} {Γ : Context s} {A B : Type} {r : grade}
                 -> multiRedux (App t1 t2) ≡ v
                 -> Γ ⊢ t1 ∶ FunTy A r B
                 -> Σ (ℕ × Term) (\(z , v1') -> multiRedux t1 ≡ Abs z v1' × ((Ext Γ (Grad A r)) ⊢ (Abs z v1') ∶  B))

  reduxTheoremBool : {tg t1 t2 v : Term} -> multiRedux (If tg t1 t2) ≡ v -> (multiRedux tg ≡ vtrue) ⊎ (multiRedux tg ≡ vfalse)
  reduxTheoremBool1 : {tg t1 t2 v : Term} -> multiRedux (If tg t1 t2) ≡ v -> multiRedux tg ≡ vtrue -> v ≡ multiRedux t1
  reduxTheoremBool2 : {tg t1 t2 v : Term} -> multiRedux (If tg t1 t2) ≡ v -> multiRedux tg ≡ vfalse -> v ≡ multiRedux t2




-- This is about the structure of substitutions and relates to abs
 -- there is some simplification here because of the definition of ,, being
 -- incorrect
  substitutionResult : {{R : Semiring}} {sz : ℕ} {v1' : Term} {γ1 : List Term} {t : Term} {Γ1 : Context sz}
   -> syntacticSubst v1' (Γlength Γ1 + 1) (multisubst' 0 γ1 t)
    ≡ multisubst (v1' ∷ γ1) t

reduxAndSubstCombinedProm : {v t : Term} {γ : List Term} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
reduxAndSubstCombinedProm {v} {t} {γ} redux =
       let qr = cong multiRedux (substPresProm {0} {γ} {t})
           qr' = trans qr (valuesDontReduce {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')
-}
