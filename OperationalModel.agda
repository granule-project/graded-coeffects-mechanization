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

data Telescope : ℕ -> Set where
  Empty : Telescope 0
  Cons  : {s : ℕ} -> Term s -> Telescope s -> Telescope (suc s)

{-
 Example
  G1 |- t1 : A1
  G2 |- t2 : A2
  G3 |- t3 : A3
  Ga , Gb , Gc , x1 : A1 , x2 : A2 , x3 : A3 |- t : B
-------------------------------------------------------
  (Ga, Gb, Gc) + G1 + G2 + G3 |- t : B

i.e., |G1| = |G2| = |G3| = |Ga|+|Gb|+|Gc|

`multisubst` assumes it is substituting into head variables in the context
-}

multisubst : (xs : List (Term s)) -> Term (length xs + s) -> Term s
multisubst [] t' = t'
multisubst (t ∷ ts) t' =
  multisubst ts (syntacticSubst (raiseTermℕ (length ts) t) zero t')

-- Note that it might be easier to reason about this with closed terms
-- i.e., is s == 0 in the above

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


-- Various preservation results about substitutions and values

substPresUnit : {γ : List (Term s)} -> multisubst γ unit ≡ unit
substPresUnit {s} {γ = []}    = refl
substPresUnit {s} {γ = x ∷ g} = substPresUnit {s} {g}

substPresTrue : {γ : List (Term s)} -> multisubst γ vtrue ≡ vtrue
substPresTrue {γ = []}    = refl
substPresTrue {γ = x ∷ g} = substPresTrue {_} {g}

substPresFalse : {γ : List (Term s)} -> multisubst γ vfalse ≡ vfalse
substPresFalse {γ = []}    = refl
substPresFalse {γ = x ∷ g} = substPresFalse {_} {g}

substPresProm : {γ : List (Term s)} {t : Term (length γ + s)}
             -> multisubst γ (Promote t) ≡ Promote (multisubst γ t)
substPresProm {_} {[]} {t} = refl
substPresProm {_} {x ∷ γ} {t} =
  substPresProm {_} {γ} {syntacticSubst (raiseTermℕ (length γ) x) zero t}

substPresApp : {γ : List (Term s)} {t1 t2 : Term (length γ + s)}
            -> multisubst γ (App t1 t2) ≡ App (multisubst γ t1) (multisubst γ t2)
substPresApp {_} {[]} {t1} {t2} = refl
substPresApp {_} {x ∷ γ} {t1} {t2} =
  substPresApp {_} {γ} {syntacticSubst (raiseTermℕ (length γ) x) zero t1}
                       {syntacticSubst (raiseTermℕ (length γ) x) zero t2}

sidPrf : {s : ℕ} {γ : List (Term s)}
       -> Term (suc (length γ + s))
       -> Term (suc (length (Data.List.map raiseTerm γ) + s))
sidPrf {s} {g} (Var x) = Var (aux {s} {g} x)
  where
    aux : {s : ℕ} -> {γ : List (Term s)} -> Fin (suc (length γ + s)) -> Fin (suc (length (Data.List.map raiseTerm γ) + s))
    aux {_} {γ} zero = zero
    aux {_} {[]} (suc x) = suc x
    aux {_} {x ∷ γ} (suc n) = let k = aux {_} {γ} n in suc k
sidPrf {s} {g} (App x x₁) = App (sidPrf {s} {g} x) (sidPrf {s} {g} x₁)
sidPrf {s} {g} (Abs x) = let y = sidPrf {suc s} {{! !}} x in Abs y
sidPrf {s} {g} unit = unit
sidPrf {s} {g} (Promote x) = Promote (sidPrf x)
sidPrf {s} {g} (Let x x₁) = Let (sidPrf x) (sidPrf x₁)
sidPrf {s} {g} vtrue = vtrue
sidPrf {s} {g} vfalse = vfalse
sidPrf {s} {g} (If x x₁ x₂) = If (sidPrf x) (sidPrf x₁) (sidPrf x₂)

substPresAbs : {γ : List (Term s)} {t : Term (suc (length γ + s))} -> multisubst γ (Abs t) ≡ Abs (multisubst (Data.List.map raiseTerm γ) (sidPrf t))
substPresAbs {_} {[]} {t} = refl
substPresAbs {_} {v ∷ γ} {t} = substPresAbs {_} {γ} {syntacticSubst (raiseTermℕ (length γ) {!!}) zero (sidPrf t)}

substPresIf : {γ : List (Term s)} {tg t1 t2 : Term (length γ + s)} -> multisubst γ (If tg t1 t2) ≡ If (multisubst γ tg) (multisubst γ t1) (multisubst γ t2)
substPresIf {_} {[]} {tg} {t1} {t2} = refl
substPresIf {_} {x ∷ γ} {tg} {t1} {t2} =
  substPresIf {_} {γ} {syntacticSubst (raiseTermℕ (length γ) x) zero tg}
                      {syntacticSubst (raiseTermℕ (length γ) x) zero t1}
                      {syntacticSubst (raiseTermℕ (length γ) x) zero t2}

reduxProm : {v : Term s} -> multiRedux (Promote v) ≡ Promote v
reduxProm {v} = refl

reduxAbs : {t : Term (suc s)} -> multiRedux (Abs t) ≡ Abs t
reduxAbs = refl

reduxFalse : multiRedux vfalse ≡ vfalse
reduxFalse = refl

reduxTrue : multiRedux vtrue ≡ vtrue
reduxTrue = refl

reduxUnit : multiRedux unit ≡ unit
reduxUnit = refl

postulate -- postulate now for development speed
  reduxTheoremApp : {sz : ℕ} {t1 t2 t v : Term sz}
                 -> multiRedux (App t1 t2) ≡ v
                 -> Σ (Term (suc sz)) (\v1' -> multiRedux t1 ≡ Abs v1')

   --  t1 ↓ \x.t   t2 ↓ v2   t[v2/x] ↓ v3
   -- --------------------------------------
   --   t1 t2 ⇣ v3

  reduxTheoremAll : {t1 t2 v : Term s}
                  -> multiRedux (App t1 t2) ≡ v
                  -> Σ (Term (suc s)) (\t ->
                      ((multiRedux t1 ≡ (Abs t)) ×
                        (multiRedux (syntacticSubst t2 zero t) ≡ v)))

  multiSubstTy : {{R : Semiring}}
            -> {γ : List (Term 0)} {Γ : Context (length γ)} {A : Type} {t : Term (length γ)}
            -> Γ ⊢ t ∶ A
            -> Empty ⊢ multisubst γ t ∶ A

  reduxTheoremAppTy :
           {{R : Semiring}}
           {t1 t2 v : Term s} {Γ : Context s} {A B : Type} {r : grade}
          -> multiRedux (App t1 t2) ≡ v
          -> Γ ⊢ t1 ∶ FunTy A r B
          -> Σ (Term (suc s)) (\v1' -> (multiRedux t1 ≡ Abs v1') × (Ext Γ (Grad A r) ⊢ v1' ∶  B))

  reduxTheoremBool : {tg t1 t2 v : Term s} -> multiRedux (If tg t1 t2) ≡ v -> (multiRedux tg ≡ vtrue) ⊎ (multiRedux tg ≡ vfalse)
  reduxTheoremBool1 : {tg t1 t2 v : Term s} -> multiRedux (If tg t1 t2) ≡ v -> multiRedux tg ≡ vtrue -> v ≡ multiRedux t1
  reduxTheoremBool2 : {tg t1 t2 v : Term s} -> multiRedux (If tg t1 t2) ≡ v -> multiRedux tg ≡ vfalse -> v ≡ multiRedux t2



-- This is about the structure of substitutions and relates to abs
 -- there is some simplification here because of the definition of ,, being
 -- incorrect
  substitutionResult : {{R : Semiring}} {v1 : Term s} {γ1 : List (Term s)} {t : Term (suc (length γ1 + s))}
   -> syntacticSubst v1 (fromℕ s) (multisubst {!γ1!} t)
    ≡ multisubst (v1 ∷ γ1) t


reduxAndSubstCombinedProm : {γ : List (Term s)} {v : Term s} {t : Term (length γ + s)} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
reduxAndSubstCombinedProm {_} {γ} {v} {t}  redux =
       let qr = cong multiRedux (substPresProm {_} {γ} {t})
           qr' = trans qr (valuesDontReduce {_} {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')
