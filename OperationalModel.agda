{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}

module OperationalModel where

open import GrCore
open import Data.Unit -- hiding (_≤_; _≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Bool hiding (_≤_; _≟_)
open import Data.Vec hiding (_++_)
open import Data.Nat hiding (_≤_)
open import Function
open import Data.Maybe hiding (map)
open import Relation.Nullary
open import Data.Sum hiding (map)
open import Data.Fin hiding (_+_; _≟_)
open import Semiring

data Telescope : ℕ -> Set where
  Empty : Telescope 0
  Cons  : {s : ℕ} -> Term s -> Telescope s -> Telescope (suc s)

multisubstT : {s s' : ℕ} -> Telescope s -> Term (s' + s) -> Term s'
multisubstT {zero} {s'} Empty t' = t'
multisubstT {suc s} {s'} (Cons t ts) t' =
  multisubstT {s} {s'} ts (syntacticSubst (raiseTermℕ s' t) zero t')

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

multisubst' : {s n : ℕ} -> (xs : Vec (Term (suc s)) n) -> Term (suc (n + s)) -> Term (suc s)
multisubst' [] t' = t'
multisubst' {s} {suc n} (t ∷ ts) t' =
  multisubst' {s} {n} ts (syntacticSubst (raiseTermℕ n t) (suc zero) t')


multisubst : {s n : ℕ} -> (xs : Vec (Term s) n) -> Term (n + s) -> Term s
multisubst [] t' = t'
multisubst {s} {suc n} (t ∷ ts) t' =
  multisubst {s} {n} ts (syntacticSubst (raiseTermℕ n t) zero t')

-- Note that it might be easier to reason about this with closed terms
-- i.e., is s == 0 in the above

postulate
  multiReduxHere : {s n : ℕ} {t : Term s} {γ : Vec (Term s) n}
                  -> multisubst (t ∷ γ) (Var zero) ≡ t

  multiSubstThere : {s n : ℕ} {t : Term s} {γ : Vec (Term s) n}
       -> multisubst γ (matchVar (raiseTermℕ n t) zero (raiseR 0 (fromℕ (n + s))))
         ≡ t

  substComAbs : {s1 s2 : ℕ} {v' : Term 0} {t : Term (suc (s1 + s2))} {γ : Vec (Term 0) (s1 + s2)}
          -> (multisubst γ (syntacticSubst (raiseTermℕ (s1 + s2) v') zero t))
          ≡ (syntacticSubst v' zero (multisubst' (Data.Vec.map (raiseTermℕ 1) γ) t))


  betaVariant1 : {bod : Term (suc s)} {t2 : Term s}
                -> multiRedux (App (Abs bod) t2)
                 ≡ multiRedux (syntacticSubst t2 zero bod)

isSimultaneous' : {s n : ℕ} {t : Term s} {t' : Term s} {γ : Vec (Term s) n}
  -> multiRedux (multisubst (t ∷ γ) (Var zero)) ≡ t'
  -> multiRedux t ≡ t'
isSimultaneous' {s} {n} {t} {t'} {γ} p rewrite multiReduxHere {s} {n} {t} {γ} = p

isSimultaneousGen : {s n s1 : ℕ} {t : Term s} {t' : Term s}
                    {γ : Vec (Term s) n} -- (fromℕ n)
  -> multiRedux (multisubst γ (matchVar (raiseTermℕ n t) zero (raiseR 0 (fromℕ (n + s))))) ≡ t'
  -> multiRedux t ≡ t'
isSimultaneousGen {s} {n} {s1} {t} {t'} {γ} p rewrite (multiSubstThere {s} {n} {t} {γ}) = p


-- Various preservation results about substitutions and values

substPresUnit : {s n : ℕ} {γ : Vec (Term s) n} -> multisubst γ unit ≡ unit
substPresUnit {s} {_} {γ = []}    = refl
substPresUnit {s} {suc n} {γ = x ∷ g} = substPresUnit {s} {n} {g}

substPresTrue : {n : ℕ} {γ : Vec (Term s) n} -> multisubst γ vtrue ≡ vtrue
substPresTrue {γ = []}    = refl
substPresTrue {s} {suc n} {γ = x ∷ g} = substPresTrue {s} {n} {g}

substPresFalse : {n : ℕ} {γ : Vec (Term s) n} -> multisubst γ vfalse ≡ vfalse
substPresFalse {γ = []}    = refl
substPresFalse {s} {suc n} {γ = x ∷ g} = substPresFalse {s} {n} {g}

substPresProm : {n : ℕ} {γ : Vec (Term s) n} {t : Term (n + s)}
             -> multisubst γ (Promote t) ≡ Promote (multisubst γ t)
substPresProm {_} {_} {[]} {t} = refl
substPresProm {_} {suc n} {x ∷ γ} {t} =
  substPresProm {_} {n} {γ} {syntacticSubst (raiseTermℕ n x) zero t}

substPresApp : {n : ℕ} {γ : Vec (Term s) n} {t1 t2 : Term (n + s)}
            -> multisubst γ (App t1 t2) ≡ App (multisubst γ t1) (multisubst γ t2)
substPresApp {_} {_} {[]} {t1} {t2} = refl
substPresApp  {_} {suc n} {x ∷ γ} {t1} {t2} =
  substPresApp {_} {n} {γ} {syntacticSubst (raiseTermℕ n x) zero t1}
                           {syntacticSubst (raiseTermℕ n x) zero t2}

substPresLet : {n : ℕ} {γ : Vec (Term s) n} {t1 : Term (n + s)} {t2 : Term (suc (n + s))}
            -> multisubst γ (Let t1 t2) ≡ Let (multisubst γ t1) (multisubst' (map raiseTerm γ) t2)
substPresLet {_} {.zero} {[]} {t1} {t2} = refl
substPresLet {s} {suc n} {v ∷ γ} {t1} {t2} =
 let
   subst1 = syntacticSubst (raiseTermℕ n v) zero t1
   subst2 = syntacticSubst (raiseTermℕ (1 + n) v) (suc zero) t2
   ih1 = substPresLet {s} {n} {γ} {subst1} {subst2}

   ihpre = cong (\h ->  multisubst γ (Let subst1 (syntacticSubst h (suc zero) t2))) (raiseProp {s} {n} {v})
   ihpost = cong (\h -> Let (multisubst γ subst1) (multisubst' (map raiseTerm γ) (syntacticSubst h (suc zero) t2)))
    (raisePropCom {s} {n} {v})
  in trans (trans ihpre ih1) ihpost

substPresAbs : {n : ℕ} {γ : Vec (Term s) n} {t : Term (suc (n + s))}
       -> multisubst γ (Abs t) ≡ Abs (multisubst' (Data.Vec.map raiseTerm γ) t)
substPresAbs {_} {_} {[]} {t} = refl
substPresAbs {s} {suc n} {v ∷ γ} {t} =

 let subst = syntacticSubst (raiseTermℕ (1 + n) v) (suc zero) t
     ih = substPresAbs {s} {n} {γ} {subst}
     ihpre = cong (\h ->  multisubst γ
        (Abs (syntacticSubst h (suc zero) t))) (raiseProp {s} {n} {v})

     ihpost = cong (\h ->  Abs
      (multisubst' (Data.Vec.map raiseTerm γ)
       (syntacticSubst h (suc zero) t))) (raisePropCom {s} {n} {v})

 in trans (trans ihpre ih) ihpost

substPresIf : {s n : ℕ} {γ : Vec (Term s) n} {tg t1 t2 : Term (n + s)} -> multisubst γ (If tg t1 t2) ≡ If (multisubst γ tg) (multisubst γ t1) (multisubst γ t2)
substPresIf {_} {_} {[]} {tg} {t1} {t2} = refl
substPresIf {_} {suc n} {x ∷ γ} {tg} {t1} {t2} =
  substPresIf {_} {n} {γ} {syntacticSubst (raiseTermℕ n x) zero tg}
                      {syntacticSubst (raiseTermℕ n x) zero t1}
                      {syntacticSubst (raiseTermℕ n x) zero t2}


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

  multiSubstTy : {{R : Semiring}} {n : ℕ}
            -> {γ : Vec (Term 0) n} {Γ : Context n} {A : Type} {t : Term n}
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

  reduxTheoremLet : {t1 v : Term s} {t2 : Term (suc s)}
                    -> multiRedux (Let t1 t2) ≡ v
                    -> Σ (Term s) (\v' -> multiRedux t1 ≡ Promote v')


-- This is about the structure of substitutions and relates to abs
 -- there is some simplification here because of the definition of ,, being
 -- incorrect
  substitutionResult : {{R : Semiring}}
      {n s : ℕ} {v1 : Term s} {γ1 : Vec (Term s) n} {t : Term (suc (n + s))}

   -> syntacticSubst v1 zero (multisubst {!γ1!} t)
    ≡ multisubst (v1 ∷ γ1) t


reduxAndSubstCombinedProm : {s n : ℕ} {γ : Vec (Term s) n} {v : Term s} {t : Term (n + s)} -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
reduxAndSubstCombinedProm {_} {_} {γ} {v} {t}  redux =
       let qr = cong multiRedux (substPresProm {_} {_} {γ} {t})
           qr' = trans qr (valuesDontReduce {_} {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')
