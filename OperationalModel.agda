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


-- # Substitution

-- `syntacticSubst {s} t x_pos t'` represents the situation:

-- G1             |- t       : A  -- substitutee
-- G2, x : A, G3  |- t'      : B  -- receiver
-- G1 + (G2,G3)   |- [t/x]t' : B

-- where |G1| = |G2|+|G3| = s

syntacticSubst : {s : ℕ} -> (t : Term s) -> Fin (suc s) -> (t' : Term (suc s)) -> Term s
syntacticSubst t x (Var y) = matchVar t x y
syntacticSubst t x (App t1 t2) = App (syntacticSubst t x t1) (syntacticSubst t x t2)
syntacticSubst t x (Abs t1) =
  Abs (syntacticSubst (raiseTerm t) (Data.Fin.suc x) t1)
syntacticSubst t x (Promote t1) = Promote (syntacticSubst t x t1)
syntacticSubst t x unit = unit
syntacticSubst t x vtrue = vtrue
syntacticSubst t x vfalse = vfalse
syntacticSubst t x (If t1 t2 t3) =
  If (syntacticSubst t x t1) (syntacticSubst t x t2) (syntacticSubst t x t3)
syntacticSubst t x (Let t1 t2) =
  Let (syntacticSubst t x t1) (syntacticSubst (raiseTerm t) (Data.Fin.suc x) t2)
syntacticSubst t x (tuple t1 t2) =
  tuple (syntacticSubst t x t1) (syntacticSubst t x t2)
syntacticSubst t x (LetProd t1 t2) =
  LetProd (syntacticSubst t x t1)
          (syntacticSubst (raiseTermℕ 2 t) (Data.Fin.suc (Data.Fin.suc x)) t2)

-- # Simultaneous substitution

{-
-- No longer needed but could be useful at some point

data Telescope : ℕ -> Set where
  Empty : Telescope 0
  Cons  : {s : ℕ} -> Term s -> Telescope s -> Telescope (suc s)

multisubstT : {s s' : ℕ} -> Telescope s -> Term (s' + s) -> Term s'
multisubstT {zero} {s'} Empty t' = t'
multisubstT {suc s} {s'} (Cons t ts) t' =
  multisubstT {s} {s'} ts (syntacticSubst (raiseTermℕ s' t) zero t')
-}

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

-- Simultaneous substitution
multisubst : {s n : ℕ} -> (xs : Vec (Term s) n) -> Term (n + s) -> Term s
multisubst [] t' = t'
multisubst {s} {suc n} (t ∷ ts) t' =
  multisubst {s} {n} ts (syntacticSubst (raiseTermℕ n t) zero t')

-- Note that it might be easier to reason about this with closed terms
-- i.e., is s == 0 in the above

-- Simultaneous substitution under a binder at position 0
multisubst' : {s n : ℕ} -> (xs : Vec (Term (suc s)) n) -> Term (suc (n + s)) -> Term (suc s)
multisubst' [] t' = t'
multisubst' {s} {suc n} (t ∷ ts) t' =
  multisubst' {s} {n} ts (syntacticSubst (raiseTermℕ n t) (suc zero) t')

-- ## (Simultaneous) substitution commutates with terms
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

substPresTuple : {s n : ℕ} {γ : Vec (Term s) n} {t1 t2 : Term (n + s)}
    -> multisubst γ (tuple t1 t2) ≡ tuple (multisubst γ t1) (multisubst γ t2)
substPresTuple {s} {.zero} {[]} {t1} {t2} = refl
substPresTuple {s} {suc n} {x ∷ γ} {t1} {t2} =
  substPresTuple {_} {n} {γ} {syntacticSubst (raiseTermℕ n x) zero t1} {syntacticSubst (raiseTermℕ n x) zero t2}

-- ## Other properties of substitution

-- Substitutions to different head variables commutes
-- TODOABLE
substComm : {s n : ℕ} {v : Term n} {t : Term (suc (suc (s + n)))} {x : Term n}
         -> (syntacticSubst (raiseTermℕ s v) zero
               (syntacticSubst (raiseTermℕ s (raiseTerm x)) (suc zero) t))

          ≡ (syntacticSubst (raiseTermℕ s x) zero
               (syntacticSubst (raiseTermℕ (suc s) v) zero t))
substComm {s} {n} {v} {Var y} {x} with Data.Fin.compare y zero
... | k = {!!}
substComm {s} {n} {v} {App t1 t2} {x} = {!!}
substComm {s} {n} {v} {Abs t} {x} = {!!}
substComm {s} {n} {v} {unit} {x} = {!!}
substComm {s} {n} {v} {Promote t} {x} = {!!}
substComm {s} {n} {v} {Let t1 t2} {x} = {!!}
substComm {s} {n} {v} {vtrue} {x} = {!!}
substComm {s} {n} {v} {vfalse} {x} = {!!}
substComm {s} {n} {v} {If t0 t1 t2} {x} = {!!}
substComm {s} {n} {v} {tuple t1 t2} {x} = {!!}
substComm {s} {n} {v} {LetProd t1 t2} {x} = {!!}

-- A simultaneous substitution can be re-organised, moving the head substitution
-- to happen after the tail substitutions
multiSubstComm :
     {s n : ℕ} {γ : Vec (Term n) s} {v : Term n} {t : Term (suc (s + n))}
    ->    syntacticSubst v zero (multisubst' (map raiseTerm γ) t)
        ≡ multisubst γ (syntacticSubst (raiseTermℕ s v) zero t)
multiSubstComm {.zero} {n} {[]} {v} {t} rewrite raiseTermℕzero {n} {v} = refl
multiSubstComm {suc s} {n} {x ∷ γ} {v} {t} rewrite sym (substComm {s} {n} {v} {t} {x}) =
  multiSubstComm {s} {n} {γ} {v} {syntacticSubst (raiseTermℕ s (raiseTerm x)) (suc zero) t}

-- # Reduction

-- Untyped reduction
untypedRedux : {s : ℕ} -> Term s -> Maybe (Term s)
untypedRedux (App (Abs t) t') = just (syntacticSubst t' Data.Fin.zero t)
untypedRedux (App t1 t2) with untypedRedux t1
... | just t1' = just (App t1' t2)
... | nothing  = nothing
untypedRedux (If vtrue t1 _) = just t1
untypedRedux (If vfalse _ t2) = just t2
untypedRedux (If t t1 t2) with untypedRedux t
... | just t' = just (If t' t1 t2)
... | nothing = nothing
untypedRedux (Let (Promote t1) t2) = just (syntacticSubst t1 zero t2)
untypedRedux (LetProd (tuple t1 t2) t) = just (syntacticSubst t2 zero (syntacticSubst (raiseTerm t1) zero t))
untypedRedux _ = nothing

{-# TERMINATING #-}
multiRedux : {s : ℕ} -> Term s -> Term s
multiRedux t with untypedRedux t
... | just t' = multiRedux t'
... | nothing = t

determinism : {t t1 t2 : Term s}
             -> multiRedux t ≡ t1
             -> multiRedux t ≡ t2
             -> t1 ≡ t2
determinism prf1 prf2 = trans (sym prf1) prf2

postulate
   -- TODOABLE
   valuesDontReduce : {s : ℕ} {t : Term s} -> Value t -> multiRedux t ≡ t


postulate
  -- Potentially remove (refactor)
  multReduxCongruence : {t1 v : Term s} {C : Term s -> Term s}
                   -> multiRedux t1 ≡ v -> multiRedux (C t1) ≡ multiRedux (C v)

  -- Proposition 1 (type safety)
  preservation : {{R : Semiring}} {Γ : Context s} {A : Type} {t : Term s}
             -> Γ ⊢ t ∶ A
             -> Γ ⊢ multiRedux t ∶ A

-- # Full-beta equality (which includes equality inside of abs)

data FullBetaEq : {s : ℕ} -> Term s -> Term s -> Set where
  VarEq     : {x : Fin (suc s)} -> FullBetaEq (Var x) (Var x)
  AppEq     : {t1 t1' t2 t2' : Term s} -> FullBetaEq t1 t1' -> FullBetaEq t2 t2' -> FullBetaEq (App t1 t2) (App t1' t2')
  AbsEq     : {t1 t2 : Term (suc s)} -> FullBetaEq t1 t2 -> FullBetaEq (Abs t1) (Abs t2)
  UnitEq    : FullBetaEq (unit {s}) (unit {s})
  PromoteEq : {t1 t2 : Term s} -> FullBetaEq t1 t2 -> FullBetaEq (Promote t1) (Promote t2)
  VTrue     : FullBetaEq (vtrue {s}) (vtrue {s})
  VFalse    : FullBetaEq (vfalse {s}) (vfalse {s})
  IfEq      : {t t' t1 t1' t2 t2' : Term s} -> FullBetaEq t t' -> FullBetaEq t1 t1' -> FullBetaEq t2 t2'
               -> FullBetaEq (If t t1 t2) (If t' t1' t2')
  BetaEq    : {t1 : Term (suc s)} {t2 : Term s} -> FullBetaEq (App (Abs t1) t2) (syntacticSubst t2 Data.Fin.zero t1)
  EmbedRedux : {t : Term s} -> FullBetaEq (multiRedux t) t
  LetEq     : {t1 t1' : Term s} {t2 t2' : Term (suc s)} -> FullBetaEq t1 t1' -> FullBetaEq t2 t2' -> FullBetaEq (Let t1 t2) (Let t1' t2')
  TupleEq   : {t1 t2 t1' t2' : Term s} -> FullBetaEq t1 t1' -> FullBetaEq t2 t2' -> FullBetaEq (tuple t1 t2) (tuple t1' t2')
  ProdLetEq : {t1 t1' : Term s} {t2 t2' : Term (suc (suc s))}
             -> FullBetaEq t1 t1'
             -> FullBetaEq t2 t2'
             -> FullBetaEq (LetProd t1 t2) (LetProd t1' t2')
  -- TODO: add tuples
  Redux     : {s : ℕ} {t1 t2 : Term s} -> multiRedux t1 ≡ multiRedux t2 -> FullBetaEq t1 t2

open FullBetaEq

_==_ : Term s -> Term s -> Set
t == t' = FullBetaEq t t'

-- Equality embeds into full beta eq

embedEq : {t1 t2 : Term s} -> t1 ≡ t2 -> FullBetaEq t1 t2
embedEq {_} {Var x} {Var .x} refl = VarEq
embedEq {_} {App t1 t2} {App .t1 .t2} refl =
  AppEq (embedEq {_} {t1} {t1} refl) (embedEq {_} {t2} {t2} refl)
embedEq {_} {Abs t1} {Abs t2} prf = AbsEq (embedEq (aux prf))
  where
    aux : Abs t1 ≡ Abs t2 -> t1 ≡ t2
    aux prf with prf
    ... | refl = refl
embedEq {_} {unit} {unit} refl = UnitEq {_}
embedEq {_} {Promote t1} {Promote .t1} refl = PromoteEq (embedEq {_} {t1} {t1} refl)
embedEq {_} {vtrue} {vtrue} refl = VTrue {_}
embedEq {_} {vfalse} {vfalse} refl = VFalse {_}
embedEq {_} {If t1 t2 t3} {If .t1 .t2 .t3} refl =
  IfEq (embedEq {_} {t1} {t1} refl) (embedEq {_} {t2} {t2} refl) (embedEq {_} {t3} {t3} refl)
embedEq {_} {Let e1 e2} {Let e3 e4} refl = LetEq ((embedEq {_} {e1} {e3} refl)) ( (embedEq {_} {e2} {e4} refl))
embedEq {_} {tuple t1 t2} {tuple .t1 .t2} refl =
  TupleEq (embedEq {_} {t1} {t1} refl) (embedEq {_} {t2} {t2} refl)
embedEq {_} {LetProd t1 t2} {LetProd .t1 .t2} refl =
  ProdLetEq (embedEq {_} {t1} {t1} refl) (embedEq {_} {t2} {t2} refl)

postulate
  transFullBetaEq : {t1 t2 t3 : Term s} -> t1 == t2 -> t2 == t3 -> t1 == t3



postulate
  -- TODOABLE
  multiSubstHere : {s n : ℕ} {t : Term s} {γ : Vec (Term s) n}
                  -> multisubst (t ∷ γ) (Var zero) ≡ t

  -- TODOABLE
  multiSubstThere : {s n : ℕ} {t : Term s} {γ : Vec (Term s) n}
       -> multisubst γ (matchVar (raiseTermℕ n t) zero (raiseR 0 (fromℕ (n + s))))
         ≡ t

-- # Properties of reduction

betaUnderMultiRedux : {bod : Term (suc s)} {t2 : Term s}
             -> multiRedux (App (Abs bod) t2)
              ≡ multiRedux (syntacticSubst t2 zero bod)
betaUnderMultiRedux {s} {bod} {t2} = refl

isSimultaneous' : {s n : ℕ} {t : Term s} {t' : Term s} {γ : Vec (Term s) n}
  -> multiRedux (multisubst (t ∷ γ) (Var zero)) ≡ t'
  -> multiRedux t ≡ t'
isSimultaneous' {s} {n} {t} {t'} {γ} p rewrite multiSubstHere {s} {n} {t} {γ} = p

isSimultaneousGen : {s n s1 : ℕ} {t : Term s} {t' : Term s}
                    {γ : Vec (Term s) n} -- (fromℕ n)
  -> multiRedux (multisubst γ (matchVar (raiseTermℕ n t) zero (raiseR 0 (fromℕ (n + s))))) ≡ t'
  -> multiRedux t ≡ t'
isSimultaneousGen {s} {n} {s1} {t} {t'} {γ} p rewrite (multiSubstThere {s} {n} {t} {γ}) = p


reduxProm : {v : Term s} -> multiRedux (Promote v) ≡ Promote v
reduxProm {v} = refl

reduxAbs : {t : Term (suc s)} -> multiRedux (Abs t) ≡ Abs t
reduxAbs = refl

reduxFalse : multiRedux {_} vfalse ≡ vfalse
reduxFalse = refl

reduxTrue : multiRedux {_} vtrue ≡ vtrue
reduxTrue = refl

reduxUnit : multiRedux {_} unit ≡ unit
reduxUnit = refl

substMultiRedux : {t t' v : Term s} -> t ≡ t' -> multiRedux t ≡ v -> multiRedux t' ≡ v
substMultiRedux {_} {t} {t'} {v} prf prf' = subst (\h -> multiRedux h ≡ v) prf prf'

postulate -- postulate now for development speed
  reduxTheoremApp : {sz : ℕ} {t1 t2 t v : Term sz}
                 -> multiRedux (App t1 t2) ≡ v
                 -> Σ (Term (suc sz)) (\v1' -> multiRedux t1 ≡ Abs v1')

   --  t1 ↓ \x.t   t2 ↓ v2   t[v2/x] ↓ v3
   -- --------------------------------------
   --   t1 t2 ⇣ v3

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

  reduxTheoremLet : {t1 : Term s} {t2 : Term (suc s)} {v : Term s}
                    -> multiRedux (Let t1 t2) ≡ v
                    -> Σ (Term s) (\e -> multiRedux t1 ≡ Promote e × multiRedux (syntacticSubst e zero t2) ≡ v)


reduxAndSubstCombinedProm : {s n : ℕ} {γ : Vec (Term s) n} {v : Term s} {t : Term (n + s)}
  -> multiRedux (multisubst γ (Promote t)) ≡ v -> Promote (multisubst γ t) ≡ v
reduxAndSubstCombinedProm {_} {_} {γ} {v} {t}  redux =
       let qr = cong multiRedux (substPresProm {_} {_} {γ} {t})
           qr' = trans qr (valuesDontReduce {_} {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym redux) qr')


-- -- Substitution lemma
-- -- TODO: Vilem
--
postulate
  substitution : {{R : Semiring}} {s1 s2 : ℕ} {Γ : Context ((1 + s1) + s2)} {Γ1 : Context s1} {Γ2 : Context (s1 + s2)} {Γ3 : Context s2} {r : grade} {A B : Type} {t1 : Term ((1 + s1) + s2)} {t2 : Term (s1 + s2)}
       -> Γ ⊢ t1 ∶ B
       -> (pos : Γ ≡ ((Ext Γ1 (Grad A r)) ,, Γ3))
       -> Γ2 ⊢ t2 ∶ A
       -> ((Γ1 ,, Γ3) ++ (r · Γ2)) ⊢ syntacticSubst t2 (raiseR s2 (fromℕ s1)) t1 ∶ B

{-
substitution {s1} {s2} {Γ} {Γ1} {Γ2} {Γ3} {.1r} {A} {.A} {Var x} {t2} (var (Here .Γ1 .A (Γ1' , allZeroesPrf))) prf substitee
  rewrite allZeroesPrf | absorptionContext {Γ1'} {1r · Γ2} | leftUnitContext {Γ2} =
     t2 , substitee
-}

postulate
  strongNormalisation : {{R : Semiring}} {A : Type} {t : Term 0}
                           -> Empty ⊢ t ∶ A
                           -> Value (multiRedux t)
