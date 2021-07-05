{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModelGhost where

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

open import Semiring

-- open Semiring.Semiring {{...}} public
-- open NonInterferingSemiring  {{...}} public
-- open InformationFlowSemiring {{...}} public

open import RelationalModel

data InfoContext {{ R : Semiring }} : (r : grade) (adv : grade) -> Set where
  Visible :   {r adv : grade}  -> r ≤ adv -> InfoContext r adv
  Invisible : {r adv : grade}  -> ¬ (r ≤ adv) -> InfoContext r adv

-- Contexts

-- unary
[_]Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> List Term -> Set
[ (Γ , ghostGrade) ]Γg γ = [ Γ ]Γ γ × ⊤

-- binary
⟦_⟧Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> (adv : grade) -> List Term -> List Term -> Set
⟦ (Γ , ghostGrade)   ⟧Γg adv γ1 γ2 = ⟦ Γ ⟧Γ adv γ1 γ2 × InfoContext ghostGrade adv

injPair1 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> a ≡ a'
injPair1 refl = refl

injPair2 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> b ≡ b'
injPair2 refl = refl

binaryImpliesUnaryGg : {{R : Semiring}} {sz : ℕ} { Γ : Context sz } {adv : grade} {γ1 γ2 : List Term}
                    -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ([ Γ ]Γ γ1) × ([ Γ ]Γ γ2)
binaryImpliesUnaryGg {.0} {Empty} {adv} {_} {_} pre = tt , tt
binaryImpliesUnaryGg {suc sz} {Ext Γ (Grad A r)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} (arg , rest)
  with binaryImpliesUnary {Box r A} {Promote v1} {Promote v2} {adv} arg | binaryImpliesUnaryG {sz} {Γ} {adv} {γ1} {γ2} rest
... | ( arg1 , arg2 ) | ( rest1 , rest2 ) = ( (arg1 , rest1) , (arg2 , rest2) )

promoteLemma : {t t' t'' : Term} -> Promote t ≡ t' -> Σ Term (\t'' -> Promote t'' ≡ t')
promoteLemma {t} {t'} {t''} pre = {!!}

-- # IDEA 1
{-# TERMINATING #-}
biFundamentalTheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2
        -> ⟦ Box ghost τ ⟧e adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))

biFundamentalTheoremGhost {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux
 rewrite injPair1 pos | sym (injPair2 pos) | sym v1redux | sym v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as position in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- goal : ghost ≤ adv
    -- eq   : 1 ≤ adv
    ... | boxInterpBiobs   eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiobs eq a1 a2 inner

    ... | boxInterpBiunobs eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiunobs eq a1 a2 inner

-- var generalisation here
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost {sz} {Γ} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

-- # IDEA 2
{-# TERMINATING #-}
biFundamentalTheoremGhost2 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {r : grade} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2
        -> ⟦ Box r τ ⟧e adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))

biFundamentalTheoremGhost2 {_} {Γ} {r} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | sym (injPair2 pos) | sym v1redux | sym v2redux with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc
  where
    conc : ⟦ Box r τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner
      rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
      -- eq : 1 ≤ adv
      -- goal: r ≤ adv
      -- we know ghost = 1 but doesn't factor into it really
          boxInterpBiobs {!!} {!!} {!!} {!!}

    ... | boxInterpBiunobs eq .a1 .a2 inner = {!!}

  -- (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
  -- (Promote (multisubst' 1 γ1' a1)) (Promote (multisubst' 1 γ2' a2))
  -- conc -- with argInterp ? ? ? ? -- argInterp (Promote a1) (Promote a2) refl refl
  -- ... | zeb = ?

-- gen for any variable
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost2 {sz} {Γ} {r} {ghost} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

-- # IDEA 3
{-# TERMINATING #-}
biFundamentalTheoremGhost3 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (adv # ghost) γ1 γ2
        -> ⟦ τ ⟧e          (adv # ghost) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost3 {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | injPair2 pos | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as p```r`tosition in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ τ ⟧v (adv # 1R) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- inner     : ⟦ τ ⟧e ((R'' InformationFlowSemiring.# adv) 1R) a1 a2
    -- eq        : ghost ≤ adv # ghost
    -- goal      : ⟦ τ ⟧v adv v1 v2
    ... | boxInterpBiobs   eq .a1 .a2 inner =
        let eqa1 = isSimultaneous' {v1} {a1} {γ1'} v1redux
            eqa2 = isSimultaneous' {v2} {a2} {γ2'} v2redux
        in inner v1 v2 eqa1 eqa2
        -- eq : ¬ (1 ≤ (adv # 1r))
        --ghost = 1
    ... | boxInterpBiunobs eq .a1 .a2 inner =
      ⊥-elim (eq (subst (\h -> 1R ≤ h) (sym (absorb# {R} {adv})) (reflexive≤ {1R})))

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost3 {_} {Γ} {ghost} {e} {τ} typing {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}



-- Non-interference result for the ghost calculus
nonInterferenceGhost :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
   {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> (Ext Empty (Grad BoolTy s) , r) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> (Empty , default) ⊢ v1 ∶ BoolTy
        -> (Empty , default) ⊢ v2 ∶ BoolTy
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterferenceGhost {{R}} {{R'}} {{R''}} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 with
    -- we can think of r as the adversary

    -- Apply fundamental binary theorem to v1
    biFundamentalTheoremGhost3 {zero} {Empty} {s *R default} {Promote v1} {Box s BoolTy}
    --  Invisible {s *R default} {r} {!trans pre (sym (unit# {s})) !}
                  (pr {_} {(Empty , default)} {Empty , s *R default} {s} {BoolTy} {v1} v1typing {refl}) {[]} {[]} r (tt , Invisible {!!} ) (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue v1))
                  (valuesDontReduce {Promote v1} (promoteValue v1))
    -- Apply fundamental binary theorem to v2
  | biFundamentalTheoremGhost3 {zero} {Empty} {s *R default} {Promote v2} {Box s BoolTy}
                  (pr {_} {(Empty , default )} {Empty , s *R default} {s} {BoolTy} {v2} v2typing {refl})  {[]} {[]} r (tt , Visible {!!}) (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  -- goal : s ≤ r
                  -- pre : r ≤ s
                  -- pre1 : s ≤ (r # (s * default))
... | boxInterpBiobs pre1 .v1 .v1 inner1 |  boxInterpBiobs pre2 .v2 .v2 inner2 = ⊥-elim {!!} --(nonEq (antisymmetry pre {!!}))
... | boxInterpBiobs pre1 .v1 .v1 inner1 | boxInterpBiunobs pre2 .v2 .v2 inner2 = ⊥-elim (⊥-elim (pre2 pre1))
... | boxInterpBiunobs pre1 .v1 .v1 inner1 | boxInterpBiobs pre2 .v2 .v2 inner2 = ⊥-elim (⊥-elim (pre1 pre2))
... | boxInterpBiunobs pre1 .v1 .v1 (valv1 , valv1') | boxInterpBiunobs pre2 .v2 .v2 (valv2 , valv2') =
 let
   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v1typing
   (v1'' , prf1) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} {Empty} {Box r BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValuesG substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v2typing
   (v2'' , prf2) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} substTy2) (multiReduxProducesValuesG substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   inner' = subst (\h -> ⟦ Box s BoolTy ⟧e h (Promote v1) (Promote v2)) (sym (idem# {R} {r})) (inner valv1' valv2')
   res = biFundamentalTheoremGhost3 {1} {Ext Empty (Grad BoolTy s)} {r} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
          ((inner' , tt) , Visible {r} {r # r} (subst (\h -> r ≤ h) (sym (idem# {R} {r})) reflexive≤)) (Promote v1'') (Promote v2'') prf1 prf2


   -- Boolean typed (low) values are equal inside the binary interepration
   res' = subst (\h -> ⟦ Box r BoolTy ⟧v h (Promote v1'') (Promote v2'')) (idem# {R} {r}) res
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' (unpack res') -- res

   -- Plug together the equalities
     -- Promote
   eq = PromoteEq {v1''} {v2''} (embedReduxCong {v1''} {v2''} boolTyEq)
   eq2 = transFullBetaEq (embedEq prf1) eq

 in transFullBetaEq eq2 (embedEq (sym prf2))
   where

     inner : [ BoolTy ]e v1 -> [ BoolTy ]e v2 -> ⟦ Box s BoolTy ⟧e r (Promote v1) (Promote v2)
     inner av1 av2 v3 v4 v3redux v4redux
       rewrite trans (sym v3redux) (valuesDontReduce {Promote v1} (promoteValue v1))
             | trans (sym v4redux) (valuesDontReduce {Promote v2} (promoteValue v2)) =
       boxInterpBiunobs (antisymmetryAlt {R} {R'} {r} {s} pre nonEq) v1 v2 (av1 , av2)

     -- Helper to unpack interpretation type
     unpack : {v1 v2 : Term} -> ⟦ Box r BoolTy ⟧v r (Promote v1) (Promote v2) -> ⟦ BoolTy ⟧e r v1 v2
     unpack {v1} {v2} (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp
     unpack {v1} {v2} (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq (reflexive≤ {r}))
