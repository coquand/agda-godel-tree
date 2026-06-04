{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.GLCodeNodesN -- the number-code analog of T4.GLCodeNodes : the k-varying
-- threshold handle and its context inside the HONEST guard's code.
--
-- The KdefN guard is  leq (var 0) predN = eqF (ap2 sub (var 0) predN) O  with
--   predNof k = exp3 (s (exp2 (natCode k)))   ( = N = 3^(2^k+1) , symbolic ).
-- The only k-varying handle inside its codeFormula is  codeTerm (natCode k) ;
-- everything around it is a fixed Pair-context  Cform'N .  This is the binary-
-- sub re-pointing of GLCodeNodes.Cform / piece / H ( the szLeqApp handle ).
-- W / Wctx / W_plug are reused VERBATIM ( generic ).

module T4.GLCodeNodesN where

open import T4.Base
open import T4.Tags using ( tag_eq ; tag_ap1 ; tag_ap2 ; tag_var )
open import T4.Code using ( codeFun1 ; codeFun2 ; codeTerm ; codeFormula )
open import T4.ProgEnc using ( nodes )
open import T4.ProgNodes using
  ( Ctx ; hole ; inAp1 ; inAp2L ; inAp2R ; plug ; nodesCtx ; nodes_plug )
open import T4.GLCodeNodes using ( W ; Wctx ; W_plug )
open import T4.Exp  using ( exp2 )
open import T4.Exp3 using ( exp3 )

open import BRA3.Church using ( sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.Code.Tag using ( addN )

------------------------------------------------------------------------
-- SECTION 1.  The threshold term  predNof k = 3^(2^k+1) ( symbolic ).

predNof : Nat -> Term
predNof k = ap1 exp3 (ap1 s (ap1 exp2 (natCode k)))

------------------------------------------------------------------------
-- SECTION 2.  The k-varying handle  pieceN k = codeTerm (natCode k)  and its
-- one-step  s-context.   codeTerm (natCode (suc k)) = ap2 Pair tag_ap1
--   (ap2 Pair (codeFun1 s) (codeTerm (natCode k))) .

pieceN : Nat -> Term
pieceN k = codeTerm (natCode k)

CsN : Ctx
CsN =
  inAp2R Pair (natCode tag_ap1)
    (inAp2R Pair (codeFun1 s) hole)

abstract
  pieceN_suc : (k : Nat) -> Eq (pieceN (suc k)) (plug CsN (pieceN k))
  pieceN_suc k = refl

------------------------------------------------------------------------
-- SECTION 3.  Cform'N : the fixed Pair-context inside  codeFormula (leq (var 0)
-- (predNof k))  reaching  pieceN k .   ( codeFormula (atomic (eqn A O)) =
-- Pair tag_eq (Pair (codeTerm A) O) ;  A = ap2 sub (var 0) predN ;
-- codeTerm predN = ap1-tower exp3 / s / exp2 over codeTerm (natCode k). )

Cform'N : Ctx
Cform'N =
  inAp2R Pair (natCode tag_eq)
   (inAp2L Pair
     (inAp2R Pair (natCode tag_ap2)
       (inAp2R Pair (codeFun2 sub)
         (inAp2R Pair (codeTerm (var zero))
           (inAp2R Pair (natCode tag_ap1)
             (inAp2R Pair (codeFun1 exp3)
               (inAp2R Pair (natCode tag_ap1)
                 (inAp2R Pair (codeFun1 s)
                   (inAp2R Pair (natCode tag_ap1)
                     (inAp2R Pair (codeFun1 exp2) hole)))))))))
     O)

abstract
  Cform'N_eq :
    (k : Nat) ->
    Eq (codeFormula (leq (var zero) (predNof k))) (plug Cform'N (pieceN k))
  Cform'N_eq k = refl

------------------------------------------------------------------------
-- SECTION 4.  The diagonal-level handle  H'N k = W (pieceN k)  and its
-- affine node recurrence ( deltaN = nodesCtx (Wctx CsN) ).

H'N : Nat -> Term
H'N k = W (pieceN k)

deltaN : Nat
deltaN = nodesCtx (Wctx CsN)

nodes_H'N_suc :
  (k : Nat) -> Eq (nodes (H'N (suc k))) (addN deltaN (nodes (H'N k)))
nodes_H'N_suc k =
  eqSubst (\ z -> Eq (nodes (W z)) (addN deltaN (nodes (H'N k))))
          (eqSym (pieceN_suc k))
          (eqTrans (eqCong nodes (W_plug CsN (pieceN k)))
                   (nodes_plug (Wctx CsN) (W (pieceN k))))
