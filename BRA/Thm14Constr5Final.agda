{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm14Constr5Final
--
-- Phase B of the Theorem 14 closure (NEXT-SESSION-THM14-CONSTR5.md):
-- definitions of the sb-chain Fun1 functors  f_part, g_part, K_part,
-- h_part, constr5 .
--
-- Each is built from BRA's combinator algebra: Comp2 / KT / I / cor /
-- D_thmT (= Thm 12 result on thmT) / D_sub (= Thm 12 result on sub).
-- The chosen construction makes  ap1 F x  BRA-equationally reduce to
-- the Term form of Guard's encoded sb-chain (so that Phase C's
-- step5_l can match these against thmTDispMp_param /
-- thmTDispRuleInst_param outputs).
--
-- Phase C (proofs of the per-step BRA-internal implications under
-- hypothesis  P = PrAtX x ) consumes these definitions and chains
-- thmTDispMp_param + thmTDispRuleInst_param + cor-bridge derivations
-- (see BRA/COR-AT-SB-LOAD-BEARING.md) into the final
--   step5_l : (x : Term) ->
--             Deriv (PrAtX x imp atomic (eqn (ap1 thmT (ap1 constr5 x))
--                                             (reify (codeFormula bot))))
-- contract that BRA.GoedelII.Compose consumes.
--
-- ASCII only.  No postulates, no holes, no with-abstraction, no dot
-- patterns.  No new Deriv constructors, no new tagged dispatchers in
-- BRA/Thm/ThmT.agda.

module BRA.Thm14Constr5Final where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor      using (cor)
open import BRA.Sub      using (sub)

open import BRA.Thm.ThmT using (thmT)
open import BRA.Thm.TagCodes
  using (tagCode_mp ; tagCode_ruleInst)

open import BRA.Thm12
  using (Thm12_F1_Result ; Thm12_F2_Result)

open import BRA.GoedelII using (i ; cG)
open import BRA.Thm14Numerals using (t_term ; t'_term)

----------------------------------------------------------------------
-- Convenience constants.

private
  varCode0T : Term
  varCode0T = reify (code (var zero))

  varCode1T : Term
  varCode1T = reify (code (var (suc zero)))

  varCode2T : Term
  varCode2T = reify (code (var (suc (suc zero))))

  -- Reify of a closed Tree, plus KT-of-reify.

  KTr : Tree -> Fun1
  KTr v = KT (reify v)

  -- Pair-of-two-Fun1-evaluations: ap1 (pairF1 f g) x = ap2 Pair (f x) (g x).
  pairF1 : Fun1 -> Fun1 -> Fun1
  pairF1 f g = Comp2 Pair f g

  -- Constant Term-valued Fun1 (works for canonical reify-of-Tree
  -- inputs; for non-canonical c, falls through KT's Z-default).
  constTermF1 : Term -> Fun1
  constTermF1 c = KT c

  -- Const-via-(D_sub i i)-shaped Fun1 (for when c = ap2 g a b is
  -- non-canonical).  ap1 (constApp2F1 g a b) x = ap2 g a b , using
  -- KT a / KT b on the closed canonical operands.
  constApp2F1 : Fun2 -> Term -> Term -> Fun1
  constApp2F1 g a b = Comp2 g (KT a) (KT b)

----------------------------------------------------------------------
-- The Th14Constr5Final module proper.
--
-- Parameters:  the Theorem 12 results on  thmT  and  sub , exposing the
-- Fun1 / Fun2 functors  D_thmT  and  D_sub .

module Th14Constr5Final
  (r12_th  : Thm12_F1_Result thmT)
  (r12_sub : Thm12_F2_Result sub)
  where

  --------------------------------------------------------------------
  -- D_thmT : Fun1 .  Applied to x , gives the Tree (as a Term) coding
  -- "th(num x) = num(thmT x)" 's proof in BRA (Thm 13's output for
  -- thmT ).  Depends on x.

  D_thmT : Fun1
  D_thmT = Thm12_F1_Result.Df r12_th

  --------------------------------------------------------------------
  -- D_sub : Fun2 .  Applied to (a, b) , gives the encoded proof of
  -- "sub(num a, num b) = num(sub a b)" .  Closed in our usage at
  -- (i, i) .

  D_sub : Fun2
  D_sub = Thm12_F2_Result.Dg r12_sub

  --------------------------------------------------------------------
  -- D_sub_at_ii : the constant-Fun1 evaluating to  ap2 D_sub i i .
  -- Used as the "Dsub(i,i)" leaf in  g_part  and  h_part .

  D_sub_at_ii : Fun1
  D_sub_at_ii = constApp2F1 D_sub i i

  --------------------------------------------------------------------
  -- Closed Term-encoded constants for the sb-chain "+1" steps.
  --
  -- The substituents of f_part 's three sb headers are:
  --   var 0  ->  ap1 cor x      (depends on x)
  --   var 1  ->  reify (code (reify (codeFormula sub_ii_form)))   (closed)
  --   var 2  ->  i               (closed)
  --
  -- For the "var 1" position we substitute the numeral "sub(i,i)" 's
  -- code (= reify (code (reify (codeFormula <sub(i,i)=...>)))).  This
  -- is closed; we expose it as  sub_ii_subst  so the per-step proofs
  -- can refer to it by name.
  --
  -- The exact closed Term used depends on Guard's Definition 12
  -- "underlined" convention (the substituent at var 1 is the Term
  -- whose Goedel code is "sub(i,i)" 's coding number).  Per
  -- corOfReify the canonical choice is  ap1 cor (ap2 sub i i) .
  -- (Computationally  cor  of a canonical reify-of-Tree input is
  -- equal to  reify (code <input>) ; see BRA/Cor.agda for the full
  -- specification.)

  sub_ii_subst : Term
  sub_ii_subst = ap1 cor (ap2 sub i i)

  --------------------------------------------------------------------
  -- f_part : the inner sb-chain on Guard's transitivity numeral t_term .
  --
  -- Encoded as the 3-deep ruleInst chain
  --   ruleInst 2 i (ruleInst 1 sub_ii_subst (ruleInst 0 (ap1 cor x) t_term))
  --
  -- which at the Term level is
  --   Pair tagCode_ruleInst (Pair varCode2T (Pair inner1(x) i))
  -- with
  --   inner1(x) = Pair tagCode_ruleInst (Pair varCode1T (Pair inner2(x) sub_ii_subst))
  --   inner2(x) = Pair tagCode_ruleInst (Pair varCode0T (Pair (reify t_term) (cor x)))

  f_part_inner2 : Fun1
  f_part_inner2 =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (constTermF1 varCode0T)
                   (pairF1 (constTermF1 (reify t_term))
                           cor))

  f_part_inner1 : Fun1
  f_part_inner1 =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (constTermF1 varCode1T)
                   (pairF1 f_part_inner2
                           (constTermF1 sub_ii_subst)))

  f_part : Fun1
  f_part =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (constTermF1 varCode2T)
                   (pairF1 f_part_inner1
                           (constTermF1 i)))

  --------------------------------------------------------------------
  -- g_part : encMp ( encMp ( f_part(x), Dth(x) ), Dsub(i,i) ) .
  --
  -- Step 3 (Guard p.17 line 3): chain f_part with steps 1 + 2 to get
  -- the encoded "th(cor x) = sub(i,i)" .

  g_part_inner : Fun1
  g_part_inner =
    pairF1 (constTermF1 tagCode_mp)
           (pairF1 f_part D_thmT)

  g_part : Fun1
  g_part =
    pairF1 (constTermF1 tagCode_mp)
           (pairF1 g_part_inner D_sub_at_ii)

  --------------------------------------------------------------------
  -- K_part : the single sb-step at var 1 of  numJ = i (the code of G).
  --
  -- Guard p.17 line 4:  th(K(x)) = "th(cor x) ≠ sub(i,i)" under
  -- hypothesis  th(x) = j .  K_part(x) is  ruleInst 1 (cor x) on the
  -- proof index  x  itself: under hypothesis  th(x) = j , the inner
  -- sb-step substitutes  cor x  for var 1 of  j  (= the code of G ),
  -- yielding the code of "th(cor x) ≠ sub(i,i)" .
  --
  -- Encoded form:
  --   Pair tagCode_ruleInst (Pair varCode1T (Pair x (cor x)))
  --
  -- The proof index slot is x itself (the Term-level reference to
  -- Guard's "th(x) = j" -bearing variable); the substituent slot is
  -- ap1 cor x .

  K_part : Fun1
  K_part =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (constTermF1 varCode1T)
                   (pairF1 I cor))

  --------------------------------------------------------------------
  -- h_part : analogous to f_part / g_part but on the ex-falso numeral
  -- t'_term .  Substitutes:
  --   var 0  ->  ap1 cor x                (depends on x; "th(x_)" code)
  --   var 1  ->  sub_ii_subst             (closed; "sub(i,i)" code)
  --
  -- Only TWO sb-headers (versus f_part 's three) since t' has free
  -- variables  x_0 , x_1  only.

  h_part_inner1 : Fun1
  h_part_inner1 =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (constTermF1 varCode0T)
                   (pairF1 (constTermF1 (reify t'_term))
                           cor))

  h_part_skel : Fun1
  h_part_skel =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (constTermF1 varCode1T)
                   (pairF1 h_part_inner1
                           (constTermF1 sub_ii_subst)))

  -- Outer mp's: combine h_part_skel with Dth(x) and Dsub(i,i) to
  -- internalise the ex-falso conclusion  "(th(cor x) = sub(i,i)) ⊃ ((th(cor x) ≠ sub(i,i)) ⊃ (0 = 1))" .
  --
  -- Mirroring g_part 's two-mp wrapping.

  h_part_thxLayer : Fun1
  h_part_thxLayer =
    pairF1 (constTermF1 tagCode_mp)
           (pairF1 h_part_skel D_thmT)

  h_part : Fun1
  h_part =
    pairF1 (constTermF1 tagCode_mp)
           (pairF1 h_part_thxLayer D_sub_at_ii)

  --------------------------------------------------------------------
  -- constr5 : Guard's "F(x)" .  Outer assembly:
  --   constr5(x) = encMp ( encMp ( h_part(x), g_part(x) ), K_part(x) )
  --
  -- Reading: under hypothesis  th(x) = j , h_part(x) gives
  --   "(th(cor x) = sub(i,i)) ⊃ ((th(cor x) ≠ sub(i,i)) ⊃ (0 = 1))" ,
  -- g_part(x) gives "(th(cor x) = sub(i,i))" , K_part(x) gives
  -- "(th(cor x) ≠ sub(i,i))" .  Two outer mp's collapse the chain to
  -- "(0 = 1)" .

  constr5_inner : Fun1
  constr5_inner =
    pairF1 (constTermF1 tagCode_mp)
           (pairF1 h_part g_part)

  constr5 : Fun1
  constr5 =
    pairF1 (constTermF1 tagCode_mp)
           (pairF1 constr5_inner K_part)
