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

open import BRA.GoedelII using (i ; cG ; G)
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
  -- After Approach A redesign (2026-05-02): substituents are encoded
  -- mixed-form Pairs (Guard's "th(x_)", "sub(i,i)" forms) so that
  -- subT^3 produces antecedents matching D_thmT and D_sub_at_ii's
  -- encoded values (per Theorem 13).
  --
  -- The substituents of f_part 's three sb headers are:
  --   var 0  ->  encoded_th_x x   (= Pair tagAp1 (Pair (codeF1 thmT) (cor x)))
  --              -- depends on x via cor x at the deepest leaf;
  --              -- analog of Guard's "th(x_)" (Def 12 underlined-x).
  --   var 1  ->  encoded_sub_ii   (= Pair tagAp2 (Pair (codeF2 sub) (Pair (cor i) (cor i))))
  --              -- closed; analog of Guard's "sub(i,i)".
  --   var 2  ->  sub_ii_subst     (= reify (code cG) = cor cG)
  --              -- closed; analog of Guard's num(j).

  -- CANONICAL Term form: reify (code cG) — closed reify-of-Tree so
  -- that  KT sub_ii_subst  reduces via the canonical KT clause.
  sub_ii_subst : Term
  sub_ii_subst = reify (code (reify (codeFormula G)))

  -- encoded_sub_ii : the closed Term encoding the term sub(i,i).
  -- CANONICAL Term form: reify (code (sub i i)) — closed reify-of-Tree
  -- so that KT encoded_sub_ii reduces via the canonical KT clause.
  -- Structurally equal to Pair (reify tagAp2) (Pair (reify (codeF2 sub))
  --                              (Pair (cor i) (cor i)))
  -- modulo closed corOfReify identities (cor i = reify (code i) since i
  -- is closed reify-of-Tree).
  -- Matches D_sub_at_ii's encoded RHS (Theorem 13 form, after closed
  -- corOfReify bridging).
  encoded_sub_ii : Term
  encoded_sub_ii = reify (code (ap2 sub i i))

  -- encoded_th_x : Fun1 such that applied to x gives
  -- Pair (reify tagAp1) (Pair (reify (codeF1 thmT)) (cor x)).
  -- Constructed as a Comp2-Pair tower of two closed KT's and  cor .
  encoded_th_x : Fun1
  encoded_th_x =
    pairF1 (constTermF1 (reify tagAp1))
           (pairF1 (constTermF1 (reify (codeF1 thmT))) cor)

  --------------------------------------------------------------------
  -- f_part : the sb-chain on Guard's transitivity numeral t_term .
  --
  -- Encoded as the 3-deep ruleInst chain matching Guard p.17 f(x):
  --   ruleInst 0 (encoded_th_x x) (ruleInst 1 encoded_sub_ii
  --                                   (ruleInst 2 sub_ii_subst t_term))
  --
  -- LAYOUT (Approach A 2026-05-02): sb-chain ordered to match Guard's
  -- f(x) at p.17 (var 0 outermost = chronologically LAST).  Substituents
  -- are the Goedel-encoded mixed-form Pairs that Guard uses
  -- ("th(x_)" / "sub(i,i)" / "j"), so that subT^3 of t_formula
  -- produces antecedents matching D_thmT's and D_sub_at_ii's encoded
  -- values (per Theorem 13).
  --
  -- At the Term level:
  --   Pair tagCode_ruleInst (Pair (Pair varCode0T (encoded_th_x x)) inner1(x))
  -- with
  --   inner1(x) = Pair tagCode_ruleInst (Pair (Pair varCode1T encoded_sub_ii)
  --                                            inner2(x))
  --   inner2(x) = Pair tagCode_ruleInst (Pair (Pair varCode2T sub_ii_subst)
  --                                            (reify t_term))

  f_part_inner2 : Fun1
  f_part_inner2 =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (pairF1 (constTermF1 varCode2T) (constTermF1 sub_ii_subst))
                   (constTermF1 (reify t_term)))

  f_part_inner1 : Fun1
  f_part_inner1 =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (pairF1 (constTermF1 varCode1T)
                           (constTermF1 encoded_sub_ii))
                   f_part_inner2)

  f_part : Fun1
  f_part =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (pairF1 (constTermF1 varCode0T) encoded_th_x)
                   f_part_inner1)

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

  -- NEW LAYOUT (refactor 2026-05-02):
  --   K_part(x) = Pair tagCode_ruleInst (Pair (Pair varCode1T (cor x)) x)
  -- closed (varCode1T, cor x) at inner Fst, OPEN proof-index x at outer Snd.
  K_part : Fun1
  K_part =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (pairF1 (constTermF1 varCode1T) cor)
                   I)

  --------------------------------------------------------------------
  -- h_part : analogous to f_part / g_part but on the ex-falso numeral
  -- t'_term .  Substitutes:
  --   var 0  ->  ap1 cor x                (depends on x; "th(x_)" code)
  --   var 1  ->  sub_ii_subst             (closed; "sub(i,i)" code)
  --
  -- Only TWO sb-headers (versus f_part 's three) since t' has free
  -- variables  x_0 , x_1  only.

  -- LAYOUT (Approach A 2026-05-02): substituents are encoded mixed-form
  -- Pairs matching Guard's "th(x_)" / "sub(i,i)" so that subT^2 of
  -- t'_formula produces the antecedents matching step 3's RHS and
  -- step 4's negated form.  sb-order inversion: var 1 (closed) inner,
  -- var 0 (encoded_th_x x) outer.
  h_part_inner1 : Fun1
  h_part_inner1 =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (pairF1 (constTermF1 varCode1T)
                           (constTermF1 encoded_sub_ii))
                   (constTermF1 (reify t'_term)))

  h_part_skel : Fun1
  h_part_skel =
    pairF1 (constTermF1 tagCode_ruleInst)
           (pairF1 (pairF1 (constTermF1 varCode0T) encoded_th_x)
                   h_part_inner1)

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
