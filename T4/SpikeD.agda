{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SpikeD -- Gate KR-2 toy: the surprise-exam INDUCTION SKELETON internalises
-- into ONE object  ruleIndNat .
--
-- This validates the structural point that SPIKE-KR-D-STRUCTURE-DECISION.md
-- argued and that I (wrongly) doubted as a "Nelson wall": the descending
-- surprise-exam is NOT an irreducibly N-deep meta-induction -- it is a SINGLE
-- object  ruleIndNat  (open in the step variable), instantiated once at the
-- boundary.  The step is UNIFORM (open in  j ) via a  byCases  on the DECIDABLE
-- count comparison: below the boundary it advances the invariant; at/above the
-- boundary the Chaitin barrier fires and ex-falso carries the invariant forward.
-- Instantiating the single induction at the boundary then yields  falseF .
--
-- Methodology = Spike B / Spike C: the KR-A/KR-B deliverables are ABSTRACTED as
-- parameters (`baseHyp`, `advance`, `barrier`); only the surprise-exam ASSEMBLY is
-- built here.  Like Spike B's arbitrary `cf`, this isolates the in-question
-- mechanism (does the step internalise as a uniform object  ruleIndNat  step?)
-- from the KR-A/KR-B internals (does `chaitin_thm` / `compress_canonical` deliver
-- the parameter shapes? -- that is KR-B, validated when built).
--
-- NON-VACUITY (cf. Spike B's "witness genuinely flows in").  The barrier is
-- GUARDED by the invariant  INV j  (= "thmT proves (m >= j)", here the concrete
-- structural stand-in "thmT(j) = codeTriv").  `INV j` is NOT a free hypothesis --
-- it is produced ONLY by running the induction (baseHyp, then `advance` steps).  So
-- the barrier cannot fire without the induction having built `INV` up to the
-- boundary.  (Were the barrier the unguarded "leq N j -> falseF", it would
-- explode at  j = N  via reflexivity, with the induction dead; the  INV -guard is
-- exactly what the real Chaitin barrier supplies -- it needs  thmT  to PROVE the
-- tightness, which only the count forces.)
--
-- DESIGN.  cT = codeTriv is a concrete CLOSED code, so  substF  on the motive
-- reduces definitionally -- no closedness coercion (`closeCoe`) is needed.  The
-- bound  N  is an arbitrary Term occurring ONLY in the parameters (`advance` /
-- `barrier`) and the finish, never in the induction motive  INV (var 0) , so the
-- induction is uniform with no  N -dependence to coerce.

module T4.SpikeD where

open import T4.Base
open import T4.Code          using ( codeTriv ; falseF )
open import T4.ThmT          using ( thmT )
open import T4.PHP           using ( byCases ; negFalseF )
open import T4.CountingObj   using ( leqNN )

open import BRA3.ChurchLeq      using ( leq )
open import BRA3.Contrapositive using ( axExFalso ; bComb ; liftP )
open import T4.Counting       using ( mapUnder1 )

------------------------------------------------------------------------
-- The concrete structural invariant.
--   INV j  =  "thmT(j) = codeTriv"   -- a stand-in for "thmT proves (m >= j)".
-- cT = codeTriv is concrete + closed, so  substF k b INV  reduces to  INV b .

INV : Term -> Formula
INV t = eqF (ap1 thmT t) codeTriv

------------------------------------------------------------------------
-- ex falso quodlibet at the object level:  falseF -> B .

exFalsoImp : (B : Formula) -> Deriv (imp falseF B)
exFalsoImp B = bComb (axExFalso falseF B) (liftP falseF negFalseF)

------------------------------------------------------------------------
-- Post-compose a fixed implication  Y -> W  on the right of  X -> Y , giving
-- X -> W .  (Combinator  \f x. g (f x) , via  axS  + necessitation of  g .)

post_compose :
  {X Y W : Formula} ->
  Deriv (imp Y W) -> Deriv (imp (imp X Y) (imp X W))
post_compose {X} {Y} {W} g = mp (axS X Y W) (liftP X g)

------------------------------------------------------------------------
-- THE TOY.  Given the abstracted KR-A/KR-B pieces, the surprise-exam yields
-- falseF via ONE object  ruleIndNat  instantiated at the boundary  N .

surpriseExam :
  (N : Term) ->
  Deriv (INV O) ->                                                              -- baseHyp: thmT proves (m >= 0)
  ((j : Term) -> Deriv (imp (neg (leq N j)) (imp (INV j) (INV (ap1 s j))))) ->  -- advance (below boundary, j < N)
  ((j : Term) -> Deriv (imp (leq N j) (imp (INV j) falseF))) ->                 -- Chaitin barrier (at boundary, j >= N), GUARDED by INV
  Deriv falseF
surpriseExam N baseHyp advance barrier =
  let v0 : Term
      v0 = var zero

      Goal : Formula
      Goal = imp (INV v0) (INV (ap1 s v0))

      -- hit branch (leq N v0):  barrier gives  INV v0 -> falseF ; ex-falso
      -- carries  INV v0 -> INV (s v0) .  This is where the Chaitin barrier
      -- advances the invariant past the boundary by explosion.
      hit : Deriv (imp (leq N v0) Goal)
      hit = mapUnder1 (leq N v0)
              (post_compose {INV v0} {falseF} {INV (ap1 s v0)}
                 (exFalsoImp (INV (ap1 s v0))))
              (barrier v0)

      -- miss branch (neg (leq N v0)):  ordinary advance.
      miss : Deriv (imp (neg (leq N v0)) Goal)
      miss = advance v0

      -- the UNIFORM step, open in  v0 , assembled by  byCases  on the decidable
      -- boundary comparison.  (This is the step I wrongly feared was non-uniform
      -- at  j = m ; the boundary case is absorbed by the barrier+ex-falso.)
      stepReal : Deriv Goal
      stepReal = byCases (leq N v0) Goal hit miss

      -- ONE object ruleIndNat (NOT an N-deep meta-tower).
      ind : Deriv (INV v0)
      ind = ruleIndNat zero {P = INV v0} baseHyp stepReal

      -- instantiate once at the boundary  N  (cost O(|N|) -- Bin-compressed in KR).
      indAtN : Deriv (INV N)
      indAtN = ruleInst zero N ind

  in mp (mp (barrier N) (leqNN N)) indAtN
