{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.KGodel1Bridge -- Phase R6: the LOCAL raw-refl bridge between the two
-- presentations of the canonical diagonal program (CHAITIN-G1-SIZE-INTERFACE.md
-- S5: "done in the module where the concrete form lives, where the raw refl
-- bridge gLcode (2^k) == plug Cmcodeb (H k) is local and cheap").
--
-- The size accounting (T4.GLCodeP, module Size) is parametric in a checker
--  tc ; here we pin  tc := thmT  (Size.gLcodeP thmT is definitionally
-- KDiag.gLcode) and RE-EXPORT the shared aliases (Cmcodeb / bound / dLen_gen)
-- so the capstone (T4.KGodel1Canon) uses the SAME Size instantiation.  (A
-- fresh  module S = Size thmT  there would desynchronise  Cmcodeb / bound  from
-- the ones in  bridge 's type, forcing a  nodes =?= nodes  reduction across two
-- distinct aliases -- i.e. traversing thmT.)
--
--   L* := exp2 (natCode (fst bound))   -- the canonical threshold.  SYMBOLIC:
--     fst bound is a neutral projection of the sealed  dom_plug , never a
--     concrete numeral.
--
--   bridge : gLcode L*  ==  plug Cmcodeb (H (fst bound))
--     -- the two forms of the ONE diagonal program.  A RAW definitional  refl
--     -- (the thmT-bearing siblings line up syntactically; cheap warm, ~10s
--     -- cold one-time).  NOT under any serialiser (enc/nodes/lenR).
--
-- SEALED  abstract  so  bridge  is an OPAQUE proof at the use site: the (B)
-- transport in KGodel1Canon must stay a NEUTRAL application.  If  bridge
-- reduced to  refl , the transport's  eqSubst  would collapse and its declared
-- type would force  nodes (gLcode L*) =?= nodes (plug Cmcodeb ..)  UNDER nodes,
-- traversing the thmT skeleton.  (abstract only seals OUTSIDE the defining
-- module, which is why  bridge  lives in this separate file, not in the
-- capstone.)

module T4.KGodel1Bridge where

open import T4.Base
open import T4.ThmT        using ( thmT )
open import T4.KDiag       using ( gLcode )
open import T4.ProgNodes   using ( plug )
open import T4.Exp         using ( exp2 )
open import T4.GLCodeNodes using ( H )
open import T4.NatExp      using ( Sg ; fst )

import T4.GLCodeP

-- ONE shared instantiation of the size module, re-exported.
module Sz = T4.GLCodeP.Size thmT
open Sz public using ( Cmcodeb ; bound ; dLen_gen )

Lstar : Term
Lstar = ap1 exp2 (natCode (fst bound))

abstract
  bridge : Eq (gLcode Lstar) (plug Cmcodeb (H (fst bound)))
  bridge = refl
