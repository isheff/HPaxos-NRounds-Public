---------------------------- MODULE CFCAntitoneR ----------------------------
EXTENDS HPaxosPlusCal, ConFromCaughtAntitone

\* Thin fresh-name wrapper (ConFromCaughtAntitone's param "B" collides with the
\* ballot operator B(_) in this module's ambient context).
LEMMA CFCAntitoneR ==
  ASSUME NEW aal \in Learners, NEW C1, NEW C2, C1 \subseteq C2
  PROVE ConFromCaught(aal, C2) \subseteq ConFromCaught(aal, C1)
BY ConFromCaughtAntitone
====================================================================
