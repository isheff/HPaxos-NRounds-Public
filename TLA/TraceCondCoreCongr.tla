------------------------ MODULE TraceCondCoreCongr ------------------------
EXTENDS MessageInterface

\* TraceCondCore only reads seq at indices x, x-1 and x-2, so any two
\* sequences agreeing there satisfy it alike.
LEMMA TraceCondCoreCongr ==
  ASSUME NEW alpha, NEW lobal, NEW CL, NEW himsg,
         NEW seq1, NEW seq2, NEW x \in Nat,
         seq1[x] = seq2[x],
         x > 1 => seq1[x-1] = seq2[x-1],
         x > 2 => seq1[x-2] = seq2[x-2]
  PROVE TraceCondCore(alpha, lobal, CL, himsg, seq1, x)
          <=> TraceCondCore(alpha, lobal, CL, himsg, seq2, x)
BY DEF TraceCondCore
====================================================================
