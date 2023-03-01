# Notes on Spanish problem

In Spanish, voiced stops (b,d,ɡ) and correspondinɡ voiced fricatives (β,ð,ɣ) are in complementary distribution. In these simplified pseudo-data sets, the stops appear word-initially and after nasals, while the fricatives appear after non-nasal sounds (in both data sets, after the vowel [a] or the fricative [s]).

One solution to the problem is to posit underlying stops everywhere and to change them to fricatives after non-nasals (one rule). This is the solution aimed for in "spanish-stops.csv". The other solution is to posit underlying fricatives everywhere and to change them to stops word-initially and after nasals (two rules). This is the solution aimed for in "spanish-fricatives.csv".

The Phonosynth Demo works well with "spanish-stops.csv", and comes up with this rule:

    [-sonorant +voice] → [+continuant +delayed release] / [-nasal] _

It doesn't come up with a solution for "spanish-fricatives.csv", though -- it just leaves the rule space blank. Shouldn't it come up with (something like) the following two rules?


    [-sonorant +voice] → [-continuant -delayed release] / # _
    [-sonorant +voice] → [-continuant -delayed release] / [+nasal] _

*(There aren't any examples of voiceless fricatives in the relevant positions so the A part could be more general, but at least the B and C parts should be something like the above.)*