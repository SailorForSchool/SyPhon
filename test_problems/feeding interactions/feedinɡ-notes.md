# TITLE

Each of these three .csv files is a supervised (= underlying representation given) problem illustrating three different types of feeding interaction. All three examples share the first rule, and the underlying representations are all the same -- only the surface representations differ, based on the differences in the second rule. For all three cases, I believe that the data set is sufficiently rich to provide evidence for each rule independently as well as for the interaction.


1. doy.csv - this is a "Duke of York" interaction, whereby A becomes B and B becomes A in overlapping contexts. (The name comes from a poem / nursery rhyme; https://en.wikipedia.org/wiki/The_Grand_Old_Duke_of_York.) The rules are intended to be the following, though there may be some variation in exactly which features are picked out:

- Rule 1: [–low] → [–high] / [+dorsal, –high] __
- Rule 2: [–low] → [+high] / __ #

    *Rule 1 lowers high vowels to mid (i,u → e,o) after uvulars (q, ɢ, ʀ), and Rule 2 raises mid vowels to high word-finally. Evidence for Rule 1 being ordered before Rule 2 comes from examples in which a high vowel appears both after a uvular and word-finally: no change happens here, because effectively A → B → A (A = high, B = mid).*

2. fof.csv - this is a "feeding on focus" interaction, whereby A becomes B and B becomes C in overlapping contexts. The rules are intended to be the following, though there may be some variation in exactly which features are picked out:

- Rule 1: [–low] → [–high] / [+dorsal, –high] __
- Rule 2: [–high, -back] → [+low] / __ #

    *Rule 1 lowers high vowels to mid (i,u → e,o) after uvulars (q, ɢ, ʀ), and Rule 2 lowers mid front vowels to low word-finally. Evidence for Rule 1 being ordered before Rule 2 comes from examples in which a high vowel appears both after a uvular and word-finally: both changes happen here, such that A → B → C (A = high front, B = mid front, C = low).*

3. foe.csv - this is a "feeding on environment" interaction, whereby A becomes B and B in turn causes another sound C to become D. The rules are intended to be the following, though there may be some variation in exactly which features are picked out:

- Rule 1: [–low] → [–high] / [+dorsal, –high] __
- Rule 2: [+dorsal] → [–high] / [–high] __

    *Rule 1 lowers high vowels to mid (i,u → e,o) after uvulars (q, ɢ, ʀ), and Rule 2 makes uvularizes velars (k,g → q,ɢ) after mid vowels. Evidence for Rule 1 being ordered before Rule 2 comes from examples in which a high vowel appears both after a uvular and before a velar: both changes happen here, such that A → B and C → D (A = high, B = mid, C = velar, D = uvular).*