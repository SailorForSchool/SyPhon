
# Solver

(declare-fun |word boundary right| () Bool)
(declare-fun |long center| () Bool)
(declare-fun |word boundary center| () Bool)
(declare-fun |syll center| () Bool)
(declare-fun |lat center| () Bool)
(declare-fun |son center| () Bool)
(declare-fun |s.g. center| () Bool)
(declare-fun |approx center| () Bool)
(declare-fun |c.g. center| () Bool)
(declare-fun |cons center| () Bool)
(declare-fun |nas center| () Bool)
(declare-fun |voice center| () Bool)
(declare-fun |word boundary left| () Bool)
(declare-fun |voice left| () Bool)
(declare-fun |syll left| () Bool)
(declare-fun |nas left| () Bool)
(declare-fun |son left| () Bool)
(declare-fun |dorsal left| () Bool)
(declare-fun |long left| () Bool)
(declare-fun |s.g. left| () Bool)
(declare-fun |cont left| () Bool)
(declare-fun |c.g. left| () Bool)
(declare-fun |cons left| () Bool)
(declare-fun |coronal left| () Bool)
(declare-fun |approx left| () Bool)
(declare-fun |lat left| () Bool)
(assert (not (and (=> (and |word boundary left| true) false)
          (=> (and |voice center| true) true)
          (=> (and |nas center| true) true)
          (=> (and |cons center| true) true)
          (=> (and |c.g. center| true) true)
          (=> (and |approx center| true) true)
          (=> (and |s.g. center| true) true)
          (=> (and |son center| true) true)
          (=> (and |lat center| true) true)
          (=> (and |syll center| true) true)
          (=> (and |word boundary center| true) true)
          (=> (and |long center| true) true)
          (=> (and |word boundary right| true) false))))
(assert-soft (not |approx center|) :weight 10046)
(assert-soft (not |c.g. center|) :weight 10002)
(assert-soft (not |lat center|) :weight 10006)
(assert-soft (not |word boundary right|) :weight 11094)
(assert-soft (not |nas center|) :weight 10009)
(assert-soft (not |voice left|) :weight 11022)
(assert-soft (not |syll left|) :weight 11067)
(assert-soft (not |nas left|) :weight 11009)
(assert-soft (not |son center|) :weight 10054)
(assert-soft (not |son left|) :weight 11042)
(assert-soft (not |s.g. center|) :weight 10003)
(assert-soft (not |dorsal left|) :weight 11044)
(assert-soft (not |long left|) :weight 11001)
(assert-soft (not |word boundary left|) :weight 11001)
(assert-soft (not |s.g. left|) :weight 11003)
(assert-soft (not |cont left|) :weight 11036)
(assert-soft (not |c.g. left|) :weight 11002)
(assert-soft (not |cons center|) :weight 10038)
(assert-soft (not |cons left|) :weight 11058)
(assert-soft (not |coronal left|) :weight 11030)
(assert-soft (not |voice center|) :weight 10022)
(assert-soft (not |syll center|) :weight 10029)
(assert-soft (not |approx left|) :weight 11050)
(assert-soft (not |word boundary center|) :weight 10001)
(assert-soft (not |lat left|) :weight 11006)
(assert-soft (not |long center|) :weight 10001)
(check-sat)


# Model():

[|word boundary left| = True,
 |word boundary right| = False,
 |long center| = False,
 |word boundary center| = False,
 |syll left| = False,
 |cons left| = False,
 |approx left| = False,
 |dorsal left| = False,
 |son left| = False,
 |cont left| = False,
 |coronal left| = False,
 |voice left| = False,
 |nas left| = False,
 |lat left| = False,
 |s.g. left| = False,
 |c.g. left| = False,
 |long left| = False,
 |son center| = False,
 |approx center| = False,
 |cons center| = False,
 |syll center| = False,
 |voice center| = False,
 |nas center| = False,
 |lat center| = False,
 |s.g. center| = False,
 |c.g. center| = False]