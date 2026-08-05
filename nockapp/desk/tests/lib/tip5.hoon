  ::  /tests/lib/tip5
::::  Tip5 as an independent witness -- the vectors are the whole point
::
::  Naming: ++test-w-* for the witness proper (agreement with the other
::  implementation) and ++test-d-* for the derivations this file makes
::  instead of transcribing, which have to be checked separately -- a
::  derivation that is wrong in the same way the vectors expect would
::  otherwise pass unnoticed.
::
::  Every vector is at 5 rounds.  The 7-round path has no published
::  answers and is deliberately NOT asserted here; see /lib/tip5's
::  header.  A green run of this suite says nothing about it.
::
/-  *racoon, *baloon
/+  *test, racoon, baloon, t5=tip5, con=tip5-constants, vec=tip5-vectors
=/  mx  mx:racoon
::  the two 5-round instances, which are NOT the same function
=/  nc5  ~(. t5 [5 rc-alt5:con])       ::  ztd/three.hoon's num-rounds=5
=/  ai5  ~(. t5 [5 (scag 80 rc-canon:con)])  ::  ai-pow-zk's permute-5round
|%
+|  %witness
::    +test-w-hash-10:  100 fixed-length digests
++  test-w-hash-10
  %+  expect-eq  !>(%.y)
  !>
  %+  levy  fixlen:vec
  |=(k=kat:vec ^-(? =(o.k (hash-10:nc5 i.k))))
::    +test-w-hash-varlen:  100 variable-length digests
::
::  These run from the empty list up to 48 elements, so they exercise
::  the padding at every residue mod 10 -- including the case where the
::  input already fills a block and the pad adds a whole one.
++  test-w-hash-varlen
  %+  expect-eq  !>(%.y)
  !>
  %+  levy  varlen:vec
  |=(k=kat:vec ^-(? =(o.k (hash-varlen:nc5 i.k))))
::    +test-w-permute:  100 bare permutations
::
::  The Rust golden KAT, which reaches the permutation directly rather
::  than through the sponge -- so a fault in the padding or the domain
::  separation cannot hide behind one in the rounds, or the reverse.
++  test-w-permute
  %+  expect-eq  !>(%.y)
  !>
  %+  levy  permute:vec
  |=(k=kat:vec ^-(? =(o.k (permute:ai5 i.k))))
::
+|  %derivations
::    +test-d-montgomery:  the transform, against its own inverse and p
::
::  Nockchain computes this by hand-derived bit manipulation; here it is
::  a modular multiply.  The vectors above already depend on the two
::  agreeing, but only through the digest -- this says so directly.
++  test-d-montgomery
  ;:  weld
    ::  r = 2^64 mod p = 2^32 - 1
    (expect-eq !>(`@ud`4.294.967.295) !>(r:nc5))
    ::  the identity the x^7 S-box rests on
    %-  expect  !>(cube-r:nc5)
    ::  demontify undoes montify across the field's edges
    ::  annotated: an un-typed ~[...] infers as a fixed tuple, which the
    ::  wet +levy cannot nest -- the same trap Baloon's suite documents
    %-  expect
    !>
    %+  levy
      ^-  (list @ud)
      ~[0 1 2 (dec p:nc5) (sub p:nc5 2) 4.294.967.295 4.294.967.296]
    |=(x=@ud ^-(? =(x (demontify:nc5 (montify:nc5 x)))))
    ::  and it is multiplicative, which is what makes the MDS layer
    ::  need no correction: (ar)b = (ab)r
    %-  expect
    !>
    =/  fd  ~(. mx p:nc5)
    %+  levy
      ^-  (list [@ud @ud])
      ~[[3 5] [7 11] [4.294.967.295 2] [12.345.678.901 987.654.321]]
    |=  [a=@ud b=@ud]
    ^-  ?
    =((montify:nc5 (cmul:fd a b)) (cmul:fd (montify:nc5 a) b))
  ==
::    +test-d-lookup-table:  the derived table against the published one
::
::  /lib/tip5 builds this from x -> (x+1)^3 - 1 mod 257 rather than
::  transcribing it.  The published table is checked in here ONCE, as a
::  test rather than as a constant, which is where a copied table
::  belongs: if the two ever diverge this fails and the library is still
::  built from the definition.
++  test-d-lookup-table
  ;:  weld
    (expect-eq !>(`@ud`256) !>((lent lookup-table:nc5)))
    ::  a permutation of the bytes -- no value repeats, none escapes
    %-  expect
    !>
    =/  srt  (sort lookup-table:nc5 lth)
    =((gulf 0 255) srt)
    ::  and, entry for entry, the table nockchain-official publishes.
    ::  This is where a copied table belongs: as a vector, checked
    ::  against the definition, rather than as the library's constant.
    ::  If the two ever diverge this fails and /lib/tip5 is still built
    ::  from x -> (x+1)^3 - 1 mod 257.
    (expect-eq !>(lookup:vec) !>(lookup-table:nc5))
  ==
::    +test-d-mds:  the circulant expansion against its column
++  test-d-mds
  ;:  weld
    (expect-eq !>(`@ud`16) !>((lent mds:nc5)))
    %-  expect  !>((levy mds:nc5 |=(r=(list @ud) =(16 (lent r)))))
    ::  row 0 of the golden KAT's MDS_ROW0
    %+  expect-eq
      !>  ^-  (list @ud)
      :~  61.402  17.845  26.798  59.689  12.021  40.901  41.351  27.521
          56.951  12.034  53.865  43.244  7.454   33.823  28.750  1.108
      ==
    !>((snag 0 mds:nc5))
    ::  every row is the previous one rotated, which is the property
    ::  "circulant" names and the reason 240 entries are not written out
    %-  expect
    !>
    =/  i=@ud  1
    |-  ^-  ?
    ?:  =(i 16)  %.y
    =/  prev  (snag (dec i) mds:nc5)
    ?.  =((snag i mds:nc5) [(rear prev) (snip prev)])  %.n
    $(i +(i))
  ==
::
+|  %contracts
::    +test-c-crash:  the two-sided crash contract
++  test-c-crash
  ;:  weld
    ::  +hash-10 takes exactly the rate
    (expect-fail |.((hash-10:nc5 (reap 9 0))))
    (expect-fail |.((hash-10:nc5 (reap 11 0))))
    (expect-success |.((hash-10:nc5 (reap 10 0))))
    ::  nothing outside the field, in either arm
    (expect-fail |.((hash-10:nc5 [p:nc5 (reap 9 0)])))
    (expect-fail |.((hash-varlen:nc5 ~[p:nc5])))
    (expect-success |.((hash-varlen:nc5 ~[(dec p:nc5)])))
    ::  +permute takes exactly the state
    (expect-fail |.((permute:ai5 (reap 15 0))))
    (expect-success |.((permute:ai5 (reap 16 0))))
    ::  and a schedule that does not match the round count is a crash
    ::  rather than a quietly truncated hash
    (expect-fail |.((permute:~(. t5 [7 rc-alt5:con]) (reap 16 0))))
  ==
::    +test-c-domains-differ:  fixed and variable are separated
::
::  Ten elements can be hashed either way and the two must disagree,
::  which is what the montified capacity in +init %fixed is for.  If
::  domain separation were dropped both digests would still look fine
::  in isolation.
++  test-c-domains-differ
  =/  in  (gulf 1 10)
  %-  expect
  !>  ?!(=((hash-10:nc5 in) (hash-varlen:nc5 in)))
::    +test-c-schedules-differ:  the two 5-round Tip5s are not the same
::
::  Recorded as a test because it is a finding, not a nuisance: the
::  header explains that "Tip5 with 5 rounds" names two functions in
::  nockchain-official, and this is the assertion that says so.
++  test-c-schedules-differ
  %-  expect
  !>  ?!(=((permute:nc5 (reap 16 0)) (permute:ai5 (reap 16 0))))
--
