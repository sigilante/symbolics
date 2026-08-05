  ::  /gen/tip5
::::  Hash from the dojo, and say which Tip5 you got
::
::  Usage:  +tip5 ~[1 2 3]
::          +tip5 ~[1 2 3], =sched %alt5
::          +tip5 ~[1 2 3 4 5 6 7 8 9 10], =mode %fixed
::
::  The positional argument is a LIST of field elements, so ~[1 2 3] and
::  not [1 2 3] -- the dojo passes the latter as a three-tuple and the
::  sample will not nest.  +hash-varlen takes any length; +hash-10 takes
::  exactly ten, which is what %fixed selects.
::
::  WHICH TIP5.  "Tip5 with 5 rounds" names two different functions in
::  nockchain-official and this generator will not pretend otherwise:
::  =sched %canon takes the first rounds*16 of the canonical schedule,
::  =sched %alt5 takes ztd/three.hoon's dedicated 5-round block.  The
::  digest is printed with the schedule that produced it, because a Tip5
::  digest without that is ambiguous.
::
::  The 7-round canonical path is UNVERIFIED -- no published vectors
::  exercise it -- and this says so on every line that uses it.
::
/-  *racoon
/+  t5=tip5, con=tip5-constants
:-  %say
|=  $:  *
        [in=(list @ud) ~]
        ::  $~ and not _5: `_5` types the argument as the CONSTANT 5, so
        ::  =rounds 7 fails to nest and every test against it mints vain
        $:  rounds=$~(5 @ud)
            mode=$~(%varlen ?(%varlen %fixed))
            sched=$~(%canon ?(%canon %alt5))
            ~
        ==
    ==
:-  %tang
|^  ^-  tang
    ?:  =(0 rounds)  ~[leaf+"rounds must be nonzero"]
    ::  bound to a leg first: ?~ on an ARM re-evaluates it, and the
    ::  refinement does not survive to the u.rc below
    =/  sch=(unit (list @ud))  rc
    ?~  sch  ~[leaf+"no schedule has {<(mul rounds 16)>} constants"]
    =/  hs  ~(. t5 [rounds u.sch])
    =/  out=(list @ud)
      ?:  =(%fixed mode)  (hash-10:hs in)
      (hash-varlen:hs in)
    %-  flop
    %+  turn
      :~  "tip5  rounds {<rounds>}  {<sched>}  {<mode>}{warn}"
          "   in   {<(lent in)>} element(s)"
          "   out  {<out>}"
      ==
    |=(t=tape ^-(tank leaf+t))
::    +rc:  the requested schedule, if it has enough constants
++  rc
  ^-  (unit (list @ud))
  =/  n=@ud  (mul rounds 16)
  =/  all=(list @ud)
    ?:(=(%alt5 sched) rc-alt5:con rc-canon:con)
  ?:  (gth n (lent all))  ~
  `(scag n all)
::    +warn:  the coverage note, on exactly the paths that lack vectors
++  warn
  ^-  tape
  ?:  ?&(=(5 rounds) |(=(%canon sched) =(%alt5 sched)))  ""
  "   -- UNVERIFIED, no published vectors"
--
