  ::  /gen/baloon-lll
::::  Reduce an integer lattice basis
::
::  Usage:  +baloon-lll '[[1 0 0 -20] [0 1 0 -2] [0 0 1 -36]]'
::          +baloon-lll '[[201 37] [1648 297]]'
::
::  Prints the basis before and after, with the squared norm of each row,
::  and confirms the two properties that matter: the result is LLL-reduced
::  at delta = 3/4, and it generates the SAME lattice -- checked by
::  comparing Hermite normal forms, which needs no external oracle.
::
/-  *baloon, *racoon
/+  baloon, vh=vanhoeij, fmt=baloon-fmt
=/  zm  zm:baloon
:-  %say
|=  [* [txt=@t ~] ~]
:-  %tang
=/  parsed=(unit zmat)  (redz:fmt txt)
?~  parsed  ~[leaf+"parse error"]
=/  b=zmat  u.parsed
?.  =((lent b) (rank:zm b))
  ~[leaf+"rows are not linearly independent -- that is not a basis"]
=/  r=zmat  (lll:vh b)
::    +nsq:  the squared euclidean norm of a row
=/  nsq
  |=  v=zvec
  ^-  @ud
  =/  acc=@ud  0
  |-  ^-  @ud
  ?~  v  acc
  $(v t.v, acc (add acc (abs:si (pro:si i.v i.v))))
::    +blk:  a matrix with a norm beside each row
=/  blk
  |=  m=zmat
  ^-  tang
  =/  ls=(list tape)  (shoz:fmt m)
  =/  ns=(list @ud)   (turn m nsq)
  |-  ^-  tang
  ?~  ls  ~
  ?~  ns  ~
  [leaf+"  {i.ls}   |v|^2 = {(dot:fmt i.ns)}" $(ls t.ls, ns t.ns)]
::  each block bound as tang explicitly: a ~[leaf+"..."] literal infers
::  narrower than tang, and +weld is wet, so the pieces would not nest
=/  hdr=tang  ~[leaf+"before" leaf+""]
=/  mid=tang  ~[leaf+"" leaf+"after" leaf+""]
=/  ftr=tang
  :~  leaf+""
      leaf+"reduced       {<(reduced:vh r)>}"
      leaf+"same lattice  {<=(h:(hnf:zm b) h:(hnf:zm r))>}"
      leaf+"was reduced   {<(reduced:vh b)>}"
  ==
::  built in display order, flopped once: %tang renders in reverse
%-  flop
:(weld hdr (blk b) mid (blk r) ftr)
