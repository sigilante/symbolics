  ::  /lib/cascabel
::::  Stateless evaluation of symbolic-computation commands
::
::  One tape in, lines of output out.  There is deliberately no session
::  state: no variables, no history, no accumulated subject.  Every
::  command is answered from its own text and nothing else, which is what
::  makes this safe to drive from a notebook cell that may be re-run, run
::  out of order, or run against a fresh agent.
::
::  This is a COMMAND language, not an expression language.  A verb and
::  its arguments, where each argument is parsed by the same +red* arm the
::  generators already use.  SPEC §13 fences out a symbolic expression
::  front end, and this does not cross that line: there is no grammar for
::  nesting calls, no precedence, and no evaluation of one result into
::  another.
::
::  Arguments that come in pairs are separated by a semicolon, since both
::  polynomials and matrices contain spaces and commas of their own.
::
/-  *racoon, *baloon
/+  racoon, baloon, fmt=racoon-fmt, bf=baloon-fmt
/+  rr=racoon-roots, al=racoon-alg, zf=racoon-zfac, vh=vanhoeij
=/  zx  zx:racoon
=/  qx  qx:racoon
=/  qq  qq:racoon
=/  qm  qm:baloon
=/  zm  zm:baloon
|%
+|  %text
::    +trim-l:  drop leading spaces
++  trim-l
  |=  t=tape
  ^-  tape
  ?~  t  ~
  ?:(=(' ' i.t) $(t t.t) t)
::    +trim:  drop leading and trailing spaces
++  trim
  |=  t=tape
  ^-  tape
  (flop (trim-l (flop (trim-l t))))
::    +word:  split off the leading whitespace-delimited token
++  word
  |=  t=tape
  ^-  [w=tape rest=tape]
  =/  s=tape  (trim-l t)
  =|  w=tape
  |-  ^-  [w=tape rest=tape]
  ?~  s  [(flop w) ~]
  ?:  =(' ' i.s)  [(flop w) (trim-l s)]
  $(s t.s, w [i.s w])
::    +halve:  split on the first semicolon
::
::  Both polynomials and matrices use spaces and commas internally, so a
::  two-argument command needs a separator that neither of them claims.
++  halve
  |=  t=tape
  ^-  (unit [a=tape b=tape])
  =|  a=tape
  =/  s=tape  t
  |-  ^-  (unit [a=tape b=tape])
  ?~  s  ~
  ?:  =(';' i.s)  `[(trim (flop a)) (trim t.s)]
  $(s t.s, a [i.s a])
::    +oops:  a one-line complaint
++  oops  |=(t=tape ^-((list tape) ~[t]))
::
+|  %dispatch
::    +usage:  what this thing answers to
++  usage
  ^-  (list tape)
  :~  "cascabel -- exact symbolic computation"
      ""
      "polynomials in x, integer coefficients:"
      "  factor <p>          factor over Z"
      "  roots <p>           real roots, isolated exactly"
      "  disc <p>            discriminant"
      "  gcd <p> ; <q>       greatest common divisor"
      "  res <p> ; <q>       resultant"
      ""
      "integers:"
      "  zfac <n>            factor, with totient and divisors"
      ""
      "matrices over Q, as [[1 2] [3 4]]:"
      "  det <m>   rank <m>   inv <m>   rref <m>"
      "  charpoly <m>        characteristic polynomial"
      "  eigen <m>           rational eigenvalues only"
      ""
      "matrices over Z:"
      "  hnf <m>   snf <m>   lll <m>"
      ""
      "  help                this text"
  ==
::    +eval:  answer one command line
::
::  Never crashes: a parse failure or a domain error comes back as a line
::  of text, because a kernel that bails takes the notebook with it.
++  eval
  |=  src=tape
  ^-  (list tape)
  =/  line=tape  (trim src)
  ?~  line  ~
  =/  sp  (word line)
  =/  cmd=@t  (crip w.sp)
  =/  arg=tape  rest.sp
  =/  res  (mule |.((run cmd arg)))
  ?-  -.res
    %&  p.res
    %|  (oops "error: that input is outside the domain of {(trip cmd)}")
  ==
::    +run:  the dispatch proper, wrapped by +eval's +mule
++  run
  |=  [cmd=@t arg=tape]
  ^-  (list tape)
  ?:  =('help' cmd)  usage
  ?:  =('' cmd)      usage
  ::  polynomial, one argument
  ?:  ?|(=('factor' cmd) =('roots' cmd) =('disc' cmd))
    =/  p  (redz:fmt (crip arg))
    ?~  p  (oops "cannot parse a polynomial from: {arg}")
    ?~  u.p  (oops "the zero polynomial has no {(trip cmd)}")
    ?:  =('factor' cmd)
      ~[:(weld (shoz:fmt u.p) "  =  " (shozf:fmt (factor:zx u.p)))]
    ?:  =('disc' cmd)
      ?:  (lth (deg:zx u.p) 1)  (oops "disc needs degree at least 1")
      ~[(sig:fmt (disc:zx u.p))]
    (show-roots u.p)
  ::  polynomial, two arguments
  ?:  ?|(=('gcd' cmd) =('res' cmd))
    =/  h  (halve arg)
    ?~  h  (oops "{(trip cmd)} takes two polynomials, separated by ;")
    =/  p  (redz:fmt (crip a.u.h))
    =/  q  (redz:fmt (crip b.u.h))
    ?~  p  (oops "cannot parse a polynomial from: {a.u.h}")
    ?~  q  (oops "cannot parse a polynomial from: {b.u.h}")
    ?:  =('gcd' cmd)  ~[(shoz:fmt (gcd:zx u.p u.q))]
    ~[(sig:fmt (res:zx u.p u.q))]
  ::  integers
  ?:  =('zfac' cmd)
    =/  n  (rush (crip (trim arg)) dem)
    ?~  n  (oops "cannot parse a number from: {arg}")
    ?:  =(0 u.n)  (oops "0 has no factorization: every prime divides it")
    (show-zfac u.n)
  ::  matrices over Q
  ?:  ?|(=('det' cmd) =('rank' cmd) =('inv' cmd) =('rref' cmd))
    (do-qmat cmd arg)
  ?:  ?|(=('charpoly' cmd) =('eigen' cmd))
    (do-qmat cmd arg)
  ::  matrices over Z
  ?:  ?|(=('hnf' cmd) =('snf' cmd) =('lll' cmd))
    (do-zmat cmd arg)
  (oops "unknown command: {(trip cmd)}   (try: help)")
::
+|  %renderers
::    +show-roots:  every real root, exactly
++  show-roots
  |=  p=zol
  ^-  (list tape)
  =/  rs  (roots:rr p)
  ?~  rs  ~["no real roots"]
  %+  turn  rs
  |=  r=rrt:rr
  ^-  tape
  =/  m=tape  ?:(=(1 m.r) "" "  (multiplicity {(dot:fmt m.r)})")
  ?:  =(lo.iv.r hi.iv.r)
    "  {(shof:fmt lo.iv.r)}   exact{m}"
  "  {(shoapp:fmt p iv.r 12)}...  in {(shoiv:fmt iv.r)}{m}"
::    +show-zfac:  an integer, and what follows from its factorization
++  show-zfac
  |=  n=@ud
  ^-  (list tape)
  =/  ds  (divisors:zf n)
  :~  "{(dot:fmt n)}  =  {(shonf:fmt (factor:zf n))}"
      "totient   {(dot:fmt (totient:zf n))}"
      "radical   {(dot:fmt (radical:zf n))}"
      "divisors  {(dot:fmt (lent ds))}"
  ==
::    +do-qmat:  the commands that take a matrix over Q
++  do-qmat
  |=  [cmd=@t arg=tape]
  ^-  (list tape)
  =/  m  (redq:bf (crip arg))
  ?~  m  (oops "cannot parse a matrix from: {arg}")
  =/  q=qmat  u.m
  ?:  =('rank' cmd)  ~[(dot:fmt (rank:qm q))]
  ?:  =('det' cmd)
    ?.  (is-square:qm q)  (oops "det needs a square matrix")
    ~[(shof:fmt (det:qm q))]
  ?:  =('inv' cmd)
    ?.  (is-square:qm q)  (oops "inv needs a square matrix")
    ?:  =([--0 1] (det:qm q))  (oops "that matrix is singular")
    (shoq:bf (inv:qm q))
  ?:  =('rref' cmd)  (shoq:bf m:(rref:qm q))
  ?:  =('charpoly' cmd)
    ?.  (is-square:qm q)  (oops "charpoly needs a square matrix")
    ~[(shoq:fmt (charpoly:qm q))]
  ::  eigen
  ?.  (is-square:qm q)  (oops "eigen needs a square matrix")
  =/  es  (eigen:qm q)
  ?~  es  ~["no rational eigenvalues"]
  %+  turn  es
  |=  [val=frac mult=@ud]
  ^-  tape
  ?:  =(1 mult)  "  {(shof:fmt val)}"
  "  {(shof:fmt val)}  (multiplicity {(dot:fmt mult)})"
::    +do-zmat:  the commands that take a matrix over Z
++  do-zmat
  |=  [cmd=@t arg=tape]
  ^-  (list tape)
  =/  m  (redz:bf (crip arg))
  ?~  m  (oops "cannot parse a matrix from: {arg}")
  =/  z=zmat  u.m
  ?:  =('hnf' cmd)  (shoz:bf h:(hnf:zm z))
  ?:  =('snf' cmd)  (shoz:bf d:(snf:zm z))
  ::  lll
  ?.  =((lent z) (rank:zm z))
    (oops "lll needs linearly independent rows")
  (shoz:bf (lll:vh z))
--
