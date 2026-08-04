  ::  /tests/lib/racoon
::::  Racoon test suite
::
::  Phase 0: scalars and elementary number theory (+nz, +qq).
::
::  Naming: ++test-p0-* for Phase 0.  Every crash row in SPEC S8 that names a
::  Phase 0 arm has a dedicated ++test-p0-crash-* arm.  Property tests drive
::  ++og from the pinned literal seeds recorded below.
::
/-  *racoon
/+  *test, racoon, vec=racoon-vectors, fmt=racoon-fmt, rs=racoon-rs
/+  fp=racoon-fp3
/+  zf=racoon-zfac
/+  rr=racoon-roots
/+  al=racoon-alg
=/  nz  nz:racoon
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  mx  mx:racoon
=/  qx  qx:racoon
::  doors at primes, a composite, and the smallest modulus
=/  m7   ~(. mx 7)
=/  m6   ~(. mx 6)
=/  m3   ~(. mx 3)
=/  m2   ~(. mx 2)
::  and at the Goldilocks prime, for the extension field tests
=/  mgl  ~(. mx 18.446.744.069.414.584.321)
|%
::    +rng:  a bounded stream of naturals from a pinned seed
::
::  [seed=@ n=@ud hi=@ud] -> (list @ud), n values each in [0, hi).
::  Sizes stay small so the interpreted suite runs in tolerable time.
++  rng
  |=  [seed=@ n=@ud hi=@ud]
  ^-  (list @ud)
  =/  gen  ~(. og seed)
  =|  out=(list @ud)
  |-  ^-  (list @ud)
  ?:  =(0 n)  (flop out)
  =^  r  gen  (rads:gen hi)
  $(n (dec n), out [r out])
::    +pairs:  zip a flat list into pairs
++  pairs
  |=  a=(list @ud)
  ^-  (list [@ud @ud])
  ?~  a  ~
  ?~  t.a  ~
  [[i.a i.t.a] $(a t.t.a)]
::    +divides:  does a divide b?
++  divides
  |=  [a=@ud b=@ud]
  ^-  ?
  ?:  =(0 a)  =(0 b)
  =(0 (mod b a))
::    +to-zol:  build a canonical zol from a list of naturals
::
::  The top coefficient is forced nonzero, so the result is canonical by
::  construction.  Deliberately does NOT call +canon:zx: property tests must
::  not depend on the arm they would otherwise be exercising.
++  to-zol
  |=  cs=(list @ud)
  ^-  zol
  =/  ss=zol
    %+  turn  cs
    |=(c=@ud ^-(@s (dif:si (sun:si (mod c 41)) --20)))
  =/  rs=zol  (flop ss)
  ?~  rs  ~
  (flop [?:(=(--0 i.rs) --1 i.rs) t.rs])
::    +to-mol:  reduce a zol into a canonical mol modulo n
::
::  Note that ++dul:si is NOT usable here: it computes (sub b +.c) for a
::  negative operand, which underflows whenever the magnitude exceeds n, and
::  the supply below reaches 20 against moduli as small as 2.  Reducing the
::  magnitude first is what makes this total.
::
::  Trailing zeros are dropped locally rather than through +canon:mx, so the
::  property tests do not depend on the arm they would be exercising.
++  to-mol
  |=  [a=zol n=@ud]
  ^-  mol
  =/  cs=(list @ud)
    %+  turn  a
    |=  c=@s
    ^-  @ud
    =/  m=@ud  (mod (abs:si c) n)
    ?:  (syn:si c)  m
    (mod (sub n m) n)
  =/  r=(list @ud)  (flop cs)
  |-  ^-  mol
  ?~  r  ~
  ?:  =(0 i.r)  $(r t.r)
  (flop r)
::    +tderiv:  formal derivative over Z, for the test suite
::
::  The library's +zderiv lives in the private +pv core and is not reachable
::  from here.  Recomputing it independently is the right thing anyway: a
::  squarefreeness check that borrowed the library's own derivative would be
::  checking less than it appears to.
++  tderiv
  |=  a=zol
  ^-  zol
  ?~  a  ~
  =/  cs=zol  t.a
  =/  k=@ud   1
  =|  out=zol
  |-  ^-  zol
  ?~  cs  (flop out)
  $(cs t.cs, k +(k), out [(pro:si (sun:si k) i.cs) out])
::    +ipow:  integer power, for checking the pseudo-division identity
::
::  The library's own +pows lives in the private +pv core, which is not
::  reachable from here -- correctly, since it is not public API.  Repeated
::  multiplication is the honest check anyway: it shares no code with the
::  square-and-multiply the library uses.
++  ipow
  |=  [b=@s e=@ud]
  ^-  @s
  ?:  =(0 e)  --1
  (pro:si b $(e (dec e)))
::    +to-qol:  embed a zol into Q[x] with varied denominators
::
::  Denominators are derived from the coefficient index, so the supply
::  exercises genuine fractions rather than integers-as-rationals.  Uses
::  +new:qq to canonicalize, which is a Phase 0 arm and so not under test
::  here; trailing zeros are dropped locally rather than via +canon:qx.
++  to-qol
  |=  a=zol
  ^-  qol
  =/  cs=(list frac)
    =/  xs=zol  a
    =/  i=@ud   1
    =|  out=(list frac)
    |-  ^-  (list frac)
    ?~  xs  (flop out)
    $(xs t.xs, i +(i), out [(new:qq i.xs (add 1 (mod i 5))) out])
  =/  r=(list frac)  (flop cs)
  |-  ^-  qol
  ?~  r  ~
  ?:  =(--0 p.i.r)  $(r t.r)
  (flop r)
::    +zols:  a deterministic supply of canonical polynomials
++  zols
  |=  [seed=@ count=@ud]
  ^-  (list zol)
  =/  ns=(list @ud)  (rng seed (mul count 6) 100)
  =|  out=(list zol)
  =/  i=@ud  0
  |-  ^-  (list zol)
  ?:  =(i count)  (flop out)
  $(i +(i), ns (slag 6 ns), out [(to-zol (scag +((mod i 5)) ns)) out])
::    +zpairs:  sliding window of consecutive pairs
++  zpairs
  |=  a=(list zol)
  ^-  (list [zol zol])
  ?~  a  ~
  ?~  t.a  ~
  [[i.a i.t.a] $(a t.a)]
::    +ztriples:  sliding window of consecutive triples
++  ztriples
  |=  a=(list zol)
  ^-  (list [zol zol zol])
  ?~  a  ~
  ?~  t.a  ~
  ?~  t.t.a  ~
  [[i.a i.t.a i.t.t.a] $(a t.a)]
::  Vector-driven arms below all follow one shape: +skip the cases whose
::  computed value matches the oracle's, then expect the empty list.  A
::  regression therefore names every failing case, rather than stopping at
::  the first one.
::
++  gl3  ~(. fp [18.446.744.069.414.584.321 ~[18.446.744.069.414.584.320 18.446.744.069.414.584.320 0 1]])
::    +f27:  F_3[x]/(x^3 - x - 1), the same cubic over the smallest prime
::  where it stays irreducible
++  f27  ~(. fp [3 ~[2 2 0 1]])
::    +f49:  F_7[x]/(x^2 + 1), a QUADRATIC -- the door is not cubic-only
++  f49  ~(. fp [7 ~[1 0 1]])
::    +f7x:  the same cubic over F_7, where it is REDUCIBLE (5 is a root).
::  Present only so that +irreducible has a negative case.
++  f7x  ~(. fp [7 ~[6 6 0 1]])
::    +els:  every element of an extension of degree k over F_pr
::
::  Index i in [0, pr^k) written in base pr, little-endian.  Trailing zero
::  coefficients make these non-canonical, so callers reduce them through
::  the field's own +canon -- which also exercises that arm 27 or 49 times.
++  els
  |=  [pr=@ud k=@ud]
  ^-  (list mol)
  =/  tot=@ud  (pow pr k)
  =/  i=@ud    0
  =|  out=(list mol)
  |-  ^-  (list mol)
  ?:  =(i tot)  (flop out)
  =/  e=mol
    =/  j=@ud  0
    =/  v=@ud  i
    =|  cs=mol
    |-  ^-  mol
    ?:  =(j k)  (flop cs)
    $(j +(j), v (div v pr), cs [(mod v pr) cs])
  $(i +(i), out [e out])
::
::    +vecs-fp3:  the Goldilocks operand pairs, for the structural tests
::
::  Same six pairs the vector tests use, so a structural law and a
::  transcribed value are always checked against the same inputs.
++  vecs-fp3
  ^-  (list [mol mol])
  :~
    [~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992] ~[15.149.836.622.520.594.227 1.736.392.818.365.009.963 10.750.541.312.280.087.032]]
    [~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368] ~[7.713.914.763.314.685.786 4.439.448.776.366.754.703 10.165.027.665.383.847.897]]
    [~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643] ~[11.632.994.891.556.335.705 10.754.394.637.803.157.173 1.141.153.371.300.629.929]]
    [~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692] ~[10.268.654.918.125.279.152 2.456.641.775.679.608.523 7.731.750.658.069.747.094]]
    [~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632] ~[12.580.729.232.405.932.079 1.901.042.282.212.365.707 10.536.861.175.493.410.705]]
    [~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753] ~[10.410.757.471.710.933.047 11.418.711.589.407.294.900 9.157.231.070.389.319.135]]
  ==
::
++  test-fp3-goldilocks-mul
  ;:  weld
    %+  expect-eq  !>(`mol`~[10.592.939.488.128.544.169 11.937.663.410.871.179.763 2.369.382.593.281.921.793])  !>((mul:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992] ~[15.149.836.622.520.594.227 1.736.392.818.365.009.963 10.750.541.312.280.087.032]))
    %+  expect-eq  !>(`mol`~[11.849.668.667.596.254.297 5.699.062.322.470.157.694 4.460.854.052.477.668.897])  !>((mul:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368] ~[7.713.914.763.314.685.786 4.439.448.776.366.754.703 10.165.027.665.383.847.897]))
    %+  expect-eq  !>(`mol`~[15.875.625.163.121.047.325 7.555.602.628.186.295.849 14.454.697.153.828.416.498])  !>((mul:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643] ~[11.632.994.891.556.335.705 10.754.394.637.803.157.173 1.141.153.371.300.629.929]))
    %+  expect-eq  !>(`mol`~[3.367.972.451.319.380.774 16.710.018.798.525.813.693 8.696.113.652.008.925.291])  !>((mul:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692] ~[10.268.654.918.125.279.152 2.456.641.775.679.608.523 7.731.750.658.069.747.094]))
    %+  expect-eq  !>(`mol`~[15.481.959.137.259.292.424 3.295.097.563.200.132.596 3.276.036.955.049.487.529])  !>((mul:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632] ~[12.580.729.232.405.932.079 1.901.042.282.212.365.707 10.536.861.175.493.410.705]))
    %+  expect-eq  !>(`mol`~[17.068.172.796.397.988.111 2.750.331.618.037.449.294 18.251.154.154.780.879.620])  !>((mul:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753] ~[10.410.757.471.710.933.047 11.418.711.589.407.294.900 9.157.231.070.389.319.135]))
  ==
++  test-fp3-goldilocks-inv
  ;:  weld
    %+  expect-eq  !>(`mol`~[12.723.468.023.368.378.352 702.075.037.308.433.792 14.408.387.085.894.643.388])  !>((inv:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992]))
    %+  expect-eq  !>(`mol`~[6.808.717.314.311.538.116 18.200.304.465.036.626.763 9.664.175.183.922.223.429])  !>((inv:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368]))
    %+  expect-eq  !>(`mol`~[17.949.377.739.245.621.234 15.047.477.832.519.149.683 5.108.731.974.324.903.550])  !>((inv:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643]))
    %+  expect-eq  !>(`mol`~[2.363.253.709.304.878.555 8.022.684.551.571.270.240 6.448.780.702.247.989.519])  !>((inv:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692]))
    %+  expect-eq  !>(`mol`~[2.957.515.314.407.620.444 16.794.988.912.772.997.060 14.692.297.148.276.400.677])  !>((inv:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632]))
    %+  expect-eq  !>(`mol`~[7.775.676.696.869.884.935 11.311.092.619.121.807.154 10.972.962.206.138.794.958])  !>((inv:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753]))
  ==
++  test-fp3-goldilocks-frob
  ;:  weld
    %+  expect-eq  !>(`mol`~[16.649.451.722.258.662.587 54.953.028.421.272.613 11.367.466.393.749.441.420])  !>((frob:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992]))
    %+  expect-eq  !>(`mol`~[8.791.301.720.535.786.212 12.336.450.217.959.254.623 4.346.739.138.459.173.681])  !>((frob:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368]))
    %+  expect-eq  !>(`mol`~[4.168.264.876.168.382.243 11.770.119.229.225.023.433 3.637.187.437.674.094.759])  !>((frob:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643]))
    %+  expect-eq  !>(`mol`~[3.681.891.593.578.633.383 3.925.650.661.787.884.683 14.757.401.702.049.438.984])  !>((frob:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692]))
    %+  expect-eq  !>(`mol`~[5.163.916.486.540.301.698 9.882.919.573.921.710.380 17.549.889.152.887.464.939])  !>((frob:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632]))
    %+  expect-eq  !>(`mol`~[14.365.609.717.408.355.583 12.242.141.900.291.252.510 15.232.867.628.034.243.478])  !>((frob:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753]))
  ==
++  test-fp3-goldilocks-norm
  ;:  weld
    %+  expect-eq  !>(`@ud`11.241.016.387.895.453.009)  !>((norm:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992]))
    %+  expect-eq  !>(`@ud`11.633.700.033.010.161.688)  !>((norm:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368]))
    %+  expect-eq  !>(`@ud`12.453.535.689.658.829.251)  !>((norm:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643]))
    %+  expect-eq  !>(`@ud`1.243.425.802.586.706.278)  !>((norm:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692]))
    %+  expect-eq  !>(`@ud`9.928.025.544.317.356.374)  !>((norm:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632]))
    %+  expect-eq  !>(`@ud`13.562.233.187.987.041.780)  !>((norm:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753]))
  ==
++  test-fp3-goldilocks-pow
  ;:  weld
    %+  expect-eq  !>(`mol`~[15.505.590.388.589.805.653 16.515.675.872.690.305.082 16.290.383.523.311.901.322])  !>((pow:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992] 7))
    %+  expect-eq  !>(`mol`~[5.962.807.838.841.906.076 9.737.786.156.774.950.341 9.246.234.658.943.802.996])  !>((pow:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368] 7))
    %+  expect-eq  !>(`mol`~[3.538.916.642.228.569.644 4.251.654.170.301.896.480 17.583.953.274.526.272.507])  !>((pow:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643] 7))
    %+  expect-eq  !>(`mol`~[15.051.117.417.199.140.143 2.891.585.061.584.434.944 1.508.287.365.661.100.857])  !>((pow:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692] 7))
    %+  expect-eq  !>(`mol`~[11.969.937.174.133.119.552 4.740.750.696.092.204.648 5.029.723.345.589.179.696])  !>((pow:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632] 7))
    %+  expect-eq  !>(`mol`~[12.731.444.577.297.748.616 4.203.591.886.033.547.102 6.027.953.068.008.595.039])  !>((pow:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753] 7))
  ==
++  test-fp3-shape
  ;:  weld
    %+  expect-eq  !>(`mol`~)     !>(zero:gl3)
    %+  expect-eq  !>(`mol`~[1])  !>(one:gl3)
    %+  expect-eq  !>(`@ud`3)     !>(rank:gl3)
    %+  expect-eq  !>(`@ud`3)     !>(rank:f27)
    %+  expect-eq  !>(`@ud`2)     !>(rank:f49)
    ::  the base field embeds as constant polynomials, reduced mod p
    %+  expect-eq  !>(`mol`~)     !>((emb:gl3 0))
    %+  expect-eq  !>(`mol`~[1])  !>((emb:gl3 1))
    %+  expect-eq  !>(`mol`~[2])  !>((emb:f27 5))
    %+  expect-eq  !>(`mol`~)     !>((emb:f27 3))
    %-  expect      !>((is-zero:gl3 ~))
    %-  expect-fail  |.(?>((is-zero:gl3 ~[1]) ~))
  ==
++  test-fp3-canon
  ;:  weld
    ::  x^3 = x + 1 is the whole content of the modulus
    %+  expect-eq  !>(`mol`~[1 1])  !>((canon:gl3 ~[0 0 0 1]))
    %+  expect-eq  !>(`mol`~[1 1])  !>((canon:f27 ~[0 0 0 1]))
    ::  x^3 + x^2 + x + 1  ->  x^2 + 2x + 2
    %+  expect-eq  !>(`mol`~[2 2 1])  !>((canon:f27 ~[1 1 1 1]))
    ::  the modulus itself is zero in the quotient
    %+  expect-eq  !>(`mol`~)  !>((canon:f27 ~[2 2 0 1]))
    ::  coefficients are folded into [0, p), unlike +canon:mx
    %+  expect-eq  !>(`mol`~[1 2])  !>((canon:f27 ~[7 5]))
    %+  expect-eq  !>(`mol`~[1])    !>((canon:f27 ~[4 3 9]))
    ::  in F_49, x^2 = -1, so a degree-2 input is NOT already reduced
    %+  expect-eq  !>(`mol`~[6])    !>((canon:f49 ~[0 0 1]))
    %+  expect-eq  !>(`mol`~[3 1])  !>((canon:f49 ~[4 1 1]))
  ==
++  test-fp3-irreducible
  ;:  weld
    ::  verified independently before this library was written
    %-  expect  !>(irreducible:gl3)
    %-  expect  !>(irreducible:f27)
    %-  expect  !>(irreducible:f49)
    ::  the same cubic over F_7, where 5 is a root
    %+  expect-eq  !>(`@ud`0)  !>((eval:m7 ~[6 6 0 1] 5))
    %-  expect-fail  |.(?>(irreducible:f7x ~))
  ==
++  test-fp3-crash
  ;:  weld
    ::  zero has no inverse
    (expect-fail |.((inv:gl3 ~)))
    (expect-fail |.((inv:f27 ~)))
    (expect-fail |.((div:gl3 ~[1] ~)))
    ::  and over a REDUCIBLE modulus, neither does a zero divisor: x + 2 is
    ::  x - 5, and 5 is a root of that cubic over F_7
    (expect-fail |.((inv:f7x ~[2 1])))
    ::  while units there still invert, so the crash is discriminating
    (expect-success |.((inv:f7x ~[0 1])))
  ==
++  test-fp3-goldilocks-structure
  =/  as=(list mol)  (turn vecs-fp3 |=([a=mol b=mol] a))
  =/  bs=(list mol)  (turn vecs-fp3 |=([a=mol b=mol] b))
  =/  ord=@ud
    6.277.101.731.002.175.853.884.774.869.567.645.561.244.584.131.361.410.908.160
  =|  out=tang
  |-  ^-  tang
  ?~  as  out
  ?~  bs  out
  %=  $
    as  t.as
    bs  t.bs
    out
      %+  weld  out
      ;:  weld
        ::  inversion round-trips
        %+  expect-eq  !>(`mol`~[1])  !>((mul:gl3 i.as (inv:gl3 i.as)))
        %+  expect-eq  !>(`mol`i.as)  !>((div:gl3 (mul:gl3 i.as i.bs) i.bs))
        ::  every nonzero element satisfies a^(p^3 - 1) = 1
        %+  expect-eq  !>(`mol`~[1])  !>((pow:gl3 i.as ord))
        ::  Frobenius has order equal to the rank
        %+  expect-eq
          !>(`mol`i.as)
        !>((frob:gl3 (frob:gl3 (frob:gl3 i.as))))
        ::  and it is a ring homomorphism
        %+  expect-eq
          !>((frob:gl3 (mul:gl3 i.as i.bs)))
        !>((mul:gl3 (frob:gl3 i.as) (frob:gl3 i.bs)))
        %+  expect-eq
          !>((frob:gl3 (add:gl3 i.as i.bs)))
        !>((add:gl3 (frob:gl3 i.as) (frob:gl3 i.bs)))
        ::  the norm is multiplicative into the base field
        %+  expect-eq
          !>((norm:gl3 (mul:gl3 i.as i.bs)))
        !>((cmul:mgl (norm:gl3 i.as) (norm:gl3 i.bs)))
      ==
  ==
++  test-fp3-goldilocks-base
  ;:  weld
    ::  a base field element's norm is its rank-th power
    %+  expect-eq  !>(`@ud`125)  !>((norm:gl3 (emb:gl3 5)))
    %+  expect-eq  !>(`@ud`0)    !>((norm:gl3 ~))
    %+  expect-eq  !>(`@ud`1)    !>((norm:gl3 ~[1]))
    ::  Frobenius fixes exactly the base field
    %+  expect-eq  !>(`mol`~[5])  !>((frob:gl3 (emb:gl3 5)))
    ::  scaling agrees with multiplying by an embedded scalar
    %+  expect-eq
      !>((scal:gl3 ~[3 4 5] 6))
    !>((mul:gl3 ~[3 4 5] (emb:gl3 6)))
    ::  a^0 is one for every a, including zero
    %+  expect-eq  !>(`mol`~[1])  !>((pow:gl3 ~ 0))
    %+  expect-eq  !>(`mol`~)     !>((pow:gl3 ~ 5))
    %+  expect-eq  !>(`mol`~[3 4 5])  !>((pow:gl3 ~[3 4 5] 1))
  ==
++  test-f27-exhaustive-ring
  =/  es=(list mol)  (turn (els 3 3) |=(e=mol (canon:f27 e)))
  =/  as=(list mol)  es
  =|  out=tang
  |-  ^-  tang
  ?~  as  out
  =/  acc=tang
    =/  bs=(list mol)  es
    |-  ^-  tang
    ?~  bs  ~
    %+  weld
      ;:  weld
        ::  commutative ring laws over all 729 pairs
        %+  expect-eq  !>((mul:f27 i.as i.bs))  !>((mul:f27 i.bs i.as))
        %+  expect-eq  !>((add:f27 i.as i.bs))  !>((add:f27 i.bs i.as))
        %+  expect-eq  !>(`mol`i.as)  !>((sub:f27 (add:f27 i.as i.bs) i.bs))
        %+  expect-eq  !>(`mol`~)     !>((add:f27 i.as (neg:f27 i.as)))
        ::  associativity and distributivity against x
        %+  expect-eq
          !>((mul:f27 (mul:f27 i.as i.bs) ~[0 1]))
        !>((mul:f27 i.as (mul:f27 i.bs ~[0 1])))
        %+  expect-eq
          !>((mul:f27 i.as (add:f27 i.bs ~[0 1])))
        !>((add:f27 (mul:f27 i.as i.bs) (mul:f27 i.as ~[0 1])))
        ::  products stay reduced: at most rank coefficients.  Counted with
        ::  +lent rather than +deg:mx, since +deg crashes on zero (S8) and
        ::  zero is a perfectly ordinary product here.
        %-  expect  !>((lte (lent (mul:f27 i.as i.bs)) 3))
        ::  the norm is multiplicative here too
        %+  expect-eq
          !>((norm:f27 (mul:f27 i.as i.bs)))
        !>((mod (mul (norm:f27 i.as) (norm:f27 i.bs)) 3))
      ==
    $(bs t.bs)
  $(as t.as, out (weld out acc))
++  test-f27-exhaustive-units
  =/  es=(list mol)  (turn (els 3 3) |=(e=mol (canon:f27 e)))
  =|  out=tang
  |-  ^-  tang
  ?~  es  out
  ?:  =(~ i.es)
    ::  zero is the one element with no inverse and zero norm
    %=  $
      es   t.es
      out  (weld out (expect-fail |.((inv:f27 i.es))))
    ==
  =/  e=mol  i.es
  %=  $
    es  t.es
    out
      %+  weld  out
      ;:  weld
        %+  expect-eq  !>(`mol`~[1])  !>((mul:f27 e (inv:f27 e)))
        %+  expect-eq  !>(`mol`~[1])  !>((div:f27 e e))
        ::  the multiplicative group has order 26
        %+  expect-eq  !>(`mol`~[1])  !>((pow:f27 e 26))
        %+  expect-eq  !>(`mol`e)     !>((pow:f27 e 27))
        ::  Frobenius has order 3 and fixes only what it should
        %+  expect-eq  !>(`mol`e)  !>((frob:f27 (frob:f27 (frob:f27 e))))
        ::  a nonzero element has nonzero norm
        %-  expect  !>(!=(0 (norm:f27 e)))
        ::  and +pow agrees with repeated multiplication
        %+  expect-eq  !>((pow:f27 e 3))  !>((mul:f27 (mul:f27 e e) e))
      ==
  ==
++  test-f49-exhaustive
  =/  es=(list mol)  (turn (els 7 2) |=(e=mol (canon:f49 e)))
  =|  out=tang
  |-  ^-  tang
  ?~  es  out
  ?:  =(~ i.es)  $(es t.es)
  =/  e=mol  i.es
  %=  $
    es  t.es
    out
      %+  weld  out
      ;:  weld
        ::  a degree-2 extension: 48 units, Frobenius of order 2
        %+  expect-eq  !>(`mol`~[1])  !>((mul:f49 e (inv:f49 e)))
        %+  expect-eq  !>(`mol`~[1])  !>((pow:f49 e 48))
        %+  expect-eq  !>(`mol`e)     !>((frob:f49 (frob:f49 e)))
        %-  expect  !>((lte (lent e) 2))
        ::  x^2 = -1 = 6, which is the entire modulus
        %+  expect-eq  !>(`mol`~[6])  !>((mul:f49 ~[0 1] ~[0 1]))
      ==
  ==
::    +ascends:  is this list strictly increasing?
++  ascends
  |=  ks=(list @ud)
  ^-  ?
  ?~  ks  %.y
  =/  prev=@ud  i.ks
  =/  rest=(list @ud)  t.ks
  |-  ^-  ?
  ?~  rest  %.y
  ?.  (gth i.rest prev)  %.n
  $(rest t.rest, prev i.rest)
::  Integer factorizations from SymPy's factorint.  Unique, so these
::  are values and not a convention: any correct algorithm agrees.
--
