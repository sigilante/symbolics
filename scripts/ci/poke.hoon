::  the poke helper from urbit/urbit nix/test-fake-ship.nix, verbatim in
::  substance: send a poke and wait for its ack
=>
|%
++  take-poke-ack
  |=  =wire
  =/  m  (strand ,?)
  ^-  form:m
  |=  tin=strand-input:strand
  ?+  in.tin  `[%skip ~]
      ~  `[%wait ~]
      [~ %agent * %poke-ack *]
    ?.  =(wire wire.u.in.tin)
      `[%skip ~]
    ?~  p.sign.u.in.tin
      `[%done %.y]
    `[%done %.n]
  ==
++  poke
  |=  [=dock =cage]
  =/  m  (strand ,?)
  ^-  form:m
  =/  =card:agent:gall  [%pass /poke %agent dock %poke cage]
  ;<  ~  bind:m  (send-raw-card card)
  (take-poke-ack /poke)
--
