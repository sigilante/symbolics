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
=/  m  (strand ,vase)
;<  =bowl:strand  bind:m  get-bowl:strandio
;<  ok=?  bind:m  (poke [our.bowl %hood] %kiln-commit !>([%base %.n]))
(pure:m !>(ok))
