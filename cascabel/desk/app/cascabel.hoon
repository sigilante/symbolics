::  Cascabel - exact symbolic computation via %shoe, and a caderno kernel
::
::    Answers the %eval-command poke, so caderno can drive it as a kernel;
::    the handling for that lives in the vendored lib/shoe.hoon, along with
::    the /x/sole/sessions scry that powers kernel discovery.  This agent
::    needs no special code for either -- a poked command and a typed one
::    take the same path through +command-parser and +on-command.
::
::    STATELESS BY DESIGN.  There is no session map, no accumulated
::    subject, and nothing in state at all.  Every command is answered
::    from its own text, so re-running a cell, running cells out of
::    order, or pointing a second notebook at the same agent all behave
::    identically.  That is the whole contract: call and response.
::
/+  default-agent, shoe, dbug
/+  cas=cascabel
::
|%
+$  versioned-state  $%  [%0 state-0]  ==
::  no state: the agent is a pure function of each command
+$  state-0  [%0 ~]
+$  command  tape   ::  raw command line; lib/cascabel does the parsing
+$  card  card:shoe
::
::  +lines-of: split a possibly multi-line %eval-command payload
::
::    In this core rather than on the agent door below: Gall checks the
::    door's arm set exactly, and an extra arm there fails that check.
::
++  lines-of
  |=  t=tape
  ^-  (list tape)
  =/  cur=tape  ~
  =/  acc=(list tape)  ~
  |-
  ^-  (list tape)
  ?~  t
    (flop `(list tape)`[(flop cur) acc])
  ?:  =(i.t `@`10)
    $(t t.t, cur ~, acc `(list tape)`[(flop cur) acc])
  $(t t.t, cur `tape`[i.t cur])
::
--
=|  state-0
=*  state  -
::
%-  agent:dbug
^-  agent:gall
%-  (agent:shoe command)
^-  (shoe:shoe command)
|_  =bowl:gall
+*  this  .
    def   ~(. (default-agent this %|) bowl)
    des   ~(. (default:shoe this command) bowl)
::
++  on-init
  ^-  (quip card _this)
  `this
::
++  on-save   !>(state)
::
++  on-load
  |=  old=vase
  ^-  (quip card _this)
  `this
::
++  on-poke    on-poke:def
++  on-watch   on-watch:def
++  on-leave   on-leave:def
++  on-peek    on-peek:def
++  on-agent   on-agent:def
++  on-arvo    on-arvo:def
++  on-fail    on-fail:def
::
::  the whole line is the command; lib/cascabel splits verb from argument
++  command-parser
  |=  =sole-id:shoe
  ^+  |~(nail *(like [? command]))
  (stag | (star prn))
::
++  tab-list  tab-list:des
::
++  can-connect
  |=  =sole-id:shoe
  ^-  ?
  =(our src):bowl
::
++  on-connect
  |=  =sole-id:shoe
  ^-  (quip card _this)
  ::  shoe's on-watch already emits the initial %pro; don't double it
  `this
::
++  on-disconnect
  |=  =sole-id:shoe
  ^-  (quip card _this)
  `this
::
::  +on-command: evaluate and emit each output line as a %txt fact
::
::    No %pro here: the interactive path prompts through shoe, and the
::    %eval-command path appends its own terminal %pro in the vendored
::    wrapper.  A payload may be several lines, so each is evaluated in
::    turn -- independently, since nothing carries between them.
::
++  on-command
  |=  [=sole-id:shoe cmd=command]
  ^-  (quip card _this)
  =/  out=(list tape)
    %-  zing
    %+  turn  (lines-of cmd)
    |=(l=tape ^-((list tape) (eval:cas l)))
  :_  this
  %+  turn  out
  |=  l=tape
  ^-  card
  [%shoe ~[sole-id] %sole [%txt l]]
--
