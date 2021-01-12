state h t

restrict (~(h&t)) & (h+t)
 
event o (test h):(test h) + (test t):(test t)

event a1 (test h):(test h)
event a0 (test t):(test t)

event b1 (test h):(test h)
event b0 (test t):(test t)

event a10 (test h):(test t)
event a01 (test t):(test h)

event b10 (test h):(test t)
event b01 (test t):(test h)

agent amy
  (o -> o)
  (a1 -> a1)
  (a0 -> a0)
  (b1 -> b1 + b0)
  (b0 -> b1 + b0)
  (a10 -> a10 + a01)
  (a01 -> a10 + a01)
  (b10 -> o)
  (b01 -> o)
  
agent bob
  (o -> o)
  (a1 -> a1 + a0)
  (a0 -> a0 + a0)
  (b1 -> b1)
  (b0 -> b0)
  (a10 -> o)
  (a01 -> o)
  (b10 -> b10 + b01)
  (b01 -> b10 + b01)





