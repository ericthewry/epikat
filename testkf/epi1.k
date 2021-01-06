state = H + T

restrict (~(H&T))&(H+T)

event announce_H = test H;id;test H
event announce_T = test T;id;test T

event aly_peek_H  = test H;id;test H
event aly_peek_T  = test T;id;test T

event bob_peek_H  = test H;id;test H
event bob_peek_T  = test T;id;test T

agent aly =
  (announce_H -> announce_H)
  (announce_T -> announce_T)
  (aly_peek_H -> aly_peek_H)
  (aly_peek_T -> aly_peek_T)
  (bob_peek_H -> bob_peek_H + bob_peek_T)
  (bob_peek_T -> bob_peek_H + bob_peek_T)

agent bob =
  (announce_H -> announce_H)
  (announce_T -> announce_T)
  (aly_peek_H -> aly_peek_H + aly_peek_T)
  (aly_peek_T -> aly_peek_T + aly_peek_T)
  (bob_peek_H -> bob_peek_H)
  (bob_peek_T -> bob_peek_T)

