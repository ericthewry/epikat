world = H + T

assert (~(H&T))&(H+T)

action announce_H = test H;id;test H
action announce_T = test T;id;test T

action aly_peek_H  = test H;id;test H
action aly_peek_T  = test T;id;test T

action bob_peek_H  = test H;id;test H
action bob_peek_T  = test T;id;test T

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

