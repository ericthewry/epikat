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
  (nothing_happened -> nothing_happened)
  (announce_H -> announce_H)
  (announce_T -> announce_T)
  (aly_peek_H -> aly_peek_H + aly_peek_T)
  (aly_peek_T -> aly_peek_T + aly_peek_T)
  (bob_peek_H -> bob_peek_H)
  (bob_peek_T -> bob_peek_T)


-- Single events
query Event = announce_H + announce_T + aly_peek_H + aly_peek_T + bob_peek_H + bob_peek_T

-- World-time zero
query WZero = (test H) + (test T)

-- It's heads
-- This only showes WZero worlds
query ItsHeads = Event*; (test H)

-- It's heads after two events.
query TwoEventItsHeads = Event; Event; (test H)

-- It's tails after three events.
query ThreeEventItsTails = Event; Event; Event; (test T)

-- At least one event
-- This only shows single-event worlds.
query AtLeastOneEvent = Event; Event*

-- Aly know it's heads after two events
-- This looks good. It should entail that Aly has peeked at heads or
-- that heads has been announced.
query AlyKnowTwoEventItsHeads = aly(TwoEventItsHeads)

-- Aly knows that Bob knows that it's tails after three events.
-- This gives an error:
-- nested QApply could not be resolved for expr bob(TwoEventItsHeads)
query AlyKnowBobKnowTwoEventItsHeads = aly(bob(TwoEventItsHeads))