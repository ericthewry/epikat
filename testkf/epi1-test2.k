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


















-- One event.
-- _
query One = _

-- Two events.
-- (_ ; _)
query Two = (_ ; _)

-- 5a. Worlds where every alternative for aly is aly_peek_H
-- out intersection at the top.
-- i.e. aly_peek_H is the sole alternative for aly.
-- It should be the unit set of aly_peek_H.
-- Without the intersection we get longer worlds in epik
-- (One & ~aly(~aly_peek_H))
query AlyBoxAlyPeek = (One & ~aly(~aly_peek_H))

-- 5b. Similar but with iteration of belief.
-- (One & ~aly(~~aly(~aly_peek_H)))
query AlyBoxAlyPeek = (One & ~aly(~~aly(~aly_peek_H)))

-- 6a. Worlds where every alternative for aly is bob_peek_H
-- i.e. bob_peek_H is the sole alternative for aly.
-- This should be null. There is no way for aly to get this
-- information in one step.
-- (One & ~aly(~bob_peek_H))
query AlyBoxBobPeek = (One & ~aly(~bob_peek_H))

-- 6b. Worlds where some alternative for aly is bob_peek_H
-- This should be bob_peek_H + bob_peek_T
-- (One & aly(bob_peek_H))
query AlyBoxBobPeek = (One & aly(bob_peek_H))

-- 7. Worlds where every alternative for aly is of the form  (bob_peek_H.announce_H)
-- This lets Aly learn that it is H in the second event.
-- The result should be the unit set of bob_peek_H.announce_H.
-- (Two & ~aly(~(bob_peek_H ; announce_H)))
query Example7 = (Two & ~aly(~(bob_peek_H ; announce_H)))

-- 8. Similar but where the second event is any event.
-- The result should be bob_peek_H.announce_H + bob_peek_H.aly_peek_H
-- (Two & ~aly(~(bob_peek_H ; _)))
query Example8 = (Two & ~aly(~(bob_peek_H ; _)))

-- 9a. Bob knows that Aly knows that Bob peeked T in the first step
-- The result should be bob_peek_H.announce_H + bob_peek_H.aly_peek_H
-- (Two & ~bob(~~aly(~(bob_peek_T ; _))))
query Example9a = (Two & ~bob(~~aly(~(bob_peek_T ; _))))

-- 9b. Bob knows that Aly knows that Aly peeked T in the first step
-- The result should be aly_peek_T;announce_T + aly_peek_T.bob_peek_T.
-- Aly peeks T in the first event and Bob figures it out in the second event.
-- (Two & ~bob(~~aly(~(aly_peek_T ; _))))
query Example9b = (Two & ~bob(~~aly(~(aly_peek_T ; _))))





