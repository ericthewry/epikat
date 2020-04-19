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


-- 8. Worlds of length two.
query two = (_;_)

-- 9. Worlds of length three.
query three = (_;_);_

-- 10. Tails event
query tails_event = announce_T + aly_peek_T + bob_peek_T

-- 11a. Peek tails event
query peek_tails_event = aly_peek_T + bob_peek_T

-- 11b. Peek event
query peek = aly_peek_H + bob_peek_H + aly_peek_T + bob_peek_T

-- 12. A peek tails event has happened
query have_peek_tails = (_*;peek_tails_event); _*

-- 13. Bob peek tails has happened
query have_bob_peek_tails = (_*;bob_peek_T); _*

-- 14. Worlds of length three including a tails event
query tails_event = three & (_*;tails_event);_

-- 15. Worlds of length three where Aly knows Bob has peeked tails
query aly_know_bob_peek_tails = three & ~aly(~ have_bob_peek_tails)

-- 16a. Announcements have happened
-- GOOD 
-- Announcements appear (together with sometimes peeks)
query have_announce = (_*;(announce_T + announce_H)); _*

-- 16b. No announcements have happened
-- GOOD
-- Announcements do not appear.
-- We get sequences of peeks.
query no_announce = ~ have_announce

-- 16c. Only peeks have happened
-- It should be equivalent to 16b.
-- GOOD we get sequences of peeks.
query only_peek = peek*

-- 17a. Worlds of length three where no announcements have happened.
-- The worlds have length three, but
-- BAD announcements sometimes appear.

query three_no_announce = three & no_announce

-- 17b. Worlds of length three where only peeks have happened.
-- Note that H/T consistency is imposed.
-- GOOD even though it should be equivalent to 17a.

query three_only_peek = three & only_peek

-- 17c. Worlds of length three some announcements have happened.
-- three & have_announce
-- GOOD apparently

query three_have_announce = three & have_announce























