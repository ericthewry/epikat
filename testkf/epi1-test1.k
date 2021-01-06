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


















-- 1. Worlds where the world announce_H is a possibility for aly.
-- The result is the unit set.
-- GOOD
-- aly(announce_H)
query Epi1ah = aly(announce_H)

-- 2. Worlds where the world announce_T is a possibility for aly.
-- Symmetric to 1.
-- GOOD
-- aly(announce_T)
query Epi1ah = aly(announce_T)

-- 3. Worlds where aly_peek_H is a possibility for aly.
-- There is just one possibility
-- that generate this option for aly.
-- GOOD
-- aly(aly_peek_H)
query aapeek = aly(aly_peek_H)

-- 4. Worlds where bob_peek_H is a possibility for aly.
-- It should be bob_peek_H + bob_peek_T.
-- GOOD we get those two worlds.
-- aly(bob_peek_H)
query abpeek = aly(bob_peek_H)


-- Now test the box modality.
-- 4a. Worlds where every alternative for aly is aly_peek_H
-- i.e. aly_peek_H is the sole alternative for aly.
-- It should be the unit set of aly_peek_H.
-- GOOD
-- The top-level intersection with _ needed in Epik because currently
-- the implementation approximates the set. This should be fixed with when
-- an automaton construction is implemented.
-- (_ & ~aly(~aly_peek_H))
query aboxapeek = (_ & ~aly(~aly_peek_H))


