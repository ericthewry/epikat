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


-- 1. Worlds where the world announce_H is a possibility for Aly.
-- The result is the unit set.
-- aly(announce_H)
-- GOOD
query Epi1ah = aly(announce_H)

-- 2. Worlds where the world announce_T is a possibility for Aly.
-- Symmetric to 1.
-- aly(announce_T)
-- GOOD
query Epi1at = aly(announce_T)

-- 3. Worlds where aly_peek_H is a possibility for Aly.
-- There is just one possibility, because there are no other actions
-- that generate this option for aly.
-- aly(aly_peek_H)
-- GOOD
query aa_peek = aly(aly_peek_H)

-- 4. Worlds where bob_peek_H is a possibility for Aly.
-- It should be bob_peek_H + bob_peek_T.
-- aly(bob_peek_H)
-- GOOD we get those two worlds.
query ab_peek = aly(bob_peek_H)


-- Now test the box modality.
-- 4a. Worlds where every alternative for aly is aly_peek_H,
-- i.e. aly_peek_H is the sole alternative for aly.
-- It should be the unit set of aly_peek_H.
-- _ & ~aly(~aly_peek_H)
-- GOOD
-- The top-level intersection with _ needed because currently the implementation approximates
--  the set. This should be fixed with when an automaton construction is implemented.
query a_box_a_peek = _ & ~aly(~aly_peek_H)

-- 4b. The same thing for announce_H.
-- _ & ~aly(~announce_H)
-- GOOD
query a_box_a_peek = _ & ~aly(~announce_H)

-- 5. Worlds where every alternative for aly is aly_peek_H,
-- Without the intersection
-- i.e. aly_peek_H is the sole alternative for aly.
-- It should be the unit set of aly_peek_H.
-- ~aly(~aly_peek_H)
-- FOR FUTURE REFERENCE
-- Without the intersection we get longer worlds, which looks wrong semantically.
query a_box_a_peek = ~aly(~aly_peek_H)

-- 6. Worlds where every alternative for aly is bob_peek_H,
-- i.e. bob_peek_H is the sole alternative for aly.
-- This should be null. There is no way for aly to get this
-- information in one step.
-- _ & ~aly(~bob_peek_H)
-- GOOD
query a_box_a_peek = _ & ~aly(~bob_peek_H)

-- 7. Worlds where every alternative for aly is of the form  (bob_peek_H.announce_H)
-- This lets Aly learn that it is H in the second event.
-- The result should be the unit set of bob_peek_H.announce_H.
-- (_;_) &  ~aly(~(bob_peek_H ; announce_H))
-- GOOD (note that there 
query a_box_a_peek_concat_pah1 = (_;_) &  ~aly(~(bob_peek_H ; announce_H))

-- 8. Worlds of length two where it is tails
query two_tails = (_;_) 






















