state = H + T

restrict (~(H&T))&(H+T)

event c1 = test H;id;test H
event c0 = test T;id;test T

event a1  = test H;id;test H
event a0  = test T;id;test T

event b1  = test H;id;test H
event b0  = test T;id;test T

agent aly =
  (c1 -> c1)
  (c0 -> c0)
  (a1 -> a1)
  (a0 -> a0)
  (b1 -> b1 + b0)
  (b0 -> b1 + b0)

agent bob =
  (c1 -> c1)
  (c0 -> c0)
  (a1 -> a1 + a0)
  (a0 -> a1 + a0)
  (b1 -> b1)
  (b0 -> b0)

-- Investigate cardinalities etc of worlds of length two.
-- Testing should be done with a high print count, e.g.
-- stack exec epik-exe 64 examples/ep1_two.k
-- 1 Two events
--  _;_
-- There are six events. But for the second event,
-- there are 3 possibilities because of the
-- fluents being set.  So there are 6*3=18 worlds of
-- length two.  This is how it comes out.
-- GOOD
query Two = _;_

-- 2 Aly considers it possible that she is in
-- a world of length two. This should
-- be equivalent to Two (18 worlds)
-- because agents always know how long
-- their world is.
-- aly(Two)
-- GOOD

query aly_diamond_two = aly(Two)


-- 3. The dual expressing box.
-- This should be equivalent to Two.
-- Gloss aly does not have an alternative with is not of length two.
-- ~aly(~Two)
-- BAD
-- We find 18 worlds of length two, but also
-- longer worlds such as c0.a0.c0.c0.b0.b0.
query aly_box_two = ~aly(~Two)

-- 4. Double negation
-- The results of length 1 are right, but a bunch of length six are found.
-- ~~a1
query neg2 = ~~a1

-- 5. Quadruple negation
-- ~~~~c0

query neg4 = ~~~~c0

-- 6. Double negation with worlds of length six.
-- This finds worlds of length six.
-- It should be empty.
query neg2b = (Two;Two;Two) & ~~a1






