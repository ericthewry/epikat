world = heads + tails

assert (~(heads&tails))&(heads+tails)

action public_announce_heads = test heads;id;test heads
action public_announce_tails = test tails;id;test tails

action alice_peek_heads  = test heads;id;test heads
action alice_peek_tails  = test tails;id;test tails

action bobby_peek_heads  = test heads;id;test heads
action bobby_peek_tails  = test tails;id;test tails

agent alice =
  (public_announce_heads -> public_announce_heads)
  (public_announce_tails -> public_announce_tails)
  (alice_peek_heads -> alice_peek_heads)
  (alice_peek_tails -> alice_peek_tails)
  (bobby_peek_heads -> bobby_peek_heads + bobby_peek_tails)
  (bobby_peek_tails -> bobby_peek_heads + bobby_peek_tails)

agent bobby =
  (public_announce_heads -> public_announce_heads)
  (public_announce_tails -> public_announce_tails)
  (alice_peek_heads -> alice_peek_heads + alice_peek_tails)
  (alice_peek_tails -> alice_peek_tails + alice_peek_tails)
  (bobby_peek_heads -> bobby_peek_heads)
  (bobby_peek_tails -> bobby_peek_tails)


query not_not_bph_pah = ~(bobby_peek_heads; public_announce_heads)


-- What is knowledge?  A knowledge query K(a, X) should be the sequences
-- that a knows in all worlds described by guarded strings X. 
-- an alternative relation R(a) in Event x Event is defined to be
--    Ra = { (e, e') | whenever e occurs, e' is a possibility for a  }
query box_not_bph_pah = alice(~(bobby_peek_heads;public_announce_heads))

query box_not_bph_pah_lit = ~alice(~(bobby_peek_heads;public_announce_heads))

query neg__box_not_bph_pah_lit = ~(box_not_bph_pah_lit)


#-- World where every alternative for alice is of the form (bobby_peek_heads; public_announc#e_heads)
#-- This lets Alice learn that it is heads in the second event
#-- This does not work
#query abox_bph_pah = ~alice(~(bobby_peek_heads; public_announce_heads))



