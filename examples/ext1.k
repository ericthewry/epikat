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

query OneEvent = _
query OneEventHeads = _; test heads
query OneEventTails = _; test tails

query TwoEventsHeads = _; _; test heads
query TwoEventsTails = _; _; test tails

query HeadsTwoEventsTails = test heads; _; _; test tails

query Union1 = 
     public_announce_heads + public_announce_tails

query ConcatenationUnion1 = 
     (bobby_peek_heads + bobby_peek_tails) ; (alice_peek_heads + alice_peek_tails)

query ConcatenationUnion2 = 
     (bobby_peek_heads + bobby_peek_tails) ; (alice_peek_heads + alice_peek_tails) ; (public_announce_heads + public_announce_tails)

query IntersectionUnion1 = 
     (bobby_peek_heads + bobby_peek_tails) & (bobby_peek_heads + alice_peek_heads)

query Heads = (_*) ; (test heads)
query Tails = (_*) ; (test tails)

query NotHeads = ~Heads
query NotTails = ~Tails

query NotHeadsThree = NotHeads & (_;_;_)




