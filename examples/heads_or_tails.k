world = heads + tails

assert (~(heads&tails))&(heads+tails)

action nothing_happened = ((test heads;id;test heads) + (test tails;id;test tails))

action public_announce_heads = test heads;id;test heads
action public_announce_tails = test tails;id;test tails

action alice_peeks_heads  = test heads;id;test heads
action alice_peeks_tails  = test tails;id;test tails

action bobby_peeks_heads  = test heads;id;test heads
action bobby_peeks_tails  = test tails;id;test tails

action alice_sneaks_heads = test heads;id;test heads
action alice_sneaks_tails = test tails;id;test tails
action bobby_sneaks_heads = test heads;id;test heads
action bobby_sneaks_tails = test tails;id;test tails

action public_flip = ((test heads;id;test tails) + (test tails;id;test heads))

agent alice =
  (nothing_happened -> nothing_happened)
  (public_announce_heads -> public_announce_heads)
  (public_announce_tails -> public_announce_tails)
  (alice_peeks_heads -> alice_peeks_heads)
  (alice_peeks_tails -> alice_peeks_tails)
  (bobby_peeks_heads -> bobby_peeks_heads + bobby_peeks_tails)
  (bobby_peeks_tails -> bobby_peeks_heads + bobby_peeks_tails)
  (alice_sneaks_heads -> alice_sneaks_heads)
  (alice_sneaks_tails -> alice_sneaks_tails)
  (bobby_sneaks_heads -> nothing_happened)
  (bobby_sneaks_tails -> nothing_happened)
  (public_flip_ht -> public_flip_ht)
  (public_flip_th -> public_flip_th)

agent bobby =
  (nothing_happened -> nothing_happened)
  (public_announce_heads -> public_announce_heads)
  (public_announce_tails -> public_announce_tails)
  (alice_peeks_heads -> alice_peeks_heads + alice_peeks_tails)
  (alice_peeks_tails -> alice_peeks_tails + alice_peeks_tails)
  (bobby_peeks_heads -> bobby_peeks_heads)
  (bobby_peeks_tails -> bobby_peeks_tails)
  (alice_sneaks_heads -> nothing_happened)		
  (alice_sneaks_tails -> nothing_happened)
  (bobby_sneaks_heads -> bobby_sneaks_heads)
  (bobby_sneaks_tails -> bobby_sneaks_tails)
  (public_flip_ht -> public_flip_ht)
  (public_flip_th -> public_flip_ht)  

query BobbySawHeadsOnce = public_announce_heads + bobby_peeks_heads + bobby_sneaks_heads
query AliceSawHeadsOnce = public_announce_heads + alice_peeks_heads + alice_sneaks_heads

query AliceAndBobbySawHeads =
      (public_announce_heads + bobby_peeks_heads + bobby_sneaks_heads) & (public_announce_heads + alice_peeks_heads + alice_sneaks_heads)


query AliceKnowsBobbyPeekHeadsSoln = bobby_sneak_heads + bobby_sneak_tails

query AliceKnowsBobbyPeekHeadsNNF = ~public_announce_heads
      				  & ~public_announce_tails
				  & ~alice_peeks_heads
				  & ~alice_peeks_tails
				  & ~bobby_peeks_tails
				  & ~bobby_peeks_heads
				  & ~alice_sneaks_heads
				  & ~alice_sneaks_tails
				  & ~nothing_happened
				  & ~nothing_happened
				  & ~nothing_happened


query AliceKnowsBobbyPeekHeads1 = ~( public_announce_heads
      				   + public_announce_tails
				   + alice_peeks_heads
				   + alice_peeks_tails
				   + bobby_peeks_tails + bobby_peeks_heads
				   + alice_sneaks_heads
				   + alice_sneaks_tails
				   + nothing_happened
				   + nothing_happened
				   + nothing_happened )
                                  

query AliceKnowsBobbyPeekHeads2 = ~alice( public_announce_heads
					+ public_announce_tails
					+ alice_peeks_heads
					+ alice_peeks_tails
					+ bobby_peeks_tails
					+ alice_sneaks_heads
					+ alice_sneaks_tails
					+ bobby_sneaks_heads
					+ bobby_sneaks_tails
					+ nothing_happened)

query AliceKnowsBobbyPeekHeads3 = alice(~bobby_peeks_heads)


query PublicAnnounceIter = (_;_) & (public_announce_heads;(public_announce_heads + public_announce_tails)*)

query Anything = _;(_*)

query Heads = _;test heads

query PublicAnnounce = public_announce_heads + public_announce_tails

query PublicAnnouncedFlips = PublicAnnounce;public_flip*;PublicAnnounce

query EvenFlips = test heads; public_flip*; test heads

query AliceNotEndingInHeads = alice(~(_*;test heads))

query AliceKnowsHeads = alice(_*; test heads)
