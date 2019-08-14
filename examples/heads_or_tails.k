world = heads + tails

assert ~(heads;tails)

action nothing_happened = 0

action public_announce_heads = test heads
action public_announce_tails = test tails

action alice_peeks_heads  = test heads
action alice_peeks_tails  = test tails
action bobby_peeks_heads  = test heads
action bobby_peeks_tails  = test tails

action alice_sneaks_heads = test heads
action alice_sneaks_tails = test tails
action bobby_sneaks_heads = test heads
action bobby_sneaks_tails = test tails

agent alice =
  (nothing_happened -> nothing_happened)
  (public_announce_heads -> public_announce_heads)
  (public_announce_tails -> public_announce_tails)
  (alice_peeks_heads -> alice_peeks_heads)
  (alice_peeks_tails -> alice_peeks_tails)
  (bobby_peeks_heads -> bobby_peeks_heads + bobby_peeks_tails)
  (bobby_peeks_tails -> bobby_peeks_tails + bobby_peeks_tails)
  (alice_sneaks_heads -> alice_sneaks_heads)
  (alice_sneaks_tails -> alice_sneaks_tails)
  (bobby_sneaks_heads -> nothing_happened)
  (bobby_sneaks_tails -> nothing_happened)


agent bob =
  (nothing_happened -> nothing_happend)
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


query DoesEverAnnounce =
  1*;(public_announce_heads + public_announce_tails);1*

query BobbySeesHeads =
    (public_announce_heads + bobby_peeks_heads + bobby_sneaks_heads);
    (public_announce_heads + bobby_peeks_heads + bobby_sneaks_heads)*

query WhatDoesAliceKnowAboutWorldsWhereBobSeesHeads =
  ~alice(
     ~((public_announce_heads + bobby_peeks_heads + bobby_sneaks_heads);
       (public_announce_heads + bobby_peeks_heads + bobby_sneaks_heads)*)
    )




