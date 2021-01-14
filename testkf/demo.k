state heads tails

restrict (heads + tails) & ~(heads & tails)
 
event nop (test heads):(test heads) + (test tails):(test tails)

event bob_peeks_heads (test heads):(test heads)
event bob_peeks_tails (test tails):(test tails)

event amy_peeks_heads (test heads):(test heads)
event amy_peeks_tails (test tails):(test tails)

event bob_turns_heads (test heads):(test tails)
event bob_turns_tails (test tails):(test heads)
event amy_turns_heads (test heads):(test tails)
event amy_turns_tails (test tails):(test heads)


agent bob
  (nop -> nop)
  (amy_peeks_heads -> amy_peeks_heads + amy_peeks_tails)
  (amy_peeks_tails -> amy_peeks_heads + amy_peeks_tails)
  (bob_peeks_heads -> bob_peeks_heads)
  (bob_peeks_tails -> bob_peeks_tails)
  (bob_turns_heads -> bob_turns_heads + bob_turns_tails)
  (bob_turns_tails -> bob_turns_heads + bob_turns_tails)
  (amy_turns_heads -> nop)
  (amy_turns_tails -> nop)

query bob_ever_peeks_heads = (_*;bob_peeks_heads;(_*))
query amy_ever_peeks_heads = (_*;amy_peeks_heads;(_*))
query bob_learns_amy_peeked_heads =
  (_;_;_) &
  amy_ever_peeks_heads &
  ~bob(~((_;_;_) & bob_ever_peeks_heads & amy_ever_peeks_heads))

query bob_is_wrong =
  (amy_peeks_tails;amy_turns_tails;bob_peeks_heads)
  & ~bob(~((_;_;_) & amy_ever_peeks_heads))


query bob_is_correct =
  (_;_;_) & amy_ever_peeks_heads & ~bob(~((_;_;_) & amy_ever_peeks_heads))
