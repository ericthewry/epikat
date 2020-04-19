set print-space ON
# Base corresponding to epi1.k and epi2.k

# Guarded strings start and end with a propositions, and have
# propositions alternating with events.
# Examples:
# HkHaHhHoHkH
# TjTmT
# HcHkH
# TiTiTbTeTmTeT

# Basic proposition, head or tails.
define H "H";
define T "T";

# Set of tests.
# It's a single boolean.
define p [H | T];

# Concatenation in the string algebra of two guarded strings results
# in a string with a sequence of two booleans as a substring.
# Define the well-formed and ill-formed such sequences.

# Well-formed sequence of two booleans.
define ppWf [H H] | [T T];

# Ill-formed sequence of two booleans, obtained in concatenation
define ppIf [H T] | [T H];

# Two booleans. 
define pp ppWf | ppIf;

# Basic state, encoding the non-epistemic information.
# This is now p.
# define BasicState [H | T];

# Table of events/Kleene elements.
# There are six events

# announce%_H	 public announcement that H
# announce%_T	 public announcement that T
# aly%_peek%_H	 Aly sensing H, with Bob aware that Amy is sensing, but not what she senses.
# bob%_peek%_H	 Symmetrically for Bob
# aly%_peek%_T	 Aly sensing H, with Bob aware that Amy is sensing, but not what she senses.
# bob%_peek%_T	 Symmetrically for Bob

# Preconditions

# announce%_H	 H
# announce%_T	 T
# aly%_peek%_H	 H
# bob%_peek%_H	 H
# aly%_peek%_T	 T
# bob%_peek%_T	 T

###########################################
#
#   Events
#
###########################################

# Bare events with precondition satisfied in an H-world.
# These can increment an H-world. 
define EventH0 [announce%_H | aly%_peek%_H | bob%_peek%_H];

# Bare events with precondition satisfied in a T-world.
# These can increment a T-world.
define EventT0 [announce%_T | aly%_peek%_T | bob%_peek%_T];

define Event0 EventH0 | EventT0;

# Guarded strings corresponding to events, with a test at the start and the end,
# surrounding the Kleene emement. 
define EventH [H EventH0 H];

# The corresponding guarded strings, with a test at the start and the end.
define EventT [T EventT0 T];

# Events in general.
define Event [EventH | EventT];

# Map a bare event to a guarded string.
define Event(X) [p X p] & Event;

# The above construction represents the pre- and post-conditions
# of Kleene elements in the set Event.

# Reduce a sequence of two tests to a single test, by deleting the second one.
define Squash p -> 0 || p _;

# String that doesn't contain a non-matching test pair.
define Wf0 ~[$ ppIf];

#########################################
#
#      KAT operations
#
#########################################

# KAT concatenation operation on sets.
# Concatenate in the string algebra, eliminate strings with
# non-matching tests, then map to a guarded string.
define Cn(X,Y) [[[X Y] & Wf0] .o. Squash].l; 
#                ---- concatenate in the string algebra
#                     ----- eliminate strings that contain non-matching tests
#                             ---------- map to a guarded string

# Remove medial Booleans.
# This is can be used to produce a shorter print name.
# It isn't used in the analysis.
define Short0 p -> 0 || Event0 _ Event0;
define Short(X) [X .o. Short0].l;

# Kleene Plus
define Pl(X) [[[X+] & Wf0] .o. Squash].l; 
#              --- Kleene plus in the string algebra
#                  ----- eliminate strings that contain non-matching tests
#                             ---------- map to a guarded string

# Kleene Star
define St(X) [[[X*] & Wf0] .o. Squash].l; 
#              --- Kleene star in the string algebra
#                  ----- eliminate strings that contain non-matching tests
#                             ---------- map to a guarded string

# KAT concatenation operation on relations
define Cnr(R,S) Squash.i .o. Wf0 .o. [R S] .o. Wf0 .o. Squash; 
#                                    ---- concatenate in the string algebra
#                            ------        ------- constrain domain and codomain
#                                                  to contain non non-matching tests
#               ------------                       ---------- map to guarded strings
#                                                             on both sides.

# Kleene Plus on relations
define Plr(X) Squash.i .o. Wf0 .o. [X+] .o. Wf0 .o. Squash;
#                                  ----   Kleene plus in the string algebra
#                          ------       -------    constrain domain and codomain
#                                                  to contain non non-matching tests
#             ------------                         ---------- map to guarded strings
#                                                             on both sides.

# Kleene Star on relations
define Str(X) Squash.i .o. Wf0 .o. [X+] .o. Wf0 .o. Squash;
#                                  ----   Kleene plus in the string algebra
#                          ------       -------    constrain domain and codomain
#                                                  to contain non non-matching tests
#             ------------                         ---------- map to guarded strings
#                                                             on both sides.

###########################################
#
#   Aly's epistemic event and world relations
#
###########################################

# These are relations on events
define Ra1 [announce%_H:announce%_H | announce%_T:announce%_T];
define Ra2 [ aly%_peek%_H:aly%_peek%_H | bob%_peek%_H:[bob%_peek%_H|bob%_peek%_T] | aly%_peek%_T:aly%_peek%_T | bob%_peek%_T:[bob%_peek%_H|bob%_peek%_T]];

# Kripke relation on bare events for Aly.
define Ra0 Ra1 | Ra2;

undefine Ra1 Ra2;

# Corresponding relation on guarded strings.
# The intersection works because Event represents preconditions,
# and the fact that events don't change the non-epistemic state
# ==> Check this.
# ==> Think about whether his generalizes, e.g. to events
# such as flip that change the basic state.

define Rae [p:p Ra0 p:p] & [Event .x. Event];

# Extend Rae to worlds using Kleene plus.
# ===> This is so simple because Kleene plus enforces
#  preconditions. This is the core benefit of using KAT. That it's so
#  simple indicates that KAT is a natural setting for dynamic epistemic logic.

# Amy's epistemic world relation
define Ra p:p | Plr(Rae);

###########################################
#
# The same for Bob.
# Bob's epistemic event and world relations
#
###########################################

define Rb1 [announce%_H:announce%_H | announce%_T:announce%_T];
define Rb2 [ bob%_peek%_H:bob%_peek%_H | aly%_peek%_H:[aly%_peek%_H|aly%_peek%_T] | bob%_peek%_T:bob%_peek%_T | aly%_peek%_T:[aly%_peek%_H|aly%_peek%_T]];

define Rb0 [Rb1 | Rb2];

define Rbe [p:p Rb0 p:p] & [Event .x. Event];

define Rb p:p | Plr(Rbe);

###########################################
#
#  Worlds
#
###########################################

# Worlds are the Kleene closure of the events. Include tests
# without a following event.
define W p | Pl(Event);

########################################################
#
#  Insert tests in a string of events to make a world
#
########################################################

# This can be used to insert tests appropriately in an event
# sequence, e.g.
#   World({cd}) = H c H d H.
# It's not always a function. If we had a nop event o, World(o) = [H o H] | [T o T].

define World(X) [X .o. [0 -> p] .o. W].l;

########################################################
#
#  Diamond modality
#
########################################################

# R is a Kripke relation on W
# X is a proposition

define Dia(R,X) [R .o. X].u;

########################################################
#
#  Complement in W
#
########################################################

define Not(X) W - X; 

########################################################
#
#  Box modality
#
########################################################

# It's the dual of diamond.

define Box(R,X) Not(Dia(R,Not(X)));

# Perfective aspect.
# Event E has happened.
define Perf(E) Cn(Cn(W,Event(E)),W);

# Propositions it's heads and it's tails.
define Heads W & [?* H];
define Tails W & [?* T];





















echo -- One event.
define One Event;
echo -- Event
regex One;
print words
echo -------------------------------------


echo -- Two events.
define Two Cn(Event,Event);
echo -- Cn(Event,Event)
regex Two;
print words
echo -------------------------------------


echo -- 5a. Worlds where every alternative for aly is aly_peek_H
echo -- out intersection at the top.
echo -- i.e. aly_peek_H is the sole alternative for aly.
echo -- It should be the unit set of aly_peek_H.
echo -- Without the intersection we get longer worlds in epik
define AlyBoxAlyPeek (One & Box(Ra,World(aly%_peek%_H)));
echo -- (One & Box(Ra,World(aly_peek_H)))
regex AlyBoxAlyPeek;
print words
echo -------------------------------------


echo -- 5b. Similar but with iteration of belief.
define AlyBoxAlyPeek (One & Box(Ra,Box(Ra,World(aly%_peek%_H))));
echo -- (One & Box(Ra,Box(Ra,World(aly_peek_H))))
regex AlyBoxAlyPeek;
print words
echo -------------------------------------


echo -- 6a. Worlds where every alternative for aly is bob_peek_H
echo -- i.e. bob_peek_H is the sole alternative for aly.
echo -- This should be null. There is no way for aly to get this
echo -- information in one step.
define AlyBoxBobPeek (One & Box(Ra,World(bob%_peek%_H)));
echo -- (One & Box(Ra,World(bob_peek_H)))
regex AlyBoxBobPeek;
print words
echo -------------------------------------


echo -- 6b. Worlds where some alternative for aly is bob_peek_H
echo -- This should be bob_peek_H + bob_peek_T
define AlyBoxBobPeek (One & Dia(Ra,World(bob%_peek%_H)));
echo -- (One & Dia(Ra,World(bob_peek_H)))
regex AlyBoxBobPeek;
print words
echo -------------------------------------


echo -- 7. Worlds where every alternative for aly is of the form  (bob_peek_H.announce_H)
echo -- This lets Aly learn that it is H in the second event.
echo -- The result should be the unit set of bob_peek_H.announce_H.
define Example7 (Two & Box(Ra,Cn(World(bob%_peek%_H),World(announce%_H))));
echo -- (Two & Box(Ra,Cn(World(bob_peek_H),World(announce_H))))
regex Example7;
print words
echo -------------------------------------


echo -- 8. Similar but where the second event is any event.
echo -- The result should be bob_peek_H.announce_H + bob_peek_H.aly_peek_H
define Example8 (Two & Box(Ra,Cn(World(bob%_peek%_H),Event)));
echo -- (Two & Box(Ra,Cn(World(bob_peek_H),Event)))
regex Example8;
print words
echo -------------------------------------


echo -- 9a. Bob knows that Aly knows that Bob peeked T in the first step
echo -- The result should be bob_peek_H.announce_H + bob_peek_H.aly_peek_H
define Example9a (Two & Box(Rb,Box(Ra,Cn(World(bob%_peek%_T),Event))));
echo -- (Two & Box(Rb,Box(Ra,Cn(World(bob_peek_T),Event))))
regex Example9a;
print words
echo -------------------------------------


echo -- 9b. Bob knows that Aly knows that Aly peeked T in the first step
echo -- The result should be aly_peek_T;announce_T + aly_peek_T.bob_peek_T.
echo -- Aly peeks T in the first event and Bob figures it out in the second event.
define Example9b (Two & Box(Rb,Box(Ra,Cn(World(aly%_peek%_T),Event))));
echo -- (Two & Box(Rb,Box(Ra,Cn(World(aly_peek_T),Event))))
regex Example9b;
print words
echo -------------------------------------






