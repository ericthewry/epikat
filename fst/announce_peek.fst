# Shortened version of kt2, with just the six events a-f.
# The guarded string algebra is embedded in a string algebra.

# Guarded strings start and end with a propositions, and have
# propositions alternating with events.
# Examples:
# HkHaHhHoHkH
# TjTmT
# HcHkH
# TiTiTbTeTmTeT

# Basic proposition, head or tails.
# In the mathematical presentation, we use 0 and 1.
# Heads
# define H "1";
# Tails
# define T "0";

# But in development, use H and T, they are easier to read.
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

# Table of actions as Kleene elements.

# a public announcement/sensing that H
# b public announcement/sensing that T
# c Amy sensing H, with Bob aware that Amy is sensing, but not what she senses.
# d Bob sensing H, semi-privately (as above)
# e Amy sensing T, semi-privately
# f Bob sensing T, semi-privately

# Preconditions
# a H
# b T
# c H
# d H
# e T
# f T

# define Act [a | b | c | d | e | f ];

# Kleene elements with precondition satisfied in an H-world.
# These can increment an H-world. NOP is included.
define ActH0 [a | c | d ];

# The corresponding guarded strings, with a test at the start and the end,
# surrounding the Kleene emement. 
define ActH [H ActH0 H];

# Kleene elements with precondition satisfied in a T-world.
# These can increment a T-world. NOP is included.
define ActT0 [b | e | f ];

# The corresponding guarded string, with a test at the start and the end.
define ActT [T ActT0 T];

# Acts in general.
define Act [ActH | ActT];
define Act0 [ActH0 | ActT0]; 

# Map to an act.
define Event(X) [p X p] & Act;

# The above represents the precondition of Kleene elements in the set Act.
# The weakest precondition of an Kleene element x is {q|qxq is an element of Act}.

# Reduce a sequence of two tests to a single test, by deleting the second one.
define Squash p -> 0 || p _;

# Doesn't contain a bad test pair
define Wf0 ~[$ ppIf];

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
define Short0 p -> 0 || Act0 _ Act0;
define Short(X) [X .o. Short0].l;

# Kleene Plus
define Pl(X) [[[X+] & Wf0] .o. Squash].l; 
#              --- Kleene plus in the string algebra
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

###########################################
#
# Amy's epistemic event and world relations
#
###########################################
# First five lines are from bm2.fst
# These are relations on Kleene elements.
define Ra1 [a:a | b:b];
define Ra2 [c:c| d:[d|f] | e:e | f:[d|f]];

# Kripke relation on Kleene elements (bare events)
# for Amy.
define Ra0 Ra1 | Ra2;

undefine Ra1 Ra2;

# Corresponding relation on Kleene elements flanked
# by tests.  The intersection works because Act represents preconditions,
# and the fact that events don't change the non-epistemic state
# ==> Check this.
# ==> Think about whether his generalizes, e.g. to events
# such as flip that change the basic state.

define Rae [p:p Ra0 p:p] & [Act .x. Act];

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

define Rb1 [a:a | b:b];
define Rb2 [c:[c|e] | d:d | e:[c|e] | f:f];

define Rb0 [Rb1 | Rb2];

define Rbe [p:p Rb0 p:p] & [Act .x. Act];

define Rb p:p | Plr(Rbe);

###########################################
#
#  Worlds
#
###########################################

# Worlds are the Kleene closure of the events. Include tests
# without a following event.
define W p | Pl(Act);

########################################################
#
#  Insert tests in a string of events to make a world
#
########################################################

# This can be used to insert tests appropriately in an event
# sequence, e.g.
#   World({cd}) = H c H d H.
# It's not a function, World(o) = [H o H] | [T o T].

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

define Box(R,X) Not(Dia(R,Not(X)));


########################################################
#
#  Relation that puts a world in the long notation
#
########################################################

define eventlong [ a : public%_announce%_heads |
                    b : public%_announce%_tails |
                    c : alice%_peek%_heads | 
                    d : bobby%_peek%_heads |
		    e : alice%_peek%_tails | 
                    f : bobby%_peek%_tails ];

define worldlong [p eventlong]* p;

define Spell(X) [X .o. worldlong].l;

# E should be a bare event
define Have(E) Cn(Cn(W,Event(E)),W);

# Propositions it's heads and it's tails.
define Heads W & [?* H];
define Tails W & [?* T];

