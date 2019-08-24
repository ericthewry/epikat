# Counterpart of epi1.k

# Source the world definition
source announce_peek.fst
set print-space ON

echo -------------------------
echo Worlds where the world public_announce_heads is a possibility for Alice.
echo There is just one.
echo regex Dia(Ra,World(a));
echo World(a) wraps the Kleene element a with tests.
regex Spell(Dia(Ra,World(a)));
print words
echo -------------------------

echo Worlds where the world public_announce_tails is a possibility for Alice.
echo regex Dia(Ra,World(b));
regex Spell(Dia(Ra,World(b)));
print words
echo -------------------------

echo Worlds where alice_peek_heads is a possibility for Alice.
echo There is just one possibility, because there are no other actions
echo that generate this option for alice.
echo Spell(Dia(Ra,World(c)));
regex Spell(Dia(Ra,World(c)));
print words
echo -------------------------

echo Worlds where bobby_peek_heads is a possibility for Alice.
echo It should be bobby_peek_heads + bobby_peek_tails.
echo regex Spell(Dia(Ra,World(d)));
regex Spell(Dia(Ra,World(d)));
print words
echo -------------------------

echo Box (universal) modality.
echo Worlds where every alternative for alice is alice_peek_heads,
echo i.e. alice_peek_heads is the sole alternative for alice.
echo regex Spell(Box(Ra,World(c)));
echo It should be alice_peek_heads.
regex Spell(Box(Ra,World(c)));
print words
echo -------------------------

echo Worlds where every alternative for alice is bobby_peek_heads,
echo i.e. bobby_peek_heads is the sole alternative for alice.
echo This should be null. There is no way for alice to get this
echo information in one step.
echo regex Spell(Box(Ra,World(d)));
echo It should be alice_peek_heads.
regex Spell(Box(Ra,World(d)));
print words
echo -------------------------

echo Worlds where some alternative for alice is (bobby_peek_heads ; public_announce_heads)
echo The result is the unit set of the complement.
echo The second event lets Alice figure out what happened in the first.
regex Spell(Dia(Ra, Cn(World(d),World(a)) ));
print words

echo Worlds where some alternative for alice is in (bobby_peek_heads ; public_announce_heads + public_announce_tails)
echo happens.
echo Or worlds that result for alice when something in (bobby_peek_heads ; public_announce_heads + public_announce_tails)
echo happens.
echo There are two results.
regex Spell(Dia(Ra, Cn(World(d) | World(f), World(a) | World(b)) ));
print words

echo Worlds where every alternative for alice is in (bobby_peek_heads ; public_announce_heads + public_announce_tails)
echo happens.
echo There are two results.
regex Spell(Box(Ra, Cn(World(d) | World(f), World(a) | World(b)) ));
print words


echo Worlds where every alternative for alice is in (bobby_peek_heads ; _)
echo happens.
echo The two results have in the second slot ways for Amy to learn what happened in the first.
regex Spell(Box(Ra, Cn(World(d), Act) ));
print words
