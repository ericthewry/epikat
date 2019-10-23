define(Cn,Cn($1,$2))
define(And,($1 & $2))
define(Not,Not($1))

define(Ev,`Event')

define(Com,echo -- $1)


define(Aly,Dia(Ra,$1))
define(Bob,Dia(Rb,$1))
define(Boxaly,Box(Ra,$1))
define(Boxbob,Box(Rb,$1))

define(Query,define $1 $2;
echo -- $2
regex $1;
print random-words)

define(Query2,define $1 $2;
echo -- $2
regex $1;
print words
echo -------------------------------------
)


