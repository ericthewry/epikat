test1.fm4: fst.m4 test1.base
	cat fst.m4 test1.base > test1.fm4
test1.km4: k.m4 test1.base
	cat k.m4 test1.base > test1.km4

test2.fm4: fst.m4 test2.base
	cat fst.m4 test2.base > test2.fm4
test2.km4: k.m4 test2.base
	cat k.m4 test2.base > test2.km4

%.fst: %.fm4
	m4 $*.fm4 | gawk -f escape.awk > $*.fst
%.k: %.km4
	m4 $*.km4 > $*.k


epi1-test1.fst: epi1.fst test1.fst
	echo 'set print-space ON' > epi1-test1.fst
	cat epi1.fst test1.fst >> epi1-test1.fst
epi1-test1.k: epi1.k test1.k
	cat epi1.k test1.k > epi1-test1.k

epi1-test2.fst: epi1.fst test2.fst
	echo 'set print-space ON' > epi1-test2.fst
	cat epi1.fst test2.fst >> epi1-test2.fst
epi1-test2.k: epi1.k test2.k
	cat epi1.k test2.k > epi1-test2.k


epi1-test1.fst.out: epi1-test1.fst
	xfst -q -f epi1-test1.fst > epi1-test1.fst.out

epi1-test1.fst.out.pdf : epi1-test1.fst.out
	enscript -b epi1-test1.fst.out -o epi1-test1.fst.out.ps epi1-test1.fst.out
	ps2pdf epi1-test1.fst.out.ps
	rm epi1-test1.fst.out.ps

epi1-test2.fst.out: epi1-test2.fst
	xfst -q -f epi1-test2.fst > epi1-test2.fst.out

epi1-test2.fst.show: epi1-test2.fst
	xfst -q -f epi1-test2.fst

epi1-test2.fst.out.pdf : epi1-test2.fst.out
	enscript -b epi1-test2.fst.out -o epi1-test2.fst.out.ps epi1-test2.fst.out
	ps2pdf epi1-test2.fst.out.ps
	rm epi1-test2.fst.out.ps

clean:
	rm test*.fst test*.k test*.km4 test*.fm4


