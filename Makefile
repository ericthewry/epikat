%.k: %.kc
	cat $*.kc | egrep -v '^--' > $*.k

%.out: %.k
	stack exec epik-exe 8 $*.k > $*.out

%.show: %.k
	stack exec epik-exe 8 $*.k

%.pdf: %.k %.out
	enscript -b' ' -o $*.out.ps $*.out
	enscript -b' ' -o $*.k.ps $*.k
	ps2pdf $*.out.ps $*.out.pdf
	ps2pdf $*.k.ps $*.k.pdf
	rm $*.out.ps $*.k.ps

%.pdf: %.hs
	enscript -b' ' -o $*.ps $*.hs
	ps2pdf $*.ps $*.pdf
	rm $*.ps



