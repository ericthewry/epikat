%.k: %.kc
	cat $*.kc | egrep -v '^--' > $*.k

%.k.out: %.k
	stack exec epik-exe 8 $*.k > $*.k.out
%.f.out: %.k
	xfst -q -f $*.fst  > $*.f.out

%.k.show: %.k
	stack exec epik-exe 8 $*.k
%.f.show: %.fst
	xfst -q -f $*.fst

%.kf.pdf: %.k.out %.f.out
	enscript -b$* -o $*.k.out.ps $*.k.out
	enscript -b$* -o $*.f.out.ps $*.f.out
	ps2pdf $*.k.out.ps $*.k.out.pdf
	ps2pdf $*.f.out.ps $*.f.out.pdf
	pdftk $*.k.out.pdf $*.f.out.pdf cat output $*.kf.pdf
	rm $*.k.out.ps $*.f.out.ps $*.k.out.pdf $*.f.out.pdf

%.pdf: %.hs
	enscript -b' ' -o $*.ps $*.hs
	ps2pdf $*.ps $*.pdf
	rm $*.ps



