
.PHONY: all clean SATToBDDot BDDCal

all: SATToBDDot BDDCal

SATToBDDot:
	ghc -fno-warn-tabs -O4 SATToBDDot.hs -igen

BDDCal:
	ghc -fno-warn-tabs -O4 BDDCal.hs -igen

clean:
	rm -f SATToBDDot BDDCal *.hi *.o gen/*.hi gen/*.o
