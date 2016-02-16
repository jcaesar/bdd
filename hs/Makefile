TARGETS=SATToBDDot BDDCal Urquhart

.PHONY: all clean $(TARGETS)

all: $(TARGETS)

$(TARGETS):
	ghc -fno-warn-tabs -O4 $@.hs -igen

clean:
	rm -f SATToBDDot BDDCal *.hi *.o gen/*.hi gen/*.o
