TARGETS=SATToBDDot BDDCal Urquhart Sudoku

.PHONY: all clean $(TARGETS)

all: $(TARGETS)

$(TARGETS):
	ghc -fno-warn-tabs -O2 -rtsopts $@.hs -igen

clean:
	rm -f $(TARGETS) *.hi *.o gen/*.hi gen/*.o
