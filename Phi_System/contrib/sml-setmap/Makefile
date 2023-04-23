MLCOMP ?= mlkit

FLAGS=-output run

.PHONY: all
all:
	$(MLCOMP) $(FLAGS) set.mlb
	$(MLCOMP) $(FLAGS) mono_set.mlb
	$(MLCOMP) $(FLAGS) string_set.mlb
	$(MLCOMP) $(FLAGS) int_set.mlb
	$(MLCOMP) $(FLAGS) word_set.mlb
	$(MLCOMP) $(FLAGS) mono_map.mlb
	$(MLCOMP) $(FLAGS) string_map.mlb
	$(MLCOMP) $(FLAGS) int_map.mlb

.PHONY: clean
clean:
	rm -rf run MLB *~ */*~ */MLB
