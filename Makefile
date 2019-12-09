
CURRENT_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
TESTDIR = t
TESTS = $(wildcard $(TESTDIR)/*.maude)
TESTRUN = $(patsubst %.maude, .build/%.maude.run.timestamp ,$(TESTS))
PANDOC_TANGLE="ext/pandoc-tangle/tangle.lua"
MAUDE_BIN="$(CURRENT_DIR)/ext/maude-a120/maude"

.PHONY= clean

all:
	test

.build/copy-dependencies.timestamp : ext/maude-private/contrib/tools/rltool/rltool.maude
	@mkdir -p .build/ext && \
	 cp -r ext/maude-private .build/ext && \
	 touch $@

.build/imp.maude : imp.md .build/copy-dependencies.timestamp
	@export LUA_PATH="ext/pandoc-tangle/?.lua" && \
	 pandoc --from markdown --to $(PANDOC_TANGLE) --metadata=code:.maude $< >$@

.build/t/%.maude.timestamp : t/%.maude .build/imp.maude
	@mkdir -p .build/t && \
	 cp $< $(basename $@) && \
	 touch $@

.build/t/%.maude.run.timestamp : .build/t/%.maude.timestamp
	$(MAUDE_BIN) $(basename $<) > /dev/null && \
	touch $@

test : $(TESTRUN)

clean :
	rm -rf .build
