TESTDIR = t
TESTS = $(wildcard $(TESTDIR)/*.maude)
TESTRUN = $(patsubst %.maude,%.run,$(TESTS))

all:
	sh build

test: $(TESTRUN)

%.run: %.maude
	-sh run $< &> /dev/null
