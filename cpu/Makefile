################################################################################
#
# Muhammad Osama Mahmoud, Eindhoven University of Technology (TU/e).
# Mathematics and Computer Science Department, SET cluster.
# GEARS Project, All rights reserved.
#
################################################################################

# operating system
HOST_OS   := $(shell uname -s 2>/dev/null | tr "[:upper:]" "[:lower:]")
TARGET_OS ?= $(HOST_OS)
ifeq (,$(filter $(TARGET_OS),linux))
    $(error ERROR - unsupported value $(TARGET_OS) for TARGET_OS!)
endif

# current directory
PWD := $(shell pwd)

# target arch
TARGET_ARCH := $(shell uname -m)

# host compiler
HOST_COMPILER ?= g++

# target size
TARGET_SIZE := $(shell getconf LONG_BIT)

# compiler flags
CCFLAGS   := -m${TARGET_SIZE} -std=c++17 -pthread -fopenmp -Wno-format-zero-length
LDFLAGS   := 

# Debug build flags
WARN := -w 
ifeq ($(debug),1)
      CCFLAGS += -g
      BUILD_TYPE := debug
      WARN :=
else  ifeq ($(assert),1)
      CCFLAGS += -O3 -use_fast_math
      BUILD_TYPE := release
      WARN :=
else
      CCFLAGS += -O3 -use_fast_math -DNDEBUG
      BUILD_TYPE := release
endif

# Common includes 
INCLUDES  := -I$(PWD)/../lib/hong-ufscc/gm_graph/inc/ -I$(PWD)/../lib/hong-ufscc/src/
LIBRARIES := -L. -lpfrost
LIBRARIES += -L../lib/hong-ufscc -lhongufscc
LIBRARIES += -L../lib/hong-ufscc/gm_graph/lib -lgmgraph

# Target rules

mainsrc := pfmain.cpp
allsrc := $(sort $(wildcard *.cpp))
src := $(filter-out $(mainsrc),$(allsrc))
obj := $(patsubst %.cpp,%.o,$(src))

all: parafrost

libhongufscc.a:
	@cd ../lib/hong-ufscc; make 

libpfrost.a: $(obj)
	ar rc $@ $+
	ranlib $@

parafrost: pfmain.o libpfrost.a libhongufscc.a
	$(HOST_COMPILER) $(CCFLAGS) $(LDFLAGS) -o $@ pfmain.o $(LIBRARIES)
	mkdir -p build/$(BUILD_TYPE)
	cp $@ build/$(BUILD_TYPE)/

pfmain.o:pfmain.cpp
	$(HOST_COMPILER) $(INCLUDES) $(CCFLAGS) $(LDFLAGS) -o $@ -c $(WARN) $<

%.o:%.cpp
	$(HOST_COMPILER) $(INCLUDES) $(LIBRARIES) $(CCFLAGS) $(LDFLAGS) -o $@ -c $(WARN) $<

clean:
	rm -f *.o libpfrost.a parafrost  
	rm -rf build/$(BUILD_TYPE)/parafrost
