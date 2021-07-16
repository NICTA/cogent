#
# Copyright 2017, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

# The name of our source file
NAME=Kernel

# Location of the Cogent repository
REPO=../../..

# Our input source file, output targets
SRC=$(NAME).cogent
OUTPUT=kernel
COUTPUT=$(addsuffix .c, $(OUTPUT))
HOUTPUT=$(addsuffix .h, $(OUTPUT))

# Location of output files
BUILD_DIR=build

# Location of Cogent stdlib
LIBGUM=$(shell cogent --libgum-dir)

# Compile with the right wrapper file depending on what we want to build
system: PLAT_DIR = plat/system/
verification: PLAT_DIR = plat/verification/

ACFILES = wrapper.ac

# Preprocessed and inferred antiquoted C files
PP      = $(ACFILES:.ac=_pp.ac)
PPINFER = $(ACFILES:.ac=_pp_inferred.c)

# Compilation objects
OBJ     = $(PPINFER:.c=.o)

# Extra flags for the C compiler
CFLAGS=-I. -I$(LIBGUM) -I$(LIBGUM)/gum/anti -std=gnu99 -I$(BUILD_DIR)

# Common flags for the cogent compiler
COGENT_FLAGS=--Wno-warn \
			 --root-dir="$(REPO)" \
			 --dist-dir=$(BUILD_DIR) \
			 --cpp-args="\$$CPPIN -o \$$CPPOUT -P $(CFLAGS)" \
			 --ext-types=types.cfg \
			 --entry-funcs=entrypoints.cfg

.PHONY: default all clean system verification

default: all

all: system verification

# Compile the actual code for running
system: $(BUILD_DIR)/${OBJ} .system
	$(CC) -o $(OUTPUT) $<

$(BUILD_DIR)/$(OBJ): .system
	$(CC) -c -o $@ $(BUILD_DIR)/$(PPINFER)  $(CFLAGS)

.system:
	mkdir -p $(BUILD_DIR)
	# Compile the Cogent source
	cogent $(SRC) -g -o$(OUTPUT) \
		$(COGENT_FLAGS) \
		--infer-c-funcs="$(PLAT_DIR)/$(ACFILES)" 

# Compile cogent source and generate all verification files
verification:
	mkdir -p $(BUILD_DIR)
	cogent $(SRC) -A -o$(OUTPUT) \
		$(COGENT_FLAGS) \
		--infer-c-funcs="$(PLAT_DIR)/$(ACFILES)" \
		--proof-input-c=wrapper_pp_inferred.c \
		--proof-name=$(NAME) 
	cp "$(BUILD_DIR)/$(OUTPUT).table" "$(BUILD_DIR)/wrapper_pp_inferred.table"

clean:
	rm -rf $(BUILD_DIR)
	rm -rf $(OUTPUT)
