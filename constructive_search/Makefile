####  COMPILING AND LINKING OPTIONS  ####

#  Uncomment the following line, for Sun compilation at di.uoa.gr domain.
#CPATH = /usr/sfw/bin/

#  Uncomment the following line, for gcc versions greater than 4.2.
#STANDARD = -std=c++0x

# Naxos Directory
ND = ../

CC = $(CPATH)g++
WFLAGS = -pedantic -Wall -W -Wshadow
CFLAGS = $(WFLAGS) $(STANDARD) -O

LD = $(CC)
LDFLAGS = -s

RM = /bin/rm -f

####  SOURCE AND OUTPUT FILENAMES  ####

NQUEENS = nqueens

ALLPROGS = $(NQUEENS)

HDRS = $(ND)naxos.h $(ND)internal.h $(ND)stack.h
NOBJ = $(ND)local_search.o $(ND)problemmanager.o $(ND)expressions.o $(ND)var_constraints.o $(ND)array_constraints.o $(ND)intvar.o $(ND)bitset_domain.o

.PHONY: all
all: $(ALLPROGS)

####  BUILDING  ####

$(NQUEENS) :  $(NQUEENS).o
	$(LD) $(LDFLAGS) $(NOBJ) $(NQUEENS).o  -o $@

%.o :  %.cpp $(HDRS)
	$(CC) $(CFLAGS) -I$(ND) -c  $<

####  CLEANING UP  ####

TODEL = $(ALLPROGS) $(ALLPROGS:=.o)

.PHONY: clean
clean :
	$(RM)  $(TODEL)
