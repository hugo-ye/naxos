####  COMPILING AND LINKING OPTIONS  ####

#  Uncomment the following line, for Sun compilation at di.uoa.gr domain.
#CPATH = /usr/sfw/bin/

#  Uncomment the following line, for gcc versions greater than 4.2.
#STANDARD = -std=c++0x

CC = $(CPATH)g++
WFLAGS = -pedantic -Wall -W -Wshadow
CFLAGS = $(WFLAGS) $(STANDARD) -O

LD = $(CC)
LDFLAGS = -s

RM = /bin/rm -f

####  SOURCE AND OUTPUT FILENAMES  ####

HDRS =  naxos.h internal.h stack.h
SRCS =  local_search.cpp problemmanager.cpp expressions.cpp var_constraints.cpp array_constraints.cpp intvar.cpp bitset_domain.cpp

OBJS = $(SRCS:.cpp=.o)

.PHONY: all
all:  $(OBJS)

####  BUILDING  ####

%.o :  %.cpp $(HDRS)
	$(CC) $(CFLAGS) -c  $<

####  CLEANING UP  ####

TODEL = $(OBJS)

.PHONY: clean
clean :
	$(RM)  $(TODEL)
