
OBJS = bit_reverse.o \
       newHopeNTT.o  \
       newHopeNTTMasuda.o

nttTest: $(OBJS) nttTest.c
	gcc -o $@ $^

bit_reverse.o: bit_reverse.c
	gcc -c $< -o $@

newHopeNTT.o: newHopeNTT.c
	gcc -c $< -o $@

newHopeNTTMasuda.o: newHopeNTTMasuda.c
	gcc -c $< -o $@

debug: newHopeNTT_debug.c

clean:
	rm $(OBJS) nttTest
