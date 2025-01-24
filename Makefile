# TP6, given functions


rsa: mpint.o rsa.o
	gcc -o rsa mpint.o rsa.o -lm

mpint.o: mpint.c mpint.h
	gcc -o mpint.o -c mpint.c -lm

rsa.o: rsa.c mpint.h rsa.h
	gcc -o rsa.o -c rsa.c -lm

