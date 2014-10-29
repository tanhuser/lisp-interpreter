CC=gcc -std=c99  -g 

default: 
	$(CC) lisp.c -o lisp 

run: default
	chmod +x lisp
	./lisp

