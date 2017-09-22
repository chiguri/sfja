SHELL = /bin/bash

VOLUMES:=lf plf vfa

.PHONY: all clean html

all:
	for volume in $(VOLUMES); do cd $$volume && make && cd .. ; done

html:
	rm -rf html
	mkdir -p html/sfja
	for volume in $(VOLUMES); do cd $$volume && make html && cd .. && cp -r $$volume/html html/sfja/$$volume ; done
	cp index.html html/sfja/index.html
	cp -r common html/sfja/common

clean:
	for volume in $(VOLUMES); do cd $$volume && make clean && cd .. ; done
	rm -rf html
